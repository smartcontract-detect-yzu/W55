import inspect
from collections import namedtuple, defaultdict
import os
import subprocess
from typing import List, Set, Union, Tuple
from slither.slither import Slither
from src.contract_info_collector import ContractInfoCollector
from slither.detectors import all_detectors
from slither.detectors.abstract_detector import AbstractDetector, DetectorClassification
from slither.core.compilation_unit import SlitherCompilationUnit
from slither.core.variables import Variable, StateVariable
from slither.core.cfg.node import Node, NodeType
from slither.core.declarations.function import Function, FunctionType, FunctionLanguage
from slither.detectors.reentrancy.reentrancy import AbstractState
from rich.console import Console
import networkx  as nx
from slither.core.declarations import Contract
import networkx.drawing.nx_pydot as nx_dot

FindingKey = namedtuple("FindingKey", ["function", "calls", "send_eth"])
FindingValue = namedtuple("FindingValue", ["variable", "node", "nodes"])

def debug_get_graph_png(graph: nx.Graph, postfix):

    dot_name = "{}_{}.dot".format(graph.graph["name"], postfix)
    cfg_name = "{}_{}.png".format(graph.graph["name"], postfix)
    nx_dot.write_dot(graph, dot_name)

    subprocess.check_call(["dot", "-Tpng", dot_name, "-o", cfg_name])
    os.remove(dot_name)

class ReDetector:

    def __init__(self, contract_info:ContractInfoCollector) -> None:
        self.contract_info = contract_info
        self.slither:Slither = contract_info.slither
        self.compilation_units:List[SlitherCompilationUnit] = self.slither.compilation_units
        self.rich_console = Console()
        self.context_key = "REENTRANCY"
        self.cfg = None


    def _display_statement_context(self, stmt:Node, info_type):
        """
            打印重入漏洞相关上下文信息（此处只有上文信息）
        """
        if self.context_key not in stmt.context:
            print(f"\t{stmt.expression}")
            print("NOTE: 该语句不包含与重入漏洞相关信息")
            return
        
        print(f"\n\t语句: {stmt.expression} 的 {info_type} 上下文信息")
        current_statement_state:AbstractState = stmt.context[self.context_key]

        if info_type == "send_eth":
            """
                打印当前语句(current_statement)前文中所有可以send_eth的语句, 且包含过程间分析
            """
            for idx, context_stmt in enumerate(current_statement_state.send_eth):
                print(f"\t\t-CONTEXT_STMT[{idx}] {context_stmt}:")
                for n in current_statement_state.send_eth[context_stmt]:
                    print(f"\t\t\t-SEND_ETH@:[{idx}] {n.expression}:") # 具体执行操作的语句, 包含过程间分析
                    

        elif info_type == "calls":
            """
                打印当前语句(current_statement)前文中所有外部调用的语句, 且包含过程间分析
            """
            for idx, context_stmt in enumerate(current_statement_state.calls):
                print(f"\t\t-CONTEXT_STMT[{idx}] {context_stmt}")
                for n in current_statement_state.calls[context_stmt]:
                    print("\t\t\t-CALL@", n.expression)
            
        elif info_type == "reads":
            """
                打印当前语句(current_statement)前文中所有读取的全局变量, 且包含过程间分析
            """
            for idx, state_var in enumerate(current_statement_state.reads):
                print(f"\t\t-READ_STATE_VAR[{idx}] NAME: {state_var.name}")
                for n in current_statement_state.reads[state_var]:
                    print("\t\t\t-READ@", n.expression, " IN ", n.function.name)


        elif info_type == "written":
            """
                打印当前语句(current_statement)前文中所有修改的全局变量, 且包含过程间分析
            """
            for idx, state_var in enumerate(current_statement_state.written):
                print(f"\t\t-WRITE_STATE_VAR[{idx}] NAME: {state_var.name}")
                for n in current_statement_state.reads[state_var]:
                    print("\t\t\t-WRTIE@", n.expression, " IN ", n.function.name)

        elif info_type == "reads_prior_calls":
            """
                打印当前语句(current_statement)前文中所有在call操作之前读取的全局变量, 且包含过程间分析
            """
            for idx, context_stmt in enumerate(current_statement_state.reads_prior_calls):
                print(f"\t\t-CONTEXT_STMT[{idx}] {context_stmt}")
                for state_var in current_statement_state.reads_prior_calls[context_stmt]:
                    print("\t\t\t-READ_PRE_CALL@", state_var.name, " IN ", context_stmt.function.name)

        elif info_type == "events":
            pass
        else:
            print("ERROR: 错误的上下文特征类型")


    def get_function_cfg(self, fun:Function, c:Contract):
        cfg_dot_file = "{}_cfg.dot".format(fun.name)
        fun.cfg_to_dot(cfg_dot_file)

        cfg: nx.DiGraph = nx.drawing.nx_agraph.read_dot(cfg_dot_file)
        cfg.graph["name"] = fun.name
        cfg.graph["contract_name"] = c.name

        if len(cfg.nodes) == 0:
            raise RuntimeError("没有CFG")
        
        leaf_nodes = []
        for cfg_node_id in cfg.nodes:
            if cfg.out_degree(cfg_node_id) == 0:  # 叶子节点列表
                leaf_nodes.append(cfg_node_id)
            
        cfg.add_node("EXIT_POINT", label="EXIT_POINT")
        for leaf_node in leaf_nodes:
            cfg.add_edge(leaf_node, "EXIT_POINT")

        # for node in fun.nodes:
        #     cfg_node = cfg.nodes[str(node.node_id)]
        #     new_label = "ID:{} {}".format(str(node.node_id), cfg_node["label"])
        #     cfg_node["label"] = new_label
        #     cfg_node["expression"] = node.expression.__str__()
        #     if cfg_node["expression"] is None:
        #         cfg_node["expression"] = cfg_node["label"]
        #     cfg_node["type"] = node.type.__str__()
        #     cfg_node["fid"] = fun.id
        #     cfg_node["node_id"] = node.node_id

        return cfg


    def get_stmt_interaction(self, stmt:Node):
        
        if self.context_key not in stmt.context:
            return None
        
        current_statement_state:AbstractState = stmt.context[self.context_key]
        if stmt not in current_statement_state.calls:
             return None
        
        print("\n",stmt.expression)
        call_stmts = current_statement_state.calls[stmt]
        for call_stmt in call_stmts:
            print("\t-当前语句的操作：", call_stmt.expression)
            print([c.name for c in call_stmt.internal_calls])
            print([str(c) for c in call_stmt.external_calls_as_expressions])
            for (_c, _t) in call_stmt.high_level_calls:
                print(_c.name, _t.name)
            print([(v.name, str(v.type)) for v in call_stmt._vars_read])

            



    def do_interact_effect_analyze(self, target_func:Function):
        """
            分析当前函数中在interact之后修改的全局变量
        """
        for node in target_func.nodes:
            
            if self.context_key not in node.context:
                continue    # unrelated code
            
            if node.context[self.context_key].calls:

                if not any(n != node for n in node.context[self.KEY].calls):  
                    continue    # 跳过interact语句
                
                """
                    interact 之后的语句:寻找修改 state variable 的语句 (effect)
                """
                # 1. memory _A = A[id]; --then--> _A += 1;
                read_then_written = []
                for c in node.context[self.KEY].calls:
                    read_then_written += [
                        v
                        for v in node.context[self.KEY].written
                        if v in node.context[self.KEY].reads_prior_calls[c]
                    ]
                
                # 2. not in 1 & A[id] += 1
                not_read_then_written = {
                    FindingValue(
                        v,
                        node,
                        tuple(sorted(nodes, key=lambda x: x.node_id)),
                    )
                    for (v, nodes) in node.context[self.KEY].written.items()
                    if v not in read_then_written
                }

    def do_interact_effect_check(self):

       _re_detector = getattr(all_detectors, "ReentrancyEth") # 随便找一个
       self.slither.register_detector(_re_detector)
       self.slither.run_detectors() # 主要目标是利用底层的reentrant检测器
       
       for unit in self.compilation_units:
           for contract in unit.contracts:
               for function in contract.functions:
                   
                   if function.name != "withdraw": # 指定分析对象
                       continue
                   
                   cfg = self.get_function_cfg(function, contract)
                   debug_get_graph_png(cfg, "cfg")
                   
                   if "REENTRANCY" in function.context.keys() and function.context["REENTRANCY"] == True:
                       self.rich_console.rule(f"可疑函数：{function.name}")
                       
                       for stmt in function.nodes:
                           self.get_stmt_interaction(stmt)
                       

                          

                        
                    




