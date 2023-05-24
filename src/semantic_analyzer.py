from collections import defaultdict
import json
import subprocess
import networkx as nx
from typing import Dict
from slither.slither import Slither
from slither.printers.abstract_printer import AbstractPrinter
from slither.core.declarations.contract import Contract
from slither.core.declarations.solidity_variables import SolidityFunction
from slither.core.declarations.function import Function as SFunction
from slither.core.declarations import Contract as SContract
from slither.core.declarations.function_contract import FunctionContract
from slither.core.variables.variable import Variable
import networkx.drawing.nx_pydot as nx_dot
from networkx.algorithms import tournament
from src.function_analyzer import FunctionAnalyzer
from src.contract_info_collector import ContractInfoCollector
from slither.core.cfg.node import Node, NodeType
from slither.core.declarations import SolidityVariableComposed
from slither.core.variables.local_variable import LocalVariable
from slither.core.variables.state_variable import StateVariable
from rich.console import Console

RE_INTERACTION = "re"
LLC_INTERACTION = "low-level call"
MINT_INTERACTION = "mint"
NORMAL_INTERACTION = "normal"

RICH_ERROR = "[red bold underline]"
RICH_WARNING = "[yellow bold]"
RICH_INFO = "[blue]"
CAN_HIJACKED_MAP = {RE_INTERACTION:1 ,LLC_INTERACTION:1, MINT_INTERACTION:0, NORMAL_INTERACTION:0}

SEMANTIC_DEBUG_FLAG = False

def _contract_subgraph(contract):
    return f"cluster_{contract.id}_{contract.name}"


# return unique id for contract function to use as node name
def _function_node(contract, function):
    return f"{contract.id}_{function.name}"


# return unique id for solidity function to use as node name
def _solidity_function_node(solidity_function):
    return f"{solidity_function.name}"


# return dot language string to add graph edge
def _edge(from_node, to_node):
    return f'"{from_node}" -> "{to_node}"'


# return dot language string to add graph node (with optional label)
def _node(node, label=None):
    return " ".join(
        (
            f'"{node}"',
            f'[label="{label}"]' if label is not None else "",
        )
    )


# pylint: disable=too-many-arguments
def _process_internal_call(
    contract,
    function,
    internal_call,
    contract_calls,
    solidity_functions,
    solidity_calls,
):
    if isinstance(internal_call, (SFunction)):
        contract_calls[contract].add(
            _edge(
                _function_node(contract, function),
                _function_node(contract, internal_call),
            )
        )
    elif isinstance(internal_call, (SolidityFunction)):
        solidity_functions.add(
            _node(_solidity_function_node(internal_call)),
        )
        solidity_calls.add(
            _edge(
                _function_node(contract, function),
                _solidity_function_node(internal_call),
            )
        )


def _render_external_calls(external_calls):
    return "\n".join(external_calls)


def _render_internal_calls(contract, contract_functions, contract_calls):
    lines = []

    lines.append(f"subgraph {_contract_subgraph(contract)} {{")
    lines.append(f'label = "{contract.name}"')

    lines.extend(contract_functions[contract])
    lines.extend(contract_calls[contract])

    lines.append("}")
    
    return "\n".join(lines)


def _render_solidity_calls(solidity_functions, solidity_calls):
    lines = []

    lines.append("subgraph cluster_solidity {")
    lines.append('label = "[Solidity]"')

    lines.extend(solidity_functions)
    lines.extend(solidity_calls)

    lines.append("}")

    return "\n".join(lines)


def _process_external_call(
    contract,
    function,
    external_call,
    contract_functions,
    external_calls,
    all_contracts,
):
    external_contract, external_function = external_call

    if not external_contract in all_contracts:
        return

    # add variable as node to respective contract
    if isinstance(external_function, (Variable)):
        contract_functions[external_contract].add(
            _node(
                _function_node(external_contract, external_function),
                external_function.name,
            )
        )

    external_calls.add(
        _edge(
            _function_node(contract, function),
            _function_node(external_contract, external_function),
        )
    )


# pylint: disable=too-many-arguments
def _process_function(
    contract,
    function,
    contract_functions,
    contract_calls,
    solidity_functions,
    solidity_calls,
    external_calls,
    all_contracts,
):
    contract_functions[contract].add(
        _node(_function_node(contract, function), function.name),
    )

    for internal_call in function.internal_calls:
        _process_internal_call(
            contract,
            function,
            internal_call,
            contract_calls,
            solidity_functions,
            solidity_calls,
        )
    for external_call in function.high_level_calls:
        _process_external_call(
            contract,
            function,
            external_call,
            contract_functions,
            external_calls,
            all_contracts,
        )


def _process_functions(functions):
    contract_functions = defaultdict(set)  # contract -> contract functions nodes
    contract_calls = defaultdict(set)  # contract -> contract calls edges

    solidity_functions = set()  # solidity function nodes
    solidity_calls = set()  # solidity calls edges
    external_calls = set()  # external calls edges

    all_contracts = set()

    for function in functions:
        all_contracts.add(function.contract_declarer)

    for function in functions:
        _process_function(
            function.contract_declarer,
            function,
            contract_functions,
            contract_calls,
            solidity_functions,
            solidity_calls,
            external_calls,
            all_contracts,
        )

    render_internal_calls = ""
    for contract in all_contracts:
        render_internal_calls += _render_internal_calls(
            contract, contract_functions, contract_calls
        )

    render_solidity_calls = _render_solidity_calls(solidity_functions, solidity_calls)

    render_external_calls = _render_external_calls(external_calls)

    return render_internal_calls + render_solidity_calls + render_external_calls

class SemanticAnalyzer:

    def __init__(self, contract_info:ContractInfoCollector, target_dir) -> None:
        
        self.contract_info = contract_info
        self.slither = contract_info.slither
        self.target_dir = target_dir
        self.target_log_dir = target_dir + "/log"
        self.call_graph_file = self.target_dir + "/log/call_graph.dot"

        #* 打印重要提示信息
        self.rich_console = Console()
        self.rich_error = "[red bold underline]"
        self.rich_warning = "[yellow bold]"
        self.rich_info = "[blue]"
        
        #* 初始情况下不能分析辅助对象
        self.auxiliary_analyze = False
              
        # 当前合约的相关成分
        self.all_functions_as_dict: Dict[str, FunctionContract] = None
        self.function_info_map = {}
        self.function_implement_map = {}
        self.contracts_calls_relations: Dict[str, set()] = {}  # contract -> contract calls edges
        self.all_contracts = set()
        self.all_construct_state_vars = set() # 在構造函數中定義的變量

        # 当前项目的call graph
        self.call_graph = nx.DiGraph(name="cg")

        # 函數相關分析器
        self.functions_analyzers: Dict[str, FunctionAnalyzer]= {}
        self.functions_analyzers_second: Dict[str, FunctionAnalyzer]= {}
        
    def add_function_analyzer(self, analyzer:FunctionAnalyzer):
        self.functions_analyzers[analyzer.key] = analyzer
        
    def get_function_analyzer(self, target_function:SFunction) -> FunctionAnalyzer:
        """
        构建当前函数的函数分析器, 并初始化
        Args:
            c (SContract): 目标合约
            f (SFunction): 目标函数
        """
        
        target_contract = target_function.contract_declarer
        slither = self.slither
        
        #* 为了避免主分析对象和辅助分析对象的函数id重复，此处需要contract和function的id一起组key
        analyzer_key = f"{target_contract.id}-{target_function.id}"  
        if analyzer_key in self.functions_analyzers: return self.functions_analyzers[analyzer_key]
        
        function_analyzer = FunctionAnalyzer(target_contract, target_function, slither, self.call_graph, self.target_dir)
        if False == function_analyzer.analyze_function_initialize():
            self.rich_console.print(f"{RICH_ERROR} 函数 {target_contract.name}-{target_function.name} 没有 CFG")
            return None #! 生成CFG失败直接退出
        
        #* 一些信息在初始化过程中就需要创建
        function_analyzer.all_construct_state_vars = self.all_construct_state_vars
        function_analyzer.get_all_written_storage_vars()
        
        self.add_function_analyzer(function_analyzer)
        return function_analyzer

    def get_construct_state_variables(self):
        """
            在構造函數裏設置的全局變量
        """
        
        for construct_function in self.contract_info.construct_functions:
            for stmt_info in construct_function.nodes:
                for state_var in stmt_info.state_variables_written:
                    self.all_construct_state_vars.add(state_var)
    
    def get_selfimplemented_risky_functions_call_chain(self):
        
        """
        函数直接调用自己定义的 financial risk函数例如mint, 而非进行外部调用, 所以这些信息在语句的context中是没有的
        对于这种直接调用的情况
        我们手动添加interaction point
        """
        
        for pub_fid in self.contract_info.public_functions:
            
            if str(pub_fid) not in self.call_graph.nodes: continue
            pub_f:SFunction = self.contract_info.public_functions[pub_fid]['f']
            
            for self_fr_fid in self.contract_info.selfimplemented_finical_risk_functions:
                
                if str(pub_fid) == str(self_fr_fid): continue
                
                #*判断当前的public函数能否调用自定义的危险函数
                reachable = nx.has_path(self.call_graph, str(pub_fid), str(self_fr_fid))
                if reachable == True:
                    self_risk_function:SFunction = self.contract_info.selfimplemented_finical_risk_functions[self_fr_fid]
                    paths = nx.all_shortest_paths(self.call_graph, str(pub_fid), str(self_fr_fid))
                    called_fun_id = list(paths)[0][1]
                    called_fun:SFunction = self.call_graph.nodes[called_fun_id]["f"]

                    pub_fanalyer:FunctionAnalyzer = self.get_function_analyzer(pub_f)
                    called_stmt:Node = pub_fanalyer.get_called_function_stmt(called_fun)

                    #! 調用了自定義的mint函數，則調用的入口函數被認爲存在financial risk
                    pub_fanalyer.interaction_points[str(called_stmt.node_id)] = {
                        "stmt":called_stmt, 
                        "to_c":self_risk_function.contract_declarer,
                        "to_f":self_risk_function, 
                        "action_type": "mint",
                        "data_dependeds": [],
                        "control_dependeds": [],
                        "balance_dependeds": [],
                        "need_cross_contract_analysis": [],
                    }
                    #* 此处仅做初始化，其属性分析由后续接口完成
                    pub_fanalyer.interaction_points_properties[str(called_stmt.node_id)] = {}
                    
                    print(f"函數{pub_f.name} 在語句 {called_stmt.expression} 間接調用自定義mint函數 {self_risk_function.name}")
                    break
                    
    def get_call_graph(self):

        # Avoid duplicate functions due to different compilation unit
        all_functionss = [
            compilation_unit.functions for compilation_unit in self.slither.compilation_units
        ]
        all_functions = [item for sublist in all_functionss for item in sublist]
        self.all_functions_as_dict = {
            function.canonical_name: function for function in all_functions
        }

        for function in all_functions:
            if function.full_name not in self.function_info_map:
                 self.function_info_map[function.full_name] = {}
            if str(function.id) not in self.function_info_map[function.full_name]:
                self.function_info_map[function.full_name][str(function.id)] = function
            
        #* 当同一个函数名出现两个以上，则表明该函数会有多种不同的实现版本，但是它的ID是唯一的
        for function_name in self.function_info_map:
            if len(self.function_info_map[function_name]) > 1:
                self.function_implement_map[function_name] = {"implemented":[], "none":[]}
                
                _functions_map = self.function_info_map[function_name]
                for _f_id in _functions_map:
                    if _functions_map[_f_id].is_implemented == None:
                        self.function_implement_map[function_name]["none"].append(_functions_map[_f_id])
                    else:
                        self.function_implement_map[function_name]["implemented"].append(_functions_map[_f_id])
        
        # 获得所有的合约列表
        for function in self.all_functions_as_dict.values():
            _contract:Contract = function.contract_declarer
            self.all_contracts.add(_contract)

            if str(_contract.id) not in self.contracts_calls_relations:
                self.contracts_calls_relations[str(_contract.id)] = set()

        # 获得所有函数内部的调用关系
        for function in self.all_functions_as_dict.values():
            current_contract:Contract = function.contract_declarer
            for internal_call in function.internal_calls:
                if isinstance(internal_call, (SFunction)):
                    
                    call_relation = {
                        "from_c": current_contract,
                        "from_f": function,
                        "to_c": current_contract,
                        "to_f": internal_call
                    }
                    self.contracts_calls_relations[str(current_contract.id)].add(tuple(call_relation.values()))
                    
                    if internal_call.full_name not in self.function_info_map: continue
                    
                    #* 其它替换的函数
                    substitutes:Dict[str, SFunction] = self.function_info_map[internal_call.full_name]
                    for fid in substitutes:
                        if fid != str(internal_call.id):
                            implemented_internal_call = substitutes[fid]
                            addtion_call_relation = {
                                "from_c": current_contract,
                                "from_f": function,
                                "to_c": current_contract,
                                "to_f": implemented_internal_call
                            }
                            self.contracts_calls_relations[str(current_contract.id)].add(tuple(addtion_call_relation.values()))

            for (external_contract, external_function) in function.high_level_calls:
                if not external_contract in self.all_contracts: continue     
                if type(external_function) == StateVariable: continue  #! 调用定义在当前合约所继承的合约内部的全局变量     
                
       
                call_relation = {
                    "from_c": current_contract,
                    "from_f": function,
                    "to_c": external_contract,
                    "to_f": external_function
                }
                self.contracts_calls_relations[str(current_contract.id)].add(tuple(call_relation.values()))
                
                if external_function.full_name not in self.function_info_map: continue
                
                #* 所有重名的全部连接，防止函数的实现和接口分析被调用
                substitutes:Dict[str, SFunction] = self.function_info_map[external_function.full_name]
                for fid in substitutes:
                    if fid != str(external_function.id):
                        implemented_external_contract = substitutes[fid].contract_declarer
                        implemented_external_function = substitutes[fid]
                        
                        addtion_call_relation = {
                            "from_c": current_contract,
                            "from_f": function,
                            "to_c": implemented_external_contract,
                            "to_f": implemented_external_function
                        }
                        self.contracts_calls_relations[str(current_contract.id)].add(tuple(addtion_call_relation.values()))
        
        for contract in self.all_contracts:
            self.get_contract_call_graph(contract, self.call_graph)
        self.get_graph_png(self.call_graph, "cg")

        return self.call_graph
    
    def get_contract_call_graph(self, contract:Contract, call_graph:nx.DiGraph):
         
         call_edges = []
         contract_call_relations = self.contracts_calls_relations[str(contract.id)]
         for call_relation in contract_call_relations:
             from_contract:Contract = call_relation[0]
             from_function:SFunction = call_relation[1]
             to_contract:Contract   = call_relation[2]
             to_function:SFunction   = call_relation[3]
             

             call_graph.add_node(
                 str(from_function.id), 
                 label=f"{from_function.full_name} {from_contract.name} {from_function.is_implemented}", 
                 f=from_function,
                 c=from_contract
             )

             call_graph.add_node(
                 str(to_function.id), 
                 label=f"{to_function.full_name} {to_contract.name} {to_function.is_implemented}", 
                 f=to_function,
                 c=to_contract
             )
             
             call_edges.append((str(from_function.id), str(to_function.id)))
        
         call_graph.add_edges_from(call_edges)

    def get_call_graph_orignal(self):
        
        with open(self.call_graph_file, "w", encoding="utf8") as f:

            # Avoid duplicate functions due to different compilation unit
            all_functionss = [
                compilation_unit.functions for compilation_unit in self.slither.compilation_units
            ]
            all_functions = [item for sublist in all_functionss for item in sublist]
            all_functions_as_dict = {
                function.canonical_name: function for function in all_functions
            }
            content = "\n".join(
                ["strict digraph {"] + [_process_functions(all_functions_as_dict.values())] + ["}"]
            )

            f.write(content)

        # 生成PNG
        cfg_png_file = self.target_dir + "/log/call_graph.png"
        subprocess.check_call(["dot", "-Tpng", self.call_graph_file, "-o", cfg_png_file])

    def get_graph_png(self, g:nx.DiGraph, profix):

        graph_dot_file = "{}//{}_{}.dot".format(self.target_log_dir, g.graph["name"], profix)
        graph_png_file = "{}//{}_{}.png".format(self.target_log_dir, g.graph["name"], profix)

        nx_dot.write_dot(g, graph_dot_file)
        subprocess.check_call(["dot", "-Tpng", graph_dot_file, "-o", graph_png_file])         
    
    def get_fake_call_chain(self, src_f:SFunction, call_stmt:Node):
        """
        不存在調用關係的情況下，直接組裝結果
        """
        call_stack = []
        call_pairs = [(src_f, None, call_stmt)]

        print(f"函数 {src_f.name} 直接调用了 {call_stmt.expression}")
        return call_stack, call_pairs
        
    def get_risk_svars_for_target(self, riskf_analyzer:FunctionAnalyzer):
        """
        分析对于给定的financial risk函数, 分析每个financial risk interaction point
            -> 针对每个point, 得到该point依赖的状态变量
                -> 分析能够修改这些变量的函数作为间接的函数入口
        
        Args:
            target_func (SFunction): _description_
            target_analyzer (FunctionAnalyzer): _description_
        """
        risk_svars = set()
        for point in riskf_analyzer.interaction_points_properties:
            
            is_risk = riskf_analyzer.is_risky_point(point)
            if is_risk == False: continue
            
            risk_svars = risk_svars.union(riskf_analyzer.interaction_points[point]["data_dependeds"])
            risk_svars = risk_svars.union(riskf_analyzer.interaction_points[point]["control_dependeds"])

        return risk_svars
        
    def get_target_call_chain(self, src_fid, dst_fid):
        """
        根据起始和结束位置得到 call_stack 和 call_pair:
            call_stack = [(f1, f1_name), (f2, f2_name), (f3, f3_name)]
            call_pair = [(f1, f2), (f2, f3)]
        """
        paths = nx.all_simple_paths(self.call_graph, str(src_fid), str(dst_fid))
        call_chain = None
        for path in paths:
            call_chain = path #TODO: 目前只取第一个
            break
        
        if call_chain == None:
            return None, None
        else:
            call_stack = [(self.call_graph.nodes[node_id]['f'], self.call_graph.nodes[node_id]['f'].name)  for node_id in call_chain]
            _call_pairs = [(call_stack[id-1][0], call_stack[id][0]) for id in range(1, len(call_stack))]
            
            #* 得到callee_function中調用的語句位置
            call_pairs = []
            for (callee_function, called_function) in _call_pairs:
                
                _callee_analyzer:FunctionAnalyzer = self.get_function_analyzer(callee_function)
                if _callee_analyzer is None: continue
                
                #* 得到callee_function中調用的語句位置
                call_stmt = _callee_analyzer.get_called_function_stmt(called_function)
                
                call_pairs.append((callee_function, called_function, call_stmt))
        
        print("得到的调用链信息: ", [name for (_, name) in call_stack])
        return call_stack, call_pairs
    
    def analyze_indirect_risk(self, riskf:SFunction, _normalf:SFunction):
        # print(f"判斷目標函数 {_normalf.name} 能否间接影响 {riskf.name}")
        
        risky_fanalyzer = self.get_function_analyzer(riskf)
        risky_svars:set = risky_fanalyzer.get_financial_risk_svars()
        
        _normal_fanalyzer = self.get_function_analyzer(_normalf)
        _normalf_written_svars:set = _normal_fanalyzer.write_state_vars
        
        risky_written_svars = risky_svars & _normalf_written_svars
        
        if _normalf.name == "acceptBidForGod" and riskf.name == "withdrawPendingFunds":
            print(f"11111111:  {[v.name for v in risky_svars]}")
            print(f"22222222:  {[v.name for v in _normalf_written_svars]}")
            print(f"33333333:  {[v.name for v in risky_written_svars]}")
        
        if len(risky_written_svars) > 0: return True, risky_written_svars, risky_fanalyzer, _normal_fanalyzer
        else:  return False, None, None, None
        
    def analyze_call_stack_for_interactions(self, root_contract:SContract, root_function:SFunction):
        """
        嵌套调用的場景下
        function root :(root_function)
            ->[FUN root] call function A @ stmt root_1
                ->[FUN A] call function B @ stmt A_2
                    ->[FUN B] call.values (leaf_interac_stmt) @ stmt B_3 #! interaction_point
                    ->[FUN B] SVAR1 = 0 @ stmt B_4
                ->[FUN A] SVAR2 = 0 @ stmt A_5  
            ->[FUN root] SVAR3 = 0 A @ stmt root_6
        
        
        得到調用棧 root -> A - > B -> interaction_point 和調用對  (root, A) (A,B)  (B, interaction_point)
        """
        
        root_function_analyzer:FunctionAnalyzer = self.get_function_analyzer(root_function)
        for interaction_point in root_function_analyzer.interaction_points:
            
            #* KEYS = ["stmt", "to_c", "to_f", "action_type","data_dependeds", "control_dependeds", "need_cross_contract_analysis"]
            interaction_stmt:Node = root_function_analyzer.interaction_points[interaction_point]["stmt"]
            interaction_type = root_function_analyzer.interaction_points[interaction_point]["action_type"]
            leaf_function:SFunction = root_function_analyzer.interaction_points[interaction_point]["to_f"]
            
            print(f"針對 interaction point {interaction_stmt.expression}")
            print(f"寻找路径：{root_function.name}@{str(root_function.id)} -> {leaf_function.name}@{str(leaf_function.id)} for {interaction_type}")
            
            if root_function.id == leaf_function.id: #* 不存在過程閒函數調用
                call_stack, call_pairs = self.get_fake_call_chain(root_function, interaction_stmt)
            else:
                call_stack, call_pairs = self.get_target_call_chain(root_function.id, leaf_function.id)
            
            root_function_analyzer.interaction_points[interaction_point]["call_stack"] = call_stack
            root_function_analyzer.interaction_points[interaction_point]["call_pairs"] = call_pairs

    def analyze_access_control(self, root_analyzer:FunctionAnalyzer, interaction_point):
        """
        判斷執行路徑 root --> interaction point 上有無 access control 和 modifier
        """
        
        total_re_modifiers = 0
        current_point_stop_analyze = False
        
        call_pairs = root_analyzer.interaction_points[interaction_point]["call_pairs"]
        for (callee_function, called_functoin, call_stmt) in call_pairs:
            
            _callee_analyzer:FunctionAnalyzer = self.get_function_analyzer(callee_function)
            if _callee_analyzer is None: continue
            
            #* access control 保護分析
            _modifier_cnt, _ac, info, protect_point = _callee_analyzer.analyze_access_control_protection(call_stmt)
            total_re_modifiers += _modifier_cnt
            if _ac:
                
                if isinstance(protect_point, Node):
                    print(f"\t->当前语句存在控制保护：{protect_point.expression} @ {callee_function.name} {info}, 分析停止...")
                
                elif isinstance(protect_point, SFunction) or isinstance(protect_point, SContract):
                    print(f"\t->当前语句存在控制保护：{protect_point.name} @ {callee_function.name} {info}, 分析停止...")
                
                _callee_analyzer.ppt = 1
                current_point_stop_analyze = True  #* 當前執行路徑存在保護，不可能重入，立刻停止分析
        
        return current_point_stop_analyze, total_re_modifiers    
    
    def analyze_intraprocedural_effect_after_interaction(self, function_analyzer:FunctionAnalyzer, interaction_point):
        """
        前向分析, 分析 root - > interaction point中每個調用點之後修改的全局變量
        callee f1 --> root
            ->[@f1] stmt 1 
            ->[@f1] called f2
                ->[@f2] stmt 2 
                ->[@f2] called f3 --> interaction point
                    ->[@f3] stmt 4
                ->[@f2] stmt 5
            ->[@f2] stmt 6
        """
        effect_after_interact_vars = set() #* interaction之後修改的變量集合
        risky_stmts_after_interact = set() #* interaction之後修改變量的語句集合
        
        call_pairs = function_analyzer.interaction_points[interaction_point]["call_pairs"]
        for (callee_function, called_functoin, call_stmt) in call_pairs:
            
            _callee_analyzer:FunctionAnalyzer = self.get_function_analyzer(callee_function)
            if _callee_analyzer is None: continue
            
            #* effect_after_interaction 分析
            _vars_set, _risky_stmts = _callee_analyzer.analyze_effect_after_interaction_point(call_stmt)
            for v in _vars_set: effect_after_interact_vars.add(v)
            for rstmt in _risky_stmts: risky_stmts_after_interact.add(rstmt)

        return effect_after_interact_vars
    
    def analyze_intraprocedural_backward_data_dependecy(self, root_analyzer:FunctionAnalyzer, interaction_point):
        
        duplicate_filter = {}
        interact_data_depedent_vars = set()
        interact_depedent_balances = set()
        call_pairs = root_analyzer.interaction_points[interaction_point]["call_pairs"]

        for (callee_function, _, call_stmt) in call_pairs:
            _depedended_data, _depedended_balance = self.analyze_data_dependecy_with_intraprocedural(callee_function, str(call_stmt.node_id), duplicate_filter)
            for v in _depedended_data: interact_data_depedent_vars.add(v)
            for v in _depedended_balance: interact_depedent_balances.add(v)
        
        return interact_data_depedent_vars, interact_depedent_balances
    
    def analyze_intraprocedural_backward_control_dependecy(self, root_analyzer:FunctionAnalyzer, interaction_point):
        
        duplicate_filter = {}
        interact_control_depedent_vars = set()
        interact_control_depedent_balances = set()
        need_cross_contract_analysis = set()
        call_pairs = root_analyzer.interaction_points[interaction_point]["call_pairs"]
        
        for (callee_function, _, call_stmt) in call_pairs:
            _depedended_data, _depedended_balance, for_cross_contract = self.analyze_control_dependecy_with_intraprocedural(callee_function, str(call_stmt.node_id), duplicate_filter)
            for v in _depedended_data: interact_control_depedent_vars.add(v)
            for v in _depedended_balance: interact_control_depedent_balances.add(v)
            for (c, f) in for_cross_contract: need_cross_contract_analysis.add((c, f, root_analyzer.target_contract))
            #* 在 root_analyzer.target_contract 内部調用了 來自 c 的 f
                
        return interact_control_depedent_vars, interact_control_depedent_balances, need_cross_contract_analysis
    
    def analyze_semantics_for_indirect_risk_point(self, root_function:SFunction, assign_point):
        """
        针对间接危险点进行分析
        Args:
            root_analyzer (FunctionAnalyzer): _description_
            assign_point (_type_): _description_
        """
        #* 
        
        duplicate_filter = {}
        data_depedent_vars = set()
        ctrl_depedent_vars = set()

        _depedended_data, _depedended_balance = self.analyze_data_dependecy_with_intraprocedural(root_function, assign_point, duplicate_filter)
        for v in _depedended_data: data_depedent_vars.add(v)
        
        __depedended_data, __depedended_balance, for_cross_contract = self.analyze_control_dependecy_with_intraprocedural(root_function, assign_point, duplicate_filter)
        for v in __depedended_data: ctrl_depedent_vars.add(v)
        
        return data_depedent_vars, ctrl_depedent_vars
    
    def analyze_semantics_for_interaction_point(self, root_analyzer:FunctionAnalyzer, interaction_point):
        """
        ! 以下的分析都是针对整个call chain的分析
        分析当前的interaction_point对应的语义信息
            --> #* STEP1: interaction的两种属性判断
        """
        interaction_stmt:Node = root_analyzer.stmt_map[str(interaction_point)]
        print(f"開始分析目標interaction 語句: {interaction_stmt.expression}")
        
        #* STEP1: interaction的两种属性判断
        hijacked, risk, risky_type = root_analyzer.analyze_interaction_properties(interaction_point)
        print(f"当前interaction point的属性列表:")
        print(f"\t -> 可被劫持属性: {hijacked}")
        print(f"\t -> 重入金融风险属性: {risk} 重入金融风险类型: {risky_type}")
        
        #* 如何兩種屬性具備其一，則先判斷有無access protect
        if hijacked or risk:
            protected, re_cnt = self.analyze_access_control(root_analyzer, interaction_point)
            root_analyzer.re_modifier = re_cnt  #* 記錄
            root_analyzer.ppt = protected  #* 記錄
            if protected: return
        
        #* STEP2: hijacked 的 interaction 需要进行过程间 effect-after-interaction 分析
        if hijacked:
            effect_after_interact_vars = self.analyze_intraprocedural_effect_after_interaction(root_analyzer, interaction_point)
            root_analyzer.effect_after_interact_svars[interaction_point] = effect_after_interact_vars #* 记录
            
        #* STEP3:
        if risk:
            
            #* 計算與interaction存在數據依賴的變量
            data_depedent_vars, _balances = self.analyze_intraprocedural_backward_data_dependecy(root_analyzer, interaction_point)    
            root_analyzer.interaction_points[interaction_point]["data_dependeds"] = data_depedent_vars #* 记录
            
            #* 計算與interaction存在控制依賴的變量，和跨合約的函數（cross-contract function）集合
            ctrl_dependet_var, __balances, ccfs = self.analyze_intraprocedural_backward_control_dependecy(root_analyzer, interaction_point)
            root_analyzer.interaction_points[interaction_point]["control_dependeds"] = ctrl_dependet_var #* 记录
            root_analyzer.interaction_points[interaction_point]["need_cross_contract_analysis"] = ccfs #* 记录
            
            #* 收集某些interaction依赖余额的信息
            #! 余额是一个可以被修改的隐藏 state variable
            depend_balances = set()
            depend_balances = depend_balances.union(_balances)
            depend_balances = depend_balances.union(__balances)
            root_analyzer.interaction_points[interaction_point]["balance_dependeds"] = depend_balances #* 记录
            
    def analyze_semantics_for_all_interactions(self, root_contract:SContract, root_function:SFunction):
        
        root_function_analyzer:FunctionAnalyzer = self.get_function_analyzer(root_function)
        for interaction_point in root_function_analyzer.interaction_points:
            self.analyze_semantics_for_interaction_point(root_function_analyzer, interaction_point)
            if root_function_analyzer.ppt: return #* 由于root_function_analyzer.ppt是分析中生成，所以每次都要检测
    
    def analyze_semantics_for_all_indirect_risky_points(self, root_function:SFunction):
        root_function_analyzer:FunctionAnalyzer = self.get_function_analyzer(root_function)
        if root_function_analyzer.ppt: return #* 已經生成完畢的
        
        for risk_point in root_function_analyzer.indirect_risk_points:
            pass
    
    def analyze_return_data_dependency_within_function(
            self, 
            f:SFunction, 
            c:Contract, 
            final_result, 
            final_balance_result,
            dup_filter:dict,
    ):
        """_summary_
        分析函數返回值的數據依賴關係，只保留返回值依賴的全局變量

        Args:
            function (SFunction): _description_
            debug_flag (bool, optional): _description_. Defaults to False.
        """
        
        #* 过滤不必要的和已经分析的函数
        
        if f in dup_filter: return 
        if "add" in f.name or "sub" in f.name or "mul" in f.name or "div" in f.name or "min" in f.name: return
        if type(f) == StateVariable: return
        
        dup_filter[f] = 1
        fake = []
        if isinstance(f, SolidityFunction): return False
        
        function_analyzer = self.get_function_analyzer(f)
        if function_analyzer == None: return True #* 需要跨合约分析
        
        ret_stmts_infos = function_analyzer.get_all_return_variable_stmts()
        for return_point in ret_stmts_infos:
            self._analyze_data_dependency(function_analyzer, return_point, final_result, final_balance_result, dup_filter)
            self._analyze_control_dependency(function_analyzer, return_point, final_result, final_balance_result, dup_filter, fake)
        return False
    
    def analyze_data_dependecy_with_intraprocedural(self, function:SFunction, interaction_point:str, duplicate_filter):
        
        function_analyzer = self.get_function_analyzer(function)
        
        start_stmt:Node = function_analyzer.stmt_map[interaction_point]
        used_vars = [v for v in start_stmt.variables_read]
        
        final_result = set([used_v for used_v in used_vars if type(used_v) is SolidityVariableComposed])
        final_balance_result = set()

        self._analyze_data_dependency(function_analyzer, str(interaction_point), final_result, final_balance_result, duplicate_filter)
        
        print("当前函数的 interaction 数据依賴分析结果为:")
        print(f"\t-> interaction point: {function_analyzer.stmt_map[interaction_point].expression}")
        print(f"\t\t-> 依赖变量 {[v.name for v in final_result]}")
        print(f"\t\t-> 依赖余额 {[bs for bs in final_balance_result]}")
        
        return final_result, final_balance_result
    
    def analyze_control_dependecy_with_intraprocedural(self, function:SFunction, interaction_point:str, duplicate_filter):
        
        function_analyzer = self.get_function_analyzer(function)
        start_stmt:Node = function_analyzer.stmt_map[interaction_point]
        used_vars = [v for v in start_stmt.variables_read]
        
        final_result = set([used_v for used_v in used_vars if type(used_v) is SolidityVariableComposed])
        final_balance_result = set()
        for_cross_contract = []
        
        self._analyze_control_dependency(function_analyzer, str(interaction_point), final_result, final_balance_result, duplicate_filter, for_cross_contract)
        
        print("【控制依賴分析】当前函数的 interaction 控制依賴分析结果为:")
        print(f"\t-> interaction point: {function_analyzer.stmt_map[interaction_point].expression}")
        print(f"\t\t-> 依赖变量 {[v.name for v in final_result if type(v) == StateVariable]}")
        print(f"\t\t-> 依赖余额 {[bs for bs in final_balance_result]}")
        
        return final_result, final_balance_result, for_cross_contract  
               
    def _analyze_control_dependency(self, 
            function_analyzer:FunctionAnalyzer, 
            start_point:str, 
            final_analyze_result:set, 
            final_balance_result:set, 
            duplicate_filter:dict, 
            for_cross_contract:list,
        ):
        """
        获得function_entry --> start_point路径上所有控制依赖的全局变量
        
        """
        debug_flag = SEMANTIC_DEBUG_FLAG
        print(f"\n 开始分析函数：{function_analyzer.name} 的控制依赖关系")
        start_stmt:Node = function_analyzer.stmt_map[start_point]
        used_vars = [v for v in start_stmt.variables_read if v is not None]
        
        print("\t-> 数据依赖起始语句: ", start_stmt.type," ",start_stmt.expression, "读取变量: ",[(type(v), str(v)) for v in used_vars])

        stmts_varinfo_map = function_analyzer.stmts_var_infos
        stmts_callinfo_map = function_analyzer.stmts_call_infos
        cfg:nx.DiGraph = function_analyzer.cfg
        
        paths = nx.all_simple_paths(cfg, "0", str(start_stmt.node_id))
        for idx, path in enumerate(paths): # TODO: 假設只有一條路徑
            
            _stack = {} #* 空栈
            _f_stack = set()
            _current_control_depended_vars = set()  #* 控制依赖的变量
            _current_path_depended_balances = set()
            
            if debug_flag:print(f"\n 開始計算第{idx}條路徑的控制依賴")
            for stmt_cnt, stmt_id in enumerate(reversed(list(path[:-1]))): # 跳過最後一個
                
                stmt_info:Node = function_analyzer.stmt_map[str(stmt_id)]
                stmt_varinfo:list = stmts_varinfo_map[str(stmt_id)]
                stmt_callinfo:list = stmts_callinfo_map[str(stmt_id)]
                
                def_vars_list = stmt_varinfo["def"]
                use_vars_list = stmt_varinfo["use"]
                use_funs_list = stmt_callinfo #* [(c,f),...,(c,f)]
                use_balance_list = stmt_varinfo["use_balance"] #* 内部是字符串
                
                need_to_pop  = set()
                need_to_push = set()
                
                #* 条件语句所有使用的变量必须入栈查明来源
                if stmt_info.is_conditional(include_loop=False):
                    for use_var in use_vars_list: need_to_push.add(use_var)
                
                for _stack_var in _stack:
                    if _stack_var in def_vars_list: #* 條件語句使用的變量被賦值，需要進一步查明來源
                        need_to_pop.add(_stack_var)
                
                if len(need_to_pop) > 0: #* 有写操作才需要将使用的变量、调用的函数入栈
                    
                    #* 读变量入栈
                    for use_var in use_vars_list:
                        need_to_push.add(use_var) #* 使用的变量入栈
                        _current_control_depended_vars.add(use_var)
                    
                    #* 使用的函数入栈
                    _f_stack = _f_stack.union(use_funs_list)
                    
                    #* 使用的余额入栈
                    _current_path_depended_balances = _current_path_depended_balances.union(use_balance_list)
                            
                for _pop_var in need_to_pop: _stack.pop(_pop_var)
                for _push_var in need_to_push: _stack[_push_var] = _push_var
                    
            print("當前路徑的控制流最終計算結果 VAR: ", [v.name for v in _current_control_depended_vars])
            print("當前路徑的控制流最終計算結果 VAR_STACK: ", [v.name for v in _stack])
            
            #* 將當前path的保存合并到縂結果内
            for _d_b in _current_path_depended_balances:
                final_balance_result.add(_d_b)
           
            for _d_v in _current_control_depended_vars:
                if type(_d_v) is not LocalVariable:
                    final_analyze_result.add(_d_v)
                    
            for _d_v in _stack:
                if type(_d_v) is not LocalVariable:
                    final_analyze_result.add(_d_v)
            
            print("需要进行过程间分析的函数列表: ", [(c.name, f.name) for (c, f) in _f_stack])
            for (c, f) in _f_stack:
                need_cross_contract = self.analyze_return_data_dependency_within_function(f, c, final_analyze_result, final_balance_result, duplicate_filter)                      
                # need_cross_contract = self.analyze_return_data_dependency_within_function_V2(f, final_analyze_result, final_balance_result, duplicate_filter)
                if need_cross_contract: for_cross_contract.append((c,f))

    def _analyze_data_dependency(
            self, 
            function_analyzer:FunctionAnalyzer, 
            start_point, 
            final_analyze_result:set, 
            final_balance_result:set, 
            duplicate_filter:dict
        ):

        """
           函数 function 中的某个语句 stmt 使用了变量 root_var
            -> 判断 root_var 依赖的所有变量集合
            -> 倒敘判斷 step 1 - step 7
           
        #! (step8) 對foo()和fun()進行分析, 判斷所有return以來的state variables (NOTE:只分析全局變量)
           
           (step7) 最後得到 root_var 依賴的變量為 [root_var, b, c, in0, in1] 和 f_stack中會剩下等待分析的函數集合 f_stack:[foo(), fun()]
           
           int in0; int in1;   -- (step6) def in0 & in1        -> stack:[in1, foo(), in0]           DO  stack.pop([in0, in1])
                                                                                                    --> pop:[root_var, b, c, in0, in1], stack:[]
                                                                                                    --> f_stack:[foo(), fun()]   

        #! c = fun(in0)        -- (step5) w c use fun(in0)     -> stack:[c, in1, foo()] f_stack:[foo()]  DO stack.pop(c) stack.push([in0]) f_stack.push([fun()])          
                                                                                                         --> pop:[root_var, b , c], stack:[in1, in0]
                                                                                                         --> f_stack:[foo(), fun()]

        #! b = foo(in1)        -- (step4) w b use foo(in1)     -> stack:[b,c] f_stack:[]            DO stack.pop(b) stack.push([in1])  f_stack.push([foo()])      
                                                                                                    --> pop:[root_var, b], stack:[c, in1]
                                                                                                    --> f_stack:[foo()]

           root_var = b + c    -- (step3) w root_var use [b,c]  -> stack:[root_var] f_stack:[]      DO stack.pop(root_var)  stack.push([b,c])  
                                                                                                    --> pop:[root_var], stack:[b,c]
                                                                                                    --> f_stack:[]

           a += a              -- (step2) not W root_var       -> stack:[root_var]  f_stack:[]      DO NA                                     
                                                                                                    --> stack:[root_var]
                                                                                                    --> f_stack:[]

           used(root_var)      -- (step1) NA                   -> stack:[root_var]  f_stack:[]      DO NA                                     
                                                                                                    --> stack:[root_var]
                                                                                                    --> f_stack:[]
        """
        debug_flag = SEMANTIC_DEBUG_FLAG
        print(f"\n开始分析函数: {function_analyzer.name} 的数据依赖关系 {debug_flag}")        
        start_stmt:Node = function_analyzer.stmt_map[start_point]

        stmts_varinfo_map = function_analyzer.stmts_var_infos
        stmts_callinfo_map = function_analyzer.stmts_call_infos
        cfg:nx.DiGraph = function_analyzer.cfg

        #* start_point相關信息初始化，等待入棧
        start_used_vars = [v for v in start_stmt.variables_read if v is not None]
        start_called_funs = stmts_callinfo_map[str(start_point)]
        start_use_balances = stmts_varinfo_map[str(start_point)]["use_balance"] 
        print("\t -> 数据依赖起始语句: ", start_stmt.type," ",start_stmt.expression, "读取变量: ",[(type(v), str(v)) for v in start_used_vars])

        paths = nx.all_simple_paths(cfg, "0", str(start_stmt.node_id))
        for idx, path in enumerate(paths): # TODO:假設只有一條路徑

            #* 栈信息初始化: 裝載start point的信息 
            _stack = {v:(v, used_var_idx) for used_var_idx, v in enumerate(start_used_vars) if type(v) != SolidityVariableComposed} # 入棧
            _f_stack = set(start_called_funs)    #* function stack只入棧不出棧
            _current_path_depended_vars = set([v for v in start_used_vars if type(v) != LocalVariable])  #* pop vars
            _current_path_depended_balances = set(start_use_balances)
            _current_path_depended_vars_detail:Dict[int, set()] =  {idx: set() for idx, v in enumerate(start_used_vars)}

            if debug_flag:print(f"\n 開始計算第{idx}條路徑的數據依賴")
            for stmt_cnt, stmt_id in enumerate(reversed(list(path[:-1]))): #! 跳過start_point

                stmt_varinfo:list = stmts_varinfo_map[str(stmt_id)]
                stmt_callinfo:list = stmts_callinfo_map[str(stmt_id)]

                if debug_flag: print("{}th -> {} :".format(stmt_cnt, cfg.nodes[stmt_id]["node"].expression))
                if debug_flag: print("\t->DEF: {}".format([v.name for v in stmt_varinfo["def"]]))
                if debug_flag: print("\t->USE: {}".format([v.name for v in stmt_varinfo["use"]]))
                if debug_flag: print("\t->balance: {}".format([bala for bala in stmt_varinfo["use_balance"]]))
                if debug_flag: print("\t->stack: {}".format([v.name for v in _stack]))    
                if debug_flag: print("\t->fstack: {}".format([f.name for (_, f) in _f_stack]))    
                if debug_flag: print("\t->depended: {}".format([v.name for v in _current_path_depended_vars]))
                
                def_vars_list = stmt_varinfo["def"]
                use_vars_list = stmt_varinfo["use"]
                use_balance_list = stmt_varinfo["use_balance"] #* 内部是字符串 
                use_funs_list = stmt_callinfo
                
                need_to_pop  = set()
                need_to_push = set()
                for _stack_var in _stack:
                        
                    if _stack_var in def_vars_list:
                        need_to_pop.add(_stack_var)
                        if debug_flag: print("\t\tpop -> ", _stack_var.name)

                        (_, _var_idx) = _stack[_stack_var]
                        for use_var in use_vars_list:
                            
                            #* 使用的变量入栈
                            need_to_push.add((use_var, _var_idx))
                            _current_path_depended_vars.add(use_var)
                            _current_path_depended_vars_detail[_var_idx].add(use_var)
                            
                            if debug_flag: print("\t\tpush -> VAR:{} ".format(use_var.name))
                            
                        #* 使用的函数入栈
                        _f_stack = _f_stack.union(use_funs_list)
                            
                        #* 使用的余额信息入栈
                        _current_path_depended_balances = _current_path_depended_balances.union(use_balance_list)

                        if debug_flag: print(f"\t\tpush -> functions:{[(c.name, f.name) for (c, f) in use_funs_list]}")
                        if debug_flag: print(f"\t\tpush -> balances:{_current_path_depended_balances}")

                for _pop_var in need_to_pop: _stack.pop(_pop_var)
                for (_push_var, _var_idx) in need_to_push: _stack[_push_var] = (_push_var, _var_idx)

            if debug_flag: print("當前路徑的最終計算結果 VAR: ", [v.name for v in _current_path_depended_vars])
            if debug_flag: print("當前路徑的最終計算結果 BAL: ", [b for b in _current_path_depended_balances])
            for _used_var_idx in _current_path_depended_vars_detail:
                if debug_flag: print("\t-> {} {}".format(start_used_vars[_used_var_idx].name, [(v.name, type(v)) for v in _current_path_depended_vars_detail[_used_var_idx]]))

            #* 將當前path的保存合并到縂結果内
            for _d_b in _current_path_depended_balances:
                final_balance_result.add(_d_b)

            for _d_v in _current_path_depended_vars:
                if type(_d_v) is not LocalVariable:
                    final_analyze_result.add(_d_v)
                     
            print(f"需要過程閒數據依賴的函數列表：{[f.name for (_, f) in _f_stack]}")
            for (c, f) in _f_stack: #* 递归调用
                self.analyze_return_data_dependency_within_function(f, c, final_analyze_result, final_balance_result, duplicate_filter)
                # self.analyze_return_data_dependency_within_function_V2(f, final_analyze_result, final_balance_result, duplicate_filter)
    
    
    def analyze_return_depended_vars_in_function(self, function:SFunction):
        """
        針對來自輔助對象的函數, 這裏只分析返回值依賴的全局變量
        Args:
            contract (SContract): _description_
            function (SFunction): _description_
        """
         
        function_analyzer = self.get_function_analyzer(function)
        return_stmts = function_analyzer.get_all_return_variable_stmts()
        function_analyzer.re_modifier = len([m for m in function.modifiers if "nonReentrant" == m.name])
        
        dup_filter = {}
        return_depend_vars = set()
        for return_stmt in return_stmts:
            result_data, _result_balances     = self.analyze_data_dependecy_with_intraprocedural(function, return_stmt, dup_filter)
            result_ctrl, __result_balances, _ = self.analyze_control_dependecy_with_intraprocedural(function, return_stmt, dup_filter)
                
            return_depend_vars = return_depend_vars.union(result_data)
            return_depend_vars = return_depend_vars.union(result_ctrl)
        
        print(f"當前函數 {function_analyzer.name} 返回值依賴的全局變量為 {[v.name for v in return_depend_vars]}")    
        return function_analyzer, return_depend_vars
    
    
    def analyze_auxiliary_reentry_point(self, depend_aux_svars:set()):
        reenter_points = set()
        potential_re_points_info = self.contract_info.auxiliary_call_main_functions
        for (potential_re_func, called_main_c, called_main_f) in potential_re_points_info:
            pre_analyzer = self.get_function_analyzer(potential_re_func)
            for wrtie_svar in pre_analyzer.write_state_vars:
                if wrtie_svar in depend_aux_svars:
                    print(f"可疑重入點 {potential_re_func.name} 調用 {called_main_f.name} 修改 {wrtie_svar.name}")
                    reenter_points.add((potential_re_func, called_main_c, called_main_f))
                    break
        
        return reenter_points