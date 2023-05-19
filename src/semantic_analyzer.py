from collections import defaultdict
import subprocess
import networkx as nx
from typing import Dict
from slither.slither import Slither
from slither.printers.abstract_printer import AbstractPrinter
from slither.core.declarations.contract import Contract
from slither.core.declarations.solidity_variables import SolidityFunction
from slither.core.declarations.function import Function
from slither.core.declarations.function_contract import FunctionContract
from slither.core.variables.variable import Variable
import networkx.drawing.nx_pydot as nx_dot
from src.function_analyzer import FunctionAnalyzer
from src.contract_info_collector import ContractInfoCollector
from slither.core.cfg.node import Node, NodeType
from slither.core.declarations import SolidityVariableComposed
from slither.core.variables.local_variable import LocalVariable
from slither.core.variables.state_variable import StateVariable

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
    if isinstance(internal_call, (Function)):
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

        # 当前合约的相关成分
        self.all_functions_as_dict: Dict[str, FunctionContract] = None
        self.contract_functions = defaultdict(set)  # contract -> contract functions nodes
        self.contracts_calls_relations: Dict[str, list] = {}  # contract -> contract calls edges
        self.solidity_functions = set()  # solidity function nodes
        self.solidity_calls = set()  # solidity calls edges
        self.external_calls = set()  # external calls edges
        self.all_contracts = set()
        self.all_construct_state_vars = set() # 在構造函數中定義的變量

        # 当前项目的call graph
        self.call_graph = nx.DiGraph(name="cg")

        # 函數相關分析器
        self.functions_analyzers: Dict[str, FunctionAnalyzer]= {}

    def get_function_analyzer(self, function:Function):
        if str(function.id) in self.functions_analyzers:
            return self.functions_analyzers[str(function.id)]
        return None

    
    def add_function_analyzer(self, analyzer:FunctionAnalyzer):
        self.functions_analyzers[analyzer.function_id] = analyzer


    def get_construct_state_variables(self):
        """
            在構造函數裏設置的全局變量
        """
        for construct_function in self.contract_info.construct_functions:
            for stmt_info in construct_function.nodes:
                for state_var in stmt_info.state_variables_written:
                    self.all_construct_state_vars.add(state_var)

    def get_call_graph(self):

        # Avoid duplicate functions due to different compilation unit
        all_functionss = [
            compilation_unit.functions for compilation_unit in self.slither.compilation_units
        ]
        all_functions = [item for sublist in all_functionss for item in sublist]
        self.all_functions_as_dict = {
            function.canonical_name: function for function in all_functions
        }

        # 获得所有的合约列表
        for function in self.all_functions_as_dict.values():
            _contract:Contract = function.contract_declarer
            self.all_contracts.add(_contract)

            if str(_contract.id) not in self.contracts_calls_relations:
                self.contracts_calls_relations[str(_contract.id)] = []

        # 获得所有函数内部的调用关系
        for function in self.all_functions_as_dict.values():

            current_contract:Contract = function.contract_declarer
            for internal_call in function.internal_calls:
                if isinstance(internal_call, (Function)):
                    call_relation = {
                        "from_c": current_contract,
                        "from_f": function,
                        "to_c": current_contract,
                        "to_f": internal_call
                    }
                    self.contracts_calls_relations[str(current_contract.id)].append(call_relation)

            for (external_contract, external_function) in function.high_level_calls:
                if not external_contract in self.all_contracts: continue
                call_relation = {
                    "from_c": current_contract,
                    "from_f": function,
                    "to_c": external_contract,
                    "to_f": external_function
                }
                self.contracts_calls_relations[str(current_contract.id)].append(call_relation)

        
        for contract in self.all_contracts:
            self.get_contract_call_graph(contract, self.call_graph)
        self.get_graph_png(self.call_graph, "cg")

        return self.call_graph
    
    def get_contract_call_graph(self, contract:Contract, call_graph:nx.DiGraph):
         
         call_edges = []
         contract_call_relations = self.contracts_calls_relations[str(contract.id)]
         for call_relation in contract_call_relations:
             from_function:Function = call_relation["from_f"]
             from_contract:Contract = call_relation["from_c"]
             to_function:Function   = call_relation["to_f"]
             to_contract:Contract   = call_relation["to_c"]

             call_graph.add_node(
                 str(from_function.id), 
                 label=f"{from_function.name} {from_contract.name}", 
                 f=from_function,
                 c=from_contract
             )

             call_graph.add_node(
                 str(to_function.id), 
                 label=f"{to_function.name} {to_contract.name}", 
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

    def prepare_for_analyze(self, function_ids:list, target_dir):
        
        for (fid, _) in function_ids:
            if str(fid) not in self.functions_analyzers:
                target_function:Function = self.call_graph.nodes[str(fid)]["f"]
                target_contract:Contract = target_function.contract_declarer
                function_analyzer = FunctionAnalyzer(target_function, target_contract, self.slither, self.call_graph, target_dir)
                function_analyzer.analyze_function_initialize(False)
                self.functions_analyzers[str(fid)] = function_analyzer


    def analyze_path_protection_technology(self, function:Function, interaction_point, debug_flag=False):
        """
            entry_point ---> interaction_point
            判断执行路径上有没有path protection technology:
            1. Access Control Before Payment
            2. Protection by Self-defined Modifiers
            3. Protection by Execution Locks
        """
        function_analyzer = self.functions_analyzers[str(function.id)]
        interact_stmt:Node =  function_analyzer.interaction_points[interaction_point]["stmt"] # 判断 interaction point 依赖的全局变量
        interact_used_vars = set([v for v in interact_stmt.variables_read])
        interact_depedend_vars:set = function_analyzer.interaction_points[interaction_point]["data_dependeds"]
        interact_related_vars = interact_depedend_vars.union(interact_used_vars)

        cfg:nx.DiGraph = function_analyzer.cfg
        paths = nx.all_simple_paths(cfg, "0", str(interact_stmt.node_id))
        for execution_path in paths:
            for stmt_id in execution_path:
                stmt_info:Node = cfg.nodes[stmt_id]["node"]

                if stmt_info.is_conditional(include_loop=False):
                    current_read_vars = set([v for v in stmt_info.variables_read])

                    # msg.sender == CONST_vAR
                    if "msg.sender" in [v.name for v in current_read_vars]:
                        for v in current_read_vars:
                            if v in self.all_construct_state_vars:
                                ppt = "Protected by Constructed Vars"
                                print("{} - INFO:{}".format(stmt_info.expression, ppt))
                                return True, ppt  
        
        return False, "No Path Protected"


    def analyze_data_dependency(self, function:Function, start_point:str, debug_flag=False):

        """
           函数 function 中的某个语句 stmt 使用了变量 root_var
            -> 判断 root_var 依赖的所有变量集合
            -> 倒敘判斷 step 1 - step 7
           
           最後得到 (step7) root_var 依賴的變量為 [root_var, b, c, in0, in1]
           
           int in0; int in1;    -- (step6) def in0 & in1        -> stack:[in1, in0]  DO  stack.pop([in0, in1])
                                                                                    --> pop:[root_var, b, c, in0, in1], stack:[]   

           c = in0              -- (step5) w c use in0          -> stack:[c, input1] DO stack.pop(c) stack.push(in0)        
                                                                                    --> pop:[root_var, b , c], stack:[in1, in0]

           b = in1              -- (step4) w b use in1          -> stack:[b,c]       DO stack.pop(b) stack.push(in1)        
                                                                                    --> pop:[root_var, b], stack:[c, in1]

           root_var = b + c    -- (step3) w root_var use [b,c]  -> stack:[root_var]  DO stack.pop(root_var)  stack.push([b,c])  
                                                                                    --> pop:[root_var], stack:[b,c]

           a += a              -- (step2) not W root_var       -> stack:[root_var]  DO NA                                     
                                                                                    --> stack:[root_var]

           used(root_var)      -- (step1) NA                   -> stack:[root_var]  DO NA                                     
                                                                                    --> stack:[root_var]
        """
        
        function_analyzer = self.functions_analyzers[str(function.id)]
        start_stmt:Node =  function_analyzer.stmt_map[start_point]
        used_vars = [v for v in start_stmt.variables_read]
        print("\t-> 数据依赖分析起始语句: ", start_stmt.expression)

        stmts_varinfo_map = function_analyzer.stmts_var_infos
        cfg:nx.DiGraph = function_analyzer.cfg

        paths = nx.all_simple_paths(cfg, "0", str(start_stmt.node_id))
        paths_result:list[set()] = []
        paths_detail_result:list[Dict[Variable, set(Variable)]] = []

        for idx, path in enumerate(paths): # TODO:假設只有一條路徑
            
            # 栈信息初始化 
            _stack = {v:(v, used_v_id) for used_v_id, v in enumerate(used_vars) if type(v) != SolidityVariableComposed} # 入棧
            print(f"{[type(v) for v in _stack]}")
            _depended_vars = set() # pop vars
            _depended_vars_detail:Dict[int, set()] =  {idx: set() for idx, v in enumerate(used_vars)}

            paths_result.append(_depended_vars)
            paths_detail_result.append(_depended_vars_detail)

            if debug_flag:print(f"\n 開始計算第{idx}條路徑的數據依賴")
            for stmt_cnt, stmt_id in enumerate(reversed(list(path[:-1]))): # 跳過最後一個
                
                stmt_varinfo:list = stmts_varinfo_map[str(stmt_id)]

                if debug_flag: print("{}th -> {} :".format(stmt_cnt, cfg.nodes[stmt_id]["node"].expression))
                if debug_flag: print("\t->DEF: {}".format([v.name for v in stmt_varinfo["def"]]))
                if debug_flag: print("\t->USE: {}".format([v.name for v in stmt_varinfo["use"]]))
                if debug_flag: print("\t->stack: {}".format([v.name for v in _stack]))    
                if debug_flag: print("\t->depended: {}".format([v.name for v in _depended_vars])) 

                need_to_pop  = set()
                need_to_push = set()
                for _stack_var in _stack:

                    def_vars_list = stmt_varinfo["def"]
                    use_vars_list = stmt_varinfo["use"]

                    if _stack_var in def_vars_list:
                        need_to_pop.add(_stack_var)
                        if debug_flag: print("\t\tpop -> ", _stack_var.name)

                        (_, _var_idx) = _stack[_stack_var]
                        for use_var in use_vars_list:
                           need_to_push.add((use_var, _var_idx))
                           _depended_vars.add(use_var)
                           _depended_vars_detail[_var_idx].add(use_var)
                           if debug_flag: print("\t\tpush -> ", use_var.name)

                for _pop_var in need_to_pop: _stack.pop(_pop_var)
                for (_push_var, _var_idx) in need_to_push: _stack[_push_var] = (_push_var, _var_idx)

            if debug_flag: print("當前路徑的最終計算結果: ", [v.name for v in _depended_vars])
            for _v_idx in _depended_vars_detail:
                if debug_flag: print("\t-> {} {}".format(used_vars[_v_idx].name, [(v.name, type(v)) for v in _depended_vars_detail[_v_idx]]))
                

        # 合并不同path的结果
        final_result = set()
        for path_result in paths_result:
            final_result = final_result.union(path_result)

        final_detail_result: Dict[Variable, set(Variable)] = {}
        for path_detail_result in paths_detail_result:
            for _var_idx in path_detail_result:

                _used_var:Variable = used_vars[_var_idx]
                _depended_vars = path_detail_result[_var_idx]

                if _used_var not in final_detail_result:
                    final_detail_result[_used_var] = _depended_vars

                    #! msg.sender之类的solidity变量是不需要进行依赖分析的，他们只依赖自己
                    if type(_used_var) == SolidityVariableComposed:
                        final_detail_result[_used_var].add(_used_var)
                        final_result.add(_used_var)
                else:
                    final_detail_result[_used_var].union(_depended_vars)

        print("最終的合并結果:")
        for __var in final_detail_result:
            print("\t {} -> {}".format(__var.name, [v.name for v in final_detail_result[__var]]))
        
        
        #! 如果一个变量没有依赖，表明这个变量就是入参
        #TODO: 存储在外面进行
        # function_analyzer.interaction_points[start_point]["data_dependeds"] = final_result
        # function_analyzer.interaction_points[start_point]["detail_data_dependeds"] = final_detail_result
        
        return final_result, final_detail_result
    
    def analyze_return_data_dependency_within_function(self, f:Function, c:Contract, final_result, final_balance_result, dup_filter:dict, debug_flag=False):
        """_summary_
        分析函數返回值的數據依賴關係，只保留返回值依賴的全局變量

        Args:
            function (Function): _description_
            debug_flag (bool, optional): _description_. Defaults to False.
        """
        
        #* 1.过滤 2.避免重複
        if "add" in f.name or "sub" in f.name or "mul" in f.name or "min" in f.name: return
        if f in dup_filter: return 
        
        function_analyzer = self.get_function_analyzer(f)
        if function_analyzer is None:
            function_analyzer = FunctionAnalyzer(f, c, self.slither, self.call_graph, self.target_dir)
            if False == function_analyzer.analyze_function_initialize(): return #* 直接退出
            self.add_function_analyzer(function_analyzer)

        dup_filter[f] = 1 #* 記錄
        ret_stmts_infos = function_analyzer.get_all_return_variable_stmts()
        for return_point in ret_stmts_infos:
            self._analyze_data_dependency(f, return_point, final_result, final_balance_result, dup_filter, debug_flag)
    
    def analyze_data_dependecy_with_intraprocedural(self, function:Function, interaction_point, debug_flag=False):
        
        duplicate_filter = {} #* 避免重复分析，加速递归
        
        function_analyzer = self.functions_analyzers[str(function.id)]
        start_stmt:Node = function_analyzer.stmt_map[interaction_point]
        used_vars = [v for v in start_stmt.variables_read]
        
        final_result = set([used_v for used_v in used_vars if type(used_v) is SolidityVariableComposed])
        final_balance_result = set()
        self._analyze_data_dependency(function, interaction_point, final_result, final_balance_result, duplicate_filter, debug_flag)

        function_analyzer.interaction_points[interaction_point]["data_dependeds"] = final_result
        function_analyzer.interaction_points[interaction_point]["balance_dependeds"] = final_balance_result
        
        print("当前函数的 interaction 数据以来分析结果为:")
        print(f"\t-> interaction point: {function_analyzer.stmt_map[interaction_point].expression}")
        print(f"\t\t-> 依赖变量 {[v.name for v in final_result]}")
        print(f"\t\t-> 依赖余额 {[bs for bs in final_balance_result]}")
        
        return final_result

    
    def _analyze_data_dependency(self, function:Function, start_point, final_analyze_result:set, final_balance_result, duplicate_filter:dict, debug_flag=False):

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
        
        print(f"\n 开始分析函数：{function.name} 的数据依赖关系")
        function_analyzer = self.functions_analyzers[str(function.id)]
        start_stmt:Node = function_analyzer.stmt_map[start_point]
        used_vars = [v for v in start_stmt.variables_read]
        print("\t-> 数据依赖起始语句: ", start_stmt.type," ",start_stmt.expression, "读取变量: ",[v.name for v in used_vars])

        stmts_varinfo_map = function_analyzer.stmts_var_infos
        stmts_callinfo_map = function_analyzer.stmts_call_infos
        cfg:nx.DiGraph = function_analyzer.cfg

        paths = nx.all_simple_paths(cfg, "0", str(start_stmt.node_id))
        for idx, path in enumerate(paths): # TODO:假設只有一條路徑
            
            #* 栈信息初始化 
            _stack = {v:(v, used_var_idx) for used_var_idx, v in enumerate(used_vars) if type(v) != SolidityVariableComposed} # 入棧
            print(f"{[type(v) for v in _stack]}")
            _f_stack = set()        #* function stack只入棧不出棧
            _current_path_depended_vars = set()  #* pop vars
            _current_path_depended_balances = set()
            _current_path_depended_vars_detail:Dict[int, set()] =  {idx: set() for idx, v in enumerate(used_vars)}

            if debug_flag:print(f"\n 開始計算第{idx}條路徑的數據依賴")
            for stmt_cnt, stmt_id in enumerate(reversed(list(path[:-1]))): # 跳過最後一個
                
                stmt_varinfo:list = stmts_varinfo_map[str(stmt_id)]
                stmt_callinfo:list = stmts_callinfo_map[str(stmt_id)]

                if debug_flag: print("{}th -> {} :".format(stmt_cnt, cfg.nodes[stmt_id]["node"].expression))
                if debug_flag: print("\t->DEF: {}".format([v.name for v in stmt_varinfo["def"]]))
                if debug_flag: print("\t->USE: {}".format([v.name for v in stmt_varinfo["use"]]))
                if debug_flag: print("\t->stack: {}".format([v.name for v in _stack]))    
                if debug_flag: print("\t->depended: {}".format([v.name for v in _current_path_depended_vars]))
                if debug_flag: print("\t->balance: {}".format([b for b in _current_path_depended_balances]))
                
                need_to_pop  = set()
                need_to_push = set()
                for _stack_var in _stack:

                    def_vars_list = stmt_varinfo["def"]
                    use_vars_list = stmt_varinfo["use"]
                    use_balance_list = stmt_varinfo["use_balance"] #* 内部是字符串
                    use_funs_list = stmt_callinfo
                    
                    if _stack_var in def_vars_list:
                        need_to_pop.add(_stack_var)
                        if debug_flag: print("\t\tpop -> ", _stack_var.name)

                        (_, _var_idx) = _stack[_stack_var]
                        for use_var in use_vars_list:
                            
                            #* 使用的变量入栈
                            need_to_push.add((use_var, _var_idx))
                            _current_path_depended_vars.add(use_var)
                            _current_path_depended_vars_detail[_var_idx].add(use_var)
                            
                            #* 使用的函数入栈
                            _f_stack = _f_stack.union(use_funs_list)
                            
                            #* 使用的余额信息入栈
                            _current_path_depended_balances = _current_path_depended_balances.union(use_balance_list)
                            
                            if debug_flag: print("\t\tpush -> VAR:{} CALLED_FUNS:{} Balance:{}".format(use_var.name, [(c.name, f.name) for (c, f) in use_funs_list], use_balance_list))

                for _pop_var in need_to_pop: _stack.pop(_pop_var)
                for (_push_var, _var_idx) in need_to_push: _stack[_push_var] = (_push_var, _var_idx)

            if debug_flag: print("當前路徑的最終計算結果 VAR: ", [v.name for v in _current_path_depended_vars])
            if debug_flag: print("當前路徑的最終計算結果 BAL: ", [b for b in _current_path_depended_balances])
            for _used_var_idx in _current_path_depended_vars_detail:
                if debug_flag: print("\t-> {} {}".format(used_vars[_used_var_idx].name, [(v.name, type(v)) for v in _current_path_depended_vars_detail[_used_var_idx]]))

            #* 將當前path的保存合并到縂結果内
            for _d_b in _current_path_depended_balances:
                final_balance_result.add(_d_b)
           
            for _d_v in _current_path_depended_vars:
                if type(_d_v) is not LocalVariable:
                    final_analyze_result.add(_d_v)
                     
            print(f"需要過程閒數據依賴的函數列表：{[f.name for (_, f) in _f_stack]}")
            for (c, f) in _f_stack: #* 递归调用
                self.analyze_return_data_dependency_within_function(f, c, final_analyze_result, final_balance_result, duplicate_filter, debug_flag)
            
        
    def analyze_data_dependency_with_intraprocedural_analyze(self, function:Function, start_point, debug_flag=False):

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
        
        function_analyzer = self.functions_analyzers[str(function.id)]
        # interact_stmt:Node =  function_analyzer.interaction_points[interaction_point]["stmt"] # 判断 interaction point 依赖的全局变量
        start_stmt:Node = function_analyzer.stmt_map[start_point]
        used_vars = [v for v in start_stmt.variables_read]
        print("\t-> 数据依赖起始语句: ", start_stmt.expression)

        stmts_varinfo_map = function_analyzer.stmts_var_infos
        stmts_callinfo_map = function_analyzer.stmts_call_infos
        cfg:nx.DiGraph = function_analyzer.cfg

        paths = nx.all_simple_paths(cfg, "0", str(start_stmt.node_id))
        paths_result:list[set()] = []
        paths_detail_result:list[Dict[Variable, set(Variable)]] = []
        
        for idx, path in enumerate(paths): # TODO:假設只有一條路徑
            
            #* 栈信息初始化 
            _stack = {v:(v, used_var_idx) for used_var_idx, v in enumerate(used_vars) if type(v) != SolidityVariableComposed} # 入棧
            print(f"{[type(v) for v in _stack]}")
            _f_stack = set()        #* function stack只入棧不出棧
            _depended_vars = set()  #* pop vars
            _depended_vars_detail:Dict[int, set()] =  {idx: set() for idx, v in enumerate(used_vars)}

            paths_result.append(_depended_vars)
            paths_detail_result.append(_depended_vars_detail)

            if debug_flag:print(f"\n 開始計算第{idx}條路徑的數據依賴")
            for stmt_cnt, stmt_id in enumerate(reversed(list(path[:-1]))): # 跳過最後一個
                
                stmt_varinfo:list = stmts_varinfo_map[str(stmt_id)]
                stmt_callinfo:list = stmts_callinfo_map[str(stmt_id)]

                if debug_flag: print("{}th -> {} :".format(stmt_cnt, cfg.nodes[stmt_id]["node"].expression))
                if debug_flag: print("\t->DEF: {}".format([v.name for v in stmt_varinfo["def"]]))
                if debug_flag: print("\t->USE: {}".format([v.name for v in stmt_varinfo["use"]]))
                if debug_flag: print("\t->stack: {}".format([v.name for v in _stack]))    
                if debug_flag: print("\t->depended: {}".format([v.name for v in _depended_vars]))
                
                need_to_pop  = set()
                need_to_push = set()
                for _stack_var in _stack:

                    def_vars_list = stmt_varinfo["def"]
                    use_vars_list = stmt_varinfo["use"]
                    use_funs_list = stmt_callinfo
                    
                    if _stack_var in def_vars_list:
                        need_to_pop.add(_stack_var)
                        if debug_flag: print("\t\tpop -> ", _stack_var.name)

                        (_, _var_idx) = _stack[_stack_var]
                        for use_var in use_vars_list:
                            
                            #* 使用的变量入栈
                            need_to_push.add((use_var, _var_idx))
                            _depended_vars.add(use_var)
                            _depended_vars_detail[_var_idx].add(use_var)
                            
                            #* 使用的函数入栈
                            _f_stack = _f_stack.union(use_funs_list)
                            
                            if debug_flag: print("\t\tpush -> VAR:{} CALLED_FUNS:{}".format(use_var.name, [(c.name, f.name) for (c, f) in use_funs_list]))

                for _pop_var in need_to_pop: _stack.pop(_pop_var)
                for (_push_var, _var_idx) in need_to_push: _stack[_push_var] = (_push_var, _var_idx)
            
            if debug_flag: print("當前路徑的最終計算結果: ", [v.name for v in _depended_vars])
            for _used_var_idx in _depended_vars_detail:
                if debug_flag: print("\t-> {} {}".format(used_vars[_used_var_idx].name, [(v.name, type(v)) for v in _depended_vars_detail[_used_var_idx]]))
                
        
        # 合并不同path的结果
        final_result = set()
        for path_result in paths_result:
            final_result = final_result.union(path_result)

        final_detail_result: Dict[Variable, set(Variable)] = {}
        for path_detail_result in paths_detail_result:
            for _var_idx in path_detail_result:

                _interact_used_var:Variable = used_vars[_var_idx]
                _depended_vars = path_detail_result[_var_idx]

                if _interact_used_var not in final_detail_result:
                    final_detail_result[_interact_used_var] = _depended_vars

                    #! msg.sender之列的solidity变量是不需要进行依赖分析的，他们只依赖自己
                    if type(_interact_used_var) == SolidityVariableComposed:
                        final_detail_result[_interact_used_var].add(_interact_used_var)
                        final_result.add(_interact_used_var)
                else:
                    final_detail_result[_interact_used_var].union(_depended_vars)

        print("最終的合并結果:")
        for __var in final_detail_result:
            print("\t {} -> {}".format(__var.name, [v.name for v in final_detail_result[__var]]))

        #! 如果一个变量没有依赖，表明这个变量就是入参
        # function_analyzer.interaction_points[interaction_point]["data_dependeds"] = final_result
        # function_analyzer.interaction_points[interaction_point]["detail_data_dependeds"] = final_detail_result

        return final_result, final_detail_result