import os
import subprocess
import time
from typing import Dict, List, Set, Union
from slither.slither import Slither
from slither.core.declarations.function import Function as SFunction
from slither.core.declarations import Contract as SContract
from slither.core.declarations import SolidityVariable
from slither.core.variables.variable import Variable as SVariable
from slither.core.cfg.node import Node, NodeType
from slither.detectors.reentrancy.reentrancy import AbstractState
from slither.analyses.data_dependency import data_dependency
from rich.console import Console
import networkx  as nx
import networkx.drawing.nx_pydot as nx_dot

ALL_CONTEXT_INFO = ["send_eth", "calls", "reads", "written", "reads_prior_calls"]
Variable_types = Union[SVariable, SolidityVariable]
KEY_NON_SSA = "DATA_DEPENDENCY"
INTERACT_BOTTOM_API = {
    "transfer(address,uint256)",
    "transferFrom(address,address,uint256)"
}

RE_INTERACTION = "re"
MINT_INTERACTION = "mint"
NORMAL_INTERACTION = "normal"

def _recheck_vars_in_expression(stmt_expression, vars):
    """
    规避SSA数据分析的bug
    利用字符串匹配的方式重新计算变量是否真的在语句中

    入参1: 当前语句
    入参2: slither解析出的当前语句使用变量
    """
    ret_vars = []
    miss_vars = []
    for var in vars:
        if var in stmt_expression:
            ret_vars.append(var)
        else:
            miss_vars.append(var)

    if len(miss_vars) != 0:
        # print("\n\t==ERROR IN DATA DEF-USE==")
        # print("\t\t语句：{}".format(stmt_expression))
        # print("\t\t变量：{}".format(miss_vars))
        # print("\t==ERROR IN DATA DEF-USE==\n")
        pass

    return ret_vars

class FunctionAnalyzer:
    def __init__(self, function:SFunction, contract:SContract, slither_core:Slither, call_graph:nx.DiGraph, target_dir) -> None:
        
        # 唯一標識符
        self.function_id = str(function.id)

        # 核心数据结构，各分析器之间共享
        self.slither_core = slither_core

        # 分析目标
        self.target_function:SFunction = function
        self.target_contract:SContract = contract
        self.target_dir = target_dir
        self.target_log_dir = f"{target_dir}//log"

        self.context_key = "REENTRANCY"
        self.init = False    

        # 打印日志相关
        self.rich_console = Console()
        self.display_stmt_call_info_flag = True
        self.display_stmt_var_info_flag = False
        self.display_stmt_context_flag = False

        self.stmt_map = {} #
        self.stmts_var_infos = {}
        self.stmts_call_infos:Dict[str, set] = {}
        self.stmts_after_interaction = {}
        self.interaction_points = {} # 可以被劫持的位置
        self.interaction_point_call_chains = {} # 过程间分析
        self.interaction_out_stmts = {} # 转账出去的的语句
        self.effect_after_interact_svars = {}
        self.return_stmts_vars = {}
        self.written_svars = set()
        self.call_graph :nx.DiGraph = call_graph
        self.cfg = None # 当前函数的CFG

        self.interact_dir = None

    def can_interaction(self):
        return len(self.interaction_points) > 0

    def display_function_context(self):

        if 1: return

        data_dependency_infos:Dict[Variable_types, Set[Variable_types]] = self.target_function.context["DATA_DEPENDENCY"]
        for var in data_dependency_infos:
            print("\t\t-> 变量 {} 依赖于 {}".format(var.name, var.context.keys(), [v.name for v in data_dependency_infos[var]]))

    # types = ["send_eth", "calls", "reads", "written", "reads_prior_calls"]
    def display_statement_context(self, stmt:Node, info_types:List[str]):
        """
            打印重入漏洞相关上下文信息（此处只有上文信息）
        """

        if not self.display_stmt_context_flag:
            return

        if self.context_key not in stmt.context:
            print(f"\t{stmt.expression}")
            print("NOTE: 该语句不包含与重入漏洞相关信息")
            return
        
        print(f"\n\t-----语句: {stmt.expression} 的 {info_types} 上下文信息----")
        current_statement_state:AbstractState = stmt.context[self.context_key]

        # ["send_eth", "calls", "reads"， "written"， "reads_prior_calls"]
        if "send_eth" in info_types:
            """
                打印当前语句(current_statement)前文中所有可以send_eth的语句, 且包含过程间分析
            """
            for idx, context_stmt in enumerate(current_statement_state.send_eth):
                print(f"\t\t-CONTEXT_STMT[{idx}] {context_stmt}:")
                for n in current_statement_state.send_eth[context_stmt]:
                    print(f"\t\t\t-SEND_ETH@:[{idx}] {n.expression}:") # 具体执行操作的语句, 包含过程间分析
        
        if "calls" in info_types:
            """
                打印当前语句(current_statement)前文中所有外部调用的语句, 且包含过程间分析
            """
            for idx, context_stmt in enumerate(current_statement_state.calls):
                print(f"\t\t-CONTEXT_STMT[{idx}] {context_stmt}")
                for call_stmt in current_statement_state.calls[context_stmt]:
                    print("\t\t\t-CALL_STMT@", call_stmt.expression)
                    for (_c, _api) in call_stmt.high_level_calls:
                        print(f"\t\t\t\t-CALL@ LIB: {_c.name} API: {_api.full_name}")
            
        if "reads" in info_types:
            """
                打印当前语句(current_statement)前文中所有读取的全局变量, 且包含过程间分析
            """
            for idx, state_var in enumerate(current_statement_state.reads):
                print(f"\t\t-READ_STATE_VAR[{idx}] NAME: {state_var.name}")
                for n in current_statement_state.reads[state_var]:
                    print("\t\t\t-READ@", n.expression, " IN ", n.function.name)


        if "written" in info_types:
            """
                打印当前语句(current_statement)前文中所有修改的全局变量, 且包含过程间分析
            """
            for idx, state_var in enumerate(current_statement_state.written):
                print(f"\t\t-WRITE_STATE_VAR[{idx}] NAME: {state_var.name}")
                for n in current_statement_state.reads[state_var]:
                    print("\t\t\t-WRTIE@", n.expression, " IN ", n.function.name)

        if "reads_prior_calls" in info_types:
            """
                打印当前语句(current_statement)前文中所有在call操作之前读取的全局变量, 且包含过程间分析
            """
            for idx, context_stmt in enumerate(current_statement_state.reads_prior_calls):
                print(f"\t\t-CONTEXT_STMT[{idx}] {context_stmt}")
                for state_var in current_statement_state.reads_prior_calls[context_stmt]:
                    print("\t\t\t-READ_PRE_CALL@", state_var.name, " IN ", context_stmt.function.name)

        if "events" in info_types:
            pass

        print(f"\t-----上下文信息----\n")

    def display_statement_call_information(self, current_statement:Node):

        if not self.display_stmt_call_info_flag: return

        print(f"\nSTMT: {current_statement.expression} {current_statement.node_id}")

        for idx, in_call in enumerate(current_statement.internal_calls):
            print(f"\tINTERNAL_CALL [{idx}] -> {in_call.name}")
        
        for idx, sol_call in enumerate(current_statement.solidity_calls):
            print(f"\tSOLIDITY_CALL [{idx}] -> {sol_call.name}")

        for idx, ex_call in enumerate(current_statement.external_calls_as_expressions): # messgae call
            print(f"\tEXTERNAL_CALL [{idx}] -> {str(ex_call)}")
            
        for idx, (called_var, call_str) in enumerate(current_statement.low_level_calls): # low_level_call
            print(f"\tLOW_LEVEL_CALL [{idx}] -> {str(called_var)} {str(call_str)}")
        
        for idx, (called_contract, called_fun_or_var) in enumerate(current_statement.high_level_calls):
            if isinstance(called_fun_or_var, SFunction):
                print(f"\tHIGH_CALL [{idx}]-> contract: {called_contract.name}  FUNC: {called_fun_or_var.name}")
            
            if isinstance(called_fun_or_var, SVariable):
                print(f"\tHIGH_CALL [{idx}]-> CONTRACT: {called_contract.name} VAR : {called_fun_or_var.name}")
        
        print(f"\tCONTEXT_KEYS:{current_statement.context.keys()}")


    def display_statement_var_information(self, current_statement:Node):
        
        if self.display_stmt_var_info_flag == False: return
        
        print(f"\n----------------STMT: {current_statement.type} {current_statement.expression} 的變量使用信息------------------")
        if current_statement.node_id == 0:
            for idx, param_var in enumerate(self.target_function.parameters):
                print(f"\tDEF PARAM_VAR [{idx}] -> {param_var.name}")
            return

        for idx, local_variable in enumerate(current_statement.local_variables_read):
            print(f"\tR LOCAL_VAR [{idx}] -> {local_variable.expression}  {local_variable.type}")
        
        for idx, local_variable in enumerate(current_statement.local_variables_written):
            print(f"\tW LOCAL_VAR [{idx}] -> {local_variable.name}  {local_variable.type}")
        
        for idx, state_variable in enumerate(current_statement.state_variables_read):
            print(f"\tR STATE_VAR [{idx}] -> {state_variable.name}  {state_variable.type}")
        
        for idx, state_variable in enumerate(current_statement.state_variables_written):
            print(f"\tW STATE_VAR [{idx}] -> {state_variable.name}  {state_variable.type}")
        
        for idx, sol_variable in enumerate(current_statement.solidity_variables_read): 
            print(f"\tR SOL_VAR [{idx}] -> {sol_variable.name}  {sol_variable.type}")

        if current_statement.variable_declaration is None: 
            print(f"\tDEF VAR NONE")
        else:
            print(f"\tDEF VAR -> {current_statement.variable_declaration.name}  {current_statement.variable_declaration.type}")

    def analyze_function_initialize(self, fpng=False):

        for stmt in self.target_function.nodes:
            if 1: self.display_statement_var_information(stmt)
            self.analyze_stmt_var_info(stmt)
            self.analyze_stmt_call_info(stmt)
            self.analyze_stmt_balance_info(stmt)
            self.stmt_map[str(stmt.node_id)] = stmt
        
        cfg_ret = self.get_function_cfg() 
        if cfg_ret == False: return False #! 获取cfg失敗
        
        self.get_graph_png(flag=fpng)
        self.init = True    
        return True      
    
    def analyze_stmt_balance_info(self, stmt:Node, debug_flag=True):
        """_summary_

        Args:
            stmt (Node): _description_
            debug_flag (bool, optional): _description_. Defaults to False.
        """
        
        if len(self.stmts_call_infos[str(stmt.node_id)]) == 0: return
        for (c, f) in self.stmts_call_infos[str(stmt.node_id)]:
            if ("token" in c.name or "Token" in c.name or "protocol" in c.name or "Protocol" in c.name) \
               and ("Balance" in f.name or "balance" in f.name):
                   if debug_flag: print(f"\t 餘額：{stmt.expression}")
                   self.stmts_var_infos[str(stmt.node_id)]["use_balance"].add(f"balance of {c.name}")
            
            elif ("Balance" in f.name or "balance" in f.name):
                self.rich_console.print(f"[read underline] 疑似使用balance {stmt.expression}")         
                
    
    def analyze_stmt_state_var_info(self, stmt:Node, debug_flag=False):

        if len(stmt.state_variables_written) > 0:
            if debug_flag: print(f"STMT_EFFECT_AFTER_INTERACT: {stmt.expression}")

        for var in stmt.state_variables_written:
            if debug_flag: print(f"\tEFFECT --> name:{var.full_name}, type:{var.type}")
            self.effect_after_interact_svars[str(stmt.node_id)] = [v for v in stmt.state_variables_written]
        
        for (called_contract, called_function) in stmt.high_level_calls:
            print("\tCALL --> {} {}".format(called_contract.name, called_function.name))

    def analyze_stmt_call_info(self, current_statement: Node):
        
        if str(current_statement.node_id) not in self.stmts_call_infos: self.stmts_call_infos[str(current_statement.node_id)] = set()
        
        for in_call_f in current_statement.internal_calls:
            self.stmts_call_infos[str(current_statement.node_id)].add((self.target_contract, in_call_f))

        for (hi_call_c, hi_call_f) in current_statement.high_level_calls:
            self.stmts_call_infos[str(current_statement.node_id)].add((hi_call_c, hi_call_f))
    
    def analyze_stmt_var_info(self, current_statement: Node):

        stmt_var_info = {"def":set(), "use":set(), "use_balance":set()}

        if current_statement.type == NodeType.ENTRYPOINT:
            stmt_var_info["def"] = self.target_function.parameters
            self.stmts_var_infos[str(current_statement.node_id)] = stmt_var_info
            return stmt_var_info # 入参定义

        for local_variable in current_statement.local_variables_read:
            stmt_var_info["use"].add(local_variable)
        
        for local_variable in current_statement.local_variables_written:
            stmt_var_info["def"].add(local_variable)
        
        for state_variable in current_statement.state_variables_read:
            stmt_var_info["use"].add(state_variable)
        
        for state_variable in current_statement.state_variables_written:
            stmt_var_info["def"].add(state_variable)
        
        for sol_variable in current_statement.solidity_variables_read:
            stmt_var_info["use"].add(sol_variable)

        if current_statement.variable_declaration is not  None: 
            stmt_var_info["def"].add(current_statement.variable_declaration)

        self.stmts_var_infos[str(current_statement.node_id)] = stmt_var_info

        return stmt_var_info
            
        

    def analyze_stmt_interaction(self, current_statement:Node):
        """
            判斷當前語句是否可以进行interaction操作
            1: 可以re的interaction操作
            2: 不可以re的interaction操作
        """
        
        for ex_call in current_statement.external_calls_as_expressions:
            if ".call" in str(ex_call): # .call
                return True, self.target_contract, current_statement, RE_INTERACTION
        
        if self.context_key not in current_statement.context:
            return False, None, None, False
        
        # 上下文信息：包含前文所有语句的上下文信息 + 当前语句的上下文信息
        context_of_current_statement:AbstractState = current_statement.context[self.context_key]
        if current_statement not in context_of_current_statement.calls:
             return False, None, None, False
        
        # token.transfer || token.transferFrom 只提取当前语句的上下文信息
        call_stmts = context_of_current_statement.calls[current_statement] # token.transfer/transferFrom
        for call_stmt in call_stmts:
            for (called_contract, called_api) in call_stmt.high_level_calls:
                
                # EIP20NonStandardInterface ERC20XXXX
                if ("ERC20" in called_contract.name or "EIP20" in called_contract.name or "ERC777" in called_contract.name) \
                    and called_api.full_name in [
                        "transfer(address,uint256)",
                        "transferFrom(address,address,uint256)",
                        "safeTransferFrom(IERC20,address,address,uint256)"
                    ]:
                    print(f"\t -> CALLE_API_STMT: {call_stmt.expression} @ {call_stmt.function.name} @ {call_stmt.function.contract_declarer}")
                    print(f"\t -> TOKEN_API INTERACT: {called_contract.name}  {called_api.full_name}")
                    return True, called_contract, called_api, RE_INTERACTION
                
                #* ERC721 onERC721Received 钩子
                if ("ERC721" in called_contract.name) \
                    and called_api.full_name in ["onERC721Received(address,address,uint256,bytes)"]:
                    print(f"\t -> CALLE_API_STMT: {call_stmt.expression}")
                    print(f"\t -> ERC721 INTERACT: {called_contract.name}  {called_api.full_name}")
                    return True, called_contract, called_api, RE_INTERACTION
                
                #* TOKEN MINT 操作
                if ("token" in called_contract.name or "Token" in called_contract.name) \
                    and ("mint" in called_api.full_name):
                    print(f"\t -> CALLE_TOKEN_STMT: {call_stmt.expression}")
                    print(f"\t -> TOKEN MINT: {called_contract.name}  {called_api.full_name}")
                    return True, called_contract, called_api, MINT_INTERACTION
                
                #? Debug
                if ("mint" in called_api.full_name): 
                    self.rich_console.print(f"[bold red] {called_contract.name}  {called_api.full_name}")
                
                
                print(f"\t -> UNKNOWN TOKEN_API INTERACT: {called_contract.name}  {called_api.full_name}")
                if "withdraw" in called_api.full_name:
                    return True, called_contract, called_api, NORMAL_INTERACTION

        return False, None, None, False
    
    
    def analyze_stmt_interaction_direction(self, current_stmt:Node, call_stmt:Node, called_api:SFunction):
        """
            判断interaction的financial risk情况, 转账出去的存在financial risk。

            err = doTransferOut(asset, msg.sender, localResults.withdrawAmount); # current_stmt
            --> mix_test(token, to, amount);  # 中間
                --> token.transfer(to,amount); # real call_stmt
        """

        # 第一个入参就是交易对象
        if called_api.full_name == "transfer(address,uint256)":
            transfer_oject_name = str(call_stmt.expression).split("transfer(")[1].split(",")[0]
            for var in call_stmt.variables_read:
                if var.name  == transfer_oject_name:
                    print(f"交易对象：{var.name} {str(var.type)}")
                    depended_vars = data_dependency.get_dependencies(var, self.target_contract)
                    for depend_var in depended_vars:
                        print(f"\t -> 依賴對象 {depend_var.name} {str(depend_var.type)}")
                        if depend_var.name == "msg.sender":
                            self.interaction_out_stmts[current_stmt] = 1 # 当前语句转账出去，代表有金融风险
                        

    

    def analyze_effect_after_interaction_intraprocedural_analysis(self, debug_flag=False):

        """
            NOTE: 得到interaction之后的全局变量分析, 且只进行过程内分析
        """
        
        stmts_need_interprocedural_analyze = set()

        for stmt_id in self.stmts_after_interaction:

            stmt_info:Node = self.stmt_map[stmt_id]
            self.effect_after_interact_svars[str(stmt_info.node_id)] = [v for v in stmt_info.state_variables_written]
            if debug_flag: print("\t interact之後语句:{} 修改的全局變量: {}".format(stmt_info.expression, [v.name for v in stmt_info.state_variables_written]))

           
            for (called_contract, called_function) in stmt_info.high_level_calls: 
                # if "mint" not in called_function.name: continue #? 此處只根據名單進行過程見分析
                if debug_flag: print(f"\t HIGH_CALL 需要過程閒分析: -> {called_function.name} - {called_contract.name}")
                stmts_need_interprocedural_analyze.add((called_contract, called_function))
                
            for called_function in stmt_info.internal_calls:
                if debug_flag: print(f"\t IN_CALL需要過程閒分析: -> {self.target_contract.name} - {called_function.name}")
                stmts_need_interprocedural_analyze.add((self.target_contract, called_function))

        return len(self.effect_after_interact_svars) > 0, list(stmts_need_interprocedural_analyze)


    def analyze_effect_after_interaction(self):
        """
        TODO: 假设当前一个函数内部只有一个interaction语句
        """
        for interaction_stmt_id in self.interaction_points:
            
            #* 如果此处interaction是不能re的interaction，不需要分析effect after interact vars
            if self.interaction_points[interaction_stmt_id]["action_type"] != RE_INTERACTION: continue

            #* 寻找interact之后执行的语句
            paths = nx.all_simple_paths(self.cfg, str(interaction_stmt_id), "EXIT_POINT")
            stmts_after_interaction = {} # 所有interaction之后执行的语句
            for path in paths:
                for stmt_id in path:
                    if stmt_id not in stmts_after_interaction and stmt_id != "EXIT_POINT":
                        stmts_after_interaction[stmt_id] = 1
            
            #* 寻找修改的变量
            for stmt_id in stmts_after_interaction:
                stmt_info:Node = self.stmt_map[stmt_id]
                self.analyze_stmt_state_var_info(stmt_info)

        return len(self.effect_after_interact_svars) > 0
            
    def analyze_function_with_interaction(self, debug_flag=False):
        """
            利用每个语句的context信息判断当前语句是否进行interaction操作
            语句的context信息已经包含了过程间分析了
        """
        for stmt in self.target_function.nodes:
            
            if 0: self.display_statement_context(stmt, ALL_CONTEXT_INFO)
            if 0: self.display_statement_call_information(stmt)
            if 0: self.display_statement_var_information(stmt)

            do_interaction, c, f, action_type =  self.analyze_stmt_interaction(stmt)
            if do_interaction:
                self.interaction_points[str(stmt.node_id)] = {"stmt":stmt, "to_c":c, "to_f":f, "action_type": action_type}
                if debug_flag: print(f"當前语句 {stmt.expression}  存在可被劫持的interaction操作 {action_type}")       
    
    #! 临时方案
    def analyze_interaction_financial_risky(self):
        """
            可以被攻击者利用的操作类型
            1. 转账出去的操作
            2. mint操作
        """

        out_keys = ["withdraw", "borrow"]
        for out_key in out_keys:
            if out_key in self.target_function.name:
                self.interact_dir = "out"
                return "out"
        
        for interaction_point in self.interaction_points:
            if self.interaction_points[interaction_point]["action_type"] == MINT_INTERACTION:
                return "mint"

        self.interact_dir = "in"
        return "in"
    
    def get_all_return_variable_stmts(self):
        """
            当前函数所有 return语句和其return的返回值
        """
        print(f"分析函數 {self.target_function.name} 的返回值：")
        for stmt in self.target_function.nodes:
            if stmt.will_return is True:
                print("\t -> EXP: {} read: {}".format(stmt.expression, [v.name for v in stmt.variables_read]))
                self.return_stmts_vars[str(stmt.node_id)] = {"vars": [v for v in stmt.variables_read]}
                
        return self.return_stmts_vars
    
    def get_all_stmts_after_interaction(self):
        """
            得到interaction之后能够执行的语句
        """
        for interaction_stmt_id in self.interaction_points:

            #* 如果此处interaction是不能re的interaction，不需要分析effect after interact vars
            if self.interaction_points[interaction_stmt_id]["action_type"] != RE_INTERACTION: continue

            #* 寻找interact之后执行的语句: 1.修改全局变量；2.mint
            paths = nx.all_simple_paths(self.cfg, str(interaction_stmt_id), "EXIT_POINT")
            for path in paths:
                for stmt_id in path:
                    
                    if stmt_id not in self.stmts_after_interaction and stmt_id != "EXIT_POINT":
                        self.stmts_after_interaction[stmt_id] = 1

                    if stmt_id in self.interaction_points and self.interaction_points[stmt_id]["action_type"] == MINT_INTERACTION:
                        self.stmts_after_interaction[stmt_id] = 1
                        
        return self.stmts_after_interaction
    
    def get_all_written_state_variabels(self):
        
        for stmt in self.target_function.nodes:
            write_svars = [v for v in stmt.state_variables_written]
            self.written_svars = self.written_svars.union(write_svars)

        return self.written_svars

    def get_interaction_call_chain(self):

        for interaction_point in self.interaction_point_call_chains:
            call_chains = self.interaction_point_call_chains[interaction_point]
            return call_chains

    
    def get_call_stmt_location(self, call_pair, entry_stmt:Node):

        call_relations = []
        for idx, (callee_function_id, called_function_id) in enumerate(call_pair):
            
            # 调用者信息
            callee_function :SFunction = self.call_graph.nodes[callee_function_id]["f"]
            callee_contract :SContract = self.call_graph.nodes[callee_function_id]["c"]

            # 被调用者信息
            called_function :SFunction = self.call_graph.nodes[called_function_id]["f"]
            called_contract :SContract = self.call_graph.nodes[called_function_id]["c"]
            
            call_relation = {
                "callee_function": callee_function,
                "callee_contract": callee_contract,
                "at_stmt": None,
                "called_function": called_function,
                "called_contract": called_contract,
                "description": None
            }

            description = f"\n{callee_function.name}-{callee_contract.name} CALL: {called_function.name}-{called_contract.name}"
            print(description)

            if idx == 0:
                description += f" @ {entry_stmt.expression}"
                call_relation["at_stmt"] = entry_stmt
                call_relation["description"] = description
                call_relations.append(call_relation)

                print(f"\t-> @ STMT :{entry_stmt.expression}")

            else: # locate the stmt in callee_function for calling called function
                found_flag = False
                for stmt in callee_function.nodes:

                    if 0: self.display_statement_call_information(stmt) # 調試

                    if found_flag == True: break # 避免重複尋找
                    for in_called_function in stmt.internal_calls:
                        if  in_called_function.id == called_function.id \
                            and in_called_function.contract_declarer.id == called_contract.id:

                            description += f" @ {stmt.expression}"
                            call_relation["at_stmt"] = stmt
                            call_relation["description"] = description
                            call_relations.append(call_relation)

                            print(f"\t-> @ STMT :{stmt.expression}")
                            found_flag = True
                            break
                    
                    if found_flag == True: break # 避免重複尋找
                    for (high_called_contract, high_called_fun_or_var)  in stmt.high_level_calls:
                        if  high_called_fun_or_var.id == called_function.id \
                            and high_called_contract.id == called_contract.id:

                            description += f" @ {stmt.expression}"
                            call_relation["at_stmt"] = stmt
                            call_relation["description"] = description
                            call_relations.append(call_relation)

                            print(f"\t-> @ STMT :{stmt.expression}")
                            found_flag = True
                            break
        
        return call_relations

    def get_call_stack(self):
        """
            get the call chain from entry_function --> low-level interaction stmt
        """

        for interact_stmt_id in self.interaction_points:

            stmt :Node = self.interaction_points[interact_stmt_id]["stmt"]
            c :SContract = self.interaction_points[interact_stmt_id]["to_c"]
            f :SFunction = self.interaction_points[interact_stmt_id]["to_f"]
            
            paths = nx.all_simple_paths(self.call_graph, str(stmt.function.id), str(f.id))
            for path in paths: # TODO:此处假设只有一条PATH
                
                call_stack = [(node_id, self.call_graph.nodes[node_id]['f'].name)  for node_id in path]
                if len(call_stack) == 1: continue # 調用棧長度小於2

                call_pair = [(call_stack[id-1][0], call_stack[id][0]) for id in range(1, len(call_stack))]
                print("\n開始解析調用棧: ", [(call_stack[id-1][1], call_stack[id][1]) for id in range(1, len(call_stack))])
                self.interaction_point_call_chains[interact_stmt_id]  = self.get_call_stmt_location(call_pair, stmt)

                return call_stack

    def get_function_cfg(self):

        cfg_dot_file = "{}//{}_cfg.dot".format(self.target_log_dir, self.target_function.name)
        self.target_function.cfg_to_dot(cfg_dot_file)

        cfg: nx.DiGraph = nx.drawing.nx_agraph.read_dot(cfg_dot_file)
        cfg.graph["name"] = self.target_function.name
        cfg.graph["contract_name"] = self.target_contract.name

        if len(cfg.nodes) == 0:
            self.rich_console.print(f"[bold red] 函數 {self.target_function.name} 没有CFG")
            return False
        
        leaf_nodes = []
        for cfg_node_id in cfg.nodes:

            if cfg.out_degree(cfg_node_id) == 0:  # 叶子节点列表
                leaf_nodes.append(cfg_node_id)
            
            cfg.nodes[cfg_node_id]["node"] = self.stmt_map[str(cfg_node_id)]
            
        cfg.add_node("EXIT_POINT", label="EXIT_POINT")
        for leaf_node in leaf_nodes:
            cfg.add_edge(leaf_node, "EXIT_POINT")
        
        self.cfg = cfg
        return True

        # os.remove(cfg_dot_file)

    def get_graph_png(self, flag=False):

        if not flag: return

        cfg_dot_file = "{}//{}_cfg.dot".format(self.target_log_dir, self.target_function.name)
        cfg_png_file = "{}//{}_cfg.png".format(self.target_log_dir, self.target_function.name)

        nx_dot.write_dot(self.cfg, cfg_dot_file)
        subprocess.check_call(["dot", "-Tpng", cfg_dot_file, "-o", cfg_png_file])
       

    
            



