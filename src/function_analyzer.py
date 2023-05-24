import os
import subprocess
import time
from typing import Dict, List, Set, Union
from slither.slither import Slither
from slither.core.declarations.function import Function as SFunction
from slither.core.declarations import Contract as SContract
from slither.core.declarations import SolidityVariable
from slither.core.variables.variable import Variable as SVariable
from slither.core.variables import StateVariable
from slither.core.cfg.node import Node, NodeType
from slither.detectors.reentrancy.reentrancy import AbstractState
from slither.analyses.data_dependency import data_dependency
from rich.console import Console
import networkx  as nx
import networkx.drawing.nx_pydot as nx_dot
from slither.core.expressions import AssignmentOperationType, AssignmentOperation, Identifier
from slither.slithir.operations import Delete

#* e.g., address(interestRateModel).call(abi.encodeWithSignature(checkpointInterest(uint256),borrowRateMantissa))
from slither.core.expressions.call_expression import CallExpression as SCallExpression 
            

ALL_CONTEXT_INFO = ["send_eth", "calls", "reads", "written", "reads_prior_calls"]
Variable_types = Union[SVariable, SolidityVariable, StateVariable]
KEY_NON_SSA = "DATA_DEPENDENCY"
INTERACT_BOTTOM_API = {
    "transfer(address,uint256)",
    "transferFrom(address,address,uint256)"
}

RE_INTERACTION = "re"
LLC_INTERACTION = "low-level call"
MINT_INTERACTION = "mint"
NORMAL_INTERACTION = "normal"

HIJACKED_INTERACTIONS = ["re", "low-level call"]

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
    def __init__(self, contract:SContract, function:SFunction, slither_core:Slither, call_graph:nx.DiGraph, target_dir) -> None:
        
        #* 唯一標識符
        self.key = f'{str(contract.id)}-{str(function.id)}'
        self.contract_id = str(contract.id)
        self.function_id = str(function.id)
        self.full_name = f"{contract.name}-{function.name}"
        self.name = f"{function.name}"
        self.call_graph :nx.DiGraph = call_graph
        
        # 核心数据结构，各分析器之间共享
        self.slither_core = slither_core

        # 分析目标
        self.target_function:SFunction = function
        self.target_contract:SContract = contract
        self.target_dir = target_dir
        self.target_log_dir = f"{target_dir}//log"

        # 開關
        self.context_key = "REENTRANCY"
        self.init = False    

        # 打印日志相关
        self.rich_console = Console()
        self.display_stmt_call_info_flag = False
        self.display_stmt_var_info_flag = False
        self.display_stmt_context_flag = True
        
        # 函數相關
        self.re_modifier = 0
        self.ppt = 0    # path protect technology
        self.hijacked = None
        self.financial_risk = None
        self.financial_risk_type = None
        self.cfg = None # 当前函数的CFG
        
        # 語句相關
        self.stmt_map:Dict[str, Node] = {} #
        self.stmts_var_infos = {}
        self.stmts_call_infos:Dict[str, set] = {}
        self.stmts_after_interaction = {}
        self.risky_stmts_after_interaction = set() #* interaction后执行mint或者变量修改的语句集合
        self.interaction_points = {} #* 可以被劫持、转账出去、铸造的位置
        self.interaction_points_properties = {} #* hijacked 和 financial_risk 兩種屬性
        self.indirect_risk_points = {} #* 间接危险点：影响直接危险点的点        
        
        #變量相關
        self.effect_after_interact_svars:Dict[str, list] = {} # 每个语句修改的全局变量列表 
        self.return_stmts_vars = {}
        self.written_svars = set()
        self.all_construct_state_vars:set = None #需要初始化時由語義分析器賦值
        self.local_storages_map_to_svar = {} #* int storage VAR = state_var storage和状态变量的指向关系
        self.write_svars_point_to_storage = set()
        self.write_state_vars = set()
        self.state_vars_write_location:Dict[Variable_types, set(Node)] = {}
    
    def is_contain_interaction(self):
        return len(self.interaction_points) > 0

    def is_risky_point(self, point_id):
        
        if point_id in self.interaction_points_properties and \
            self.interaction_points_properties[point_id]["financial_risk"] == True:
                return True
        return False
    
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
                    print(f"\t\t\t-SEND_ETH@:[{idx}] {n.expression}:") #* 例如 to.transfer(amount)
        
        if "calls" in info_types:
            """
                打印当前语句(current_statement)前文中所有外部调用的语句, 且包含过程间分析
            """
            for idx, context_stmt in enumerate(current_statement_state.calls):
                print(f"\t\t-CONTEXT_STMT[{idx}] {context_stmt}")
                for call_stmt in current_statement_state.calls[context_stmt]:
                    print("\t\t\t-CALL_STMT@", call_stmt.expression, " type: ", type(call_stmt.expression))
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

        print(f"\nSTMT: {current_statement.expression} {current_statement.node_id} CALL INFORMATION:")

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

    
    def display_interactions_informations(self, debug_flag=False):
        
        if debug_flag == False: return
        
        print(f"\n 函数 {self.full_name} 的 interaction points相关信息列表:")
        for idx, interaction_point in enumerate(self.interaction_points):
            print(f"\t 第 [{idx}] 个 point {self.stmt_map[interaction_point].expression} 的详细信息")
            pinfo = self.interaction_points[interaction_point]
            properties = self.interaction_points_properties[interaction_point]
            
            print("\t\t -> Access Control {}".format(self.ppt))
            print("\t\t -> Re Modifier    {}".format(self.re_modifier))
            print("\t\t -> 是否可被劫持:   {}".format(properties["hijacked"]))
            if properties["hijacked"] == True:
                sources = self.effect_after_interact_svars[interaction_point]
                print("\t\t -> 污染源变量:     {}".format([v.name for v in sources]))
                
            print("\t\t -> 存在金融风险点: {}".format(properties["financial_risk"]))
            print("\t\t -> 金融风险点类型: {}".format(properties["financial_risk_type"]))
            
            if pinfo["data_dependeds"] == None: pass
            else: print("\t\t -> 数据依赖变量为: {}".format([v.name for v in pinfo["data_dependeds"]]))
            
            if pinfo["control_dependeds"] == None: pass
            else: print("\t\t -> 控制依赖变量为: {}".format([v.name for v in pinfo["control_dependeds"]]))
            
            if pinfo["balance_dependeds"] == None: pass
            else: print("\t\t -> 依赖账号余额为: {}".format([balance for balance in pinfo["balance_dependeds"]]))
            
            if pinfo["need_cross_contract_analysis"] == None: pass
            else: print("\t\t -> 跨函数分析对象: {}".format([(c.name, f.name, rc.name) for (c, f, rc) in pinfo["need_cross_contract_analysis"]]))
   
    def analyze_function_initialize(self, fpng=False):

        print(f"为 {self.target_contract.name} {self.target_function.full_name} 构建函数分析器")
        
        for stmt in self.target_function.nodes:
            if 0: self.display_statement_var_information(stmt)
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
                   if 1: print(f"\t 餘額：{stmt.expression}")
                   self.stmts_var_infos[str(stmt.node_id)]["use_balance"].add(f"balance of {c.name}")
            
            elif ("Balance" in f.name or "balance" in f.name):
                self.rich_console.print(f"[read underline] 疑似使用balance {stmt.expression}")
                self.stmts_var_infos[str(stmt.node_id)]["use_balance"].add(f"balance of {c.name}")         
    
    def analyze_stmt_state_var_info(self, stmt:Node, debug_flag=False):

        if len(stmt.state_variables_written) > 0:
            if debug_flag: print(f"STMT_EFFECT_AFTER_INTERACT: {stmt.expression}")
        
        self.effect_after_interact_svars[str(stmt.node_id)] = [v for v in stmt.state_variables_written]
        
        return set([v for v in stmt.state_variables_written])

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
    
    def analyze_function_interactions(self, debug_flag=False):
        """_summary_
        判断当前函数是否存在interaction操作:
        FUN1-C1
            -> stmt_a @ FUN1-C1: call FUN2-C1
                -> stmt_b @ FUN2-C1: call FUN3-C2
                    -> stmt_c @ FUN3-C2: call token.transfer 
        分析结果为：{"stmt":stmt_a, "to_c":C2, "to_f":FUN3, "action_type": RE}
        
        Args:
            debug_flag (bool, optional): _description_. Defaults to False.
        """
        for stmt in self.target_function.nodes:
            
            if 0: self.display_statement_context(stmt, ALL_CONTEXT_INFO)
            if 0: self.display_statement_call_information(stmt)
            if 0: self.display_statement_var_information(stmt)

            do_interaction, c, f, action_type =  self.analyze_stmt_interaction(stmt)
            if do_interaction:
                
                self.interaction_points[str(stmt.node_id)] = {
                    "stmt":stmt, 
                    "to_c":c,
                    "to_f":f, 
                    "action_type": action_type,
                    "data_dependeds": [],
                    "control_dependeds": [],
                    "balance_dependeds": [],
                    "need_cross_contract_analysis": [],
                }
                if debug_flag: print(f"當前语句 {stmt.expression}  存在可被劫持的interaction操作 {action_type}") 
                
                #* interaction对应的属性初始化
                self.interaction_points_properties[str(stmt.node_id)] = {"hijacked":False, "financial_risk":False,"financial_risk_type":""}
    
    def analyze_stmt_interaction(self, current_statement:Node):
        """ 
            判斷當前語句是否可以包含interaction操作
            1: 可以re的interaction操作
            2: 不可以re的interaction操作
        """
        
        for (called_var, called_llc) in current_statement.low_level_calls:
            if called_llc == "call":  
                return True, self.target_contract, current_statement.function, LLC_INTERACTION

        if self.context_key not in current_statement.context:
            return False, None, None, False
        
        # 上下文信息：包含前文所有语句的上下文信息 + 当前语句的上下文信息
        context_of_current_statement:AbstractState = current_statement.context[self.context_key]
        if current_statement not in context_of_current_statement.calls:
             return False, None, None, False
        
        #* 上下文中有直接调用 transfer 接口的
        for idx, context_stmt in enumerate(context_of_current_statement.send_eth):
            for send_eth_stmt in context_of_current_statement.send_eth[context_stmt]:
                self.display_statement_call_information(send_eth_stmt)
                if ".transfer(" in str(send_eth_stmt.expression):
                    return True, send_eth_stmt.function.contract_declarer, send_eth_stmt.function, NORMAL_INTERACTION

        #TODO 当前语句可能是一个函数调用，其内部可能包含多个interaction操作，规避
        call_stmts = context_of_current_statement.calls[current_statement] # token.transfer/transferFrom
        for call_stmt in call_stmts:
            
            #* 调用LOW-LEVEL CALL   e.g., FUN1 call FUN2 {add.call.valu()}
            for (called_var, called_llc) in call_stmt.low_level_calls:
                if called_llc == "call" \
                    and "abi.encodeWithSignature" not in str(call_stmt.expression): #todo:规避 for 008 
                    print(f"\t -> CALLED VAR:{called_var.name} CALLED_LLC:{called_llc} @ {call_stmt.expression}")
                    return True, call_stmt.function.contract_declarer, call_stmt.function, LLC_INTERACTION
            
            #* 调用其他合约的接口
            for (called_contract, called_api) in call_stmt.high_level_calls:
                
                all_inherit_cnames = [c.name for c in called_contract.inheritance]
                
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
                if ("ERC721" in all_inherit_cnames or "IERC721" in all_inherit_cnames) \
                    and called_api.name in ["onERC721Received", "transfer", "transferFrom", "safeTransferFrom"]:
                    print(f"\t -> CALLE_API_STMT: {call_stmt.expression}")
                    print(f"\t -> ERC721 INTERACT: {called_contract.name}  {called_api.full_name}")
                    return True, called_contract, called_api, RE_INTERACTION
                
                #* 非直接為ERC777, 而是繼承自繼承自ERC777
                if( "ERC777" in all_inherit_cnames or "ERC1155" in all_inherit_cnames)\
                    and called_api.name in ["transfer", "transferFrom", "safeTransferFrom"]:
                    print(f"\t -> CALLE_API_STMT: {call_stmt.expression}")
                    print(f"\t -> ERC777 INTERACT: {called_contract.name}  {called_api.full_name}")
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
                
                #* openzeppelin的Address庫
                if "Address" == called_contract.name and called_api.name == "sendValue":
                    print(f"\t -> CALLE_openzeppelin: {call_stmt.expression}")
                    print(f"\t -> openzeppelin lib: {called_contract.name}  API:{called_api.full_name}")
                    return True, called_contract, called_api, LLC_INTERACTION
                    
                print(f"\t -> UNKNOWN TOKEN_API INTERACT: {called_contract.name}  {called_api.full_name}")
                if "withdraw" in called_api.full_name:
                    return True, called_contract, called_api, NORMAL_INTERACTION

        return False, None, None, False
    
    def analyze_effect_after_interaction_point(self, interaction_point:Node):
        """
        对于指定的interaction point, 得到：
        1. 之后修改的全局变量
        2. 修改全局变量的语句
        """
        state_vars = set()
        stmts_after_interaction = {}
        
        #* 寻找interact之后执行的语句，包含当前的interaction_point
        paths = nx.all_simple_paths(self.cfg, str(interaction_point.node_id), "EXIT_POINT")
        for path in paths:
            for stmt_id in path:
                if stmt_id not in stmts_after_interaction and stmt_id != "EXIT_POINT":
                    stmts_after_interaction[stmt_id] = 1
        
        #* 寻找修改的变量
        for stmt_id in stmts_after_interaction:
            stmt_info:Node = self.stmt_map[stmt_id]
            if len(stmt_info.state_variables_written) > 0:
                self.risky_stmts_after_interaction.add(stmt_info)
                for v in stmt_info.state_variables_written: state_vars.add(v)
            
            if  stmt_id in self.interaction_points and self.interaction_points[stmt_id]["action_type"] == MINT_INTERACTION:
                self.risky_stmts_after_interaction.add(stmt_info)
        
        return state_vars, self.risky_stmts_after_interaction
    
    def analyze_interaction_properties(self, interaction_point):
        
        #* 1:判断当前的interaction_point是否能够被攻击者劫持控制流
        interaction_type = self.interaction_points[interaction_point]["action_type"]
        if interaction_type in HIJACKED_INTERACTIONS:
            self.interaction_points_properties[interaction_point]["hijacked"] = True
        else: 
            self.interaction_points_properties[interaction_point]["hijacked"] = False
        
        #* 2:判断当前的interaction_point是否存在重入金融风险
        financial_risk_keys = ["sendValue", "withdraw", "borrow", "doTransferOut", "mint", "_safeMint", "safeMint"]
        no_financial_risk_keys = ["deposit", "doTransferIn"]
        
        if interaction_type == MINT_INTERACTION: 
            self.interaction_points_properties[interaction_point]["financial_risk"] = True
            self.interaction_points_properties[interaction_point]["financial_risk_type"]  = "mint"
        else:
            
            stmt:Node = self.interaction_points[interaction_point]["stmt"]
            if "msg.sender.call" in str(stmt.expression): #* 直接调用交易发起方
                    self.interaction_points_properties[interaction_point]["financial_risk"] = True
                    self.interaction_points_properties[interaction_point]["financial_risk_type"] = "out"
                    return  self.interaction_points_properties[interaction_point]["hijacked"], \
                            self.interaction_points_properties[interaction_point]["financial_risk"] ,\
                            self.interaction_points_properties[interaction_point]["financial_risk_type"]  
            
            call_stack = self.interaction_points[interaction_point]["call_stack"]
            for (_, fname) in call_stack:
                
                if fname in financial_risk_keys: 
                    self.interaction_points_properties[interaction_point]["financial_risk"] = True
                    self.interaction_points_properties[interaction_point]["financial_risk_type"] = "out"
                    break
                
                if fname in no_financial_risk_keys:
                    self.interaction_points_properties[interaction_point]["financial_risk"] = False
                    self.interaction_points_properties[interaction_point]["financial_risk_type"] = "no"
                    break
        
        return  self.interaction_points_properties[interaction_point]["hijacked"], \
            self.interaction_points_properties[interaction_point]["financial_risk"] ,\
            self.interaction_points_properties[interaction_point]["financial_risk_type"]    
    
    def analyze_access_control_protection(self, end_point:Node):
        """
        entry_point ---> end_point
            判断执行路径上有没有path protection technology:
            1. Access Control Before Payment
            2. Protection by Modifiers
        Args:
            end_point (Node): 分析的结束节点
        """
        ac_flag = False
        modifier_cnt = len([m.name for m in self.target_function.modifiers if "nonReentrant" in m.name])
        
        for modifier in self.target_function.modifiers:
            
            if "onlyOwner" in modifier.name:
                ac_flag = True
                ppt = "Protected by onlyOwner"
                print("{} - INFO:{}".format(modifier.name, ppt))
                return modifier_cnt, ac_flag, ppt, modifier

            if 0 and str(modifier.name).startswith("only"): #! 造成漏報
                ac_flag = True
                ppt = "Protected by only-type modifier"
                print("{} - INFO:{}".format(modifier.name, ppt))
                return modifier_cnt, ac_flag, ppt, modifier

        paths = nx.all_simple_paths(self.cfg, "0", str(end_point.node_id))
        for path in paths:
            for stmt_id in path:
                stmt_info:Node = self.cfg.nodes[stmt_id]["node"]
                
                if stmt_info.is_conditional(include_loop=False):
                    current_read_vars = set([v for v in stmt_info.variables_read])
                    #* require(msg.sender == CONST_vAR)
                    if "msg.sender" in [v.name for v in current_read_vars]:
                        for v in current_read_vars:
                            if v in self.all_construct_state_vars:
                                ac_flag = True
                                ppt = "Protected by Constructed Vars"
                                print("{} - INFO:{}".format(stmt_info.expression, ppt))
                                return modifier_cnt, ac_flag, ppt, stmt_info

                    #TODO: 条件较粗
                    if "msg.sender ==" in str(stmt_info.expression) \
                        or "== msg.sender" in str(stmt_info.expression):
                        ac_flag = True
                        ppt = "Protected by msg.sender check" 
                        print("{} - INFO:{}".format(stmt_info.expression, ppt))
                        return modifier_cnt, ac_flag, ppt, stmt_info

                    #TODO: modifier保护
                    
        return modifier_cnt, ac_flag, "No Path Protected", None
    
    def analyze_return_point_for_auxiliary(self, svars):
        
        self.interaction_points["return"] = {
            "action_type": "return",
            "data_dependeds": svars,
            "control_dependeds": [],
            "balance_dependeds": [],
            "need_cross_contract_analysis":[]
        }
        self.interaction_points_properties["return"] = {
            "hijacked": False,
            "financial_risk": True,
            "financial_risk_type": "cross_contract_return"
        }
        
    def get_financial_risk_svars(self):
        """
        分析对于给定的financial risk函数, 分析每个financial risk interaction point
            -> 针对每个point, 得到该point依赖的状态变量
                -> 分析能够修改这些变量的函数作为间接的函数入口
        
        Args:
            target_func (SFunction): _description_
            target_analyzer (FunctionAnalyzer): _description_
        """
        risk_svars = set()
        for point in self.interaction_points_properties:
            
            is_risk = self.is_risky_point(point)
            if is_risk == False: continue
            
            risk_svars = risk_svars.union(self.interaction_points[point]["data_dependeds"])
            risk_svars = risk_svars.union(self.interaction_points[point]["control_dependeds"])
        
        return risk_svars
    
    def get_all_return_variable_stmts(self):
        """
            当前函数所有 return语句和其return的返回值
        """
        print(f"分析函數 {self.target_function.name} {self.target_function.is_implemented} {self.target_function.id} 的返回值：")
        for stmt in self.target_function.nodes:
            if stmt.will_return is True:
                print(f"\t -> EXP: {stmt.expression}")
                print(f"\t -> EXP: {len(stmt.variables_read)}")
                # print("\t -> EXP: {} read: {}".format(stmt.expression, [v.name for v in stmt.variables_read]))
                self.return_stmts_vars[str(stmt.node_id)] = {"vars": [v for v in stmt.variables_read]}
                
        return self.return_stmts_vars
    
    def get_function_properties(self):
        """
        综合函数内部所有的interaction point的属性
        得到function-level的属性
        """
        
        hijacked = False
        financial_risk = False
        financial_risk_type = ""
        for _properties in self.interaction_points_properties.values():
            hijacked |= _properties["hijacked"]
            financial_risk |= _properties["financial_risk"]
            financial_risk_type += _properties["financial_risk_type"] + "  "
        
        self.hijacked = hijacked
        self.financial_risk = financial_risk
        self.financial_risk_type = financial_risk_type
        
        return self.ppt, hijacked, financial_risk, financial_risk_type
    

    def get_called_function_stmt(self, called_functoin:SFunction):
        
        stmt_function_calling:Node = None
        for stmt in self.target_function.nodes: 
            for in_called_function in stmt.internal_calls:
                if in_called_function.full_name == called_functoin.full_name:
                    stmt_function_calling = stmt
                    break
            
            if stmt_function_calling != None: break
            for (_, high_called_fun_or_var)  in stmt.high_level_calls:  
                if high_called_fun_or_var.full_name == called_functoin.full_name:
                    stmt_function_calling = stmt
                    break
        
        return stmt_function_calling
     
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
            
        cfg.add_node("EXIT_POINT", label="EXIT_POINT", node="EXIT_POINT")
        for leaf_node in leaf_nodes:
            cfg.add_edge(leaf_node, "EXIT_POINT")
        
        self.cfg = cfg
        os.remove(cfg_dot_file)
        return True

    def get_graph_png(self, flag=False):
        
        if not flag: return
        
        tmp_cfg = nx.DiGraph(self.cfg)
        for node_id in tmp_cfg.nodes: tmp_cfg.nodes[node_id].pop("node")
        
        cfg_dot_file = "{}//{}_cfg.dot".format(self.target_log_dir, self.target_function.name)
        cfg_png_file = "{}//{}_cfg.png".format(self.target_log_dir, self.target_function.name)

        nx_dot.write_dot(tmp_cfg, cfg_dot_file)
        subprocess.check_call(["dot", "-Tpng", cfg_dot_file, "-o", cfg_png_file])
       

    def get_all_written_storage_vars(self):
        """
        storage var 分爲2種
        1. state var
        2. storage var
        """
        for write_state_var in self.target_function.state_variables_written:
            self.write_state_vars.add(write_state_var)

        for stmt in self.target_function.nodes:
            
            for svar_write in stmt.state_variables_written:
                if svar_write not in self.state_vars_write_location:
                    self.state_vars_write_location[svar_write] = set()
                self.state_vars_write_location[svar_write].add(stmt)

            delete_op = [ir for ir in  stmt.all_slithir_operations() if isinstance(ir, Delete)]
            write_local_storage_list = [w_v for w_v in stmt.local_variables_written if w_v.is_storage == True]
            read_state_vars = set([v for v in stmt.state_variables_read])
            if 0: print(f"STORAGE_VAR补全 {stmt.expression}: {len(delete_op), len(write_local_storage_list), len(read_state_vars)}")   
            
            #*  Market storage marketToExit (write storage) = markets[address(cToken)] (read state_var); 定義storage
            #* local_storage: marketToExit --> State_Var:markets 的指向关系需要保存
            if len(read_state_vars) != 0 and len(write_local_storage_list) > 0:
                for write_local_storage in write_local_storage_list:
                    self.local_storages_map_to_svar[write_local_storage] = read_state_vars

            #* delete marketToExit.accountMembership[msg.sender];
            #* marketToExit.accountMembership[msg.sender] = 0
            elif len(write_local_storage_list) > 0:
                for write_local_storage in write_local_storage_list:
                    
                    #* 修改被定义过的storage变量 =等价于=> 修改其对应的state_var
                    if write_local_storage in self.local_storages_map_to_svar:
                        for state_var in self.local_storages_map_to_svar[write_local_storage]:
                            self.write_svars_point_to_storage.add(state_var)
                            self.write_state_vars.add(state_var)
                            
                            if state_var not in self.state_vars_write_location:
                                self.state_vars_write_location[state_var] = set()
                            self.state_vars_write_location[state_var].add(stmt)     
                                   
        print(f"當前函數：{self.name} 修改的狀態為{[v.name for v in self.write_state_vars]}")



