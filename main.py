import argparse
import os
from src.semantic_analyzer import SemanticAnalyzer
from src.contract_info_collector import ContractInfoCollector
from src.function_analyzer import FunctionAnalyzer
from src.reentrancy_detector import ReDetector
from rich.console import Console as Rich_Console
from slither.core.declarations.function import Function as SFunction
from slither.core.declarations import Contract as SContract
from slither.core.cfg.node import Node, NodeType
import re
from slither.core.declarations.solidity_variables import SolidityFunction

def argParse():
    parser = argparse.ArgumentParser(description='manual to this script')
    parser.add_argument('-id', type=int, default=-1)  # clean all flag
    args = parser.parse_args()
    return args.id

if __name__ == '__main__':

    _id = argParse()
    if _id < 0: raise RuntimeError("请输入正确的ID")
        
    target_dir = "dataset/00{}".format(str(_id)) if _id < 10 else "dataset/0{}".format(str(_id))
    if not os.path.exists(target_dir):
        raise RuntimeError("输入的ID不存在")
    
    rich_console = Rich_Console()

    contract_info = ContractInfoCollector(target_dir)
    contract_info.get_sol_ver() # 编译准备
    contract_info.get_slither_result()  # 利用slither进行编译
    contract_info.do_slither_re_detector() # reentrant相关分析
    contract_info.get_external_functions() # 获得目标函数

    # SemanticAnalyzer
    semantic_analyzer = SemanticAnalyzer(contract_info, target_dir)
    call_graph = semantic_analyzer.get_call_graph() # call graph construct
    semantic_analyzer.get_construct_state_variables()
    
    # 开始分析具体函数
    for target_id in contract_info.target_functions:

        #* 获得目标函数：external public
        target_contract = contract_info.target_functions[target_id]['c']
        target_function:SFunction = contract_info.target_functions[target_id]['f']
        slither_core    = contract_info.target_functions[target_id]['s']

        #* 开始分析
        if( _id == 999 and target_function.name != "deposit"): continue
        rich_console.rule(f"分析對象：{target_function.full_name} VISIBILITY: {target_function.visibility}")  
        
        #* 分析器初始化
        function_analyzer = semantic_analyzer.get_function_analyzer(target_function)
        if function_analyzer is None:
            function_analyzer = FunctionAnalyzer(target_function, target_contract, slither_core, call_graph, target_dir)
            semantic_analyzer.add_function_analyzer(function_analyzer)
        
        #* 分析函数所有语句，判断当前函数是否有interaction操作
        function_analyzer.analyze_function_with_interaction(True) 
        if function_analyzer.can_interaction():
            
            #* 获得CFG，每条语句的变量使用情况
            function_analyzer.analyze_function_initialize()         

            # TODO：判断当前函数有没有可以被利用的interact操作：transfer out/mint
            risky_interaction_type = function_analyzer.analyze_interaction_financial_risky() 
            
            #* （过程内）分析函数内 effect after interaction 变量集合
            function_analyzer.get_all_stmts_after_interaction()  
            re_pattern, wait_inter_analyze = function_analyzer.analyze_effect_after_interaction_intraprocedural_analysis(True) # 寻找在interact之后修改的全局变量
            contract_info.add_interaction_function(target_function, function_analyzer, risky_interaction_type, re_pattern) # 记录
            print(f"當前函數的交易类型 -> {risky_interaction_type} re_pattern_flag:{re_pattern}")
            
            #TODO: 過程间分析 --> 得到過程间修改的全局變量

            if risky_interaction_type in ["out", "mint"]:
                print("\t->當前函數的危险interaction类型为: ", risky_interaction_type)
                
                for interaction_point in function_analyzer.interaction_points:

                    #* 判斷interaction依賴的變量
                    semantic_analyzer.analyze_data_dependecy_with_intraprocedural(target_function, interaction_point, False) #!!必須先分析data dependency, 再分析ppt

                    #* 判斷執行路徑是否可衝入，有無path protect technology的保護 
                    (ppt, info) = semantic_analyzer.analyze_path_protection_technology(target_function, interaction_point)

                    #* 记录当前函数为 reenter risky function
                    if not ppt: contract_info.add_reenter_risky_function(target_function) # 记录

    
    rich_console.rule("开始污点分析")
    print("污點分析入口：",  [contract_info.interaction_functions[fid]['f'].name for fid in contract_info.interaction_functions])
    print("污點分析sink: ", [contract_info.reenter_risky_functions[fid].name for fid in contract_info.reenter_risky_functions])
    
    reentry_detect_result = []
    #* 基於污點分析的 interaction_function --> canreenter_transferout_function
    for interaction_fid in contract_info.interaction_functions:

        print("\t - > 當前的source 為: {} {}".format(
            contract_info.interaction_functions[interaction_fid]["f"].name,
            contract_info.interaction_functions[interaction_fid]["re_pattern"]
        ))
        interaction_finfo = contract_info.interaction_functions[interaction_fid]
        if not interaction_finfo["re_pattern"]: continue #* re_pattern 既 effect after interaction

        interaction_func :SFunction   = interaction_finfo["f"]
        interfunc_analyzer :FunctionAnalyzer = interaction_finfo["a"]

        #* self.effect_after_interact_svars[str(stmt.node_id)] = [v for v in stmt.state_variables_written]
        tainted_sources_info = interfunc_analyzer.effect_after_interact_svars
        tainted_sources = []
        for interact_stmtid in tainted_sources_info:
            tainted_sources += tainted_sources_info[interact_stmtid]
        tainted_sources = set(tainted_sources)
        
        # TODO: 隱含的餘額修改，目前簡單的使用字符串表示
        #! 隱藏的effect -> 修改了balance
        print("污点源列表: ", [v.name for v in tainted_sources], "for FUNC: ", interaction_func.name)

        
        for risky_func_id in contract_info.reenter_risky_functions:
            
            _next = False

            #* 分析是否可以进行重入攻擊 interaction_func -> risky_func
            risky_func = contract_info.reenter_risky_functions[risky_func_id]
            risky_func_analyzer = semantic_analyzer.get_function_analyzer(risky_func)
            print("開始進行污點分析 from: {} to:{}".format(interaction_func.name, risky_func.name))

            #*  self.interaction_points[str(stmt.node_id)] = {"stmt":stmt, "to_c":c, "to_f":f }
            for interaction_point_id in risky_func_analyzer.interaction_points:
                interaction_point:Node = risky_func_analyzer.interaction_points[interaction_point_id]["stmt"]
                _to_tainted_sinks = risky_func_analyzer.interaction_points[interaction_point_id]["data_dependeds"]

                for source in tainted_sources:
                    if source in _to_tainted_sinks:
                        
                        ret_info = "存在重入攻擊 {} -> {}".format(interaction_func.name, risky_func.name)
                        reentry_detect_result.append(ret_info)
                        _next = True
                        
                        print(ret_info)
                        break
                
                #TODO: 一旦risky操作被依赖于balance且前面有transfer，则被认为可能被重入
                __to_tainted_sinks_balances = risky_func_analyzer.interaction_points[interaction_point_id]["balance_dependeds"]
                if len(__to_tainted_sinks_balances) > 0 :
                    
                    ret_info = "BALANCE: 存在重入攻擊 {} -> {}".format(interaction_func.name, risky_func.name)
                    reentry_detect_result.append(ret_info)
                    _next = True
                    
                    print(ret_info)
                    break

                
                if _next: break #* 結束當前函數，進入下一個函數
        
    print("重入漏洞检测结果: ") 
    for info in reentry_detect_result:        
        print("-> ", info)
            



    



    
    
    

