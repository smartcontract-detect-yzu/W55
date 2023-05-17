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

def argParse():
    parser = argparse.ArgumentParser(description='manual to this script')
    parser.add_argument('-id', type=int, default=-1)  # clean all flag
    args = parser.parse_args()
    return args.id



if __name__ == '__main__':

    id = argParse()
    if id < 0: raise RuntimeError("请输入正确的ID")
        
    target_dir = "dataset/00{}".format(str(id)) if id < 10 else "dataset/0{}".format(str(id))
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

        # 获得目标函数：external public
        target_contract = contract_info.target_functions[target_id]['c']
        target_function:SFunction = contract_info.target_functions[target_id]['f']
        slither_core    = contract_info.target_functions[target_id]['s']

        rich_console.rule(target_function.full_name + "   " + target_function.visibility)  

        # 开始分析
        function_analyzer = semantic_analyzer.get_function_analyzer(target_function)
        if function_analyzer is None:
            function_analyzer = FunctionAnalyzer(target_function, target_contract, slither_core, call_graph, target_dir)
            semantic_analyzer.add_function_analyzer(function_analyzer)
        
        function_analyzer.analyze_function_with_interaction() # 代码所有语句，判断当前合约是否可以re-enter
        if function_analyzer.can_interaction():
            
            function_analyzer.analyze_function_initialize()          # 初始化，包括获得cfg
            _dir = function_analyzer.analyze_interaction_direction() # TODO：暫時規避
            print(f"當前函數的交易方向為：{_dir}")

            effect_svar = set()
            function_analyzer.get_all_stmts_after_interaction()  #* 得到interaction之后执行的所有语句列表
            re_pattern, _for_inter_funs = function_analyzer.analyze_effect_after_interaction_intraprocedural_analysis() # 寻找在interact之后修改的全局变量
            contract_info.add_interaction_function(target_function, function_analyzer, _dir, re_pattern) # 记录

            #! 针对mint函数需要进行函数间分析
            inter_svar_effect = set()
            for (called_contract, called_function) in _for_inter_funs:
                called_function_analyzer = semantic_analyzer.get_function_analyzer(called_function)
                if called_function_analyzer is None:
                    called_function_analyzer = FunctionAnalyzer(called_function, called_contract, slither_core, call_graph, target_dir)
                    semantic_analyzer.add_function_analyzer(called_function_analyzer)
                _inter_svar_effect = called_function_analyzer.get_all_written_state_variabels()
                print("INTER SVAR WRITE @ {}-{} {}".format(called_function.name, called_contract.name, [v.name for v in _inter_svar_effect]))
                inter_svar_effect.union(inter_svar_effect)

            if _dir == "out":

                for interaction_point in function_analyzer.interaction_points:

                     #* 判斷interaction依賴的變量
                    (r, d_r)  = semantic_analyzer.analyze_data_dependency(target_function, interaction_point) #!!必須先分析data dependency, 再分析ppt

                    #* 判斷執行路徑是否可衝入，有無path protect technology的保護 
                    (ppt, info) = semantic_analyzer.analyze_path_protection_technology(target_function, interaction_point)

                    #* 一個轉賬出去的操作，且沒有ppt，表示這個函數是值得攻擊者重入的
                    if not ppt: contract_info.add_canreenter_transferout_function(target_function) # 记录


    print("污點分析入口：",  [contract_info.interaction_functions[fid]['f'].name for fid in contract_info.interaction_functions])
    print("污點分析sink: ", [contract_info.canreenter_transferout_functions[fid].name for fid in contract_info.canreenter_transferout_functions])

    #* 基於污點分析的 interaction_function --> canreenter_transferout_function
    for interaction_fid in contract_info.interaction_functions:

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
        print("污点源列表: ", [v.name for v in tainted_sources], "for FUNC: ", interaction_func.name)

        for canre_func_id in contract_info.canreenter_transferout_functions:
            
            _next = False

            #* 分析是否可以进行re interaction_func -> can_re_func
            can_re_func = contract_info.canreenter_transferout_functions[canre_func_id]
            can_re_func_analyzer = semantic_analyzer.get_function_analyzer(can_re_func)
            print("開始進行污點分析 from: {} to:{}".format(interaction_func.name, can_re_func.name))

            #*  self.interaction_points[str(stmt.node_id)] = {"stmt":stmt, "to_c":c, "to_f":f }
            for interaction_point_id in can_re_func_analyzer.interaction_points:
                interaction_point:Node = can_re_func_analyzer.interaction_points[interaction_point_id]["stmt"]
                _to_tainted_sinks = can_re_func_analyzer.interaction_points[interaction_point_id]["data_dependeds"]

                for source in tainted_sources:
                    if source in _to_tainted_sinks:
                        print("存在重入攻擊 {} -> {}".format(interaction_func.name, can_re_func.name))
                        _next = True
                        break
                
                if _next: break #* 結束當前函數，進入下一個函數
                        
                





            # call_stack = function_analyzer.get_call_stack() # entry -> bottom_transfer_operation
            # semantic_analyzer.prepare_for_analyze(call_stack[:-1], target_dir) # 判断分析当前函数所依赖的其它函数是否都创建了分析器
            
            # # 逐層分析，判斷交易方向 存/取
            # call_chain = function_analyzer.get_interaction_call_chain()
            # for idx, _call_relation in enumerate(reversed(call_chain)):
                
            #     print("調用關係: ", _call_relation["description"])

            #     # 调用者信息
            #     callee_function :SFunction = _call_relation["callee_function"]
            #     callee_contract :SContract = _call_relation["callee_contract"]

            #     # 调用者调用被调用者的语句
            #     call_at_stmt :Node = _call_relation["at_stmt"]

            #     # 被调用者信息
            #     called_function :SFunction = _call_relation["called_function"]
            #     called_contract :SContract = _call_relation["called_contract"]

            #     if idx == 0:
            #         if called_function.full_name == "transfer(address,uint256)":
            #             first_param_name = str(call_at_stmt.expression).split("transfer(")[1].split(",")[0]
            #             print("EXP: {}, PARAM_F: {}".format(call_at_stmt.expression, first_param_name))
                        
            #             for v in call_at_stmt.variables_read:
            #                 if v.name == first_param_name:
            #                     (flag, v, param_idx) = semantic_analyzer.analyze_data_dependency(callee_function, call_at_stmt, v)
            #                     if flag == "withdraw":
            #                          pass
            #                     else:
            #                         break
            #     else:
            #         print("一键三连")
            #         print(call_at_stmt.expression)
            #         print(called_function.name)
            #         print(param_idx)
            #         str(call_at_stmt.expression).split(called_function.name + "(")[0]
            #         params = re.findall(re.compile(called_function.name + "\((\S*)\)"), str(call_at_stmt.expression))
            #         param_lists = str(params).split(",")
            #         for var in call_at_stmt.variables_read:
            #             if var.name == param_lists[param_idx-1]:
            #                 print("EXP: {}, PARAM_F: {} @ FUN:{}".format(call_at_stmt.expression, var.name, callee_function.name))
            #                 (flag, v, param_idx) = semantic_analyzer.analyze_data_dependency(callee_function, call_at_stmt, var)
            #                 if flag == "withdraw":
            #                     pass
            #                 else:
            #                     break

            #         pass

                



    



    
    
    

