import argparse
import json
import os
from src.semantic_analyzer import SemanticAnalyzer
from src.contract_info_collector import ContractInfoCollector
from src.function_analyzer import FunctionAnalyzer
from rich.console import Console as Rich_Console
from slither.core.declarations.function import Function as SFunction
from slither.core.declarations import Contract as SContract
from slither.core.cfg.node import Node, NodeType
import re
from slither.core.declarations.solidity_variables import SolidityFunction
from slither.slithir.operations import Delete

def arg_parse():
    parser = argparse.ArgumentParser(description='manual to this script')
    parser.add_argument('-id', type=int, default=-1)  # clean all flag
    args = parser.parse_args()
    return args.id

def get_contract_info(target_dir):
    
    contract_info = ContractInfoCollector(target_dir)
    contract_info.get_sol_ver() # 编译准备
    contract_info.get_slither_result()  # 利用slither进行编译
    contract_info.do_slither_re_detector() # reentrant相关分析
    contract_info.get_public_functions_and_selfimplement_risk_functions() # 获得函数列表

    return contract_info


def get_semantic_analyzer(contract_info:ContractInfoCollector, target_dir):
    
    semantic_analyzer = SemanticAnalyzer(contract_info, target_dir)
    semantic_analyzer.get_call_graph()  #* 得到主分析對象的call graph
    semantic_analyzer.get_construct_state_variables() #* 得到主分析對象在構造函數中定義的變量
    
    return semantic_analyzer

def do_analyze_function(semantic_analyzer:SemanticAnalyzer, contract_info:ContractInfoCollector, target_id):
    """
    分析目标函数：
    得到所有 interaction point 和 其相关的全局变量以及性质
    """
    
    target_contract:SContract = contract_info.public_functions[target_id]['c']
    target_function:SFunction = contract_info.public_functions[target_id]['f']
    slither_core = contract_info.public_functions[target_id]['s']
    
    if( _id == 999 and target_function.name != "safeTransferFrom"): 
        rich_console.print("[red bold underline] 存在過濾器")
        rich_console.print("[red bold underline] 存在過濾器")
        return
    
    #* 开始分析
    rich_console.rule(f"分析對象：{target_function.name} VISIBILITY: {target_function.visibility}")  
    
    #* 函数分析器初始化
    function_analyzer = semantic_analyzer.get_function_analyzer(target_function)
    if function_analyzer == None: raise RuntimeError("根函數創建CFG失敗....")

    #* 分析函数所有语句，判断当前函数是否存在interaction操作
    function_analyzer.analyze_function_interactions(debug_flag=True) 
    if function_analyzer.is_contain_interaction():
        
        #* 得到從 target_function 到 interaction 的調用棧
        semantic_analyzer.analyze_call_stack_for_interactions(target_contract, target_function)
        
        #* 对目标函数内的每个interaction进行语义分析
        semantic_analyzer.analyze_semantics_for_all_interactions(target_contract, target_function)
        
        #* 所有 interaction point 的解析属性
        ppt, hijacked, risk, risk_type = function_analyzer.get_function_properties()
        print(f"PROTECT:{ppt}  當前函數是否可被劫持:{hijacked} - 是否存在重入金融风险:{risk} {risk_type}")

         #* 分析完成后打印查看每个interaction point的结果，有ppt的一概不管
        if not ppt: function_analyzer.display_interactions_informations(True)
        
        #* 记录控制流可能被劫持的函数，有ppt的一概不管
        if (not ppt and hijacked): contract_info.add_can_be_hijacked_function(target_function, function_analyzer, hijacked, risk, risk_type)
        
        #* 记录存在金融风险的函数，有ppt的一概不管
        if (not ppt and risk):  contract_info.add_finical_risk_function(target_function, function_analyzer, None)    
        

def do_tainted_analyze():
    
    #* tainted source
    for fid in contract_info.canbe_hijacked_functions:
        pass
    
    #* tainted sinks related state vars
    
    pass

if __name__ == '__main__':

    _id = arg_parse()
    if _id < 0: raise RuntimeError("请输入正确的ID")
        
    target_dir = "dataset/00{}".format(str(_id)) if _id < 10 else "dataset/0{}".format(str(_id))
    if not os.path.exists(target_dir):
        raise RuntimeError("输入的ID不存在")
    
    rich_console = Rich_Console()

    #* 收集當前文件夾下智能合約相關信息
    contract_info = get_contract_info(target_dir) 

    #* 得到语义分析器，只能分析主分析对象，辅助分析对象的分析功能暂未开启
    semantic_analyzer = get_semantic_analyzer(contract_info, target_dir)
    
    #* 調用自定義的financial risk函数: 合约自己实现了mint，且被某public funciton 调用
    semantic_analyzer.get_selfimplemented_risky_functions_call_chain()
    
    #* 分析所有的入口函數
    for target_id in contract_info.public_functions:
       do_analyze_function(semantic_analyzer, contract_info, target_id) #* 开始分析函数

    #* 分析針對financial risk函数的间接影响函数 -> state var 修改
    rich_console.rule("\n[blue bold]間接影響分析")
    for risk_fid in contract_info.finical_risk_functions:
        
        risky_fun:SFunction = contract_info.finical_risk_functions[risk_fid][0]
        for _fid in contract_info.public_functions:
            
            _candicate_fun:SFunction = contract_info.public_functions[_fid]["f"]            
            _is_risk, _riskw_svars, risky_analyzer, _candicate_analyzer  = semantic_analyzer.analyze_indirect_risk(risky_fun, _candicate_fun)
            if _is_risk == False: continue
            if _candicate_analyzer.ppt: continue
            if risky_analyzer.re_modifier > 0 and _candicate_analyzer.re_modifier > 0: continue
            
            print(f"当前函数 {_candicate_fun.name} 可能间接影响 {risky_fun.name}, 通过:")
            for w_svar in _riskw_svars:
                
                if w_svar not in _candicate_analyzer.state_vars_write_location: continue
                w_svar_stmts = _candicate_analyzer.state_vars_write_location[w_svar]
                for stmt in w_svar_stmts:
                    
                    print(f"\t修改 -> {w_svar.name} 在语句 {stmt.expression}")
                    if str(stmt.node_id) in _candicate_analyzer.interaction_points: continue
                    
                    _candicate_analyzer.indirect_risk_points[str(stmt.node_id)] = {
                        "stmt":stmt, 
                        "to_c":_candicate_fun.contract_declarer,
                        "to_f":_candicate_fun, 
                        "action_type": "write risky state vars",
                        "data_dependeds": [],
                        "control_dependeds": [],
                        "balance_dependeds": [],
                        "need_cross_contract_analysis": []
                    }
                    
                    dd_svars, cd_svars = semantic_analyzer.analyze_semantics_for_indirect_risk_point(_candicate_fun, str(stmt.node_id))
                    print(f"该修改变量语句依赖的全局变量为 {[v.name for v in (dd_svars | cd_svars)]}")
                    _candicate_analyzer.indirect_risk_points[str(stmt.node_id)]["data_dependeds"] = dd_svars
                    _candicate_analyzer.indirect_risk_points[str(stmt.node_id)]["control_dependeds"] = cd_svars

            #* 加入队列
            contract_info.add_indirect_risk_function(_candicate_fun, _candicate_analyzer, risky_fun)   
            
    #* 寻找辅助对象中的可疑重入点
    if contract_info.is_need_analyze_auxiliary():
        
        #* 收集信息
        contract_info.get_auxiliary_slither_result()
        contract_info.get_auxiliary_target_functions()
        
        #* 針對aux中調用main接口的函數，得到其全局變量修改列表
        #! main内部的污染源想要污染aux的狀態,必須通過調用main的接口
        for (aux_function, _, _) in contract_info.auxiliary_call_main_functions:
            fanalyzer = semantic_analyzer.get_function_analyzer(aux_function)
            fanalyzer.get_all_written_storage_vars()
        
        #* 开始分析
        for (aux_c, aux_f, main_c) in contract_info.auxiliary_analyze_targets:
            
            #* 獲得當前函數返回值以來的全局變量
            _, depend_aux_svars = semantic_analyzer.analyze_return_depended_vars_in_function(aux_f)
            
            #* 根據上一步的全局變量得到可疑重入點
            re_points = semantic_analyzer.analyze_auxiliary_reentry_point(depend_aux_svars)
            
            contract_info.auxiliary_reenter_points = contract_info.auxiliary_reenter_points.union(re_points)
            print(f"可疑的輔助對象重入點為：{[(f.name, mc.name, mf.name) for (f, mc, mf) in re_points]}")
    
    #* 分析辅助对象中的可疑重入点中调用的主对象接口，且判断这些接口是否依赖taint source
    if contract_info.is_need_analyze_auxiliary():
        
        #* 尋找auxiliary重入函數中調用的main對象的接口
        risk_main_funcs_called_by_aux_reenterpoint = contract_info.get_sink_functions_in_main()
        
        #* main對象中的Taint source 通過影響 risk_main_funcs_called_by_aux_reenterpoint 來影響aux中的函數
        for (aux_f, main_fun, main_contract) in risk_main_funcs_called_by_aux_reenterpoint:
            
            main_f_analyzer, depend_main_svars = semantic_analyzer.analyze_return_depended_vars_in_function(main_fun)
            
            main_f_analyzer.analyze_return_point_for_auxiliary(depend_main_svars)
            
            contract_info.add_finical_risk_function(main_fun, main_f_analyzer, aux_f) #* 加入到危险函数列表
    
    rich_console.rule("开始污点分析")
    print("污點分析source:",  [contract_info.canbe_hijacked_functions[fid]['function'].name for fid in contract_info.canbe_hijacked_functions])
    print("污點分析sink: ",   [f.name for (f, _, _) in contract_info.finical_risk_functions.values()])

    #* 基於污點分析的 interaction_function --> canreenter_transferout_function
    reentry_detect_result = []
    for fid in contract_info.canbe_hijacked_functions:
        
        canbe_hijacked_function :SFunction   = contract_info.canbe_hijacked_functions[fid]["function"]
        canbe_hijacked_function_analyzer :FunctionAnalyzer = contract_info.canbe_hijacked_functions[fid]["analyzer"]
        is_hijacked_function_financial_risk = contract_info.is_financial_risk(canbe_hijacked_function)

        if str(canbe_hijacked_function.name).startswith("_"): continue #TODO: 暴力过滤
        
        print(f"\n污點來源: {canbe_hijacked_function.name}: {is_hijacked_function_financial_risk}")
        
        #* 得到污点源的数据列表
        tainted_sources = []
        for point in canbe_hijacked_function_analyzer.interaction_points:
            #* taint source 必须来自可被劫持的interaction操作
            if canbe_hijacked_function_analyzer.interaction_points_properties[point]["hijacked"] == True:
                tainted_sources += canbe_hijacked_function_analyzer.effect_after_interact_svars[point]
       
        tainted_sources = set(tainted_sources)    #* 去重

        #! 隱藏的effect -> 修改了balance
        print(f"函数 { canbe_hijacked_function.name} 的污点源列表: {[v.name for v in tainted_sources]}")

        for (main_f, main_f_analyzer, aux_f) in contract_info.finical_risk_functions.values():
            
            _next = False #* 當前函數已經分析完，轉到下一個
            risky_func:SFunction = main_f
            risky_func_analyzer:FunctionAnalyzer = main_f_analyzer
            print("開始進行污點分析 from: {} to:{}".format(canbe_hijacked_function.name, risky_func.name))
            
            #* 判斷有沒有互斥鎖
            if canbe_hijacked_function_analyzer.re_modifier > 0 and risky_func_analyzer.re_modifier > 0:
                print("\t -> 當前 調用點和重入點存在 re 互斥鎖的保護，不能重入")
                continue
            
            for interaction_point_id in risky_func_analyzer.interaction_points:
                
                if risky_func_analyzer.interaction_points_properties[interaction_point_id]["financial_risk"] == False: continue
                
                _to_tainted_sinks = risky_func_analyzer.interaction_points[interaction_point_id]["data_dependeds"]
                print("可疑污染点: ", [v.name for v in _to_tainted_sinks], "for FUNC: ", risky_func.name, "Point: ", interaction_point_id)
                for source in tainted_sources:
                    if source in _to_tainted_sinks:
                        
                        if aux_f is not None and is_hijacked_function_financial_risk == True: #* 如果存在跨函數攻擊，mian的起始位置需要為 financial_risk的
                            ret_info = "[DATA_DEP]存在重入攻擊 {} -> {}".format(canbe_hijacked_function.name, aux_f.name)
                            reentry_detect_result.append(ret_info)
                            print(ret_info)
                        elif aux_f is None:
                            ret_info = "[DATA_DEP]存在重入攻擊 {} -> {}".format(canbe_hijacked_function.name, risky_func.name)
                            reentry_detect_result.append(ret_info)
                            print(ret_info)
                        _next = True
                        break
                
                if _next: break
                _to_tainted_sinks = risky_func_analyzer.interaction_points[interaction_point_id]["control_dependeds"]
                print("可疑污染点: ", [v.name for v in _to_tainted_sinks], "for FUNC: ", risky_func.name, "Point: ", interaction_point_id)
                for source in tainted_sources:
                    if source in _to_tainted_sinks:
                        
                        if aux_f is not None and is_hijacked_function_financial_risk == True: #* 如果存在跨函數攻擊，mian的起始位置需要為 financial_risk的
                            ret_info = "[CTRL_DEP]存在重入攻擊 {} -> {}".format(canbe_hijacked_function.name, aux_f.name)
                            reentry_detect_result.append(ret_info)
                            print(ret_info)
                        elif aux_f is None:
                            ret_info = "[CTRL_DEP]存在重入攻擊 {} -> {}".format(canbe_hijacked_function.name, risky_func.name)
                            reentry_detect_result.append(ret_info)
                            print(ret_info)
                        _next = True
                        break
                
                #TODO: 一旦risky操作被依赖于balance且前面有transfer，则被认为可能被重入
                if _next: break
                __to_tainted_sinks_balances = risky_func_analyzer.interaction_points[interaction_point_id]["balance_dependeds"]
                if len(__to_tainted_sinks_balances) > 0 :
                    
                    if aux_f is not None and is_hijacked_function_financial_risk == True: #* 如果存在跨函數攻擊，mian的起始位置需要為 financial_risk的
                        ret_info = "[BALANCE_DEP] 存在重入攻擊 {} -> {}".format(canbe_hijacked_function.name, aux_f.name)
                        reentry_detect_result.append(ret_info)
                        print(ret_info)
                    elif aux_f is None:
                        ret_info = "[BALANCE_DEP] 存在重入攻擊 {} -> {}".format(canbe_hijacked_function.name, risky_func.name)
                        reentry_detect_result.append(ret_info)
                        print(ret_info)
                    _next = True
                    break
                
                if _next: break #* 結束當前函數，進入下一個函數
        
        for (indir_riskf, indir_riskf_analyze, dir_f) in contract_info.indirect_risk_functions.values():
            
            _next = False #* 當前函數已經分析完，轉到下一個
            risky_func:SFunction = indir_riskf
            risky_func_analyzer:FunctionAnalyzer = indir_riskf_analyze
            print("開始進行污點分析 from: {} to:{}".format(canbe_hijacked_function.name, risky_func.name))
            
            #* 判斷有沒有互斥鎖
            if canbe_hijacked_function_analyzer.re_modifier > 0 and risky_func_analyzer.re_modifier > 0:
                print("\t -> 當前 調用點和重入點存在 re 互斥鎖的保護，不能重入")
                continue
            
            for indirect_risk_pid in risky_func_analyzer.indirect_risk_points:
                
                _to_tainted_sinks = risky_func_analyzer.indirect_risk_points[indirect_risk_pid]["data_dependeds"]
                print("可疑污染点: ", [v.name for v in _to_tainted_sinks], "for FUNC: ", risky_func.name, "Point: ", indirect_risk_pid)
                for source in tainted_sources:
                    if source in _to_tainted_sinks:
                        ret_info = "[DATA_DEP]存在间接重入 {} -> {} effect {}".format(canbe_hijacked_function.name, risky_func.name, dir_f.name)
                        reentry_detect_result.append(ret_info)
                        print(ret_info)
                        _next = True
                        break
                    
                _to_tainted_sinks = risky_func_analyzer.indirect_risk_points[indirect_risk_pid]["control_dependeds"]
                print("可疑污染点: ", [v.name for v in _to_tainted_sinks], "for FUNC: ", risky_func.name, "Point: ", indirect_risk_pid)
                for source in tainted_sources:
                    if source in _to_tainted_sinks:
                        ret_info = "[DATA_DEP]存在间接重入 {} -> {} effect {}".format(canbe_hijacked_function.name, risky_func.name, dir_f.name)
                        reentry_detect_result.append(ret_info)
                        print(ret_info)
                        _next = True
                        break

    print("\n重入漏洞检测结果: ") 
    for info in reentry_detect_result:        
        print("-> ", info)
    
            



    



    
    
    

