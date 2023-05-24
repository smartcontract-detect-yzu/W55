import json
import os
import platform
import subprocess
import time
from slither.slither import Slither
from rich.console import Console
from slither.detectors import all_detectors
from typing import Optional, List, Set, Dict, Tuple, Union, TYPE_CHECKING
from slither.core.declarations.function import Function as SFunction
from slither.analyses.data_dependency import data_dependency
from src.function_analyzer import FunctionAnalyzer

COMPIILE_INFO_FILE = "/compile.json"
STANDARD_MINT = ["mint(address,uint256,uint256,bytes)", "mint(address,uint256)"]

class ContractInfoCollector:
    """
        负责收集和储存合约中的信息
    """
    def __init__(self, target_dir) -> None:
        self.target_dir = target_dir
        self.console = Console()

        # 编译相关信息
        self.sol_ver = None   #* 編譯器版本
        self.sol_file = None  #* 主分析文件
        self.auxiliary_sol_file = None #* 輔助文件，用於跨合約分析
        
        # slither
        self.slither:Slither = None  #* 主分析文件的 slither 核心數據結構
        self.auxiliary_slither:Slither = None #* 輔助文件的 slither 核心數據結構

        #! 函數相關信息, 未加auxiliary前綴均爲 主文件對應信息
        self.construct_functions:list[SFunction] = [] #* 主分析文件的構造函數列表
        self.public_functions = {}  #* 主分析文件的公共函數列表，作爲分析入口函數
        self.canbe_hijacked_functions = {}  #* interaction操作可能被hijack的函数列表
        self.canbe_hijacked_points = set()
        self.finical_risk_functions:Dict[str, any] = {} #* 主分析文件的中存在重入金融風險的合約
        self.indirect_risk_functions:Dict[str, any] = {} #* 主分析文件的中存在重入金融風險的合約
        self.selfimplemented_finical_risk_functions:Dict[str, SFunction] = {}
        
        #* 辅助合约相关信息
        self.for_auxiliary_analyze_targets = set() #* 疑似的 (c, f, rc)
        self.auxiliary_analyze_targets = set()     #* 最終找到的 (c, f, rc)
        self.auxiliary_call_main_functions = set() #* 辅助合约中调用主合约接口的函数 (aux_f, called_main_c, called_main_f)
        self.auxiliary_reenter_points = set()
        self.risk_main_funcs_called_by_aux_reenterpoint = set()

        if not os.path.exists(self.target_dir + "/log"): os.mkdir(self.target_dir + "/log")
    
    def add_hijacked_interaction_points(self, fanalyzer:FunctionAnalyzer):
        for interact_point in fanalyzer.interaction_points:
            
            interact_property = fanalyzer.interaction_points_properties[interact_point]
            if interact_property["hijacked"] == True:
                self.canbe_hijacked_points.add((interact_point, fanalyzer))
    
    def add_can_be_hijacked_function(self, f:SFunction, fanalyzer: FunctionAnalyzer, can_re:bool, risky:bool, risky_info:str):
        self.canbe_hijacked_functions[str(f.id)] = {
            "function": f, 
            "analyzer": fanalyzer, 
            "can_re":can_re, 
            "risky":risky,
            "risky_info": risky_info
        }

    def add_indirect_risk_function(self, f:SFunction, fanalyzer:FunctionAnalyzer, directf:SFunction):
        self.indirect_risk_functions[str(f.id)] = (f, fanalyzer, directf)
    
    def add_finical_risk_function(self, f:SFunction, fanalyzer:FunctionAnalyzer, aux_f:SFunction):
        """
        记录存在金融风险的函数列表
        !同时, 只有存在金融风险的函数才有资格判断是否分析辅助合约文件
        """
        for interact_point in fanalyzer.interaction_points:
            analyze_list = fanalyzer.interaction_points[interact_point]["need_cross_contract_analysis"] #[(f,f,rc)]
            for analyze_target in analyze_list: 
                self.for_auxiliary_analyze_targets.add(analyze_target)
              
        self.finical_risk_functions[str(f.id)] = (f, fanalyzer, aux_f)

    def get_sol_ver(self):
        """
        解析compile.json文件, 得到編譯相關信息
        Raises:
            RuntimeError: _description_
        """
        if not os.path.exists(self.target_dir + COMPIILE_INFO_FILE):
            raise RuntimeError("没有编译信息文件compile.json")
        else:
            with open(self.target_dir + COMPIILE_INFO_FILE, "r") as f:
                compile_info = json.load(f)
                self.sol_file = compile_info["name"]
                if "auxiliary" in compile_info: 
                    self.auxiliary_sol_file = compile_info["auxiliary"]
                else: 
                    self.auxiliary_sol_file = None
                self.sol_ver = compile_info["ver"]
    
    def get_slither_result(self):
        """
            编译和分析都在具体的项目目录下执行
        """
        pwd = os.getcwd() # 记录下当前的工作空间
        os.chdir(self.target_dir) # 切换工作空间

        subprocess.check_call(["solc-select", "use", self.sol_ver])

        print(f"开始编译主分析對象 {self.target_dir}.........")
        s = time.time()
        self.slither = Slither(self.sol_file)
        e = time.time()
        print(f"編譯結束，耗时 {e-s}")

        os.chdir(pwd) # 回到原本的工作空间

    def get_auxiliary_slither_result(self):
        """
            编译和分析都在具体的项目目录下执行
        """
        pwd = os.getcwd() # 记录下当前的工作空间
        os.chdir(self.target_dir) # 切换工作空间

        print(f"开始编译第二個 {self.target_dir}.........")
        s = time.time()
        self.auxiliary_slither = Slither(self.auxiliary_sol_file)
        e = time.time()
        print(f"編譯第二個結束，耗时 {e-s}")

        os.chdir(pwd) # 回到原本的工作空间
    
    def get_auxiliary_target_functions(self):    
        """
        尋找在auxiliary中需要分析的函數列表
        从main contract中得到分析对象 aux_c, aux_f
        1. 寻找aux slither中寻找与aux_c名称相同 ,或者其继承合约名称与aux_c相同的合约
        2. 在上一步找到的合约中寻找那些与aux_f名称相同的函数
        3. 在aux中尋找調用main對象接口的public函數, 作爲重入攻擊點
        """
       
        for (_for_aux_c, _for_aux_f, main_c) in self.for_auxiliary_analyze_targets:
            main_contract_names = [_c.name for _c in main_c.inheritance]
            for contract in self.auxiliary_slither.contracts:
                
                #* step1: 辅助合约继承了在主合约中得到的夸合约对象
                if _for_aux_c.name in [c.name for c in contract.inheritance]:
                    for func in contract.functions:
                        
                        #* step2: 辅助函数和主合约得到的函数明相同，且存在具体实现
                        if func.full_name == _for_aux_f.full_name and func.is_implemented == True:
                            self.auxiliary_analyze_targets.add((contract, func, main_c))
                            print(f"\t 在辅助对象中找到目标 {contract.name} {func.full_name}")
                        
                        #* step3: 该辅助函数调用了主函数的接口 
                        for (_called_c, _called_f) in func.high_level_calls:
                            if (_called_c.name in main_contract_names ) \
                                and (func.visibility in ["external", "public"]) \
                                    and (func.is_implemented and not func.is_constructor and not func.view):
                                print(f"\t -> 辅助函数調用了主函數的接口 { _called_c.name} {_called_f.name}")
                                self.auxiliary_call_main_functions.add((func, _called_c, _called_f)) #! 這些也就是重入點
        print(f"可疑的辅助对象内部重入点:{[f.name for (f, mc, mf) in self.auxiliary_call_main_functions]}")
        
    def get_sink_functions_in_main(self):
        """
        辅助对象中的潜在可重入函数内部调用了主函数的接口
        这些主函数的接口可否被主函数中的effect-after-check污染
        --> 所以被认为是有可能的risk_main_funcs
        """
        for (aux_fun, called_mc, called_mf) in self.auxiliary_reenter_points:
            for main_contract in self.slither.contracts:
                if called_mc.name in [c.name for c in main_contract.inheritance]:
                    for main_function in main_contract.functions:
                        if main_function.full_name == called_mf.full_name and main_function.is_implemented == True:
                            self.risk_main_funcs_called_by_aux_reenterpoint.add((aux_fun, main_function, main_contract))
                            break
        
        return self.risk_main_funcs_called_by_aux_reenterpoint
    
    def get_public_functions_and_selfimplement_risk_functions(self):
        """
        1.收集合约内自己实现的, 且存在可重入金融风险的函数列表, 作为可疑的sink
        2.收集合约中可以外部调用的合约列表，作为分析入口
        """
        for _contract in self.slither.contracts:
            
            for _function in _contract.functions:
                
                #* 自定义的mint函数是存在金融风险的函数，被重入攻击会造成金融损失
                if _function.full_name in ["mint(address,uint256,uint256,bytes)", "mint(address,uint256)"]\
                    and _function.is_implemented == True:
                        self.selfimplemented_finical_risk_functions[str(_function.id)] = _function

                #* 不怎么标准的自定义金融风险函数
                elif _function.name in ["_safeMint", "safeMint", "_Mint", "Mint", "_mint", "mint"]\
                    and _function.is_implemented == True:
                        print(f"不标准的金融风险函数 {_function.name}")
                        self.selfimplemented_finical_risk_functions[str(_function.id)] = _function
                
                if _function.is_constructor:
                    self.construct_functions.append(_function)
                
                if _function.is_implemented and not _function.view and not _function.is_constructor \
                    and "REENTRANCY" in _function.context \
                    and  _function.visibility in ["public", "external"]:

                    # 重复检测 override
                    if _function.id in self.public_functions and _function != self.public_functions[_function.id]['f']:
                        self.console.print(f"已经存在：{self.public_functions[_function.id]['f'].name} 与目标 {_function.name} ID 重复", style="red on white")
                    
                    # 保存函数，进行下一步分析
                    self.public_functions[_function.id] = {
                        'c': _contract, 
                        'f': _function,
                        's': self.slither
                    }
    
    def do_slither_re_detector(self):
        _re_detector = getattr(all_detectors, "ReentrancyEth") # 随便找一个，主要目标是为了底层的reentrancy检测器，上层检测器没啥用
        self.slither.register_detector(_re_detector) # 注册
        self.slither.run_detectors() # 执行，主要目标是利用底层的reentrant检测器
    
    
    def is_need_analyze_auxiliary(self):
        """
        判断是否需要分析辅助sol文件
        1.启发式匹配规则
        ControllerInterface -- Controller.sol
        """
        if self.auxiliary_sol_file is None:
            return False

        #* "Control/Controller.sol" 
        no_path_auxiliary_name = str(self.auxiliary_sol_file).split("/")[-1]
        auxiliary_name = str(no_path_auxiliary_name).strip(".sol")
        for (c, _, _) in self.for_auxiliary_analyze_targets:
            
            print(f"开始匹配: {str(auxiliary_name).lower()} {str(c.name).lower()}")
            
            #* Controller Controller.sol
            if str(auxiliary_name).lower() in str(c.name).lower() \
                or str(c.name).lower() in str(auxiliary_name).lower():
                return True
        
        return False

    def is_financial_risk(self, fun:SFunction):
        if str(fun.id) in self.finical_risk_functions:
            return True
        return False