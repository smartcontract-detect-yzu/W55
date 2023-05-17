import json
import os
import platform
import subprocess
from slither.slither import Slither
from rich.console import Console
from slither.detectors import all_detectors
from typing import Optional, List, Set, Dict, Tuple, Union, TYPE_CHECKING
from slither.core.declarations.function import Function as SFunction
from slither.analyses.data_dependency import data_dependency
from src.function_analyzer import FunctionAnalyzer

COMPIILE_INFO_FILE = "/compile.json"


class ContractInfoCollector:
    """
        负责收集和储存合约中的信息
    """
    def __init__(self, target_dir) -> None:
        self.target_dir = target_dir
        self.console = Console()

        # 编译相关信息
        self.sol_file = None
        self.sol_ver = None

        # slither总体信息
        self.slither:Slither = None

        # 函数相关
        self.construct_functions:list[SFunction] = []
        self.target_functions = {} # 目标函数：external或者public
        self.interaction_functions = {} # 存在交易行爲的函數
        self.canreenter_transferout_functions :Dict[str, SFunction] = {}

        if not os.path.exists(self.target_dir + "/log"): os.mkdir(self.target_dir + "/log")
    
    def add_interaction_function(self, f:SFunction, fanalyzer: FunctionAnalyzer, interact_dir:str, re_pattern:bool):
        self.interaction_functions[str(f.id)] = {"f": f, "a": fanalyzer, "d":interact_dir, "re_pattern":re_pattern}

    def add_canreenter_transferout_function(self, f:SFunction):
        self.canreenter_transferout_functions[str(f.id)] = f

    def get_sol_ver(self):

        if not os.path.exists(self.target_dir + COMPIILE_INFO_FILE):
            raise RuntimeError("没有编译信息文件compile.json")
        else:
            with open(self.target_dir + COMPIILE_INFO_FILE, "r") as f:
                compile_info = json.load(f)
                self.sol_file = compile_info["name"]
                self.sol_ver = compile_info["ver"]
    
    def get_slither_result(self):
        """
            编译和分析都在具体的项目目录下执行
        """
        pwd = os.getcwd() # 记录下当前的工作空间
        os.chdir(self.target_dir) # 切换工作空间

        subprocess.check_call(["solc-select", "use", self.sol_ver])

        self.slither = Slither(self.sol_file)
        print(f"开始编译 {self.target_dir}.........")
        
        os.chdir(pwd) # 回到原本的工作空间

    def get_external_functions(self):
        
        for _contract in self.slither.contracts:
            for _function in _contract.functions:

                if _function.is_constructor:
                    self.construct_functions.append(_function)

                if _function.is_implemented and not _function.view and not _function.is_constructor \
                    and "REENTRANCY" in _function.context \
                    and  _function.visibility in ["public", "external"]:

                    # 重复检测 override
                    if _function.id in self.target_functions and _function != self.target_functions[_function.id]['f']:
                        self.console.print(f"已经存在：{self.target_functions[_function.id]['f'].name} 与目标 {_function.name} ID 重复", style="red on white")

                    # 保存函数，进行下一步分析
                    self.target_functions[_function.id] = {
                        'c': _contract, 
                        'f': _function,
                        's': self.slither
                    }
    
    def do_slither_re_detector(self):
        _re_detector = getattr(all_detectors, "ReentrancyEth") # 随便找一个，主要目标是为了底层的reentrancy检测器，上层检测器没啥用
        self.slither.register_detector(_re_detector) # 注册
        self.slither.run_detectors() # 执行，主要目标是利用底层的reentrant检测器