import os
import os.path as osp
import subprocess
import re
import argparse
import pandas as pd
from functools import partial
print = partial(print, flush=True)

parser = argparse.ArgumentParser()
timeLimit = None

benchmarks=[
    # "ctrl", 
    # "arbiter", "ctrl", "cavlc", "dec", "i2c", 
    # "int2float", "mem_ctrl", "priority", "router", "voter", 
    # "adder", "bar", "div", "log2", "max", "multiplier", "sin", "sqrt", "square",
    # "hyp", 
    # "sixteen", "twenty", "twentythree",
    # "div_10xd", "hyp_8xd", "mem_ctrl_10xd", 
    # "log2_10xd", 
    # "multiplier_10xd", "sqrt_10xd", "square_10xd", "voter_10xd", "sin_10xd",
    # "ac97_ctrl_10xd", "vga_lcd_5xd",  # case not exist
]

abc_bin = "/data/ssd/ysun/github/abc/abc"
benchmark_dir = "/data/ssd/ysun/github/abc/logic_my_suite"
# lib_name = "rec6lib_area.aig"
# lib_name = "rec6lib_area_reduce.aig"
lib_name = "temp.aig"
# recadd3_cmd = "st; rec_add3; b; rec_add3; dc2; rec_add3; if -K 8; bidec; st; rec_add3; dc2; rec_add3; if -g -K 6; st; rec_add3"
recadd3_cmd = "st; rec_add3; b; rec_add3; dc2; rec_add3; if -K 8; bidec; st; rec_add3; dc2; rec_add3; if -a -K 6; st; rec_add3"
abc_cmd = ' "rec_start3; '

for case in benchmarks:
    case_path = osp.join(benchmark_dir, case + ".aig")
    abc_cmd += case_path + "; " + recadd3_cmd + "; "
    # print("added ", case)

abc_cmd += "rec_dump3 "+lib_name +"; "
abc_cmd += 'rec_stop3; "'
print(abc_cmd)

abc_log = subprocess.check_output("%s -c %s"%(abc_bin, abc_cmd), shell=True, stderr=subprocess.DEVNULL, timeout=timeLimit).decode("utf-8")
print("writing to", lib_name, "done")


