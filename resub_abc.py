import os
import os.path as osp
import subprocess
import re
import argparse
import pandas as pd
from functools import partial
print = partial(print, flush=True)

parser = argparse.ArgumentParser()
parser.add_argument("--cec", action="store_true")
parser.add_argument("--dept_machine", action="store_true")
args = parser.parse_args()

benchmarks=[
    # "ctrl", "mem_ctrl"
    "arbiter", "ctrl", "cavlc", "dec", "i2c", 
    "int2float", "mem_ctrl", "priority", "router", "voter", 
    "adder", "bar", "div", "log2", "max", "multiplier", "sin", "sqrt", "square",
    "hyp", 
    # "sixteen", "twenty", "twentythree",
    # "div_10xd", "hyp_8xd", "mem_ctrl_10xd", "log2_10xd", 
    # "multiplier_10xd", "sqrt_10xd", "square_10xd", "voter_10xd", "sin_10xd",
    # "ac97_ctrl_10xd", "vga_lcd_5xd", 
]

if not args.dept_machine:
    os.environ["CUDA_VISIBLE_DEVICES"] = "1"

abc_bin = "/data/ssd/ysun/github/abc/abc"
benchmark_dir = "/data/ssd/ysun/github/abc/logic_my_suite"
result_dir = "/data/ssd/ysun/github/abc/results"
output_dir = "/data/ssd/ysun/github/abc/outputs"

if not osp.exists(result_dir):
    os.makedirs(result_dir)
# os.system("rm -rf %s/*" % result_dir)

abc_time_pattern = re.compile(r"elapse:")
gpuls_time_pattern = re.compile(r"\{time\}")
abc_stats_pattern = re.compile(r"and.*?([0-9]+).*?lev.*?([0-9]+)")
gpuls_stats_pattern = re.compile(r"AIG\sstats")
cec_pattern = re.compile(r"equivalent")

output_files = []
mode = 1
f_log = osp.join(result_dir, 'resub_abc1.txt')
result_sheet = osp.join(result_dir, "resub_abc1.csv")
f_log = open(f_log, 'w')
timeLimit = None #seconds

all_case_result = []
output_num = 0
columns = ["benchmark", "area", "delay", "time"]
# add_nodes = [0, 1, 2, 3]
add_nodes = [2]


for case in benchmarks:
    for add_node in add_nodes:
        output_num += 1
        case_path = osp.join(benchmark_dir, case + ".aig")
        output_path = osp.join(output_dir, case + "_resub_abc.aig")
        case_result = []
        print("===== [case] %s =====" % case)

        case_result.extend([case])

        case_time = []
        case_stats = []
        abc_cmd = '%s -c "read %s; time; resub -N %d; time; print_stats; write test.aig"' % (abc_bin, case_path, add_node)
        # abc_cmd = '%s -c "read %s; time; resub -N %d; time; print_stats; "' % (abc_bin, case_path, add_node)
        print(abc_cmd)
        print(abc_cmd, file=f_log)
        try:
            abc_log = subprocess.check_output(abc_cmd, shell=True, stderr=subprocess.DEVNULL, timeout=timeLimit).decode("utf-8")
        except subprocess.TimeoutExpired:
            case_result.extend([0, 0, "timeout"])
            print("timeout")
        except subprocess.CalledProcessError as e:
            case_result.extend([0, 0, "process error"])
            print("process error: ", str(e))
        else:
            for line in abc_log.split("\n"):
                print(line)
                print(line, file=f_log)
                if re.search(abc_time_pattern, line):
                    time = float(line.split(" ")[-5])
                    case_time = [time]
                if re.search(abc_stats_pattern, line):
                    tokens = re.findall(abc_stats_pattern, line)[0]
                    nAnd, lev = int(tokens[0]), int(tokens[1])
                    case_stats.append(nAnd)
                    case_stats.append(lev)
            case_result.extend(case_stats + case_time)

        if args.cec:
            print("  >> cec results <<")
            # cec_cmd = '%s -c "&cec %s %s"' % (abc_bin, output_path, case_path)
            cec_cmd = '%s -c "&cec %s test.aig"' % (abc_bin, case_path)
            print(cec_cmd)
            print(cec_cmd, file=f_log)
            cec_log = subprocess.check_output(cec_cmd, shell=True, stderr=subprocess.DEVNULL).decode("utf-8")
            for line in cec_log.split("\n"):
                if re.search(cec_pattern, line):
                    print(line)
                    print(line, file=f_log)
                    break

        print(case_result)
        print(case_result, file=f_log)
        df_result = pd.DataFrame(data=[case_result], columns=columns)

        if output_num==1:
            df_result.to_csv(result_sheet, index=False)
        else:
            with open(result_sheet,"a") as f:
                df_result.to_csv(f,header=False,index=False)
        
        all_case_result.append(case_result)
    

# df_result = pd.DataFrame(data=all_case_result, columns=columns)
# print(df_result)

# df_result.to_csv(result_sheet)
f_log.close()
