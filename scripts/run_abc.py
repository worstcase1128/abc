import os
import os.path as osp
import subprocess
import re
import pandas as pd
from functools import partial
print = partial(print, flush=True)

benchmarks=[
    # "arbiter", "ctrl", "cavlc", "dec", "i2c", 
    # "int2float", "mem_ctrl", "priority", "router", "voter", 
    # "adder", "bar", "div", "hyp", 
    # "log2", 
    # "max", "multiplier", "sin", "sqrt", "square",
    "sixteen", "twenty", "twentythree",
    "div_10xd",   # stuck
    "hyp_8xd",
    "mem_ctrl_10xd", 
    "log2_10xd", 
    # "multiplier_10xd", "sqrt_10xd", "square_10xd", "voter_10xd", "sin_10xd",
]
sat_types = [" ", "-c", "-x"]

abc_bin = "/data/ssd/ysun/github/abc/abc_pure"
# abc_bin = "/data/ssd/ysun/github/abc/abc"
benchmark_dir = "/data/ssd/ysun/github/abc/logic_my_suite"
result_dir = "/data/ssd/ysun/github/abc/results"

# time_pattern = re.compile(r"elapse:.*?([+-]?(?:[0-9]*[.])?[0-9]+)")
time_pattern = re.compile(r"elapse:")
# stats_num_pattern = re.compile(r"and.*?([0-9]+).*?lev.*?([0-9]+)")
stats_num_pattern = re.compile(r"and.*?([0-9]+).*?lev.*?([0-9]+)")

timeLimit = 300 #seconds

f_log = osp.join(result_dir, 'log.txt')
f_log = open(f_log, 'w')
# f_log = open(f_log, 'a')
# f_log.write("%s\n"%(string))


all_case_stats = []
all_case_times = []
for case in benchmarks:
    for sat_type in sat_types:
        print("===== [case] %s %s=====" % (case, sat_type))
        case_path = osp.join(benchmark_dir, case + ".aig")
        # abc_cmd = ("read %s; time; balance; print_stats; drw; print_stats; drw; print_stats; balance; print_stats; "
        #            "drw; print_stats; drw; print_stats; balance; print_stats; drw; print_stats; drw; print_stats; balance; time; print_stats" % case_path)
        # abc_cmd = ("read %s; time; balance; drw; drf; balance; "
        #            "drw; drw; balance; drf; drw; balance; time; print_stats" % case_path)
        # abc_cmd = ("read %s; time; balance; time; print_stats; drw; time; print_stats; drf; time; print_stats; balance; time; print_stats; "
        #            "drw; time; print_stats; drw; time; print_stats; balance; time; print_stats; "
        #            "drf; time; print_stats; drw; time; print_stats; balance; time; print_stats" % case_path)
        # abc_cmd = "read %s; time; drf; time; print_stats" % case_path
        abc_cmd = "&r %s; &ps; time; &fraig %s; time; &ps" % (case_path, sat_type)

        case_times = []
        case_stats = []
        try:
            output_log = subprocess.check_output('%s -c "%s"' % (abc_bin, abc_cmd),
            shell=True, stderr=subprocess.DEVNULL, timeout=timeLimit).decode("utf-8")
        except subprocess.TimeoutExpired:
            case_times.append("timeout")
            case_stats.extend([0, 0, 0, 0])
        else: 
            output_lines = output_log.split("\n")

            stats_lines = []
            first_time = None
            for line in output_lines:
                print(line)
                print(line, file=f_log)
                # f_log.write(line)
                if re.search(time_pattern, line):
                    time = float(line.split(" ")[-2])
                    if first_time is None:
                        first_time = time
                    else:
                        case_times.append(time - first_time)
                        # print("time",case_times)
                    # print(line)
                if re.search(stats_num_pattern, line):
                    tokens = re.findall(stats_num_pattern, line)[0]
                    area, delay = int(tokens[0]), int(tokens[1])
                    # print("area", area, "delay", delay)
                    case_stats.append(area)
                    case_stats.append(delay)
                    # case_stats.append([area, delay])
                    # print(case_stats)
                    # print(line)

        # all_case_times.append([case, "time"] + case_times)
        all_case_stats.append([case] + case_stats + case_times + [sat_type])
        print("case_stats", case_stats)
        print("case_time", case_times)

# columns = ["benchmark", "and", "level"] + list(range(len(all_case_stats[0]) - 2))
columns = ["benchmark", "ori_and", "ori_level", "fr_and", "fr_level", "time", "sat_type"] 
print(columns)
df_stats = pd.DataFrame(data=all_case_stats, columns=columns)
# df_times = pd.DataFrame(data=all_case_times, columns=columns)
print(df_stats)
# print(df_times)

# df_stats.to_csv("run_abc_stats.csv")
df_stats.to_csv(osp.join(result_dir, "run_abc_stats.csv"))
f_log.close()
# df_times.to_csv("run_abc_times.csv")

