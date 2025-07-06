import os

os.system(' ./abc -c "read logic_my_suite/ctrl.aig; print_stats; resub -N 2 -F 2 -w -v; time; print_stats" ')
