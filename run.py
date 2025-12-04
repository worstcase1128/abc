import os
os.environ["CUDA_VISIBLE_DEVICES"] = "1"


# os.system(' ./abc -c "read logic_my_suite/voter.aig; ps; time; resub -N 2 -F 5 -v; ps; time; write test.aig" ')
os.system('    ./abc -c "read logic_my_suite/hyp.aig; ps; time; resub -N 2 -c; ps; time; write test.aig" ')

# os.system(' valgrind --leak-check=yes ./abc -c "read logic_my_suite/i2c.aig; ps; time; resub -N 2 -F 1 -w; ps;" ')