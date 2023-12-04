# ./abc -c "&r test.aig; &ps; rec_start3 logic_my_suite/rec6Lib_final_filtered3_recanon.aig; time; &if -K 6 -y; &ps ; time"
#./abc_pure -c "&cec logic_my_suite/voter.aig test.aig"
./abc -c "read logic_my_suite/log2.aig; ps; resub -v -N 1; ps"
