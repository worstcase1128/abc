./abc -c "&r logic_my_suite/sin.aig; &ps; rec_start3 logic_my_suite/rec6Lib_final_filtered3_recanon.aig; &if -K 6 -y -a; &ps; &if -K 6 -y -a; &ps ; &w test.aig"
#./abc_pure -c "&cec logic_my_suite/voter.aig test.aig"
