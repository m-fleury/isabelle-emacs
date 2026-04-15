theory Alethe_CheckSMT
  imports Main

begin 

declare [[smt_trace=true,smt_verbose=true]]

check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/connective_def_xor_1.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/connective_def_xor_1.alethe"
check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos_1.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos_1.alethe"
check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg_1.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg_1.alethe"
 
end