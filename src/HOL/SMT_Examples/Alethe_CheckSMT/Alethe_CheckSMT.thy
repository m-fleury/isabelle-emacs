theory Alethe_CheckSMT
  imports Main

begin 

declare [[smt_trace=true,smt_verbose=true]]

check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/connective_def_xor.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/connective_def_xor.alethe"

end