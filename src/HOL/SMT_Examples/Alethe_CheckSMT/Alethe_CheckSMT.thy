theory Alethe_CheckSMT
  imports HOL.SMT_CVC

begin 

declare [[smt_trace=false,smt_verbose=false]]
(*declare [[smt_statistics]]*)

(* and_pos *)

check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_1.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_1.alethe" 
(* check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_1_slice.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_1_slice.alethe" *)
check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_2.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_2.alethe" 
(* check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_2_slice.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_2_slice.alethe" *)
check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_3.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_3.alethe" 
(* check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_3_slice.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_3_slice.alethe" *)
check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_4.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_4.alethe" 
(* check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_4_slice.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_4_slice.alethe" *)
check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_5.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_5.alethe" 
(* check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_5_slice.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/and_pos/and_pos_5_slice.alethe" *)

(* or_neg *)

check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_1.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_1.alethe" 
(* check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_1_slice.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_1_slice.alethe" *)
check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_2.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_2.alethe" 
(* check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_2_slice.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_2_slice.alethe" *)
check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_3.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_3.alethe" 
(* check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_3_slice.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_3_slice.alethe" *)
check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_4.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_4.alethe" 
(* check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_4_slice.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_4_slice.alethe" *)
check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_5.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_5.alethe" 
(* check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_5_slice.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/or_neg/or_neg_5_slice.alethe" *)

(* connective_def (xor) *)

check_smt "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/connective_def/connective_def_xor_1.smt2" "~~/src/HOL/SMT_Examples/Alethe_CheckSMT/connective_def/connective_def_xor_1.alethe" 

end