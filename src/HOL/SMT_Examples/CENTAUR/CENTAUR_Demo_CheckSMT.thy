theory CENTAUR_Demo_CheckSMT
  imports "HOL.SMT_CVC"
begin
declare [[smt_cvc_alethe]]
declare [[smt_trace]]

















(* Checking external SMT-LIB Problems and Proofs *)

check_smt("cvc5") "~~/src/HOL/SMT_Examples/CENTAUR/testProblem.smt2" "~~/src/HOL/SMT_Examples/CENTAUR/testProblem.alethe"
  




















end