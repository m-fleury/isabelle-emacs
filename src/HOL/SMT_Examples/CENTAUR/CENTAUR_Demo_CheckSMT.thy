theory CENTAUR_Demo_CheckSMT
  imports "HOL-CVC.SMT_CVC"
begin
declare [[smt_cvc_lethe]]
declare [[smt_trace]]
declare[[cvc5_options="--dag-thres=0 --proof-format-mode=alethe --proof-granularity=dsl-rewrite --proof-alethe-experimental --proof-prune-input --full-saturate-quant --proof-alethe-define-skolems --proof-elim-subtypes --no-stats --sat-random-seed=1 --lang=smt2"]]

















(* Checking external SMT-LIB Problems and Proofs *)

check_smt("cvc5") "~~/src/HOL/SMT_Examples/CENTAUR/testProblem.smt2" "~~/src/HOL/SMT_Examples/CENTAUR/testProblem.alethe"
  




















end