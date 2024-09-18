theory CENTAUR_Demo_Real
  imports HOL.SMT HOL.Real
begin
declare [[smt_cvc_alethe]]
declare [[smt_trace]]
declare [[z3_extensions]]

declare[[cvc5_options="--dag-thres=0 --proof-format-mode=alethe  --proof-alethe-experimental --proof-prune-input --full-saturate-quant --proof-alethe-define-skolems --proof-elim-subtypes --no-stats --sat-random-seed=1 --lang=smt2"]]


















(* Real Arithmetic *)

lemma "\<bar>(x::real) + y\<bar> \<le> \<bar>x\<bar> + \<bar>y\<bar>"
  by (smt (cvc5))




















end