theory CENTAUR_Demo_Quant
  imports HOL.SMT
begin
declare [[smt_cvc_alethe]]
declare [[smt_trace]]
declare[[cvc5_options="--dag-thres=0 --proof-format-mode=alethe --proof-granularity=dsl-rewrite --proof-alethe-experimental --proof-prune-input --full-saturate-quant --proof-alethe-define-skolems --proof-elim-subtypes --no-stats --sat-random-seed=1 --lang=smt2"]]


















(* Quantifiers *)

lemma "\<exists>x::int. x + 1 = x * 2"
  by (smt (cvc5))
  























end