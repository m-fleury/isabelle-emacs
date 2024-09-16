theory CENTAUR_Demo_Bool
  imports HOL.SMT
begin
declare [[smt_cvc_lethe]]
declare [[smt_trace]]
declare[[cvc5_options="--dag-thres=0 --proof-format-mode=alethe --proof-granularity=dsl-rewrite --proof-alethe-experimental --proof-prune-input --full-saturate-quant --proof-alethe-define-skolems --proof-elim-subtypes --no-stats --sat-random-seed=1 --lang=smt2"]]

















(* Booleans *)

lemma
  assumes "(p \<or> q) \<and> \<not>p"
  shows "q"
  using assms
  by (smt (cvc5))
  




















end