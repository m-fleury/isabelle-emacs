theory CENTAUR_Demo
  imports HOL.SMT HOL.Real
begin
declare [[smt_cvc_lethe]]
declare [[smt_trace]]
declare[[cvc5_options="--dag-thres=0 --proof-format-mode=alethe --proof-granularity=dsl-rewrite --proof-alethe-experimental --proof-prune-input --full-saturate-quant --proof-alethe-define-skolems --proof-elim-subtypes --no-stats --sat-random-seed=1 --lang=smt2"]]

(*TODOs:

Open Files:
1. CENTAUR_Demo_Bool.thy
2. CENTAUR_Demo_Quant.thy
4. CENTAUR_Demo_BV.thy
5. CENTAUR_Demo_CheckSMT.thy
   Open problem and proof

*)



















(* Quantifiers *)

lemma "\<exists>x::int. x + 1 = x * 2"
  by (smt (cvc5))



















(* Real Arithmetic *)

lemma "(3 :: real) + 1 = 4"
  by (smt (cvc5))









(* Bit-Vectors *)


(* Translation of new Operators *)

 




(*check smt*)






end