theory CENTAUR_Demo_BV
  imports HOL.SMT "HOL-CVC.SMT_CVC_Word"
begin
declare [[smt_cvc_alethe]]
declare [[smt_trace]]
declare[[cvc5_options="--dag-thres=0 --proof-format-mode=alethe --proof-granularity=dsl-rewrite --proof-alethe-experimental --proof-prune-input --full-saturate-quant --proof-alethe-define-skolems --proof-elim-subtypes --no-stats --sat-random-seed=1 --lang=smt2"]]











(* Bit-vector translation *)

lemma
  shows "bit (8::16 word) 3" (* 0000000000001000 \<longrightarrow> 1  *)
  by (smt (cvc5))
  
lemma
  shows "\<not> bit (8::16 word) 10" (* 0000000000001000 \<longrightarrow> 0  *)
  by (smt (cvc5))




(*

(a \<and> b \<and> c)
-----------
     b

(step t0 (a \<and> b \<and> c) ..)
(step t1 (b) rule: and premises: t0 args:1)

*)



















(* Reconstruction of Bit-Vector Proofs *)
(* Contains bitblasting of constants, bvult and bveq *)
lemma "a > (6::3 word) \<Longrightarrow> a = 7"
  by (smt (cvc5))













(* How big can we get? *)
lemma "a > (8589934590::32 word) \<Longrightarrow> a = 8589934591"
  supply[[smt_trace=false]]
  by (smt (cvc5))

lemma "a > (36893488147419103230::64 word) \<Longrightarrow> a = 36893488147419103231"
  supply[[smt_trace=false]]
  by (smt (cvc5))

lemma "a > (680564733841876926926749214863536422910::128 word) \<Longrightarrow> a = 680564733841876926926749214863536422911"
  supply[[smt_trace=false]]
  by (smt (cvc5))






















(*For the future... Embedding of natural numbers to integers*)
lemma
  shows "\<forall>i. i \<noteq> 3 \<longrightarrow> \<not> bit (8::16 word) i" (* 0000000000001000 \<longrightarrow> 0  *)
  supply [[smt_nat_as_int,smt_nat_as_int_bv]]
  by (smt (cvc5))




















end