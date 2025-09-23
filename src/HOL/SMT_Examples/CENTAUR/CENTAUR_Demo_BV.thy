theory CENTAUR_Demo_BV
  imports HOL.SMT HOL.SMT_CVC_Word
begin
declare [[smt_cvc_alethe]]
declare [[smt_trace]]







declare[[smt_expert_debug_alethe_level=0]]
declare[[smt_expert_debug_alethe_files="alethe_replay_rare"]]



lemmas [bv_reconstruction_length] = len_num0 len_num1 len_bit0 len_bit1





















(* Reconstruction of Bit-Vector Proofs *)
(* Contains bitblasting of constants, bvult and bveq *)
lemma "a > (6::3 word) \<Longrightarrow> a = 7"
  by (smt (cvc5))













                                        

(* How big can we get? Pidgeonhole lemmas for bit-vectors: *)
declare[[smt_trace=false,smt_verbose=false]]

lemma "a > (4294967294::32 word) \<Longrightarrow> a = 4294967295"
  by (smt (cvc5))

lemma "a > (18446744073709551614::64 word) \<Longrightarrow> a = 18446744073709551615"
  by (smt (cvc5))

lemma "a > (340282366920938463463374607431768211454::128 word)
   \<Longrightarrow> a = 340282366920938463463374607431768211455"
  by (smt (cvc5))





















(*For the future... Embedding of natural numbers to integers*)
lemma
  shows "\<forall>i. i \<noteq> 3 \<longrightarrow> \<not> bit (8::16 word) i" (* 0000000000001000 \<longrightarrow> 0  *)
  supply [[smt_nat_as_int,smt_nat_as_int_bv]]
  by (smt (cvc5))




















end