(*  Title:      HOL/SMT_Examples/SMT_Word_Examples.thy
    Author:     Sascha Boehme, TU Muenchen
    Author:     Hanna Lachnitt, Stanford University

*)

section \<open>Word examples for for SMT binding\<close>

theory SMT_Word_Examples_CVC       
imports "HOL-Library.Word" "HOL.SMT_CVC_Word"
begin

declare [[smt_nat_as_int,smt_trace]]
declare[[smt_expert_debug_alethe_level=0]]
declare[[show_hyps]]

lemmas [bv_reconstruction_length] = len_num0 len_num1 len_bit0 len_bit1 (*TODO: Move to appropriate place if this is necessary*)

(* Overview:

What has been done?

- Word constants now translate correctly even with overflow
- Conversions work well (of_int, Word.Word)
- LENGTH translation works well

What is still to do?

- Word constants that overflow e.g., (27 :: 4 word) are now normalized during normalization using the simplifier. It would
  be better to first check if that is necessary before calling the simplifier.
- Normalization of negative word constants disturbs checking as in this lemma: lemma "- (- 11) = (11::5 word)"
- int.log2 does not parse correctly
- Problem with finding the assumptions in cases where parsing adds a nat cast
    lemma "(2::4 word) ^ 3 = 8"
    by (smt (cvc5))

  Goal: "__normalized_input"
       assumptions:
         push_bit_lift (3::int) 1 \<noteq> (8::4 word)
       proposition:
         push_bit (nat (3::int)) 1 \<noteq> (8::4 word) 
- Evaluate abstracts too much for bit-vector operators:
  SMT: Goal: "rare_rewrite"
       arguments:
         ''evaluate''
       proposition:
         push_bit (nat (3::int)) 1 = (8::4 word) 
  Proof failed.
  1. uint t1 = (8::int)

- slice does not get translated correctly anymore
  (declare-fun smt_extract_lift$ (Int Int (_ BitVec 3)) (_ BitVec 2))
  (assert (! (not (= (smt_extract_lift$ 3 1 (_ bv6 3)) (_ bv3 2))) :named a0))

*)

ML\<open>

val y1 = @{term "(7 :: 3 word)"} (*111*)
val y2 = @{term "(6 :: 3 word)"} (*011*)
val y3 = @{term "(2 :: 3 word)"} (*01*)
val y4 = @{term "(3 :: 3 word)"} (*11*)
val y5 = @{term "(4 :: 3 word)"} (*001*)

val z0 = @{term "(0 :: 3 word)"} (*0 ---> *)

val z1 = @{term "(8 :: 3 word)"} (*0001 ---> *)
val z2 = @{term "(9 :: 3 word)"} (*1001 ---> 1*)
val z3 = @{term "(10 :: 3 word)"} (*0101 ---> 01*)
val z4 = @{term "(11 :: 3 word)"} (*1101 ---> 11*)
val z5 = @{term "(12 :: 3 word)"} (*0011 ---> 001*)

\<close>





section \<open>Bitvector numbers\<close>

lemma "(27 :: 4 word) = -5" by (smt (cvc5))
lemma "(27 :: 4 word) = 11" by (smt (cvc5))
lemma "23 < (27::8 word)" by (smt (cvc5))
lemma "27 + 11 = (6::5 word)" by (smt (cvc5))
lemma "7 * 3 = (21::8 word)" by (smt (cvc5))
lemma "11 - 27 = (-16::8 word)" by (smt (cvc5))


lemma "- (- 11) = (11::5 word)" by (smt (cvc5)) (*negs are weirdly deleted while printing but why and where?*)
lemma "-40 + 1 = (-39::7 word)" by (smt (cvc5))
lemma "a + 2 * b + c - b = (b + c) + (a :: 32 word)" supply [[smt_trace]](* by (smt (cvc5))*) sorry
lemma "x = (5 :: 4 word) \<Longrightarrow> 4 * x = 4" by (smt (cvc5))


section \<open>Conversions\<close>

lemma "Word.Word 0 = (0::5 word)" by (smt (cvc5))
lemma "Word.Word 8 = (8::5 word)" by (smt (cvc5))
lemma "Word.Word 72 = (8::5 word)" by (smt (cvc5))
lemma "of_int 0 = (0::5 word)" by (smt (cvc5))
lemma "of_int 8 = (8::5 word)" by (smt (cvc5))
lemma "of_int 72 = (8::5 word)" by (smt (cvc5))
lemma "of_int (-8) = (24::5 word)" by (smt (cvc5))
lemma "of_int (-8) = (-8::5 word)" by (smt (cvc5))
lemma "word_of_int 0 = (0::5 word)" by (smt (cvc5))
lemma "word_of_int 8 = (8::5 word)" by (smt (cvc5))
lemma "word_of_int 72 = (8::5 word)" by (smt (cvc5))


section \<open>LENGTH\<close>

text \<open>
LENGTH(constant) is now calculated during normalization using the simplifier
LENGTH(type variable) is lifted to len_of_lift during normalization
(len_of_lift TYPE('a::len0))
 \<close>

lemma "LENGTH(0) = 0" by (smt(cvc5))
lemma "LENGTH(1) = 1" by (smt(cvc5))
lemma "LENGTH(64) = 64" by (smt(cvc5))
lemma "LENGTH(5) = 5" by (smt(cvc5))
lemma "LENGTH('a::len0) = LENGTH('a)" by (smt(cvc5))
lemma "2 * LENGTH('n::len) = LENGTH('n) + LENGTH('n)" by (smt(cvc5))

section \<open>power\<close>

ML \<open>
val x = @{term "push_bit ::nat \<Rightarrow> 4 word \<Rightarrow> 4 word"} |> fastype_of |> strip_type
\<close>


lemma "(2::4 word) ^ 3 = 8"
  by (smt (cvc5))

lemma bnd_0: "3000 < (2^12::32 word)"
  apply (smt (cvc5))
  done

lemma bnd_0_variable: "0 \<le> (2^x::32 word)"
  apply (smt (cvc5))
  done

section \<open>slice and extract\<close>

lemma "slice 1 (0b10110 :: 3 word) = (0b11 :: 2 word)" by (smt (cvc5))

lemma "smt_extract 1 1 (4 :: 3 word) = (0 :: 1 word)" 
  by (smt (cvc5))


(*Bit operators*)

lemma "push_bit 3 (2::5 word) = (16::5 word)"
  by (smt (cvc5))

lemma "x = 2 \<Longrightarrow> push_bit (x + 1) (2::5 word) = (16::5 word)"
  by (smt (cvc5))

ML\<open> 
val x = @{term "slice"}\<close>

section \<open>Bit-level logic\<close>

context
  includes bit_operations_syntax
begin

value "(0b0110 :: 4 word)"
value "slice 2 (6 :: 4 word)::2 word" (*0110*)
value "slice 2 (6 :: 4 word)::3 word"
value "slice 2 (6 :: 4 word)::1 word"


lemma "0b110 AND 0b101 = (0b100 :: 32 word)" by (smt (cvc5))
lemma "0b110 OR 0b011 = (0b111 :: 8 word)" by (smt (cvc5))
lemma "0xF0 XOR 0xFF = (0x0F :: 8 word)" by (smt (cvc5))
lemma "NOT (0xF0 :: 16 word) = 0xFF0F" by (smt (cvc5))
lemma "word_cat (27::4 word) (27::8 word) = (2843::12 word)" by (smt (cvc5))
lemma "word_cat (0b0011::4 word) (0b1111::6 word) = (0b0011001111 :: 10 word)" by (smt (cvc5))
lemma "slice 2 (0b10110 :: 4 word) = (0b11 :: 2 word)" by (smt (cvc5)) (*Overflow*)




lemma "ucast (0b1010 :: 4 word) = (0b1010 :: 10 word)" by (smt (cvc5))
lemma "scast (0b1010 :: 4 word) = (0b111010 :: 6 word)" by (smt (cvc5))
lemma "push_bit 2 0b10011 = (0b1001100::8 word)" by (smt (cvc5))
lemma "drop_bit 2 0b11001 = (0b110::8 word)" by (smt (cvc5))
lemma "signed_drop_bit 2 0b10011 = (0b100::8 word)" by (smt (cvc5))
lemma "word_rotr 2 0b0110 = (0b1001::4 word)" by (smt (cvc5))
lemma "word_rotl 1 0b1110 = (0b1101::4 word)" by (smt (cvc5))
lemma "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)" by (smt (cvc5))
lemma "w < 256 \<Longrightarrow> (w :: 16 word) AND 0x00FF = w" by (smt (cvc5))



(*From AFP Word_Lib Examples.thy*)
section \<open>\<^typ>\<open>nat\<close>\<close>

text \<open>These should not be encoded into bit-vector operators but any natural numbers
should be lifted to integers\<close>

lemma \<open>bit (1705 :: nat) (Suc (Suc (Suc 0)))\<close>
  using Bit_Operations.semiring_bits_class.bit_Suc
  supply[[smt_expert_debug_alethe_level=3]]


lemma \<open>bit (1705 :: nat) 3\<close>
  by (smt (cvc5))
lemma \<open>\<not> bit (1 :: nat) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma \<open>\<not> bit (1 :: nat) 3\<close> by (smt (cvc5))

lemma \<open>(1705 :: nat) AND 42 = 40\<close> by (smt (cvc5))
lemma \<open>(1705 :: nat) AND Suc 0 = 1\<close> by (smt (cvc5))
lemma \<open>(1705 :: nat) OR 42 = 1707\<close> by (smt (cvc5))
lemma \<open>(1705 :: nat) OR Suc 0 = 1705\<close> by (smt (cvc5))
lemma \<open>(1705 :: nat) XOR 42 = 1667\<close> by (smt (cvc5))
lemma \<open>(1705 :: nat) XOR 1 = 1704\<close> by (smt (cvc5))

lemma \<open>push_bit 3 (1705 :: nat) = 13640\<close> by (smt (cvc5))
lemma \<open>push_bit (Suc (Suc (Suc 0))) (1705 :: nat) = 13640\<close> by (smt (cvc5))
lemma \<open>push_bit 3 (Suc 0) = 8\<close> by (smt (cvc5))
lemma
  \<open>push_bit (Suc (Suc (Suc 0))) (Suc 0) = 8\<close> by (smt (cvc5))
lemma \<open>(1705 :: nat) << 3 = 13640\<close> by (smt (cvc5))
lemma \<open>(1705 :: nat) << Suc (Suc (Suc 0)) = 13640\<close> by (smt (cvc5))
lemma \<open>Suc 0 << 3 = 8\<close> by (smt (cvc5))
lemma \<open>Suc 0 << Suc (Suc (Suc 0)) = 8\<close> by (smt (cvc5))
lemma \<open>drop_bit 3 (1705 :: nat) = 213\<close> by (smt (cvc5))
lemma \<open>drop_bit (Suc (Suc (Suc 0))) (1705 :: nat) = 213\<close> by (smt (cvc5))
lemma \<open>drop_bit 3 (Suc 0) = 0\<close> by (smt (cvc5))
lemma \<open>drop_bit (Suc (Suc (Suc 0))) (Suc 0) = 0\<close> by (smt (cvc5))
lemma \<open>(1705 :: nat) >> 3 = 213\<close> by (smt (cvc5))
lemma \<open>(1705 :: nat) >> Suc (Suc (Suc 0)) = 213\<close> by (smt (cvc5))
lemma \<open>Suc 0 >> 3 = 0\<close> by (smt (cvc5))
lemma \<open>Suc 0 >> Suc (Suc (Suc 0)) = 0\<close> by (smt (cvc5))
lemma \<open>take_bit 3 (1705 :: nat) = 1\<close> by (smt (cvc5))
lemma \<open>take_bit (Suc (Suc (Suc 0))) (1705 :: nat) = 1\<close>
  by (simp flip: add_2_eq_Suc)

lemma \<open>take_bit 3 (Suc 0) = 1\<close> by (smt (cvc5))
lemma \<open>take_bit (Suc (Suc (Suc 0))) (Suc 0) = 1\<close> by (smt (cvc5))


section \<open>\<^typ>\<open>int\<close>\<close>

lemma \<open>bit (1705 :: int) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma \<open>bit (1705 :: int) 3\<close> by (smt (cvc5))
lemma \<open>\<not> bit (- 1705 :: int) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma \<open>\<not> bit (- 1705 :: int) 3\<close> by (smt (cvc5))
lemma \<open>\<not> bit (1 :: int) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma \<open>\<not> bit (1 :: int) 3\<close> by (smt (cvc5))
lemma \<open>(NOT 1705 :: int) = - 1706\<close> by (smt (cvc5))
lemma \<open>(NOT (- 42 :: int)) = 41\<close> by (smt (cvc5))
lemma \<open>(NOT 1 :: int) = - 2\<close> by (smt (cvc5))
lemma \<open>(1705 :: int) AND 42 = 40\<close> by (smt (cvc5))
lemma \<open>(1705 :: int) AND - 42 = 1664\<close> by (smt (cvc5))
lemma \<open>(1705 :: int) AND 1 = 1\<close> by (smt (cvc5))
lemma \<open>- (1705 :: int) AND 42 = 2\<close> by (smt (cvc5))
lemma \<open>- (1705 :: int) AND - 42 = - 1706\<close> by (smt (cvc5))
lemma \<open>- (1705 :: int) AND 1 = 1\<close> by (smt (cvc5))
lemma \<open>(1705 :: int) OR 42 = 1707\<close> by (smt (cvc5))
lemma \<open>(1705 :: int) OR - 42 = - 1\<close> by (smt (cvc5))
lemma \<open>(1705 :: int) OR 1 = 1705\<close> by (smt (cvc5))
lemma \<open>- (1705 :: int) OR 42 = - 1665\<close> by (smt (cvc5))
lemma \<open>- (1705 :: int) OR - 42 = - 41\<close> by (smt (cvc5))
lemma \<open>- (1705 :: int) OR 1 = - 1705\<close> by (smt (cvc5))
lemma \<open>(1705 :: int) XOR 42 = 1667\<close> by (smt (cvc5))
lemma \<open>(1705 :: int) XOR - 42 = - 1665\<close> by (smt (cvc5))
lemma \<open>(1705 :: int) XOR 1 = 1704\<close> by (smt (cvc5))
lemma \<open>- (1705 :: int) XOR 42 = - 1667\<close> by (smt (cvc5))
lemma \<open>- (1705 :: int) XOR - 42 = 1665\<close> by (smt (cvc5))
lemma \<open>- (1705 :: int) XOR 1 = - 1706\<close> by (smt (cvc5))
lemma \<open>push_bit 3 (1705 :: int) = 13640\<close> by (smt (cvc5))
lemma \<open>push_bit (Suc (Suc (Suc 0))) (1705 :: int) = 13640\<close> by (smt (cvc5))
lemma \<open>push_bit 3 (- 1705 :: int) = - 13640\<close> by (smt (cvc5))
lemma \<open>push_bit (Suc (Suc (Suc 0))) (- 1705 :: int) = - 13640\<close> by (smt (cvc5))
lemma \<open>push_bit 3 (1 :: int) = 8\<close> by (smt (cvc5))
lemma \<open>push_bit (Suc (Suc (Suc 0))) (1 :: int) = 8\<close> by (smt (cvc5))
lemma \<open>push_bit 3 (- 1 :: int) = - 8\<close> by (simp add: mask_eq_exp_minus_1)
lemma \<open>push_bit (Suc (Suc (Suc 0))) (- 1 :: int) = - 8\<close> by (simp add: mask_eq_exp_minus_1)

lemma \<open>(1705 :: int) << 3  = 13640\<close> by (smt (cvc5))
lemma
  \<open>(1705 :: int) << Suc (Suc (Suc 0)) = 13640\<close> by (smt (cvc5))
lemma \<open>(- 1705 :: int) << 3 = - 13640\<close> by (smt (cvc5))
lemma \<open>(- 1705 :: int) << Suc (Suc (Suc 0)) = - 13640\<close> by (smt (cvc5))
lemma \<open>(1 :: int) << 3 = 8\<close> by (smt (cvc5))
lemma \<open>(1 :: int) << Suc (Suc (Suc 0)) = 8\<close> by (smt (cvc5))
lemma \<open>(- 1 :: int) << 3 = - 8\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma \<open>(- 1 :: int) << Suc (Suc (Suc 0)) = - 8\<close> by (smt (cvc5))
lemma \<open>drop_bit 3 (1705 :: int) = 213\<close> by (smt (cvc5))
lemma \<open>drop_bit (Suc (Suc (Suc 0))) (1705 :: int) = 213\<close> by (smt (cvc5))
lemma \<open>drop_bit 3 (- 1705 :: int) = - 214\<close> by (smt (cvc5))
lemma \<open>drop_bit (Suc (Suc (Suc 0))) (- 1705 :: int) = - 214\<close> by (smt (cvc5))
lemma \<open>drop_bit 3 (1 :: int) = 0\<close> by (smt (cvc5))
lemma \<open>drop_bit (Suc (Suc (Suc 0))) (1 :: int) = 0\<close> by (smt (cvc5))
lemma \<open>(1705 :: int) >> 3 = 213\<close> by (smt (cvc5))
lemma \<open>(1705 :: int) >> Suc (Suc (Suc 0)) = 213\<close> by (smt (cvc5))
lemma \<open>(- 1705 :: int) >> 3 = - 214\<close> by (smt (cvc5))
lemma \<open>(- 1705 :: int) >> Suc (Suc (Suc 0)) = - 214\<close> by (smt (cvc5))
lemma \<open>(1 :: int) >> 3 = 0\<close> by (smt (cvc5))
lemma \<open>(1 :: int) >> Suc (Suc (Suc 0)) = 0\<close> by (smt (cvc5))
lemma \<open>take_bit 3 (1705 :: int) = 1\<close> by (smt (cvc5))
lemma \<open>take_bit (Suc (Suc (Suc 0))) (1705 :: int) = 1\<close>
  by (simp flip: add_2_eq_Suc)

lemma \<open>take_bit 3 (- 1705 :: int) = 7\<close> by (smt (cvc5))
lemma \<open>take_bit (Suc (Suc (Suc 0))) (- 1705 :: int) = 7\<close>
  by (simp flip: add_2_eq_Suc)

lemma \<open>take_bit 3 (1 :: int) = 1\<close> by (smt (cvc5))
lemma \<open>take_bit (Suc (Suc (Suc 0))) (1 :: int) = 1\<close> by (smt (cvc5))
lemma \<open>take_bit 3 (- 1 :: int) = 7\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma \<open>take_bit (Suc (Suc (Suc 0))) (- 1 :: int) = 7\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma \<open>signed_take_bit 3 (1705 :: int) = - 7\<close> by (smt (cvc5))
lemma \<open>signed_take_bit (Suc (Suc (Suc 0))) (1705 :: int) = - 7\<close> by (smt (cvc5))
lemma \<open>signed_take_bit 3 (- 1705 :: int) = 7\<close> by (smt (cvc5))
lemma \<open>signed_take_bit (Suc (Suc (Suc 0))) (- 1705 :: int) = 7\<close> by (smt (cvc5))
lemma \<open>signed_take_bit 3 (1 :: int) = 1\<close> by (smt (cvc5))
lemma \<open>signed_take_bit (Suc (Suc (Suc 0))) (1 :: int) = 1\<close> by (smt (cvc5))


section \<open>\<^typ>\<open>'a word\<close> (I instantiated the ones using symbolic bit-widths with 32)\<close>
declare[[smt_expert_debug_alethe_level=0]]

lemma \<open>(1705 :: 8 word) = 169\<close> by (smt (cvc5))
lemma \<open>(- 1705 :: 8 word) = 87\<close> by (smt (cvc5))
lemma \<open>(257 :: 8 word) = 1\<close> by (smt (cvc5))
lemma \<open>(42 :: 8 word) \<le> 1705\<close> by (smt (cvc5))
lemma \<open>(- 42 :: 8 word) \<le> 230\<close> by (smt (cvc5))
lemma \<open>(42 :: 8 word) \<le> - 1705\<close> by (smt (cvc5))
lemma \<open>- (42 :: 8 word) \<le> 235\<close> by (smt (cvc5))
lemma \<open>(1 :: 8 word) \<le> 1705\<close> by (smt (cvc5))
lemma \<open>(- 1 :: 8 word) \<le> 65535\<close> by (smt (cvc5))
lemma \<open>(42 :: 8 word) < 1705\<close> by (smt (cvc5))
lemma \<open>(- 42 :: 8 word) < 230\<close> by (smt (cvc5))
lemma \<open>(42 :: 8 word) < - 1705\<close> by (smt (cvc5))
lemma \<open>- (42 :: 8 word) < 230\<close> by (smt (cvc5))
lemma \<open>(1 :: 8 word) < 1705\<close> by (smt (cvc5))
lemma \<open>(1705 :: 8 word) < - 1\<close> by (smt (cvc5))
lemma \<open>(42 :: 8 word) \<le>s 1333\<close> by (smt (cvc5))
lemma \<open>(- 42 :: 8 word) \<le>s 230\<close> by (smt (cvc5))
lemma \<open>(42 :: 8 word) \<le>s - 1705\<close> by (smt (cvc5))
lemma \<open>- (42 :: 8 word) \<le>s - 1705\<close> by (smt (cvc5))
lemma \<open>(1 :: 8 word) \<le>s 42\<close> by (smt (cvc5))
lemma \<open>(42 :: 8 word) <s 1333\<close> by (smt (cvc5))
lemma \<open>(- 42 :: 8 word) <s 230\<close> by (smt (cvc5))
lemma \<open>(42 :: 8 word) <s - 1705\<close> by (smt (cvc5))
lemma \<open>- (42 :: 8 word) <s - 1705\<close> by (smt (cvc5))
lemma \<open>(1 :: 8 word) <s 42\<close> by (smt (cvc5))
lemma \<open>bit (1705 :: 16 word) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma \<open>bit (1705 :: 16 word) 3\<close> by (smt (cvc5))
lemma \<open>\<not> bit (- 1705 :: 16 word) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma \<open>\<not> bit (- 1705 :: 16 word) 3\<close> by (smt (cvc5))
lemma \<open>\<not> bit (1 :: 32 word) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma \<open>\<not> bit (1 :: 32 word) 3\<close> by (smt (cvc5))
lemma \<open>(NOT 1705 :: 32 word) = - 1706\<close> by (smt (cvc5))
lemma \<open>(NOT (- 42 :: 32 word)) = 41\<close> by (smt (cvc5))
lemma \<open>(NOT 1 :: 32 word) = - 2\<close> by (smt (cvc5))
lemma \<open>(1705 :: 32 word) AND 42 = 40\<close> by (smt (cvc5))
lemma \<open>(1705 :: 32 word) AND - 42 = 1664\<close> by (smt (cvc5))
lemma \<open>(1705 :: 32 word) AND 1 = 1\<close> by (smt (cvc5))
lemma \<open>- (1705 :: 32 word) AND 42 = 2\<close> by (smt (cvc5))
lemma \<open>- (1705 :: 32 word) AND - 42 = - 1706\<close> by (smt (cvc5))
lemma \<open>- (1705 :: 32 word) AND 1 = 1\<close> by (smt (cvc5))
lemma \<open>(1705 :: 32 word) OR 42 = 1707\<close> by (smt (cvc5))
lemma \<open>(1705 :: 32 word) OR - 42 = - 1\<close> by (smt (cvc5))
lemma \<open>(1705 :: 32 word) OR 1 = 1705\<close> by (smt (cvc5))
lemma \<open>- (1705 :: 32 word) OR 42 = - 1665\<close> by (smt (cvc5))
lemma \<open>- (1705 :: 32 word) OR - 42 = - 41\<close> by (smt (cvc5))
lemma \<open>- (1705 :: 32 word) OR 1 = - 1705\<close> by (smt (cvc5))
lemma \<open>(1705 :: 32 word) XOR 42 = 1667\<close> by (smt (cvc5))
lemma \<open>(1705 :: 32 word) XOR - 42 = - 1665\<close> by (smt (cvc5))
lemma \<open>(1705 :: 32 word) XOR 1 = 1704\<close> by (smt (cvc5))
lemma \<open>- (1705 :: 32 word) XOR 42 = - 1667\<close> by (smt (cvc5))
lemma \<open>- (1705 :: 32 word) XOR - 42 = 1665\<close> by (smt (cvc5))
lemma \<open>- (1705 :: 32 word) XOR 1 = - 1706\<close> by (smt (cvc5))



lemma \<open>push_bit 3 (1705 :: 32 word) = 13640\<close> by (smt (cvc5))
lemma \<open>push_bit (Suc (Suc (Suc 0))) (1705 :: 32 word) = 13640\<close> by (smt (cvc5))
lemma \<open>push_bit 3 (- 1705 :: 32 word) = - 13640\<close> by (smt (cvc5))
lemma \<open>push_bit (Suc (Suc (Suc 0))) (- 1705 :: 32 word) = - 13640\<close> by (smt (cvc5))
lemma \<open>push_bit 3 (1 :: 32 word) = 8\<close> by (smt (cvc5))
lemma \<open>push_bit (Suc (Suc (Suc 0))) (1 :: 32 word) = 8\<close> by (smt (cvc5))
lemma \<open>push_bit 3 (- 1 :: 32 word) = - 8\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma \<open>push_bit (Suc (Suc (Suc 0))) (- 1 :: 32 word) = - 8\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma \<open>(1705 :: 32 word) << 3 = 13640\<close> by (smt (cvc5))
lemma \<open>(1705 :: 32 word) << Suc (Suc (Suc 0)) = 13640\<close> by (smt (cvc5))
lemma \<open>(- 1705 :: 32 word) << 3 = - 13640\<close> by (smt (cvc5))
lemma \<open>(- 1705 :: 32 word) << Suc (Suc (Suc 0)) = - 13640\<close> by (smt (cvc5))
lemma \<open>(1 :: 32 word) << 3 = 8\<close> by (smt (cvc5))
lemma \<open>(1 :: 32 word) << Suc (Suc (Suc 0)) = 8\<close> by (smt (cvc5))
lemma \<open>(- 1 :: 32 word) << 3 = - 8\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma \<open>(- 1 :: 32 word) << Suc (Suc (Suc 0)) = - 8\<close> by (smt (cvc5))
lemma \<open>drop_bit 3 (1705 :: 16 word) = 213\<close> by (smt (cvc5))
lemma \<open>drop_bit (Suc (Suc (Suc 0))) (1705 :: 16 word) = 213\<close> by (smt (cvc5))
lemma \<open>drop_bit 3 (- 1705 :: 16 word) = 7978\<close> by (smt (cvc5))
lemma \<open>drop_bit (Suc (Suc (Suc 0))) (- 1705 :: 16 word) = 7978\<close> by (smt (cvc5))
lemma \<open>drop_bit 3 (1 :: 16 word) = 0\<close> by (smt (cvc5))
lemma \<open>drop_bit (Suc (Suc (Suc 0))) (1 :: 16 word) = 0\<close> by (smt (cvc5))
lemma \<open>(1705 :: 16 word) >> 3 = 213\<close>
  by simp

lemma \<open>(1705 :: 16 word) >> Suc (Suc (Suc 0)) = 213\<close>
  by simp

lemma \<open>(- 1705 :: 16 word) >> 3 = 7978\<close>
  by simp

lemma \<open>(- 1705 :: 16 word) >> Suc (Suc (Suc 0)) = 7978\<close>
  by simp

lemma \<open>(1 :: 16 word) >> 3 = 0\<close>
  by simp

lemma \<open>(1 :: 16 word) >> Suc (Suc (Suc 0)) = 0\<close>
  by simp

lemma \<open>signed_drop_bit 3 (1705 :: 16 word) = 213\<close>
  by simp

lemma \<open>signed_drop_bit (Suc (Suc (Suc 0))) (1705 :: 16 word) = 213\<close>
  by simp

lemma \<open>signed_drop_bit 3 (- 1705 :: 16 word) = - 214\<close>
  by simp

lemma \<open>signed_drop_bit (Suc (Suc (Suc 0))) (- 1705 :: 16 word) = - 214\<close>
  by simp

lemma \<open>signed_drop_bit 3 (1 :: 16 word) = 0\<close>
  by simp

lemma \<open>signed_drop_bit (Suc (Suc (Suc 0))) (1 :: 16 word) = 0\<close>
  by simp

lemma \<open>(1705 :: 16 word) >>> 3 = 213\<close>
  by simp

lemma \<open>(1705 :: 16 word) >>> Suc (Suc (Suc 0)) = 213\<close>
  by simp

lemma \<open>(- 1705 :: 16 word) >>> 3 = - 214\<close>
  by simp

lemma \<open>(- 1705 :: 16 word) >>> Suc (Suc (Suc 0)) = - 214\<close>
  by simp

lemma \<open>(1 :: 16 word) >>> 3 = 0\<close>
  by simp

lemma \<open>(1 :: 16 word) >>> Suc (Suc (Suc 0)) = 0\<close>
  by simp

lemma \<open>take_bit 3 (1705 :: 16 word) = 1\<close>
  by simp

lemma \<open>take_bit (Suc (Suc (Suc 0))) (1705 :: 16 word) = 1\<close>
  by (simp flip: add_2_eq_Suc)

lemma \<open>take_bit 3 (- 1705 :: 16 word) = 7\<close>
  by simp

lemma \<open>take_bit (Suc (Suc (Suc 0))) (- 1705 :: 16 word) = 7\<close>
  by (simp flip: add_2_eq_Suc)

lemma \<open>take_bit 3 (1 :: 16 word) = 1\<close>
  by simp

lemma \<open>take_bit (Suc (Suc (Suc 0))) (1 :: 16 word) = 1\<close>
  by simp

lemma \<open>take_bit 3 (- 1 :: 16 word) = 7\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma \<open>take_bit (Suc (Suc (Suc 0))) (- 1 :: 16 word) = 7\<close>
  by (simp add: mask_eq_exp_minus_1)

lemma \<open>signed_take_bit 3 (1705 :: 16 word) = - 7\<close>
  by simp

lemma \<open>signed_take_bit (Suc (Suc (Suc 0))) (1705 :: 16 word) = - 7\<close>
  by simp

lemma \<open>signed_take_bit 3 (- 1705 :: 16 word) = 7\<close>
  by simp

lemma \<open>signed_take_bit (Suc (Suc (Suc 0))) (- 1705 :: 16 word) = 7\<close>
  by simp

lemma \<open>signed_take_bit 3 (1 :: 16 word) = 1\<close>
  by simp

lemma \<open>signed_take_bit (Suc (Suc (Suc 0))) (1 :: 16 word) = 1\<close>
  by simp

lemma \<open>(1705 :: 16 word) div 42 = 40\<close>
  by simp

lemma \<open>(- 1705 :: 16 word) div 42 = 1519\<close>
  by simp

lemma \<open>(1705 :: 16 word) div - 42 = 0\<close>
  by simp

lemma \<open>(- 1705 :: 16 word) div - 42 = 0\<close>
  by simp

lemma \<open>(1705 :: 16 word) div 1 = 1705\<close>
  by simp

lemma \<open>(1705 :: 16 word) div - 1 = 0\<close>
  by simp

lemma \<open>(1 :: 16 word) div 42 = 0\<close>
  by simp

lemma \<open>(- 1 :: 16 word) div 42 = 1560\<close>
  by simp

lemma \<open>(1705 :: 16 word) mod 42 = 25\<close>
  by simp

lemma \<open>(- 1705 :: 16 word) mod 42 = 33\<close>
  by simp

lemma \<open>(1705 :: 16 word) mod - 42 = 1705\<close>
  by simp

lemma \<open>(- 1705 :: 16 word) mod - 42 = 63831\<close>
  by simp

lemma \<open>(1705 :: 16 word) mod 1 = 0\<close>
  by simp

lemma \<open>(1705 :: 16 word) mod - 1 = 1705\<close>
  by simp

lemma \<open>(1 :: 16 word) mod 42 = 1\<close>
  by simp

lemma \<open>(- 1 :: 16 word) mod 42 = 15\<close>
  by simp

lemma \<open>(1705 :: 16 word) sdiv 42 = 40\<close>
  by simp

lemma \<open>(- 1705 :: 16 word) sdiv 42 = 65496\<close>
  by simp

lemma \<open>(1705 :: 16 word) sdiv - 42 = 65496\<close>
  by simp

lemma \<open>(- 1705 :: 16 word) sdiv - 42 = 40\<close>
  by simp

lemma \<open>(1705 :: 16 word) sdiv 1 = 1705\<close>
  by simp

lemma \<open>(1705 :: 16 word) sdiv - 1 = 63831\<close>
  by simp

lemma \<open>(1 :: 16 word) sdiv 42 = 0\<close>
  by simp

lemma \<open>(- 1 :: 16 word) sdiv 42 = 0\<close>
  by simp

lemma \<open>(1705 :: 16 word) smod 42 = 25\<close>
  by simp

lemma \<open>(- 1705 :: 16 word) smod 42 = 65511\<close>
  by simp

lemma \<open>(1705 :: 16 word) smod - 42 = 25\<close>
  by simp

lemma \<open>(- 1705 :: 16 word) smod - 42 = 65511\<close>
  by simp

lemma \<open>(1705 :: 16 word) smod 1 = 0\<close>
  by simp

lemma \<open>(1705 :: 16 word) smod - 1 = 0\<close>
  by simp

lemma \<open>(1 :: 16 word) smod 42 = 1\<close>
  by simp

lemma \<open>(- 1 :: 16 word) smod 42 = 65535\<close>
  by simp

text "modulus"

lemma "(27 :: 4 word) = -5" by simp

lemma "(27 :: 4 word) = 11" by simp

lemma "27 \<noteq> (11 :: 6 word)" by simp

text "signed"

lemma "(127 :: 6 word) = -1" by simp

text "number ring simps"

lemma
  "27 + 11 = (38::32 word)"
  "27 + 11 = (6::5 word)"
  "7 * 3 = (21::32 word)"
  "11 - 27 = (-16::32 word)"
  "- (- 11) = (11::32 word)"
  "-40 + 1 = (-39::32 word)"
  by simp_all

lemma "word_pred 2 = 1" by simp

lemma "word_succ (- 3) = -2" by simp

lemma "23 < (27::8 word)" by simp
lemma "23 \<le> (27::8 word)" by simp
lemma "\<not> 23 < (27::2 word)" by simp
lemma "0 < (4::3 word)" by simp
lemma "1 < (4::3 word)" by simp
lemma "0 < (1::3 word)" by simp

text "ring operations"

lemma "a + 2 * b + c - b = (b + c) + (a :: 32 word)" by simp

text "casting"

lemma "uint (234567 :: 10 word) = 71" by simp
lemma "uint (-234567 :: 10 word) = 953" by simp
lemma "sint (234567 :: 10 word) = 71" by simp
lemma "sint (-234567 :: 10 word) = -71" by simp
lemma "uint (1 :: 10 word) = 1" by simp

lemma "unat (-234567 :: 10 word) = 953" by simp
lemma "unat (1 :: 10 word) = 1" by simp

lemma "ucast (0b1010 :: 4 word) = (0b10 :: 2 word)" by simp
lemma "ucast (0b1010 :: 4 word) = (0b1010 :: 10 word)" by simp
lemma "scast (0b1010 :: 4 word) = (0b111010 :: 6 word)" by simp
lemma "ucast (1 :: 4 word) = (1 :: 2 word)" by simp

text "reducing goals to nat or int and arith:"
lemma "i < x \<Longrightarrow> i < i + 1" for i x :: "32 word"
  by unat_arith
lemma "i < x \<Longrightarrow> i < i + 1" for i x :: "32 word"
  by unat_arith

text "bit operations"

lemma "0b110 AND 0b101 = (0b100 :: 32 word)" by simp
lemma "0b110 OR 0b011 = (0b111 :: 8 word)" by simp
lemma "0xF0 XOR 0xFF = (0x0F :: 8 word)" by simp
lemma "NOT (0xF0 :: 16 word) = 0xFF0F" by simp
lemma "0 AND 5 = (0 :: 8 word)" by simp
lemma "1 AND 1 = (1 :: 8 word)" by simp
lemma "1 AND 0 = (0 :: 8 word)" by simp
lemma "1 AND 5 = (1 :: 8 word)" by simp
lemma "1 OR 6 = (7 :: 8 word)" by simp
lemma "1 OR 1 = (1 :: 8 word)" by simp
lemma "1 XOR 7 = (6 :: 8 word)" by simp
lemma "1 XOR 1 = (0 :: 8 word)" by simp
lemma "NOT 1 = (254 :: 8 word)" by simp
lemma "NOT 0 = (255 :: 8 word)" by simp

lemma "(-1 :: 32 word) = 0xFFFFFFFF" by simp

lemma "bit (0b0010 :: 4 word) 1" by simp
lemma "\<not> bit (0b0010 :: 4 word) 0" by simp
lemma "\<not> bit (0b1000 :: 3 word) 4" by simp
lemma "\<not> bit (1 :: 3 word) 2" by simp

lemma "bit (0b11000 :: 10 word) n = (n = 4 \<or> n = 3)"
  by (auto simp add: bit_numeral_rec bit_1_iff split: nat.splits)

lemma "set_bit 55 7 True = (183::32 word)" by simp
lemma "set_bit 0b0010 7 True = (0b10000010::32 word)" by simp
lemma "set_bit 0b0010 1 False = (0::32 word)" by simp
lemma "set_bit 1 3 True = (0b1001::32 word)" by simp
lemma "set_bit 1 0 False = (0::32 word)" by simp
lemma "set_bit 0 3 True = (0b1000::32 word)" by simp
lemma "set_bit 0 3 False = (0::32 word)" by simp

lemma "odd (0b0101::32 word)" by simp
lemma "even (0b1000::32 word)" by simp
lemma "odd (1::32 word)" by simp
lemma "even (0::32 word)" by simp

lemma "\<not> msb (0b0101::4 word)" by simp
lemma   "msb (0b1000::4 word)" by simp
lemma "\<not> msb (1::4 word)" by simp
lemma "\<not> msb (0::4 word)" by simp

lemma "word_cat (27::4 word) (27::8 word) = (2843::32 word)"
  by simp
lemma "word_cat (0b0011::4 word) (0b1111::6word) = (0b0011001111 :: 10 word)"
  by simp

lemma "0b1011 << 2 = (0b101100::32 word)" by simp
lemma "0b1011 >> 2 = (0b10::8 word)" by simp
lemma "0b1011 >>> 2 = (0b10::8 word)" by simp
lemma "1 << 2 = (0b100::32 word)" apply simp? oops

lemma "slice 3 (0b101111::6 word) = (0b101::3 word)" by simp
lemma "slice 3 (1::6 word) = (0::3 word)" apply simp? oops

lemma "word_rotr 2 0b0110 = (0b1001::4 word)" by simp
lemma "word_rotl 1 0b1110 = (0b1101::4 word)" by simp
lemma "word_roti 2 0b1110 = (0b1011::4 word)" by simp
lemma "word_roti (- 2) 0b0110 = (0b1001::4 word)" by simp
lemma "word_rotr 2 0 = (0::4 word)" by simp
lemma "word_rotr 2 1 = (0b0100::4 word)" apply simp? oops
lemma "word_rotl 2 1 = (0b0100::4 word)" apply simp? oops
lemma "word_roti (- 2) 1 = (0b0100::4 word)" apply simp? oops

lemma "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)"
proof -
  have "(x AND 0xff00) OR (x AND 0x00ff) = x AND (0xff00 OR 0x00ff)"
    by (simp only: word_ao_dist2)
  also have "0xff00 OR 0x00ff = (-1::16 word)"
    by simp
  also have "x AND -1 = x"
    by simp
  finally show ?thesis .
qed

lemma "word_next (2:: 8 word) = 3" by eval
lemma "word_next (255:: 8 word) = 255" by eval
lemma "word_prev (2:: 8 word) = 1" by eval
lemma "word_prev (0:: 8 word) = 0" by eval

text \<open>signed division\<close>

lemma
  "( 4 :: 32 word) sdiv  4 =  1"
  "(-4 :: 32 word) sdiv  4 = -1"
  "(-3 :: 32 word) sdiv  4 =  0"
  "( 3 :: 32 word) sdiv -4 =  0"
  "(-3 :: 32 word) sdiv -4 =  0"
  "(-5 :: 32 word) sdiv -4 =  1"
  "( 5 :: 32 word) sdiv -4 = -1"
  by (simp_all add: sdiv_word_def signed_divide_int_def)

lemma
  "( 4 :: 32 word) smod  4 =   0"
  "( 3 :: 32 word) smod  4 =   3"
  "(-3 :: 32 word) smod  4 =  -3"
  "( 3 :: 32 word) smod -4 =   3"
  "(-3 :: 32 word) smod -4 =  -3"
  "(-5 :: 32 word) smod -4 =  -1"
  "( 5 :: 32 word) smod -4 =   1"
  by (simp_all add: smod_word_def signed_modulo_int_def signed_divide_int_def)


text \<open>comparison\<close>

lemma "1 < (1024::32 word) \<and> 1 \<le> (1024::32 word)"
  by simp

text "bool lists"

lemma "of_bl [True, False, True, True] = (0b1011::32 word)" by simp

lemma "to_bl (0b110::4 word) = [False, True, True, False]" by simp

lemma "of_bl (replicate 32 True) = (0xFFFFFFFF::32 word)"
  by (simp add: numeral_eq_Suc)

text "proofs using bitwise expansion"

lemma "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)"
  by word_bitwise

lemma "(x AND NOT 3) >> 4 << 2 = ((x >> 2) AND NOT 3)"
  for x :: "10 word"
  by word_bitwise

lemma "((x AND -8) >> 3) AND 7 = (x AND 56) >> 3"
  for x :: "12 word"
  by word_bitwise

text "some problems require further reasoning after bit expansion"

lemma "x \<le> 42 \<Longrightarrow> x \<le> 89"
  for x :: "8 word"
  apply word_bitwise
  apply blast
  done

lemma "(x AND 1023) = 0 \<Longrightarrow> x \<le> -1024"
  for x :: \<open>32 word\<close>
  apply word_bitwise
  apply clarsimp
  done

text "operations like shifts by non-numerals will expose some internal list
 representations but may still be easy to solve"

lemma shiftr_overflow: "32 \<le> a \<Longrightarrow> b >> a = 0"
  for b :: \<open>32 word\<close>
  apply word_bitwise
  apply simp
  done

(* testing for presence of word_bitwise *)
lemma "((x :: 32 word) >> 3) AND 7 = (x AND 56) >> 3"
  by word_bitwise

end


end


section \<open>Combined integer-bitvector properties\<close>

lemma
  assumes "bv2int 0 = 0"
      and "bv2int 1 = 1"
      and "bv2int 2 = 2"
      and "bv2int 3 = 3"
      and "\<forall>x::2 word. bv2int x > 0"
  shows "\<forall>i::int. i < 0 \<longrightarrow> (\<forall>x::2 word. bv2int x > i)"
  using assms by (smt (cvc5)) (*TODO Mathias type problem*)

lemma "P (0 \<le> (a :: 4 word)) = P True" by (smt (cvc5))

section \<open>Misc\<close>

(*TODO: support ABSORB rule*)
lemma "a > (4294967294::32 word) \<Longrightarrow> a = 4294967295"
  by (smt (cvc5))



end
