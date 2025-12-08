(*  Title:      HOL/SMT_Examples/SMT_Word_Examples.thy
    Author:     Sascha Boehme, TU Muenchen
    Author:     Hanna Lachnitt, Stanford University

*)

section \<open>Word examples for for SMT binding\<close>

theory SMT_Word_Examples_CVC       
imports "HOL-Library.Word" "HOL.SMT_CVC_Word"
begin


declare[[smt_expert_debug_alethe_level=3]]
declare[[smt_expert_debug_alethe_files="smt_normalize"]]

definition shiftl_lift :: "'a::len word \<Rightarrow> int \<Rightarrow> 'a::len word" 
  where "shiftl_lift x i = x << (nat i)"
lemma [nat_normalized_input]:
  "shiftl_lift w (int x) \<equiv> shiftl w x "
  unfolding shiftl_lift_def by simp

lemma test:
  "(x << i) \<equiv> push_bit_lift (int i) x"
  unfolding shiftl_def push_bit_lift_def by simp

ML \<open>
val nat_native_ops_tab =
[
  ("Bit_Shifts_Infix_Syntax.semiring_bit_operations_class.shiftl",@{thms test})
]
val ops_tab = fold SMT_Normalize.add_nat_native_ops_tab nat_native_ops_tab
val _ = Theory.setup (Context.theory_map (ops_tab))

\<close>


declare [[smt_nat_as_int,smt_trace]]
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


section \<open>Overview Regressions\<close>

text \<open>
From AFP Word_Lib Examples.thy

These are now part of our monthly metrics that is why I numbered them

Total: 336
Date counted: 12/08/26


Section           Total      Success
------------------------------------------------
nat                 30        0
int                 69        0
basic words         141       53
modulus             3         2
signed              1         0
number ring simps   9         4
ring operations     1         0
casting             11        0
reduction to arith  1         0
bit operations      55        24
signed division     2         0
comparision         1         1
bool lists          3         0
bitwise expansion   5         0
symbol shifts       2         0
combined integer-bv 2         0
misc                1         0
------------------------------------------------
total               337       84
\<close>

section \<open>\<^typ>\<open>nat\<close>\<close>

text \<open>
These should not be encoded into bit-vector operators but any natural numbers
should be lifted to integers.

Benchmark Nrs: 1-30
Date counted: 12/08/26

Total:    30
Success:  0

\<close>

lemma bvex_1: \<open>bit (1705 :: nat) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma bvex_2: \<open>bit (1705 :: nat) 3\<close> by (smt (cvc5))
lemma bvex_3: \<open>\<not> bit (1 :: nat) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma bvex_4: \<open>\<not> bit (1 :: nat) 3\<close> by (smt (cvc5))

lemma bvex_5: \<open>(1705 :: nat) AND 42 = 40\<close> by (smt (cvc5))
lemma bvex_6: \<open>(1705 :: nat) AND Suc 0 = 1\<close> by (smt (cvc5))
lemma bvex_7: \<open>(1705 :: nat) OR 42 = 1707\<close> by (smt (cvc5))
lemma bvex_8: \<open>(1705 :: nat) OR Suc 0 = 1705\<close> by (smt (cvc5))
lemma bvex_9: \<open>(1705 :: nat) XOR 42 = 1667\<close> by (smt (cvc5))
lemma bvex_10: \<open>(1705 :: nat) XOR 1 = 1704\<close> by (smt (cvc5))

lemma bvex_11: \<open>push_bit 3 (1705 :: nat) = 13640\<close> by (smt (cvc5))
lemma bvex_12: \<open>push_bit (Suc (Suc (Suc 0))) (1705 :: nat) = 13640\<close> by (smt (cvc5))
lemma bvex_13: \<open>push_bit 3 (Suc 0) = 8\<close> by (smt (cvc5))
lemma bvex_14: \<open>push_bit (Suc (Suc (Suc 0))) (Suc 0) = 8\<close> by (smt (cvc5))

lemma bvex_15: \<open>(1705 :: nat) << 3 = 13640\<close> by (smt (cvc5))
lemma bvex_16: \<open>(1705 :: nat) << Suc (Suc (Suc 0)) = 13640\<close> by (smt (cvc5))
lemma bvex_17: \<open>Suc 0 << 3 = 8\<close> by (smt (cvc5))
lemma bvex_18: \<open>Suc 0 << Suc (Suc (Suc 0)) = 8\<close> by (smt (cvc5))

lemma bvex_19: \<open>drop_bit 3 (1705 :: nat) = 213\<close> by (smt (cvc5))
lemma bvex_20: \<open>drop_bit (Suc (Suc (Suc 0))) (1705 :: nat) = 213\<close> by (smt (cvc5))
lemma bvex_21: \<open>drop_bit 3 (Suc 0) = 0\<close> by (smt (cvc5))
lemma bvex_22: \<open>drop_bit (Suc (Suc (Suc 0))) (Suc 0) = 0\<close> by (smt (cvc5))

lemma bvex_23: \<open>(1705 :: nat) >> 3 = 213\<close> by (smt (cvc5))
lemma bvex_24: \<open>(1705 :: nat) >> Suc (Suc (Suc 0)) = 213\<close> by (smt (cvc5))
lemma bvex_25: \<open>Suc 0 >> 3 = 0\<close> by (smt (cvc5))
lemma bvex_26: \<open>Suc 0 >> Suc (Suc (Suc 0)) = 0\<close> by (smt (cvc5))

lemma bvex_27: \<open>take_bit 3 (1705 :: nat) = 1\<close> by (smt (cvc5))
lemma bvex_28: \<open>take_bit (Suc (Suc (Suc 0))) (1705 :: nat) = 1\<close> by (smt (cvc5))
lemma bvex_29: \<open>take_bit 3 (Suc 0) = 1\<close> by (smt (cvc5))
lemma bvex_30: \<open>take_bit (Suc (Suc (Suc 0))) (Suc 0) = 1\<close> by (smt (cvc5))


section \<open>\<^typ>\<open>int\<close>\<close>

text \<open>
These should not be encoded into bit-vector operators.

Benchmark Nrs: 31-99
Date counted: 12/08/26

Total:    69
Success:  0

\<close>
lemma bvex_31: \<open>bit (1705 :: int) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma bvex_32: \<open>bit (1705 :: int) 3\<close> by (smt (cvc5))
lemma bvex_33: \<open>\<not> bit (- 1705 :: int) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma bvex_34: \<open>\<not> bit (- 1705 :: int) 3\<close> by (smt (cvc5))
lemma bvex_35: \<open>\<not> bit (1 :: int) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma bvex_36: \<open>\<not> bit (1 :: int) 3\<close> by (smt (cvc5))

lemma bvex_37: \<open>(NOT 1705 :: int) = - 1706\<close> by (smt (cvc5))
lemma bvex_38: \<open>(NOT (- 42 :: int)) = 41\<close> by (smt (cvc5))
lemma bvex_39: \<open>(NOT 1 :: int) = - 2\<close> by (smt (cvc5))

lemma bvex_40: \<open>(1705 :: int) AND 42 = 40\<close> by (smt (cvc5))
lemma bvex_41: \<open>(1705 :: int) AND - 42 = 1664\<close> by (smt (cvc5))
lemma bvex_42: \<open>(1705 :: int) AND 1 = 1\<close> by (smt (cvc5))
lemma bvex_43: \<open>- (1705 :: int) AND 42 = 2\<close> by (smt (cvc5))
lemma bvex_44: \<open>- (1705 :: int) AND - 42 = - 1706\<close> by (smt (cvc5))
lemma bvex_45: \<open>- (1705 :: int) AND 1 = 1\<close> by (smt (cvc5))

lemma bvex_46: \<open>(1705 :: int) OR 42 = 1707\<close> by (smt (cvc5))
lemma bvex_47: \<open>(1705 :: int) OR - 42 = - 1\<close> by (smt (cvc5))
lemma bvex_48: \<open>(1705 :: int) OR 1 = 1705\<close> by (smt (cvc5))
lemma bvex_49: \<open>- (1705 :: int) OR 42 = - 1665\<close> by (smt (cvc5))
lemma bvex_50: \<open>- (1705 :: int) OR - 42 = - 41\<close> by (smt (cvc5))
lemma bvex_51: \<open>- (1705 :: int) OR 1 = - 1705\<close> by (smt (cvc5))

lemma bvex_52: \<open>(1705 :: int) XOR 42 = 1667\<close> by (smt (cvc5))
lemma bvex_53: \<open>(1705 :: int) XOR - 42 = - 1665\<close> by (smt (cvc5))
lemma bvex_54: \<open>(1705 :: int) XOR 1 = 1704\<close> by (smt (cvc5))
lemma bvex_55: \<open>- (1705 :: int) XOR 42 = - 1667\<close> by (smt (cvc5))
lemma bvex_56: \<open>- (1705 :: int) XOR - 42 = 1665\<close> by (smt (cvc5))
lemma bvex_57: \<open>- (1705 :: int) XOR 1 = - 1706\<close> by (smt (cvc5))

lemma bvex_58: \<open>push_bit 3 (1705 :: int) = 13640\<close> by (smt (cvc5))
lemma bvex_59: \<open>push_bit (Suc (Suc (Suc 0))) (1705 :: int) = 13640\<close> by (smt (cvc5))
lemma bvex_60: \<open>push_bit 3 (- 1705 :: int) = - 13640\<close> by (smt (cvc5))
lemma bvex_61: \<open>push_bit (Suc (Suc (Suc 0))) (- 1705 :: int) = - 13640\<close> by (smt (cvc5))
lemma bvex_62: \<open>push_bit 3 (1 :: int) = 8\<close> by (smt (cvc5))
lemma bvex_63: \<open>push_bit (Suc (Suc (Suc 0))) (1 :: int) = 8\<close> by (smt (cvc5))
lemma bvex_64: \<open>push_bit 3 (- 1 :: int) = - 8\<close>  by (smt (cvc5)) (*by (simp add: mask_eq_exp_minus_1)*)
lemma bvex_65: \<open>push_bit (Suc (Suc (Suc 0))) (- 1 :: int) = - 8\<close>  by (smt (cvc5)) (*by (simp add: mask_eq_exp_minus_1)*)

lemma bvex_66: \<open>(1705 :: int) << 3  = 13640\<close> by (smt (cvc5))
lemma bvex_67: \<open>(1705 :: int) << Suc (Suc (Suc 0)) = 13640\<close> by (smt (cvc5))
lemma bvex_68: \<open>(- 1705 :: int) << 3 = - 13640\<close> by (smt (cvc5))
lemma bvex_69: \<open>(- 1705 :: int) << Suc (Suc (Suc 0)) = - 13640\<close> by (smt (cvc5))
lemma bvex_70: \<open>(1 :: int) << 3 = 8\<close> by (smt (cvc5))
lemma bvex_71: \<open>(1 :: int) << Suc (Suc (Suc 0)) = 8\<close> by (smt (cvc5))
lemma bvex_72: \<open>(- 1 :: int) << 3 = - 8\<close>  by (smt (cvc5)) (*by (simp add: mask_eq_exp_minus_1)*)
lemma bvex_73: \<open>(- 1 :: int) << Suc (Suc (Suc 0)) = - 8\<close> by (smt (cvc5))

lemma bvex_74: \<open>drop_bit 3 (1705 :: int) = 213\<close> by (smt (cvc5))
lemma bvex_75: \<open>drop_bit (Suc (Suc (Suc 0))) (1705 :: int) = 213\<close> by (smt (cvc5))
lemma bvex_76: \<open>drop_bit 3 (- 1705 :: int) = - 214\<close> by (smt (cvc5))
lemma bvex_77: \<open>drop_bit (Suc (Suc (Suc 0))) (- 1705 :: int) = - 214\<close> by (smt (cvc5))
lemma bvex_78: \<open>drop_bit 3 (1 :: int) = 0\<close> by (smt (cvc5))
lemma bvex_79: \<open>drop_bit (Suc (Suc (Suc 0))) (1 :: int) = 0\<close> by (smt (cvc5))

lemma bvex_80: \<open>(1705 :: int) >> 3 = 213\<close> by (smt (cvc5))
lemma bvex_81: \<open>(1705 :: int) >> Suc (Suc (Suc 0)) = 213\<close> by (smt (cvc5))
lemma bvex_82: \<open>(- 1705 :: int) >> 3 = - 214\<close> by (smt (cvc5))
lemma bvex_83: \<open>(- 1705 :: int) >> Suc (Suc (Suc 0)) = - 214\<close> by (smt (cvc5))
lemma bvex_84: \<open>(1 :: int) >> 3 = 0\<close> by (smt (cvc5))
lemma bvex_85: \<open>(1 :: int) >> Suc (Suc (Suc 0)) = 0\<close> by (smt (cvc5))

lemma bvex_86: \<open>take_bit 3 (1705 :: int) = 1\<close> by (smt (cvc5))
lemma bvex_87: \<open>take_bit (Suc (Suc (Suc 0))) (1705 :: int) = 1\<close> by (smt (cvc5)) (*by (simp flip: add_2_eq_Suc)*)
lemma bvex_88: \<open>take_bit 3 (- 1705 :: int) = 7\<close> by (smt (cvc5))
lemma bvex_89: \<open>take_bit (Suc (Suc (Suc 0))) (- 1705 :: int) = 7\<close> by (smt (cvc5)) (* by (simp flip: add_2_eq_Suc)*)
lemma bvex_90: \<open>take_bit 3 (1 :: int) = 1\<close> by (smt (cvc5))
lemma bvex_91: \<open>take_bit (Suc (Suc (Suc 0))) (1 :: int) = 1\<close> by (smt (cvc5))
lemma bvex_92: \<open>take_bit 3 (- 1 :: int) = 7\<close> by (smt (cvc5)) (*by (simp add: mask_eq_exp_minus_1)*)
lemma bvex_93: \<open>take_bit (Suc (Suc (Suc 0))) (- 1 :: int) = 7\<close> by (smt (cvc5)) (*by (simp add: mask_eq_exp_minus_1)*)

lemma bvex_94: \<open>signed_take_bit 3 (1705 :: int) = - 7\<close> by (smt (cvc5))
lemma bvex_95: \<open>signed_take_bit (Suc (Suc (Suc 0))) (1705 :: int) = - 7\<close> by (smt (cvc5))
lemma bvex_96: \<open>signed_take_bit 3 (- 1705 :: int) = 7\<close> by (smt (cvc5))
lemma bvex_97: \<open>signed_take_bit (Suc (Suc (Suc 0))) (- 1705 :: int) = 7\<close> by (smt (cvc5))
lemma bvex_98: \<open>signed_take_bit 3 (1 :: int) = 1\<close> by (smt (cvc5))
lemma bvex_99: \<open>signed_take_bit (Suc (Suc (Suc 0))) (1 :: int) = 1\<close> by (smt (cvc5))


section \<open>basic word 32 word\<close>

text \<open>
I instantiated any lemmas using symbolic bit-widths with 32.

Benchmark Nrs: 100-240
Date counted: 12/08/26

Total:    141
Success:  53

\<close>

lemma bvex_100: \<open>(1705 :: 8 word) = 169\<close> by (smt (cvc5))
lemma bvex_101: \<open>(- 1705 :: 8 word) = 87\<close> by (smt (cvc5))
lemma bvex_102: \<open>(257 :: 8 word) = 1\<close> by (smt (cvc5))
lemma bvex_103: \<open>(42 :: 8 word) \<le> 1705\<close> by (smt (cvc5))
lemma bvex_104: \<open>(- 42 :: 8 word) \<le> 230\<close> by (smt (cvc5))
lemma bvex_105: \<open>(42 :: 8 word) \<le> - 1705\<close> by (smt (cvc5))
lemma bvex_106: \<open>- (42 :: 8 word) \<le> 235\<close> by (smt (cvc5))
lemma bvex_107: \<open>(1 :: 8 word) \<le> 1705\<close> by (smt (cvc5))
lemma bvex_108: \<open>(- 1 :: 8 word) \<le> 65535\<close> by (smt (cvc5))
lemma bvex_109: \<open>(42 :: 8 word) < 1705\<close> by (smt (cvc5))
lemma bvex_110: \<open>(- 42 :: 8 word) < 230\<close> by (smt (cvc5))
lemma bvex_111: \<open>(42 :: 8 word) < - 1705\<close> by (smt (cvc5))
lemma bvex_112: \<open>- (42 :: 8 word) < 230\<close> by (smt (cvc5))
lemma bvex_113: \<open>(1 :: 8 word) < 1705\<close> by (smt (cvc5))
lemma bvex_114: \<open>(1705 :: 8 word) < - 1\<close> by (smt (cvc5))
lemma bvex_115: \<open>(42 :: 8 word) \<le>s 1333\<close> by (smt (cvc5))
lemma bvex_116: \<open>(- 42 :: 8 word) \<le>s 230\<close> by (smt (cvc5))
lemma bvex_117: \<open>(42 :: 8 word) \<le>s - 1705\<close> by (smt (cvc5))
lemma bvex_118: \<open>- (42 :: 8 word) \<le>s - 1705\<close> by (smt (cvc5))
lemma bvex_119: \<open>(1 :: 8 word) \<le>s 42\<close> by (smt (cvc5))
lemma bvex_120: \<open>(42 :: 8 word) <s 1333\<close> by (smt (cvc5))
lemma bvex_121: \<open>(- 42 :: 8 word) <s 230\<close> by (smt (cvc5))
lemma bvex_122: \<open>(42 :: 8 word) <s - 1705\<close> by (smt (cvc5))
lemma bvex_123: \<open>- (42 :: 8 word) <s - 1705\<close> by (smt (cvc5))
lemma bvex_124: \<open>(1 :: 8 word) <s 42\<close> by (smt (cvc5))

lemma bvex_125: \<open>bit (1705 :: 16 word) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma bvex_126: \<open>bit (1705 :: 16 word) 3\<close> by (smt (cvc5))
lemma bvex_127: \<open>\<not> bit (- 1705 :: 16 word) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma bvex_128: \<open>\<not> bit (- 1705 :: 16 word) 3\<close> by (smt (cvc5))
lemma bvex_129: \<open>\<not> bit (1 :: 32 word) (Suc (Suc (Suc 0)))\<close> by (smt (cvc5))
lemma bvex_130: \<open>\<not> bit (1 :: 32 word) 3\<close> by (smt (cvc5))

lemma bvex_131: \<open>(NOT 1705 :: 32 word) = - 1706\<close> by (smt (cvc5))
lemma bvex_132: \<open>(NOT (- 42 :: 32 word)) = 41\<close> by (smt (cvc5))
lemma bvex_133: \<open>(NOT 1 :: 32 word) = - 2\<close> by (smt (cvc5))

lemma bvex_134: \<open>(1705 :: 32 word) AND 42 = 40\<close> by (smt (cvc5))
lemma bvex_135: \<open>(1705 :: 32 word) AND - 42 = 1664\<close> by (smt (cvc5))
lemma bvex_136: \<open>(1705 :: 32 word) AND 1 = 1\<close> by (smt (cvc5))
lemma bvex_137: \<open>- (1705 :: 32 word) AND 42 = 2\<close> by (smt (cvc5))
lemma bvex_138: \<open>- (1705 :: 32 word) AND - 42 = - 1706\<close> by (smt (cvc5))
lemma bvex_139: \<open>- (1705 :: 32 word) AND 1 = 1\<close> by (smt (cvc5))

lemma bvex_140: \<open>(1705 :: 32 word) OR 42 = 1707\<close> by (smt (cvc5))
lemma bvex_141: \<open>(1705 :: 32 word) OR - 42 = - 1\<close> by (smt (cvc5))
lemma bvex_142: \<open>(1705 :: 32 word) OR 1 = 1705\<close> by (smt (cvc5))
lemma bvex_143: \<open>- (1705 :: 32 word) OR 42 = - 1665\<close> by (smt (cvc5))
lemma bvex_144: \<open>- (1705 :: 32 word) OR - 42 = - 41\<close> by (smt (cvc5))
lemma bvex_145: \<open>- (1705 :: 32 word) OR 1 = - 1705\<close> by (smt (cvc5))

lemma bvex_146: \<open>(1705 :: 32 word) XOR 42 = 1667\<close> by (smt (cvc5))
lemma bvex_147: \<open>(1705 :: 32 word) XOR - 42 = - 1665\<close> by (smt (cvc5))
lemma bvex_148: \<open>(1705 :: 32 word) XOR 1 = 1704\<close> by (smt (cvc5))
lemma bvex_149: \<open>- (1705 :: 32 word) XOR 42 = - 1667\<close> by (smt (cvc5))
lemma bvex_150: \<open>- (1705 :: 32 word) XOR - 42 = 1665\<close> by (smt (cvc5))
lemma bvex_151: \<open>- (1705 :: 32 word) XOR 1 = - 1706\<close> by (smt (cvc5))

lemma bvex_152: \<open>push_bit 3 (1705 :: 32 word) = 13640\<close> by (smt (cvc5))
lemma bvex_153: \<open>push_bit (Suc (Suc (Suc 0))) (1705 :: 32 word) = 13640\<close> by (smt (cvc5))
lemma bvex_154: \<open>push_bit 3 (- 1705 :: 32 word) = - 13640\<close> by (smt (cvc5))
lemma bvex_155: \<open>push_bit (Suc (Suc (Suc 0))) (- 1705 :: 32 word) = - 13640\<close> by (smt (cvc5))
lemma bvex_156: \<open>push_bit 3 (1 :: 32 word) = 8\<close> by (smt (cvc5))
lemma bvex_157: \<open>push_bit (Suc (Suc (Suc 0))) (1 :: 32 word) = 8\<close> by (smt (cvc5))
lemma bvex_158: \<open>push_bit 3 (- 1 :: 32 word) = - 8\<close> by (smt (cvc5)) (*by (simp add: mask_eq_exp_minus_1)*)
lemma bvex_159: \<open>push_bit (Suc (Suc (Suc 0))) (- 1 :: 32 word) = - 8\<close> by (smt (cvc5)) (*by (simp add: mask_eq_exp_minus_1)*)

lemma bvex_160: \<open>(1705 :: 32 word) << 3 = 13640\<close> by (smt (cvc5))
lemma bvex_161: \<open>(1705 :: 32 word) << Suc (Suc (Suc 0)) = 13640\<close> by (smt (cvc5))
lemma bvex_162: \<open>(- 1705 :: 32 word) << 3 = - 13640\<close> by (smt (cvc5))
lemma bvex_163: \<open>(- 1705 :: 32 word) << Suc (Suc (Suc 0)) = - 13640\<close> by (smt (cvc5))
lemma bvex_164: \<open>(1 :: 32 word) << 3 = 8\<close> by (smt (cvc5))
lemma bvex_165: \<open>(1 :: 32 word) << Suc (Suc (Suc 0)) = 8\<close> by (smt (cvc5))
lemma bvex_166: \<open>(- 1 :: 32 word) << 3 = - 8\<close> by (smt (cvc5)) (* by (simp add: mask_eq_exp_minus_1)*)
lemma bvex_167: \<open>(- 1 :: 32 word) << Suc (Suc (Suc 0)) = - 8\<close> by (smt (cvc5))

lemma bvex_168: \<open>drop_bit 3 (1705 :: 16 word) = 213\<close> by (smt (cvc5))
lemma bvex_169: \<open>drop_bit (Suc (Suc (Suc 0))) (1705 :: 16 word) = 213\<close> by (smt (cvc5))
lemma bvex_170: \<open>drop_bit 3 (- 1705 :: 16 word) = 7978\<close> by (smt (cvc5))
lemma bvex_171: \<open>drop_bit (Suc (Suc (Suc 0))) (- 1705 :: 16 word) = 7978\<close> by (smt (cvc5))
lemma bvex_172: \<open>drop_bit 3 (1 :: 16 word) = 0\<close> by (smt (cvc5))
lemma bvex_173: \<open>drop_bit (Suc (Suc (Suc 0))) (1 :: 16 word) = 0\<close> by (smt (cvc5))

lemma bvex_174: \<open>(1705 :: 16 word) >> 3 = 213\<close> by (smt (cvc5))
lemma bvex_175: \<open>(1705 :: 16 word) >> Suc (Suc (Suc 0)) = 213\<close> by (smt (cvc5))
lemma bvex_176: \<open>(- 1705 :: 16 word) >> 3 = 7978\<close> by (smt (cvc5))
lemma bvex_177: \<open>(- 1705 :: 16 word) >> Suc (Suc (Suc 0)) = 7978\<close> by (smt (cvc5))
lemma bvex_178: \<open>(1 :: 16 word) >> 3 = 0\<close> by (smt (cvc5))
lemma bvex_179: \<open>(1 :: 16 word) >> Suc (Suc (Suc 0)) = 0\<close> by (smt (cvc5))

lemma bvex_180: \<open>signed_drop_bit 3 (1705 :: 16 word) = 213\<close> by (smt (cvc5))
lemma bvex_181: \<open>signed_drop_bit (Suc (Suc (Suc 0))) (1705 :: 16 word) = 213\<close> by (smt (cvc5))
lemma bvex_182: \<open>signed_drop_bit 3 (- 1705 :: 16 word) = - 214\<close> by (smt (cvc5))
lemma bvex_183: \<open>signed_drop_bit (Suc (Suc (Suc 0))) (- 1705 :: 16 word) = - 214\<close> by (smt (cvc5))
lemma bvex_184: \<open>signed_drop_bit 3 (1 :: 16 word) = 0\<close> by (smt (cvc5))
lemma bvex_185: \<open>signed_drop_bit (Suc (Suc (Suc 0))) (1 :: 16 word) = 0\<close> by (smt (cvc5))

lemma bvex_186: \<open>(1705 :: 16 word) >>> 3 = 213\<close> by (smt (cvc5))
lemma bvex_187: \<open>(1705 :: 16 word) >>> Suc (Suc (Suc 0)) = 213\<close> by (smt (cvc5))
lemma bvex_188: \<open>(- 1705 :: 16 word) >>> 3 = - 214\<close> by (smt (cvc5))
lemma bvex_189: \<open>(- 1705 :: 16 word) >>> Suc (Suc (Suc 0)) = - 214\<close> by (smt (cvc5))
lemma bvex_190: \<open>(1 :: 16 word) >>> 3 = 0\<close> by (smt (cvc5))
lemma bvex_191: \<open>(1 :: 16 word) >>> Suc (Suc (Suc 0)) = 0\<close> by (smt (cvc5))

lemma bvex_192: \<open>take_bit 3 (1705 :: 16 word) = 1\<close> by (smt (cvc5))
lemma bvex_193: \<open>take_bit (Suc (Suc (Suc 0))) (1705 :: 16 word) = 1\<close> by (smt (cvc5))(* by (simp flip: add_2_eq_Suc)*)
lemma bvex_194: \<open>take_bit 3 (- 1705 :: 16 word) = 7\<close> by (smt (cvc5))
lemma bvex_195: \<open>take_bit (Suc (Suc (Suc 0))) (- 1705 :: 16 word) = 7\<close> by (smt (cvc5)) (* by (simp flip: add_2_eq_Suc)*)
lemma bvex_196: \<open>take_bit 3 (1 :: 16 word) = 1\<close> by (smt (cvc5))
lemma bvex_197: \<open>take_bit (Suc (Suc (Suc 0))) (1 :: 16 word) = 1\<close> by (smt (cvc5))
lemma bvex_198: \<open>take_bit 3 (- 1 :: 16 word) = 7\<close> by (smt (cvc5)) (* by (simp add: mask_eq_exp_minus_1*)
lemma bvex_200: \<open>take_bit (Suc (Suc (Suc 0))) (- 1 :: 16 word) = 7\<close> by (smt (cvc5)) (* by (simp add: mask_eq_exp_minus_1)*)

lemma bvex_201: \<open>signed_take_bit 3 (1705 :: 16 word) = - 7\<close> by (smt (cvc5))
lemma bvex_202: \<open>signed_take_bit (Suc (Suc (Suc 0))) (1705 :: 16 word) = - 7\<close> by (smt (cvc5))
lemma bvex_203: \<open>signed_take_bit 3 (- 1705 :: 16 word) = 7\<close> by (smt (cvc5))
lemma bvex_204: \<open>signed_take_bit (Suc (Suc (Suc 0))) (- 1705 :: 16 word) = 7\<close> by (smt (cvc5))
lemma bvex_205: \<open>signed_take_bit 3 (1 :: 16 word) = 1\<close> by (smt (cvc5))
lemma bvex_206: \<open>signed_take_bit (Suc (Suc (Suc 0))) (1 :: 16 word) = 1\<close> by (smt (cvc5))

lemma bvex_207: \<open>(1705 :: 16 word) div 42 = 40\<close> by (smt (cvc5))
lemma bvex_208: \<open>(- 1705 :: 16 word) div 42 = 1519\<close> by (smt (cvc5))
lemma bvex_209: \<open>(1705 :: 16 word) div - 42 = 0\<close> by (smt (cvc5))
lemma bvex_210: \<open>(- 1705 :: 16 word) div - 42 = 0\<close> by (smt (cvc5))
lemma bvex_211: \<open>(1705 :: 16 word) div 1 = 1705\<close> by (smt (cvc5))
lemma bvex_212: \<open>(1705 :: 16 word) div - 1 = 0\<close> by (smt (cvc5))
lemma bvex_213: \<open>(1 :: 16 word) div 42 = 0\<close> by (smt (cvc5))
lemma bvex_214: \<open>(- 1 :: 16 word) div 42 = 1560\<close> by (smt (cvc5))

lemma bvex_215: \<open>(1705 :: 16 word) mod 42 = 25\<close> by (smt (cvc5))
lemma bvex_216: \<open>(- 1705 :: 16 word) mod 42 = 33\<close> by (smt (cvc5))
lemma bvex_217: \<open>(1705 :: 16 word) mod - 42 = 1705\<close> by (smt (cvc5))
lemma bvex_219: \<open>(- 1705 :: 16 word) mod - 42 = 63831\<close> by (smt (cvc5))
lemma bvex_220: \<open>(1705 :: 16 word) mod 1 = 0\<close> by (smt (cvc5))
lemma bvex_221: \<open>(1705 :: 16 word) mod - 1 = 1705\<close> by (smt (cvc5))
lemma bvex_222: \<open>(1 :: 16 word) mod 42 = 1\<close> by (smt (cvc5))
lemma bvex_223: \<open>(- 1 :: 16 word) mod 42 = 15\<close> by (smt (cvc5))

lemma bvex_224: \<open>(1705 :: 16 word) sdiv 42 = 40\<close> by (smt (cvc5))
lemma bvex_225: \<open>(- 1705 :: 16 word) sdiv 42 = 65496\<close> by (smt (cvc5))
lemma bvex_226: \<open>(1705 :: 16 word) sdiv - 42 = 65496\<close> by (smt (cvc5))
lemma bvex_227: \<open>(- 1705 :: 16 word) sdiv - 42 = 40\<close> by (smt (cvc5))
lemma bvex_228: \<open>(1705 :: 16 word) sdiv 1 = 1705\<close> by (smt (cvc5))
lemma bvex_229: \<open>(1705 :: 16 word) sdiv - 1 = 63831\<close> by (smt (cvc5))
lemma bvex_230: \<open>(1 :: 16 word) sdiv 42 = 0\<close> by (smt (cvc5))
lemma bvex_232: \<open>(- 1 :: 16 word) sdiv 42 = 0\<close> by (smt (cvc5))

lemma bvex_233: \<open>(1705 :: 16 word) smod 42 = 25\<close> by (smt (cvc5))
lemma bvex_234: \<open>(- 1705 :: 16 word) smod 42 = 65511\<close> by (smt (cvc5))
lemma bvex_235: \<open>(1705 :: 16 word) smod - 42 = 25\<close> by (smt (cvc5))
lemma bvex_236: \<open>(- 1705 :: 16 word) smod - 42 = 65511\<close> by (smt (cvc5))
lemma bvex_237: \<open>(1705 :: 16 word) smod 1 = 0\<close> by (smt (cvc5))
lemma bvex_238: \<open>(1705 :: 16 word) smod - 1 = 0\<close> by (smt (cvc5))
lemma bvex_239: \<open>(1 :: 16 word) smod 42 = 1\<close> by (smt (cvc5))
lemma bvex_240: \<open>(- 1 :: 16 word) smod 42 = 65535\<close> by (smt (cvc5))


section "modulus"

text \<open>
Benchmark Nrs: 241-243
Date counted: 12/08/26

Total:    3
Success:  2
\<close>

lemma bvex_241: "(27 :: 4 word) = -5" by (smt (cvc5))
lemma bvex_242: "(27 :: 4 word) = 11" by (smt (cvc5))
lemma bvex_243: "27 \<noteq> (11 :: 6 word)" by (smt (cvc5))

section "signed"

text \<open>
Benchmark Nrs: 244
Date counted: 12/08/26

Total:    1
Success:  0
\<close>

lemma bvex_244: "(127 :: 6 word) = -1" by (smt (cvc5))

section "number ring simps"

text \<open>
Benchmark Nrs: 245-253
Date counted: 12/08/26

Total:    9
Success:  4
\<close>

lemma bvex_245:
  "27 + 11 = (38::32 word)"
  "27 + 11 = (6::5 word)"
  "7 * 3 = (21::32 word)"
  "11 - 27 = (-16::32 word)"
  "- (- 11) = (11::32 word)"
  "-40 + 1 = (-39::32 word)"
   by (smt (cvc5))

lemma bvex_246: "word_pred 2 = 1" by (smt (cvc5))
lemma bvex_247: "word_succ (- 3) = -2" by (smt (cvc5))
lemma bvex_248: "23 < (27::8 word)" by (smt (cvc5))
lemma bvex_249: "23 \<le> (27::8 word)" by (smt (cvc5))
lemma bvex_250: "\<not> 23 < (27::2 word)" by (smt (cvc5))
lemma bvex_251: "0 < (4::3 word)" by (smt (cvc5))
lemma bvex_252: "1 < (4::3 word)" by (smt (cvc5))
lemma bvex_253: "0 < (1::3 word)" by (smt (cvc5))

section "ring operations"

text \<open>
Benchmark Nrs: 254
Date counted: 12/08/26

Total:    1
Success:  0
\<close>

lemma bvex_254: "a + 2 * b + c - b = (b + c) + (a :: 32 word)" oops (*by (smt (cvc5))*)

section "casting"

text \<open>
Benchmark Nrs: 254-264
Date counted: 12/08/26

Total:    11
Success:  0
\<close>

lemma bvex_254: "uint (234567 :: 10 word) = 71" by (smt (cvc5))
lemma bvex_255: "uint (-234567 :: 10 word) = 953" by (smt (cvc5))
lemma bvex_256: "sint (234567 :: 10 word) = 71" by (smt (cvc5))
lemma bvex_257: "sint (-234567 :: 10 word) = -71" by (smt (cvc5))
lemma bvex_258: "uint (1 :: 10 word) = 1" by (smt (cvc5))

lemma bvex_259: "unat (-234567 :: 10 word) = 953" by (smt (cvc5))
lemma bvex_260: "unat (1 :: 10 word) = 1" by (smt (cvc5))

lemma bvex_261: "ucast (0b1010 :: 4 word) = (0b10 :: 2 word)" by (smt (cvc5))
lemma bvex_262: "ucast (0b1010 :: 4 word) = (0b1010 :: 10 word)" by (smt (cvc5))
lemma bvex_263: "scast (0b1010 :: 4 word) = (0b111010 :: 6 word)" by (smt (cvc5))
lemma bvex_264: "ucast (1 :: 4 word) = (1 :: 2 word)" by (smt (cvc5))

section "reducing goals to nat or int and arith:"

text \<open>
Benchmark Nrs: 265
Date counted: 12/08/26

Total:    1
Success:  0
\<close>

lemma bvex_265: "i < x \<Longrightarrow> i < i + 1" for i x :: "32 word" oops (*by (smt (cvc5))*) (* by unat_arith*)

section "bit operations"

text \<open>
Benchmark Nrs: 266-320
Date counted: 12/08/26

Total:    55
Success:  24
\<close>

lemma bvex_266: "0b110 AND 0b101 = (0b100 :: 32 word)" by (smt (cvc5))
lemma bvex_267: "0b110 OR 0b011 = (0b111 :: 8 word)" by (smt (cvc5))
lemma bvex_268: "0xF0 XOR 0xFF = (0x0F :: 8 word)" by (smt (cvc5))
lemma bvex_269: "NOT (0xF0 :: 16 word) = 0xFF0F" by (smt (cvc5))
lemma bvex_270: "0 AND 5 = (0 :: 8 word)" by (smt (cvc5))
lemma bvex_271: "1 AND 1 = (1 :: 8 word)" by (smt (cvc5))
lemma bvex_272: "1 AND 0 = (0 :: 8 word)" by (smt (cvc5))
lemma bvex_273: "1 AND 5 = (1 :: 8 word)" by (smt (cvc5))
lemma bvex_274: "1 OR 6 = (7 :: 8 word)" by (smt (cvc5))
lemma bvex_275: "1 OR 1 = (1 :: 8 word)" by (smt (cvc5))
lemma bvex_276: "1 XOR 7 = (6 :: 8 word)" by (smt (cvc5))
lemma bvex_277: "1 XOR 1 = (0 :: 8 word)" by (smt (cvc5))
lemma bvex_278: "NOT 1 = (254 :: 8 word)" by (smt (cvc5))
lemma bvex_279: "NOT 0 = (255 :: 8 word)" by (smt (cvc5))
lemma bvex_280: "(-1 :: 32 word) = 0xFFFFFFFF" by (smt (cvc5))

lemma bvex_281: "bit (0b0010 :: 4 word) 1" by (smt (cvc5))
lemma bvex_282: "\<not> bit (0b0010 :: 4 word) 0" by (smt (cvc5))
lemma bvex_283: "\<not> bit (0b1000 :: 3 word) 4" by (smt (cvc5))
lemma bvex_284: "\<not> bit (1 :: 3 word) 2" by (smt (cvc5))

lemma bvex_285: "bit (0b11000 :: 10 word) n = (n = 4 \<or> n = 3)" by (smt (cvc5))
 (* by (auto simp add: bit_numeral_rec bit_1_iff split: nat.splits)*)

lemma bvex_286: "set_bit 55 7 True = (183::32 word)" by (smt (cvc5))
lemma bvex_287: "set_bit 0b0010 7 True = (0b10000010::32 word)" by (smt (cvc5))
lemma bvex_288: "set_bit 0b0010 1 False = (0::32 word)" by (smt (cvc5))
lemma bvex_289: "set_bit 1 3 True = (0b1001::32 word)" by (smt (cvc5))
lemma bvex_290: "set_bit 1 0 False = (0::32 word)" by (smt (cvc5))
lemma bvex_291: "set_bit 0 3 True = (0b1000::32 word)" by (smt (cvc5))
lemma bvex_292: "set_bit 0 3 False = (0::32 word)" by (smt (cvc5))

lemma bvex_292: "odd (0b0101::32 word)" by (smt (cvc5))
lemma bvex_293: "even (0b1000::32 word)" by (smt (cvc5))
lemma bvex_294: "odd (1::32 word)" by (smt (cvc5))
lemma bvex_295: "even (0::32 word)" by (smt (cvc5))

lemma bvex_296: "\<not> msb (0b0101::4 word)" by (smt (cvc5))
lemma bvex_297: "msb (0b1000::4 word)" by (smt (cvc5))
lemma bvex_298: "\<not> msb (1::4 word)" by (smt (cvc5))
lemma bvex_299: "\<not> msb (0::4 word)" by (smt (cvc5))

lemma bvex_300: "word_cat (27::4 word) (27::8 word) = (2843::32 word)"
  by (smt (cvc5))
lemma bvex_301: "word_cat (0b0011::4 word) (0b1111::6word) = (0b0011001111 :: 10 word)"
  by (smt (cvc5))

lemma bvex_302: "0b1011 << 2 = (0b101100::32 word)" by (smt (cvc5))
lemma bvex_303: "0b1011 >> 2 = (0b10::8 word)" by (smt (cvc5))
lemma bvex_304: "0b1011 >>> 2 = (0b10::8 word)" by (smt (cvc5))
lemma bvex_305: "1 << 2 = (0b100::32 word)"  by (smt (cvc5)) (*apply simp? oops*)

lemma bvex_306: "slice 3 (0b101111::6 word) = (0b101::3 word)" by (smt (cvc5))
lemma bvex_307: "slice 3 (1::6 word) = (0::3 word)"  by (smt (cvc5)) (*apply simp? oops*)

lemma bvex_308: "word_rotr 2 0b0110 = (0b1001::4 word)" by (smt (cvc5))
lemma bvex_309: "word_rotl 1 0b1110 = (0b1101::4 word)" by (smt (cvc5))
lemma bvex_310: "word_roti 2 0b1110 = (0b1011::4 word)" by (smt (cvc5))
lemma bvex_311: "word_roti (- 2) 0b0110 = (0b1001::4 word)" by (smt (cvc5))
lemma bvex_312: "word_rotr 2 0 = (0::4 word)" by (smt (cvc5))
lemma bvex_313: "word_rotr 2 1 = (0b0100::4 word)" by (smt (cvc5)) (*apply simp? oops*)
lemma bvex_314: "word_rotl 2 1 = (0b0100::4 word)" by (smt (cvc5)) (*apply simp? oops*)
lemma bvex_315: "word_roti (- 2) 1 = (0b0100::4 word)" by (smt (cvc5)) (*apply simp? oops*)

lemma bvex_316: "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)"
  by (smt (cvc5)) (*
proof -
  have "(x AND 0xff00) OR (x AND 0x00ff) = x AND (0xff00 OR 0x00ff)"
    by (simp only: word_ao_dist2)
  also have "0xff00 OR 0x00ff = (-1::16 word)"
    by (smt (cvc5))
  also have "x AND -1 = x"
    by (smt (cvc5))
  finally show ?thesis .
qed*)

lemma bvex_317: "word_next (2:: 8 word) = 3" by (smt (cvc5)) (* by eval*)
lemma bvex_318: "word_next (255:: 8 word) = 255" by (smt (cvc5))
lemma bvex_319: "word_prev (2:: 8 word) = 1" by (smt (cvc5))
lemma bvex_320: "word_prev (0:: 8 word) = 0" by (smt (cvc5))

section \<open>signed division\<close>

text \<open>
Benchmark Nrs: 321-322
Date counted: 12/08/26

Total:    2
Success:  0
\<close>

lemma bvex_321:
  "( 4 :: 32 word) sdiv  4 =  1"
  "(-4 :: 32 word) sdiv  4 = -1"
  "(-3 :: 32 word) sdiv  4 =  0"
  "( 3 :: 32 word) sdiv -4 =  0"
  "(-3 :: 32 word) sdiv -4 =  0"
  "(-5 :: 32 word) sdiv -4 =  1"
  "( 5 :: 32 word) sdiv -4 = -1"
   by (smt (cvc5)) (*by (simp_all add: sdiv_word_def signed_divide_int_def)*)

lemma bvex_322:
  "( 4 :: 32 word) smod  4 =   0"
  "( 3 :: 32 word) smod  4 =   3"
  "(-3 :: 32 word) smod  4 =  -3"
  "( 3 :: 32 word) smod -4 =   3"
  "(-3 :: 32 word) smod -4 =  -3"
  "(-5 :: 32 word) smod -4 =  -1"
  "( 5 :: 32 word) smod -4 =   1"
   by (smt (cvc5)) (*by (simp_all add: smod_word_def signed_modulo_int_def signed_divide_int_def)*)


section \<open>comparison\<close>

text \<open>
Benchmark Nrs: 323
Date counted: 12/08/26

Total:    1
Success:  1
\<close>

lemma bvex_323: "1 < (1024::32 word) \<and> 1 \<le> (1024::32 word)" by (smt (cvc5))

section "bool lists"

text \<open>
Benchmark Nrs: 324-326
Date counted: 12/08/26

Total:    3
Success:  0
\<close>
lemma bvex_324: "of_bl [True, False, True, True] = (0b1011::32 word)" by (smt (cvc5))

lemma bvex_325: "to_bl (0b110::4 word) = [False, True, True, False]" by (smt (cvc5))

lemma bvex_326: "of_bl (replicate 32 True) = (0xFFFFFFFF::32 word)" by (smt (cvc5))
 (* by (simp add: numeral_eq_Suc)*)

section "proofs using bitwise expansion"

text \<open>
Benchmark Nrs: 327-331
Date counted: 12/08/26

Total:    5
Success:  0
\<close>
lemma bvex_327: "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)" by (smt (cvc5)) (*by word_bitwise*)

lemma bvex_328: "(x AND NOT 3) >> 4 << 2 = ((x >> 2) AND NOT 3)"
  for x :: "10 word"
  by (smt (cvc5)) (*by word_bitwise*)

lemma bvex_329: "((x AND -8) >> 3) AND 7 = (x AND 56) >> 3"
  for x :: "12 word"
  by (smt (cvc5)) (*by word_bitwise*)

lemma bvex_330: "x \<le> 42 \<Longrightarrow> x \<le> 89"
  for x :: "8 word" (*by (smt (cvc5)) *) oops
  (*apply word_bitwise
  apply blast
  done*)

lemma bvex_331: "(x AND 1023) = 0 \<Longrightarrow> x \<le> -1024"
  for x :: \<open>32 word\<close> (*by (smt (cvc5)) *) oops
 (* apply word_bitwise
  apply clarsimp
  done*)

section "operations like shifts by non-numerals will expose some internal list
 representations but may still be easy to solve"

text \<open>
Benchmark Nrs: 332-333
Date counted: 12/08/26

Total:    2
Success:  0
\<close>

lemma bvex_332: "32 \<le> a \<Longrightarrow> b >> a = 0"
  for b :: \<open>32 word\<close>
  by (smt (cvc5))
  (*apply word_bitwise
  apply simp
  done*)

(* testing for presence of word_bitwise *)
lemma bvex_333: "((x :: 32 word) >> 3) AND 7 = (x AND 56) >> 3"
  (*by word_bitwise*)
  by (smt (cvc5))

end


section \<open>Combined integer-bitvector properties\<close>

text \<open>
Benchmark Nrs: 334-335
Date counted: 12/08/26

Total:    2
Success:  0
\<close>

lemma bvex_334:
  assumes "bv2int 0 = 0"
      and "bv2int 1 = 1"
      and "bv2int 2 = 2"
      and "bv2int 3 = 3"
      and "\<forall>x::2 word. bv2int x > 0"
  shows "\<forall>i::int. i < 0 \<longrightarrow> (\<forall>x::2 word. bv2int x > i)"
  using assms (*by (smt (cvc5))*) oops

lemma bvex_335: "P (0 \<le> (a :: 4 word)) = P True" by (smt (cvc5))

section \<open>Misc and Unsorted\<close>

(*TODO: support ABSORB rule*)
lemma bvex_336: "a > (4294967294::32 word) \<Longrightarrow> a = 4294967295"
  (*by (smt (cvc5))*) oops



end
