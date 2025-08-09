(*  Title:      HOL/SMT_Examples/SMT_Word_Examples.thy
    Author:     Sascha Boehme, TU Muenchen
    Author:     Hanna Lachnitt, Stanford University

*)

section \<open>Word examples for for SMT binding\<close>

theory SMT_Word_Examples_CVC
imports "HOL-Library.Word" "HOL.SMT_CVC_Word"
begin

declare [[smt_nat_as_int,smt_trace]]


section \<open>Bitvector numbers\<close>

lemma "(27 :: 4 word) = -5" by (smt (cvc5))
lemma "(27 :: 4 word) = 11" by (smt (cvc5))
lemma "23 < (27::8 word)" by (smt (cvc5))
lemma "27 + 11 = (6::5 word)" by (smt (cvc5))
lemma "7 * 3 = (21::8 word)" by (smt (cvc5))
lemma "11 - 27 = (-16::8 word)" by (smt (cvc5))
lemma "- (- 11) = (11::5 word)" by (smt (cvc5))
lemma "-40 + 1 = (-39::7 word)" by (smt (cvc5))
lemma "a + 2 * b + c - b = (b + c) + (a :: 32 word)" supply [[smt_trace]] by (smt (cvc5))
lemma "x = (5 :: 4 word) \<Longrightarrow> 4 * x = 4" by (smt (cvc5))

lemma "(27::4 word) = 11"
  supply[[simp_trace]]
  apply simp

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

declare[[show_hyps]]

ML\<open>
val cterm_x = @{cterm "LENGTH(64)"}

val conv_x = Simplifier.rewrite @{context}
val y = conv_x cterm_x
val typ3 = @{typ "('a::len0)"} |> Term.dest_TFree

\<close>

section \<open>power\<close>

lemma "(2::4 word) ^ 3 = 8"
  by (smt (cvc5))

lemma bnd_0: "3000 < (2^12::32 word)"
  apply (smt (cvc5))
  done

lemma bnd_0_variable: "3000 < (2^x::32 word)"
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

lemma "0b110 AND 0b101 = (0b100 :: 32 word)" by (smt (cvc5))
lemma "0b110 OR 0b011 = (0b111 :: 8 word)" by (smt (cvc5))
lemma "0xF0 XOR 0xFF = (0x0F :: 8 word)" by (smt (cvc5))
lemma "NOT (0xF0 :: 16 word) = 0xFF0F" by (smt (cvc5))
lemma "word_cat (27::4 word) (27::8 word) = (2843::12 word)" by (smt (cvc5))
lemma "word_cat (0b0011::4 word) (0b1111::6word) = (0b0011001111 :: 10 word)" by (smt (cvc5))
lemma "slice 1 (0b10110 :: 4 word) = (0b11 :: 2 word)" by (smt (cvc5))
lemma "ucast (0b1010 :: 4 word) = (0b1010 :: 10 word)" by (smt (cvc5))
lemma "scast (0b1010 :: 4 word) = (0b111010 :: 6 word)" by (smt (cvc5))
lemma "push_bit 2 0b10011 = (0b1001100::8 word)" by (smt (cvc5))
lemma "drop_bit 2 0b11001 = (0b110::8 word)" by (smt (cvc5))
lemma "signed_drop_bit 2 0b10011 = (0b100::8 word)" by (smt (cvc5))
lemma "word_rotr 2 0b0110 = (0b1001::4 word)" by (smt (cvc5))
lemma "word_rotl 1 0b1110 = (0b1101::4 word)" by (smt (cvc5))
lemma "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)" by (smt (cvc5))
lemma "w < 256 \<Longrightarrow> (w :: 16 word) AND 0x00FF = w" by (smt (cvc5))

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

end
