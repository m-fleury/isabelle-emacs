(*  Title:      HOL/SMT_Examples/SMT_Word_Examples.thy
    Author:     Sascha Boehme, TU Muenchen
*)

section \<open>Word examples for for SMT binding\<close>

theory SMT_Word_Examples
imports "HOL-Library.Word"
begin

(* declare [[smt_oracle = true]]
declare [[z3_extensions = true]]
declare [[smt_certificates = "SMT_Word_Examples.certs"]]
declare [[smt_read_only_certificates = true]] *)
declare [[smt_trace,z3_extensions]]
text \<open>
Currently, there is no proof reconstruction for words.
All lemmas are proved using the oracle mechanism.
\<close>
type_synonym w32 = "32 word"

declare [[show_types=true]]
declare [[cvc4_options = "--proof-format-mode=verit-extended --simplification=none --dag-thres=0 --lang=smt2 --full-saturate-quant"]]
declare [[smt_nat_as_int=true]]

definition bound :: nat where
  [simplified, simp]: "bound = unat (2^11 :: w32)"

definition bseg :: "w32 \<Rightarrow> w32 \<Rightarrow> bool" where
  [simp]: "bseg x s \<longleftrightarrow> unat x < bound \<and> unat x + unat s \<le> bound"


lemma b2:
  assumes
  "bseg x s"
   "i < unat s"
 shows "unat x + i < bound"
  supply [[smt_trace]]
using assms unfolding bound_def bseg_def
  apply (smt (cvc4) )
  using assms by auto


section \<open>Bitvector numbers\<close>

lemma "(27 :: 4 word) = -5" by smt
lemma "(27 :: 4 word) = 11" by smt
lemma "23 < (27::8 word)" by smt
lemma "27 + 11 = (6::5 word)" by smt
lemma "7 * 3 = (21::8 word)" by smt
lemma "11 - 27 = (-16::8 word)" by smt
lemma "- (- 11) = (11::5 word)" by smt
lemma "-40 + 1 = (-39::7 word)" by smt
lemma "a + 2 * b + c - b = (b + c) + (a :: 32 word)" by smt
lemma "x = (5 :: 4 word) \<Longrightarrow> 4 * x = 4" by smt


section \<open>Bit-level logic\<close>

context
  includes bit_operations_syntax
begin

lemma "0b110 AND 0b101 = (0b100 :: 32 word)" by smt
lemma "0b110 OR 0b011 = (0b111 :: 8 word)" by smt
lemma "0xF0 XOR 0xFF = (0x0F :: 8 word)" by smt
lemma "NOT (0xF0 :: 16 word) = 0xFF0F" by smt
lemma "word_cat (27::4 word) (27::8 word) = (2843::12 word)" by smt
lemma "word_cat (0b0011::4 word) (0b1111::6word) = (0b0011001111 :: 10 word)" by smt
lemma "slice 1 (0b10110 :: 4 word) = (0b11 :: 2 word)" by smt
lemma "ucast (0b1010 :: 4 word) = (0b1010 :: 10 word)" by smt
lemma "scast (0b1010 :: 4 word) = (0b111010 :: 6 word)" by smt
lemma "push_bit 2 0b10011 = (0b1001100::8 word)" by smt
lemma "drop_bit 2 0b11001 = (0b110::8 word)" by smt
lemma "signed_drop_bit 2 0b10011 = (0b100::8 word)" by smt
lemma "word_rotr 2 0b0110 = (0b1001::4 word)" by smt
lemma "word_rotl 1 0b1110 = (0b1101::4 word)" by smt
lemma "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)" by smt
lemma "w < 256 \<Longrightarrow> (w :: 16 word) AND 0x00FF = w" by smt

end


section \<open>Combined integer-bitvector properties\<close>

lemma
  assumes "bv2int 0 = 0"
      and "bv2int 1 = 1"
      and "bv2int 2 = 2"
      and "bv2int 3 = 3"
      and "\<forall>x::2 word. bv2int x > 0"
  shows "\<forall>i::int. i < 0 \<longrightarrow> (\<forall>x::2 word. bv2int x > i)"
  using assms by smt

lemma "P (0 \<le> (a :: 4 word)) = P True" by smt

end
