(*  Title:      HOL/Tools/SMT/strict_smt_parser.ML
    Author:     Hanna Lachnitt, Stanford University

Stricter term parsing for SMT-LIB terms
*)

signature STRICT_SMT_PARSER =
sig

end

structure Strict_SMT_Parser : STRICT_SMT_PARSER =
struct

exception STRICT_SMT_PARSING of string



open Word_Lib
open SMT_Parser_Util

fun has_wordT w = is_wordT (fastype_of w)
fun same_bw Tw1 Tw2 = (dest_wordT Tw1 = dest_wordT Tw2)

fun both_word_and_same_bw w1 w2 =
  let
    val Tw1 = (fastype_of w1)
    val Tw2 = (fastype_of w2)
  in
    is_wordT Tw1 andalso is_wordT Tw2 andalso same_bw Tw1 Tw2
  end

fun all_word_and_same_bw [] _ = true |
    all_word_and_same_bw (w::ws) T = has_wordT w andalso same_bw (fastype_of w) T andalso all_word_and_same_bw ws T

fun strict_unary n t1 = if has_wordT t1 then SOME (mk_unary n t1) else NONE
fun strict_lassoc n t1 ts = if all_word_and_same_bw (t1::ts) (fastype_of t1) then SOME (mk_lassoc' n t1 ts) else NONE



fun 
(*From the FixedSizeBitVectors theory*)
    strict_bv_term_parser (SMTLIB.BVNum (i, base), []) = SOME (HOLogic.mk_number (mk_wordT(base)) i) (*TODO*)
  | strict_bv_term_parser (SMTLIB.Sym "bvnot", [t1]) =
      strict_unary \<^const_name>\<open>ring_bit_operations_class.not\<close> t1
  | strict_bv_term_parser (SMTLIB.Sym "bvand", (t1::(ts as _::_))) =
      strict_lassoc \<^const_name>\<open>semiring_bit_operations_class.and\<close> t1 ts
  | strict_bv_term_parser (SMTLIB.Sym "bvor", (t1::(ts as _::_))) =
      strict_lassoc \<^const_name>\<open>semiring_bit_operations_class.or\<close> t1 ts
  | strict_bv_term_parser (SMTLIB.Sym "bvneg", [t1]) =
      strict_unary \<^const_name>\<open>uminus_class.uminus\<close> t1
  | strict_bv_term_parser (SMTLIB.Sym "bvadd", (t1::(ts as _::_))) = (*TODO*)
      strict_lassoc \<^const_name>\<open>Groups.plus\<close> t1 ts
  | strict_bv_term_parser (SMTLIB.Sym "bvmul", (t1::(ts as _::_))) = (*TODO*)
      strict_lassoc \<^const_name>\<open>Groups.times\<close> t1 ts








end