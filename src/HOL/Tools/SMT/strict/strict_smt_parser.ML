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

val strict = true

datatype sort =
{
  sort_id : string,
  transformation : SMTLIB.tree list * typ list => typ
} 

fun translate_sort (SMTLIB.S (SMTLIB.Sym "_" :: SMTLIB.Sym sort_id :: xs), ts) {sort_id=id,transformation=f} =
f xs ts
translate_sort (SMTLIB.S (SMTLIB.Sym sort_id :: xs), ts) = 


fun temp f xs = SOME (f xs)
handle MATCH => NONE

val smtlib_types : sort list =
[
 {sort_id = "Bool", (fn ([],[]) => @{typ "HOL.true"}}) }
]

datatype attribute =  RIGHT_ASSOC | LEFT_ASSOC | PAIRWISE | CHAINABLE
datatype sort = SORT of typ list | PAR_SORT of int list * (typ list => typ list)

type smt_op =
{
  name : string,
  par_sort : sort,
  annotation : attribute option
  transform : term list => term
  restrictions : (term list => term list) option
}

(*TODO: constructor that takes SMT-LIB sort list*)


fun check_sorts_args (SORT sorts) ts =
  (length sorts = length ts + 1) andalso (fn (s,t) => (s = fastype_of t)) |
  check_sorts_args (PAR_SORT (is,f)) = true (*Get is out of children*)


fun transform_term (SMTLIB.Sym operator, ts) { name = n, par_sort = f, annotation = attr, transform = g} =
  let
    val sorts_ok = check_sorts ts par_sort (*Check if enough children and children have right type*)
    val transformed_term = g ts (*Add handling for annotation here*)
    val output_sort_ok (*Check if transformed term has the right output type*)
  



  
val smtlib_bool = SMTLIB.Sym "Bool"

fun sort_without_par sort_list =
  (fn [] => sort_list |
   fn _ => raise STRICT_SMT_PARSING "This operator does not accept sort parameters")



(* Core *)

val core_funs = [
(* (true Bool) *)
{ name = "true", sort = SORT [smtlib_bool], annotation = NONE, transform = mk_unary \<^Const>\<open>True\<close> }
(* (false Bool) *)
{ name = "false", sort = ([], fn _ => [smtlib_bool]), annotation = NONE, transform = mk_unary \<^Const>\<open>False\<close> }
(* (not Bool Bool) *)
{ name = "not", sort = ([], fn _ => [smtlib_bool,smtlib_bool]), annotation = NONE, transform = mk_unary \<^Const>\<open>False\<close> }
(* (=> Bool Bool Bool :right-assoc) *)
{ name = "=>", sort = ([], fn _ => [smtlib_bool,smtlib_bool,smtlib_bool]), annotation = RIGHT_ASSOC, transform = temp }
(* (and Bool Bool Bool :left-assoc) *)
{ name = "and", sort = ([], fn _ => [smtlib_bool,smtlib_bool,smtlib_bool]), annotation = LEFT_ASSOC, transform = temp }
(* (or Bool Bool Bool :left-assoc) *)
{ name = "or", sort = ([], fn _ => [smtlib_bool,smtlib_bool,smtlib_bool]), annotation = LEFT_ASSOC, transform = temp }
(* (xor Bool Bool Bool :left-assoc) *)
{ name = "xor", sort = ([], fn _ => [smtlib_bool,smtlib_bool,smtlib_bool]), annotation = LEFT_ASSOC, transform = temp }
(* (par (A) (= A A Bool :chainable)) *)
{ name = "=", sort = ([0], fn [A] => [A,A,smtlib_bool]), annotation = CHAINABLE, transform = temp }
(* (par (A) (distinct A A Bool :pairwise)) *)
{ name = "distinct", sort = ([0],fn [A] => [A,A,smtlib_bool]), annotation = PAIRWISE, transform = temp }
(* (par (A) (ite Bool A A A) *)
{ name = "ite", sort = ([0],fn [A] => [smtlib_bool,A,A,A]), annotation = NONE, transform = temp }
]

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