(*  Title:      HOL/Library/Tools/word_lib.ML
    Author:     Sascha Boehme, TU Muenchen and Thomas Sewell, NICTA

Helper routines for operating on the word type.
*)

signature WORD_LIB =
sig
  val dest_binT: typ -> int
  val is_wordT: typ -> bool
  val dest_wordT: typ -> int
  val mk_wordT: int -> typ
  val mk_word_const: int -> int -> term
  val is_overflow_bv_const: term -> bool
  val is_concrete_bw: typ -> bool
  val has_concrete_bw: term -> bool
end

structure Word_Lib: WORD_LIB =
struct

fun dest_binT T =
  (case T of
    Type (\<^type_name>\<open>Numeral_Type.num0\<close>, _) => 0
  | Type (\<^type_name>\<open>Numeral_Type.num1\<close>, _) => 1
  | Type (\<^type_name>\<open>Numeral_Type.bit0\<close>, [T]) => 2 * dest_binT T
  | Type (\<^type_name>\<open>Numeral_Type.bit1\<close>, [T]) => 1 + 2 * dest_binT T
  | _ => raise TYPE ("dest_binT", [T], []))

fun is_wordT (Type (\<^type_name>\<open>word\<close>, _)) = true
  | is_wordT _ = false

fun dest_wordT (Type (\<^type_name>\<open>word\<close>, [T])) = dest_binT T
  | dest_wordT T = raise TYPE ("dest_wordT", [T], [])


fun mk_bitT i T =
  if i = 0
  then Type (\<^type_name>\<open>Numeral_Type.bit0\<close>, [T])
  else Type (\<^type_name>\<open>Numeral_Type.bit1\<close>, [T])

fun mk_binT size =
  if size = 0 then \<^typ>\<open>Numeral_Type.num0\<close>
  else if size = 1 then \<^typ>\<open>Numeral_Type.num1\<close>
  else let val (q, r) = Integer.div_mod size 2 in mk_bitT r (mk_binT q) end

fun mk_wordT size =
  if size >= 0 then Type (\<^type_name>\<open>word\<close>, [mk_binT size])
  else raise TYPE ("mk_wordT: " ^ string_of_int size, [], [])

fun mk_word_const value size = HOLogic.mk_number (mk_wordT size) value

(*Find out if a bit-vector constant is larger than it's bit-width allows. Purely syntactical.*)
fun count_consts (Const _ $ t) = 1 + count_consts t |
    count_consts _ = 1

fun is_overflow_bv_const (Const ("Num.numeral_class.numeral", Type("fun",[_,T])) $ t1) =
      (case try dest_wordT T of
         NONE => false
       | SOME bitwidth => bitwidth < count_consts t1)
  | is_overflow_bv_const _ = false

val is_concrete_bw = can dest_wordT
val has_concrete_bw = can (is_concrete_bw o fastype_of)
end
