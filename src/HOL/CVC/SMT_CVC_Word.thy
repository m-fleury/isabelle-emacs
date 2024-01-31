theory SMT_CVC_Word \<comment> \<open>More Setup for CVC that should be in HOL-Word eventually\<close>
  imports SMT_Word "SMT_CVC" "BV_Rewrites"
begin


lemma cvc_ListOp_neutral_bv_and [cvc_ListOp_neutral]:
 "cvc_isListOp (ListOp (semiring_bit_operations_class.and) (-1::'a::len word))"
  by auto


ML_file \<open>ML/SMT_string.ML\<close>
ML_file \<open>ML/SMT_set.ML\<close>
ML_file \<open>ML/SMT_array.ML\<close>

ML \<open>

fun mk_binary' n T U t1 t2 = Const (n, [T, T] ---> U) $ t1 $ t2

fun mk_binary n t1 t2 =
  let val T = fastype_of t1
  in mk_binary' n T T t1 t2 end

fun mk_rassoc f ts =
  let val us = rev ts
  in fold f (tl us) (hd us) end

fun mk_rassoc' n = mk_rassoc (mk_binary n)

fun pairwise _ [] = []
  | pairwise f (t1::tss)
           = (map (fn u => f (t1,u)) tss) @ pairwise f tss

(*cvc5 specific terms that are not present in veriT's output*)
fun cvc_term_parser (SMTLIB.Sym "xor",[t1,t2]) = SOME(Const(\<^const_name>\<open>SMT_CVC_Util.xor\<close>, \<^typ>\<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close>)
       $ t1 $ t2)
  | cvc_term_parser (SMTLIB.Sym "cvc5_nary_op", []) =
   (*If there are no elements in the list we cannot know the type at this point*)
    SOME(Const( \<^const_name>\<open>ListVar\<close> ,dummyT --> dummyT)
       $ Const( \<^const_name>\<open>List.Nil\<close>, dummyT))
  | cvc_term_parser (SMTLIB.Sym "cvc5_nary_op", ts) = 
    let
      (*Figure out if types are different, this should only be the case if they have different
        bitwidths*)
      fun remove_duplicates [] = []
        | remove_duplicates (x::xs) = x::remove_duplicates(List.filter (fn y => y <> x) xs)

      val types_eq = map fastype_of ts |> remove_duplicates |> length 
      val new_ts =
         if types_eq > 0
         then ts
         else (map (fn t => Const( \<^const_name>\<open>unsigned\<close>, \<^typ>\<open>'a::len word \<Rightarrow> Nat.nat \<close>) $ t) ts)
      val new_type = if types_eq > 0 then fastype_of (hd ts) else \<^typ>\<open>Nat.nat\<close>

    in
    SOME(Const( \<^const_name>\<open>ListVar\<close>, Type(\<^type_name>\<open>List.list\<close>,[new_type])  --> Type(\<^type_name>\<open>cvc_ListVar\<close>,[new_type]))
      $ (HOLogic.mk_list new_type new_ts))
    end
  | cvc_term_parser (SMTLIB.Sym "emptyString", []) = SOME (Free ("''''", \<^typ>\<open>String.string\<close>))
  | cvc_term_parser (SMTLIB.Sym "distinct", ts)
     = SOME (mk_rassoc' \<^const_name>\<open>HOL.conj\<close> (pairwise (HOLogic.mk_eq #> HOLogic.mk_not) ts))
  | cvc_term_parser xs = (case SMT_String.string_term_parser xs of
    SOME x => SOME x |
    NONE =>
      case SMT_Set.set_term_parser xs of
        SOME y => SOME y |
        NONE => SMT_Array.array_term_parser xs)

 fun cvc_type_parser (SMTLIB.Sym "?", _) = SOME dummyT |
     cvc_type_parser (SMTLIB.Sym "?BitVec", []) = SOME (Type (\<^type_name>\<open>word\<close>, [dummyT])) |
  cvc_type_parser xs =
  (case SMT_String.string_type_parser xs of
    SOME x => SOME x |
    NONE => 
      case SMT_Set.set_type_parser xs of
        SOME y => SOME y |
        NONE => SMT_Array.array_type_parser xs)
\<close>

ML \<open>
val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_term_parser cvc_term_parser)
)
val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser cvc_type_parser))
\<close>


cvc5_rare "BV_Rewrites.rewrite_bv_extract_whole"
cvc5_rare "BV_Rewrites.rewrite_bv_ugt_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_uge_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_sgt_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_sge_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_slt_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_sle_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_redor_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_redand_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_sub_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_ule_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_comp_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_repeat_eliminate_1"
cvc5_rare "BV_Rewrites.rewrite_bv_repeat_eliminate_2"
cvc5_rare "BV_Rewrites.rewrite_bv_rotate_left_eliminate_1"
cvc5_rare "BV_Rewrites.rewrite_bv_rotate_left_eliminate_2"
cvc5_rare "BV_Rewrites.rewrite_bv_rotate_right_eliminate_2"
cvc5_rare "BV_Rewrites.rewrite_bv_nand_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_nor_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_xnor_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_sign_extend_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_sdivo_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_srem_eliminate_fewer_bitwise_ops"
cvc5_rare "BV_Rewrites.rewrite_bv_usubo_eliminate"
cvc5_rare "BV_Rewrites.rewrite_bv_ite_equal_children"
cvc5_rare "BV_Rewrites.rewrite_bv_ite_const_children_1"
cvc5_rare "BV_Rewrites.rewrite_bv_ite_const_children_2"
cvc5_rare "BV_Rewrites.rewrite_bv_ite_equal_cond_1"
cvc5_rare "BV_Rewrites.rewrite_bv_ite_equal_cond_2"
cvc5_rare "BV_Rewrites.rewrite_bv_ite_equal_cond_3"
cvc5_rare "BV_Rewrites.rewrite_bv_ite_merge_then_if"
cvc5_rare "BV_Rewrites.rewrite_bv_ite_merge_else_if"
cvc5_rare "BV_Rewrites.rewrite_bv_ite_merge_then_else"
cvc5_rare "BV_Rewrites.rewrite_bv_ite_merge_else_else"
cvc5_rare "BV_Rewrites.rewrite_bv_shl_by_const_0"
cvc5_rare "BV_Rewrites.rewrite_bv_shl_by_const_1"
cvc5_rare "BV_Rewrites.rewrite_bv_shl_by_const_2"
cvc5_rare "BV_Rewrites.rewrite_bv_lshr_by_const_0"

end