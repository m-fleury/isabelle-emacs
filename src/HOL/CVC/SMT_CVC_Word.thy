theory SMT_CVC_Word \<comment> \<open>More Setup for CVC that should be in HOL-Word eventually\<close>
  imports SMT_Word "SMT_CVC" "BV_Rewrites" SMT_Native_Output
begin
declare[[show_types,show_sorts]]

(*Evaluation Steps*)

(*This evaluation should be high in success instead of fast on average*)
named_theorems cvc_evaluate_bv \<open>Theorems to reconstruct bit-vector evaluate steps in cvc5 proofs\<close>
lemmas [cvc_evaluate_bv] = bv_reconstruction_length

lemmas bit_operations = drop_bit_eq_div take_bit_eq_mod push_bit_eq_mult
                        numeral_mod_numeral divmod_cancel

lemma evaluate_concat:
"(word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
   = ucast x * (2::'c word) ^ LENGTH('b) + ucast y"
  unfolding word_cat_eq[of x y] push_bit_eq_mult
  by simp


lemma "(smt_extract 1 2 (4::7 word)::2 word) = 0"
  by (code_simp) (*Benutzt die code regeln aber als simp*)


lemma evaluate_extract1:
 "(smt_extract j i (w::'a::len word)::'b::len word) = 
    (if 0 < i then ucast (drop_bit i (take_bit (Suc j) w))
     else push_bit i (ucast (take_bit (Suc j) w)))"
  (*code generation*)
  unfolding smt_extract_def slice_def 
  unfolding slice1_def
  apply (cases "0 < i")
   apply simp_all
  by (metis diff_diff_cancel diff_is_0_eq drop_bit_word_beyond nat_le_linear)

value "(3::int) mod 4"

thm Word.modulo_word_def
thm modulo_integer_def
 



lemma evaluate_extract2:
 "(smt_extract j 0 (w::'a::len word)::'b::len word) = (ucast (w) mod ucast ((2::'b::len word) ^ (Suc j)))"
  apply (simp add: evaluate_extract1[of j 0 w])
  apply (simp add: take_bit_eq_mod)
  using unat_mod
  by (metis power_Suc take_bit_eq_mod unsigned_take_bit_eq)

lemma evaluate_extract3:
 "(smt_extract j (Suc i) (w::'a::len word)::'b::len word) = ucast (drop_bit (Suc i) (take_bit (Suc j) w))"
  using evaluate_extract1[of j "Suc i"] by simp

lemmas evaluate_extract = evaluate_extract2 evaluate_extract3

lemmas evaluate_power = power_0 power_Suc
lemmas evaluate_casts = unsigned_numeral of_nat_numeral 
lemmas bv_mult = word_mult_def (*Is this the best way?*)

lemmas [cvc_evaluate_bv]
  = evaluate_casts bit_operations 
    bv_mult
    evaluate_concat evaluate_power 
lemmas [cvc_evaluate] = cvc_evaluate_bv


lemma cvc_ListOp_neutral_bv_and [cvc_ListOp_neutral]:
 "cvc_isListOp (ListOp (semiring_bit_operations_class.and) (-1::'a::len word))"
  by auto



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
fun  cvc_term_parser (SMTLIB.Sym "rare-list", []) = (@{print}("rare-list");
   (*If there are no elements in the list we cannot know the type at this point*)
    SOME(Const( \<^const_name>\<open>ListVar\<close> ,dummyT --> dummyT)
       $ Const( \<^const_name>\<open>List.Nil\<close>, dummyT)))
  | cvc_term_parser (SMTLIB.Sym "rare-list", ts) =(@{print}("rare-list");
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
    end)
  | cvc_term_parser (SMTLIB.Sym "emptyString", []) = SOME (Free ("''''", \<^typ>\<open>String.string\<close>))
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