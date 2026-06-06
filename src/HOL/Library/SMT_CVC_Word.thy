theory SMT_CVC_Word \<comment> \<open>More Setup for CVC that should be in HOL-Word eventually\<close>
  imports CVC_Word "Alethe_UF_BV_Rewrites" "Alethe_BV_Rewrites" "Alethe_BV_Rewrites_Simplification" "Alethe_BV_Rewrites_Elimination"
begin

(*Evaluation Steps*)

(*This evaluation should be high in success instead of fast on average*)

lemmas bit_operations = drop_bit_eq_div take_bit_eq_mod push_bit_eq_mult
                        numeral_mod_numeral divmod_cancel
lemmas [bv_reconstruction_length] = smt_word_len_evaluate
  lemmas [cvc_evaluate] = Word_eq_word_of_int

lemmas [cvc_evaluate_bv] = bv_reconstruction_length bit_operations word_size
lemmas [bv_reconstruction_const_test] = upt_zero_numeral_unfold pred_numeral_simps



lemma evaluate_concat[cvc_evaluate_bv]:
"(word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
   = ucast x * (2::'c word) ^ LENGTH('b) + ucast y"
  unfolding word_cat_eq[of x y] push_bit_eq_mult
  by simp


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
    push_bit_lift drop_bit_lift



lemma drop_numeral_Cons [bv_reconstruction_list_funs]:
"drop (numeral n) (x # xs) = drop (pred_numeral n) xs"
  by (simp add: numeral_eq_Suc)

lemma take_numeral_Cons [bv_reconstruction_list_funs]:
"take (numeral n) (x # xs) = x # take (pred_numeral n) xs"
  by (simp add: numeral_eq_Suc)

lemma takefill_numeral_Cons [bv_reconstruction_list_funs]:
"takefill c (numeral n) (x # xs) = x # takefill c (pred_numeral n) xs"
  by (simp add: numeral_eq_Suc takefill_Suc_Cons)

lemmas [arith_simp_cvc5] = nat_numeral pred_numeral_simps                                                                                                 

ML \<open>
val nat_native_ops_tab =
[
("Bit_Shifts_Infix_Syntax.semiring_bit_operations_class.shiftl", @{thms eq_reflection[OF shiftl_def] push_bit_lift}),
("Bit_Shifts_Infix_Syntax.semiring_bit_operations_class.shiftr", @{thms eq_reflection[OF shiftr_def] drop_bit_lift})

]
fun bit_should_lift (_ $ (w $ i)) = Word_Lib.has_concrete_bw w andalso can HOLogic.dest_numeral i(*TODO: Also check if concrete value*)
  | bit_should_lift _ = false
val simplify_norm_table = [
  ("Bit_Operations.semiring_bits_class.bit",(SOME bit_should_lift,(@{thms bit_lift},NONE))) (*TODO: Add condition*)

]


val _ = fold SMT_Normalize.add_nat_native_ops_tab (nat_native_ops_tab)
    |> Theory.setup o  Context.theory_map


val _ = fold SMT_Normalize.add_simplify_ops_tab (simplify_norm_table)
    |> Theory.setup o  Context.theory_map
\<close>

lemmas [bv_aci_simp] =
Bit_Operations.semiring_bit_operations_class.zero_and_eq
Bit_Operations.semiring_bit_operations_class.and_zero_eq
Bit_Operations.semiring_bit_operations_class.and.commute
Bit_Operations.semiring_bit_operations_class.or.comm_neutral
Bit_Operations.semiring_bit_operations_class.or.left_neutral
Bit_Operations.semiring_bit_operations_class.or.commute
Bit_Operations.semiring_bit_operations_class.xor.comm_neutral
Bit_Operations.semiring_bit_operations_class.xor.left_neutral
Bit_Operations.semiring_bit_operations_class.xor.commute




ML \<open>
(*
TODO: Re-write, written by AI

Word-specific reconstruction for poly_simp. A word equality is not a generic ring identity: it
  may hold only because of the ring characteristic 2 ^ LENGTH('a) = 0. The generic poly_simp
  simplification already reduces such a goal to a pure integer goal modulo 2 ^ LENGTH('a)
  (numerals collected, then code evaluation pushes the word arithmetic to uint ... mod 2 ^ n); all
  that is missing for the characteristic-dependent cases is a linear-arithmetic closer, which
  presburger provides. As a fall-back we also try transfer to int. Both routes stay clear of the
  if-then-else blow-up that unat normalization causes for truncated subtraction.

  poly_simp_word below is a copy of Alethe_Replay_Methods.poly_simp extended with one extra
  alternative (the word_finish_tac branch) and registered via declare_alethe_rule. Word equalities
  that are not generic ring identities first run through the unchanged simplification attempts and,
  only when those do not close the goal, through the word route.*)
(*tracing as in alethe_replay_methods: gated by smt_expert_debug_alethe_level / _files*)
fun debug_msg_tac' ctxt str =
  K (SMT_Config.alethe_debug_msg_tac ctxt "SMT_CVC_Word" SMT_Config.high str)

fun word_finish_tac ctxt =
  let
    fun trace msg tac = debug_msg_tac' ctxt msg THEN' tac
    val reduce_to_int_tac =
      full_simp_tac ctxt THEN_ALL_NEW (fn i => TRY (Code_Simp.dynamic_tac ctxt i))
    val to_int_tac = Transfer.gen_frees_tac [] ctxt THEN' Transfer.transfer_tac true ctxt
    val mod_simp_tac = full_simp_tac (ctxt addsimps @{thms take_bit_eq_mod})
    val presburger_tac = Cooper.tac true [] [] ctxt
    val finish_tac =
      SOLVED' (trace "word route: simp+code_simp then presburger" (reduce_to_int_tac THEN_ALL_NEW presburger_tac))
      ORELSE' SOLVED' (trace "word route: transfer+mod then presburger" (to_int_tac THEN_ALL_NEW mod_simp_tac THEN_ALL_NEW presburger_tac))
      ORELSE' SOLVED' (trace "word route: transfer then presburger" (to_int_tac THEN_ALL_NEW presburger_tac))
      ORELSE' SOLVED' (trace "word route: presburger" presburger_tac)
  in
    SUBGOAL (fn (goal, i) =>
      (case Logic.strip_assums_concl goal of
        \<^Const_>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>HOL.eq\<close>, T) $ _ $ _) =>
          (case Term.domain_type T of
            Type (\<^type_name>\<open>word\<close>, _) =>
              (debug_msg_tac' ctxt "entering word route" THEN' finish_tac) i
          | _ => no_tac)
      | _ => no_tac))
  end

(*copied from the (private) Alethe_Replay_Methods.prove_abstract: abstract the goal after stripping
  the Trueprop judgment and eta-normalizing, run tac on it, and transfer the result back*)
fun prove_abstract abstracter tac ctxt thms t =
  let
    val t_eta_long_eq = Thm.eta_long_conversion (Object_Logic.dest_judgment ctxt (Thm.cterm_of ctxt t))
    val (_, t_eta_long) = Logic.dest_equals (Thm.prop_of t_eta_long_eq)
    val thms_eta_long = map (Conv.fconv_rule Thm.eta_long_conversion) thms
    val abstract_thm =
      SMT_Replay_Methods.prove_abstract ctxt thms_eta_long t_eta_long tac
        (fold_map (abstracter o SMT_Replay_Methods.dest_thm) thms_eta_long ##>>
         abstracter (SMT_Replay_Methods.dest_prop t_eta_long))
  in
    @{thm alethe_Pure_trans} OF [t_eta_long_eq, abstract_thm]
  end

(*copied from Alethe_Replay_Methods.poly_simp, extended with the word_finish_tac branch*)
fun poly_simp_word ctxt _ _ =
  let
    val TRY' = Alethe_Replay_Methods.TRY'
    (*push of_int through arithmetic operators first*)
    val of_int_push_thms = @{thms of_int_add of_int_diff of_int_mult of_int_minus
      of_int_numeral of_int_neg_numeral of_int_1 of_int_0 of_int_of_nat_eq}
    fun push_of_int_tac ctxt =
      ctxt
      |> Simplifier.empty_simpset
      |> Simplifier.put_simpset HOL_basic_ss
      |> Simplifier.add_simps of_int_push_thms
      |> Simplifier.full_simp_tac
    fun simplify_tac ctxt thms =
      ctxt
      |> Simplifier.empty_simpset
      |> Simplifier.put_simpset HOL_basic_ss
      |> Simplifier.add_simps (@{thms simp_thms} @ thms)
      |> (Simplifier.add_cong @{thm if_weak_cong})
      |> fold Simplifier.add_proc [@{simproc int_div_cancel_numeral_factors}, @{simproc int_combine_numerals},
           @{simproc divide_cancel_numeral_factor}, @{simproc divide_cancel_factor},
           @{simproc intle_cancel_numerals}, @{simproc intless_cancel_numerals}, @{simproc inteq_cancel_numerals},
           @{simproc field_combine_numerals},
           @{simproc ring_le_cancel_numeral_factor},
           @{simproc HOL.NO_MATCH}, @{simproc Numeral_Simprocs.semiring_assoc_fold},
           @{simproc Numeral_Simprocs.field_divide_cancel_numeral_factor},
           @{simproc Numeral_Simprocs.field_eq_cancel_numeral_factor}]
      |> Simplifier.full_simp_tac
    fun simplify_tac_with_background_simp ctxt thms =
      ctxt
      |> Simplifier.add_simps thms
      |> Simplifier.full_simp_tac
    val tac = (fn _ => fn _ =>
        TRY' (push_of_int_tac ctxt)
        THEN' debug_msg_tac' ctxt "pushed of_int to leaves before poly simp"
        THEN' TRY' (simplify_tac ctxt (Named_Theorems.get ctxt @{named_theorems alethe_poly_norm}))
        THEN' debug_msg_tac' ctxt "tried to solve poly simp with custom simplify tac"
        (*new: word equalities that rely on the ring characteristic 2 ^ LENGTH('a) = 0*)
      THEN' TRY' (word_finish_tac ctxt)
        (*if the previous does not solve, use full simplification power with the current content*)
      THEN' TRY' (simplify_tac_with_background_simp ctxt [])
        THEN' debug_msg_tac' ctxt "tried full simplifier power on current arith_poly_norm step"
      THEN' TRY' (Code_Simp.dynamic_tac ctxt)
      THEN' debug_msg_tac' ctxt "tried code evaluation on arith_poly_norm step since nothing else worked")
  in
    prove_abstract (SMT_Replay_Methods.abstract_for_poly_norm ctxt) tac ctxt []
  end

val _ = Theory.setup (Context.theory_map (
  Alethe_Replay_Methods.declare_alethe_rule "poly_simp" poly_simp_word))
\<close>

cvc5_rare "Alethe_UF_BV_Rewrites.rewrite_uf_bv2nat_int2bv"
cvc5_rare "Alethe_UF_BV_Rewrites.rewrite_uf_bv2nat_int2bv_extend"
cvc5_rare "Alethe_UF_BV_Rewrites.rewrite_uf_bv2nat_int2bv_extract"
cvc5_rare "Alethe_UF_BV_Rewrites.rewrite_uf_int2bv_bv2nat"
cvc5_rare "Alethe_UF_BV_Rewrites.rewrite_uf_bv2nat_geq_elim"
cvc5_rare "Alethe_UF_BV_Rewrites.rewrite_uf_int2bv_bvult_equiv"
cvc5_rare "Alethe_UF_BV_Rewrites.rewrite_uf_int2bv_bvule_equiv"
cvc5_rare "Alethe_UF_BV_Rewrites.rewrite_uf_sbv_to_int_elim"





cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_ule_eliminate"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_ugt_eliminate"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_uge_eliminate"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_sgt_eliminate"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_sge_eliminate"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_slt_eliminate"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_rotate_left_eliminate_1"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_rotate_left_eliminate_2"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_rotate_right_eliminate_1"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_rotate_right_eliminate_2"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_nand_eliminate"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_nor_eliminate"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_xnor_eliminate"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_zero_extend_eliminate"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_uaddo_eliminate"
cvc5_rare "Alethe_BV_Rewrites_Elimination.rewrite_bv_saddo_eliminate"

cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_extract_whole"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_extract_concat_1"

(*cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_concat_extract_merge"*)
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_extract_extract"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_extract_whole"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_extract_concat_1"
(*cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_extract_concat_2"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_extract_concat_3"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_extract_concat_4"*)
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_eq_extract_elim1"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_eq_extract_elim2"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_eq_extract_elim3"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_extract_not"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_extract_sign_extend_1"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_extract_sign_extend_2"
(*cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_extract_sign_extend_3"*)
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_not_xor"
(*cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_and_simplify_1"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_and_simplify_2"*)
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_or_simplify_1"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_or_simplify_2"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_xor_simplify_1"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_xor_simplify_2"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_xor_simplify_3"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_ult_add_one"
(*cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_mult_slt_mult_1"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_mult_slt_mult_2"*)
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_commutative_xor"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_commutative_comp"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_zero_extend_eliminate_0"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_sign_extend_eliminate_0"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_not_neq"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_ult_ones"
(*cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_concat_merge_const"*)
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_commutative_add"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_sub_eliminate"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_ite_width_one"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_ite_width_one_not"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_eq_xor_solve"
cvc5_rare "Alethe_BV_Rewrites.rewrite_bv_eq_not_solve"

cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ite_equal_children"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ite_const_children_1"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ite_const_children_2"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ite_equal_cond_1"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ite_equal_cond_2"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ite_equal_cond_3"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ite_merge_then_if"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ite_merge_else_if"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ite_merge_then_else"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ite_merge_else_else"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_shl_by_const_0"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_shl_by_const_1"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_shl_by_const_2"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_lshr_by_const_0"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_lshr_by_const_1"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_lshr_by_const_2"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ashr_by_const_0"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ashr_by_const_1"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ashr_by_const_2"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_and_concat_pullup"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_xor_duplicate"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_xor_not"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_not_idemp"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ult_zero_1"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ult_zero_2"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ult_self"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_lt_self"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ule_self"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_zero_ule"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ule_zero"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_sle_self"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ule_max"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_not_ult"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_xor_ones"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_mult_pow2_1"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_mult_pow2_2"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_mult_pow2_2b"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_extract_mult_leading_bit"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_udiv_pow2_not_one"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_udiv_zero"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_udiv_one"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_urem_pow2_not_one"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_urem_one"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_urem_self"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_shl_zero"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_lshr_zero"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ashr_zero"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ugt_urem"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_ult_one"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_slt_zero"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_merge_sign_extend_1"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_merge_sign_extend_2"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_zero_extend_eq_const_1"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_zero_extend_eq_const_2"
cvc5_rare "Alethe_BV_Rewrites_Simplification.rewrite_bv_zero_extend_ult_const_1"



lemmas [alethe_aci_simp] =
 Bit_Operations.semiring_bit_operations_class.and.idem
 Bit_Operations.semiring_bit_operations_class.or.idem
 Bit_Operations.ring_bit_operations_class.bit.xor_self


lemmas [cvc5_normalized_input] = Word_of_int


end
