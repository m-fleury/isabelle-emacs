theory SMT_CVC \<comment> \<open>More Setup for CVC that should be in HOL eventually\<close>
  imports HOL.SMT "cvc5_dsl_rewrites/Rare_Interface"
  keywords "smt_status" "check_smt_dir" "check_smt" :: diag
begin



named_theorems rare_simplify_temp \<open>Theorems to reconstruct bitvector theorems concerning list
                                  functions, e.g. take.\<close>

named_theorems cvc_evaluate \<open>Theorems to reconstruct evaluate steps in cvc5 proofs\<close>

named_theorems arith_simp_cvc5 \<open>Might be temp and integrated into smt_arith_simplify \<close>

lemmas [arith_simp_cvc5] = 
         Groups.monoid_mult_class.mult_1_right Nat.mult_Suc_right
         Nat.mult_0_right Nat.add_Suc_right Groups.monoid_add_class.add.right_neutral
         Num.numeral_2_eq_2 Nat.One_nat_def Num.numeral_2_eq_2 Nat.One_nat_def
         Nat.Suc_less_eq Nat.zero_less_Suc minus_nat.diff_0 Nat.diff_Suc_Suc Nat.le0
         prod.case numeral_plus_one divmod_step_def order.refl le_zero_eq
         le_numeral_simps less_numeral_simps mult.right_neutral divides_aux_eq
         mult_nonneg_nonneg dvd_imp_mod_0 dvd_add zero_less_one mod_mult_self4 numeral_mod_numeral
         divmod_trivial prod.sel mult.left_neutral div_pos_pos_trivial arith_simps div_add div_mult_self1
         add_le_cancel_left add_le_same_cancel2 not_one_le_zero le_numeral_simps add_le_same_cancel1
         zero_neq_one zero_le_one le_num_simps add_Suc mod_div_trivial nat.distinct mult_minus_right
         add.inverse_inverse distrib_left_numeral mult_num_simps numeral_times_numeral add_num_simps
         divmod_steps rel_simps if_True if_False numeral_div_numeral divmod_cancel prod.case
         add_num_simps one_plus_numeral fst_conv arith_simps sub_num_simps dbl_inc_simps
         dbl_simps mult_1 add_le_cancel_right left_diff_distrib_numeral add_uminus_conv_diff zero_neq_one
         zero_le_one One_nat_def add_Suc mod_div_trivial nat.distinct of_int_1 numerals numeral_One
         of_int_numeral add_uminus_conv_diff zle_diff1_eq add_less_same_cancel2 minus_add_distrib
         add_uminus_conv_diff mult.left_neutral semiring_class.distrib_right
         add_diff_cancel_left' add_diff_eq ring_distribs mult_minus_left minus_diff_eq
         ab_semigroup_mult_class.mult.commute
(*lemmas [cvc_evaluate] = arith_simp_cvc5*)


named_theorems alethe_poly_norm \<open>Extra theorems for poly norm.\<close>

lemmas [alethe_poly_norm] = mult_1_right mult_1_left

(*Term rewrites*)

ML_file \<open>ML/alethe_replay_rare_simplify_methods.ML\<close>

ML \<open>
fun cvc_term_parser (SMTLIB.Sym "rare-list", []) = (
   (*If there are no elements in the list we cannot know the type at this point*)
    SOME(Const( \<^const_name>\<open>ListVar\<close> ,dummyT --> dummyT)
       $ Const( \<^const_name>\<open>List.Nil\<close>, dummyT)))
  | cvc_term_parser (SMTLIB.Sym "rare-list", ts) =(
    let
      (*Figure out if types are different, this should only be the case if they have different
        bitwidths*)
      fun remove_duplicates [] = []
        | remove_duplicates (x::xs) = x::remove_duplicates(List.filter (fn y => y <> x) xs)

      val types_eq = map fastype_of ts |> remove_duplicates |> length 
      val new_ts =ts
         (*if types_eq > 0
         then ts
         else (map (fn t => Const( \<^const_name>\<open>unsigned\<close>, \<^typ>\<open>'a::len word \<Rightarrow> Nat.nat \<close>) $ t) ts)*)
      val new_type = if types_eq > 0 then fastype_of (hd ts) else \<^typ>\<open>Nat.nat\<close>

    in
    SOME(Const( \<^const_name>\<open>ListVar\<close>, Type(\<^type_name>\<open>List.list\<close>,[new_type])  --> Type(\<^type_name>\<open>cvc_ListVar\<close>,[new_type]))
      $ (HOLogic.mk_list new_type new_ts))
    end)
  | cvc_term_parser _ = NONE

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_term_parser cvc_term_parser)
)
\<close>


(*External proof checking*)
ML_file \<open>ML/smt_parse_problem.ML\<close>
ML_file \<open>ML/smt_check_external.ML\<close>
                
ML \<open>

(*Call replay from SMT_Solver and add replay_data on your own*)
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>check_smt\<close>
          "parse a file in SMTLIB2 format and check proof. <problem_file,proof_file>"
    (Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.string --| \<^keyword>\<open>)\<close>) "cvc5" --
    (Parse.string -- Parse.string)
    >> (fn (prover, (problem_file_name,proof_file_name)) => fn lthy =>
  let
    val ctxt = Local_Theory.target_of lthy
    fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of
    val _ = SMT_Config.verbose_msg ctxt (pretty "Checking Alethe proof...") []
    (*Replay proof*)
    val _ = SMT_Check_External.check_smt (if prover = "cvc5" then "cvc5_proof" else prover)
        problem_file_name proof_file_name NONE lthy
    val _ = SMT_Config.verbose_msg ctxt (pretty "Finished checking Alethe proof!") []
  in
   lthy
  end))

(*Call replay from SMT_Solver and add replay_data on your own*)
(*The problem (name.smt2) and proof files (name.alethe) should be in the same directory.*)
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>check_smt_dir\<close>
         "parse a directory with SMTLIB2 format and check proof. <dir>"
    ((Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.string --| \<^keyword>\<open>)\<close>) "cvc5" -- Parse.string)
    >> (fn (prover, dir_name) => fn lthy =>
  let
    val _ = SMT_Check_External.check_all_benchmarks prover dir_name NONE lthy
  in
   lthy
   end))

\<close>


(**)
cvc5_rare "Arith_Rewrites.rewrite_arith_plus_zero"
cvc5_rare "Arith_Rewrites.rewrite_arith_mul_one"
cvc5_rare "Arith_Rewrites.rewrite_arith_mul_zero"
cvc5_rare "Arith_Rewrites.rewrite_arith_int_div_one"
cvc5_rare "Arith_Rewrites.rewrite_arith_neg_neg_one"
cvc5_rare "Arith_Rewrites.rewrite_arith_elim_uminus"
cvc5_rare "Arith_Rewrites.rewrite_arith_elim_minus"
cvc5_rare "Arith_Rewrites.rewrite_arith_elim_gt"
cvc5_rare "Arith_Rewrites.rewrite_arith_elim_lt"
cvc5_rare "Arith_Rewrites.rewrite_arith_int_gt"
cvc5_rare "Arith_Rewrites.rewrite_arith_int_lt"
cvc5_rare "Arith_Rewrites.rewrite_arith_elim_leq"
cvc5_rare "Arith_Rewrites.rewrite_arith_leq_norm"
cvc5_rare "Arith_Rewrites.rewrite_arith_geq_tighten"
cvc5_rare "Arith_Rewrites.rewrite_arith_geq_norm1_int"
cvc5_rare "Arith_Rewrites.rewrite_arith_refl_leq"
cvc5_rare "Arith_Rewrites.rewrite_arith_refl_lt"
cvc5_rare "Arith_Rewrites.rewrite_arith_refl_geq"
cvc5_rare "Arith_Rewrites.rewrite_arith_refl_gt"
cvc5_rare "Arith_Rewrites.rewrite_arith_eq_elim_int"
cvc5_rare "Arith_Rewrites.rewrite_arith_plus_flatten"
cvc5_rare "Arith_Rewrites.rewrite_arith_mult_flatten"
cvc5_rare "Arith_Rewrites.rewrite_arith_mult_dist"
cvc5_rare "Arith_Rewrites.rewrite_arith_plus_cancel1"
cvc5_rare "Arith_Rewrites.rewrite_arith_plus_cancel2"

cvc5_rare "Boolean_Rewrites.rewrite_bool_double_not_elim"
cvc5_rare "Boolean_Rewrites.rewrite_bool_not_true"
cvc5_rare "Boolean_Rewrites.rewrite_bool_not_false"

cvc5_rare "Boolean_Rewrites.rewrite_bool_eq_true"
cvc5_rare "Boolean_Rewrites.rewrite_bool_eq_false"
cvc5_rare "Boolean_Rewrites.rewrite_bool_eq_nrefl"

cvc5_rare "Boolean_Rewrites.rewrite_bool_impl_false1"
cvc5_rare "Boolean_Rewrites.rewrite_bool_impl_false2"
cvc5_rare "Boolean_Rewrites.rewrite_bool_impl_true1"
cvc5_rare "Boolean_Rewrites.rewrite_bool_impl_true2"
cvc5_rare "Boolean_Rewrites.rewrite_bool_impl_elim"

cvc5_rare "Boolean_Rewrites.rewrite_bool_dual_impl_eq"

cvc5_rare "Boolean_Rewrites.rewrite_bool_or_true"
cvc5_rare "Boolean_Rewrites.rewrite_bool_or_flatten"

cvc5_rare "Boolean_Rewrites.rewrite_bool_and_false"
cvc5_rare "Boolean_Rewrites.rewrite_bool_and_flatten"

cvc5_rare "Boolean_Rewrites.rewrite_bool_and_conf"
cvc5_rare "Boolean_Rewrites.rewrite_bool_and_conf2"
cvc5_rare "Boolean_Rewrites.rewrite_bool_or_taut"
cvc5_rare "Boolean_Rewrites.rewrite_bool_or_taut2"

cvc5_rare "Boolean_Rewrites.rewrite_bool_or_de_morgan"
cvc5_rare "Boolean_Rewrites.rewrite_bool_implies_de_morgan"
cvc5_rare "Boolean_Rewrites.rewrite_bool_and_de_morgan"

cvc5_rare "Boolean_Rewrites.rewrite_bool_or_and_distrib"

cvc5_rare "Boolean_Rewrites.rewrite_bool_implies_or_distrib"

cvc5_rare "Boolean_Rewrites.rewrite_bool_xor_refl"
cvc5_rare "Boolean_Rewrites.rewrite_bool_xor_nrefl"
cvc5_rare "Boolean_Rewrites.rewrite_bool_xor_false"
cvc5_rare "Boolean_Rewrites.rewrite_bool_xor_true"
cvc5_rare "Boolean_Rewrites.rewrite_bool_xor_comm"
cvc5_rare "Boolean_Rewrites.rewrite_bool_xor_elim"
cvc5_rare "Boolean_Rewrites.rewrite_bool_not_xor_elim"

cvc5_rare "Boolean_Rewrites.rewrite_bool_not_eq_elim1"
cvc5_rare "Boolean_Rewrites.rewrite_bool_not_eq_elim2"

cvc5_rare "Boolean_Rewrites.rewrite_ite_neg_branch"

cvc5_rare "Boolean_Rewrites.rewrite_ite_then_true"
cvc5_rare "Boolean_Rewrites.rewrite_ite_else_false"
cvc5_rare "Boolean_Rewrites.rewrite_ite_then_false"
cvc5_rare "Boolean_Rewrites.rewrite_ite_else_true"

cvc5_rare "Boolean_Rewrites.rewrite_ite_then_lookahead_self"
cvc5_rare "Boolean_Rewrites.rewrite_ite_else_lookahead_self"

cvc5_rare "Boolean_Rewrites.rewrite_ite_then_lookahead_not_self"
cvc5_rare "Boolean_Rewrites.rewrite_ite_else_lookahead_not_self"

cvc5_rare "Boolean_Rewrites.rewrite_ite_expand"

cvc5_rare "Boolean_Rewrites.rewrite_bool_not_ite_elim"

(*legacy*)
cvc5_rare "Boolean_Rewrites.rewrite_bool_commutative_and"
cvc5_rare "Boolean_Rewrites.rewrite_bool_commutative_or"
cvc5_rare "Boolean_Rewrites.rewrite_bool_commutative_xor"
cvc5_rare "Boolean_Rewrites.rewrite_bool_not_ite_elim"
cvc5_rare "Boolean_Rewrites.rewrite_bool_or_false"
cvc5_rare "Boolean_Rewrites.rewrite_bool_or_dup"
cvc5_rare "Boolean_Rewrites.rewrite_bool_and_true"
cvc5_rare "Boolean_Rewrites.rewrite_bool_and_dup"

cvc5_rare "Builtin_Rewrites.rewrite_ite_true_cond"
cvc5_rare "Builtin_Rewrites.rewrite_ite_false_cond"
cvc5_rare "Builtin_Rewrites.rewrite_ite_not_cond"
cvc5_rare "Builtin_Rewrites.rewrite_ite_eq_branch"
cvc5_rare "Builtin_Rewrites.rewrite_ite_then_lookahead"
cvc5_rare "Builtin_Rewrites.rewrite_ite_else_lookahead"
cvc5_rare "Builtin_Rewrites.rewrite_ite_then_neg_lookahead"
cvc5_rare "Builtin_Rewrites.rewrite_ite_else_neg_lookahead"

cvc5_rare "UF_Rewrites.rewrite_eq_refl"
cvc5_rare "UF_Rewrites.rewrite_eq_symm"
cvc5_rare "UF_Rewrites.rewrite_eq_ite_lift"
cvc5_rare "UF_Rewrites.rewrite_distinct_binary_elim"

end
