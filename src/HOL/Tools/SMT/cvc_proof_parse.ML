(*  Title:      HOL/Tools/SMT/cvc_proof_parse.ML
    Author:     Jasmin Blanchette, TU Muenchen

CVC4 and cvc5 proof (actually, unsat core) parsing.
*)

signature CVC_PROOF_PARSE =
sig
  val parse_proof: SMT_Translate.replay_data ->
    ((string * ATP_Problem_Generate.stature) * thm) list -> term list -> term -> string list ->
    SMT_Solver.parsed_proof
  val parse_proof_lethe: SMT_Translate.replay_data ->
    ((string * ATP_Problem_Generate.stature) * thm) list -> term list -> term -> string list ->
    SMT_Solver.parsed_proof
  val cvc_matching_assms: Proof.context -> thm list -> term list -> term -> thm -> bool

end;

structure CVC_Proof_Parse: CVC_PROOF_PARSE =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Proof_Reconstruct
open Lethe_Isar
open Lethe_Proof

(*taken from verit*)
fun add_used_asserts_in_step (Lethe_Proof.Lethe_Step {prems, ...}) =
  union (op =) (map_filter (try (snd o SMTLIB_Interface.role_and_index_of_assert_name)) prems)

fun cvc_matching_assms ctxt rewrite_rules ll_defs th th' =
  let
    val expand =
       not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
       #> Object_Logic.dest_judgment ctxt o (Thm.cterm_of ctxt)
       #> Thm.eta_long_conversion
       #> Thm.prop_of
       #> snd o Logic.dest_equals
       #> Raw_Simplifier.rewrite_term (Proof_Context.theory_of
          (empty_simpset ctxt addsimps rewrite_rules @ @{thms eq_True})) rewrite_rules []


    val normalize = 
       Object_Logic.dest_judgment ctxt o (Thm.cprop_of)
       #> Thm.eta_long_conversion
       #> Thm.prop_of
       #> snd o Logic.dest_equals
       #> Raw_Simplifier.rewrite_term (Proof_Context.theory_of
          (empty_simpset ctxt addsimps rewrite_rules @ @{thms eq_True})) rewrite_rules []
  in (expand th) aconv (normalize th') end

fun parse_proof_unsatcore ({ll_defs, assms, ...} : SMT_Translate.replay_data) xfacts prems _ output =
  if exists (String.isPrefix "(error \"This build of CVC4 doesn't have proof support") output then
    {outcome = NONE, fact_ids = NONE, atp_proof = K []}
  else
    let
      val num_ll_defs = length ll_defs

      val id_of_index = Integer.add num_ll_defs
      val index_of_id = Integer.add (~ num_ll_defs)

      val used_assert_ids =
        map_filter (try (snd o SMTLIB_Interface.role_and_index_of_assert_name)) output
      val used_assm_js =
        map_filter (fn id => let val i = index_of_id id in if i >= 0 then SOME i else NONE end)
          used_assert_ids

      val conjecture_i = 0
      val prems_i = conjecture_i + 1
      val num_prems = length prems
      val facts_i = prems_i + num_prems

      val fact_ids' =
        map_filter (fn j =>
          let val ((i, _), _) = nth assms j in
            try (apsnd (nth xfacts)) (id_of_index j, i - facts_i)
          end) used_assm_js
    in
      {outcome = NONE, fact_ids = SOME fact_ids', atp_proof = K []}
    end


fun parse_proof_lethe
    ({context = ctxt, typs, terms, ll_defs, rewrite_rules, assms} : SMT_Translate.replay_data)
    xfacts prems concl output =
   if exists (String.isPrefix "(error \"This build of CVC4 doesn't have proof support") output then
     {outcome = NONE, fact_ids = NONE, atp_proof = K []}
   else
     let
    val num_ll_defs = length ll_defs
    val id_of_index = Integer.add num_ll_defs
    val index_of_id = Integer.add (~ num_ll_defs)
(* FIXME
The eq_True is needed for:
lemma
fixes a :: int
  assumes \<open>a = 0 + 0\<close>
  shows \<open>a = 0\<close> 
  supply [[smt_trace=false,smt_nat_as_int=false,ML_print_depth=1000]]
  sledgehammer[cvc4,debug,verbose,dont_preplay]
(Nat.add_0_right Nat.ex_has_greatest_nat ab_semigroup_add_class.add_ac(1) ab_semigroup_mult_class.mult_ac(1) add.assoc add.comm_monoid_axioms add.comm_neutral add.commute add.group_left_neutral add.inverse_neutral add.left_cancel add.left_commute add.left_inverse add.left_neutral add.monoid_axioms add.right_cancel add.right_inverse add.right_neutral add_0_iff add_cancel_left_left add_cancel_left_right add_cancel_right_left add_cancel_right_right add_decreasing add_decreasing2 add_eq_0_iff_both_eq_0 add_eq_self_zero add_gr_0 add_increasing add_increasing2 add_is_0 add_leD1 add_leD2 add_leE add_le_cancel_left add_le_cancel_right add_le_imp_le_left add_le_imp_le_right add_le_mono add_le_mono1 add_le_same_cancel1 add_le_same_cancel2 add_left_cancel add_left_imp_eq add_left_mono add_lessD1 add_less_cancel_left add_less_cancel_right add_less_mono add_less_mono1 add_less_same_cancel1 add_less_same_cancel2 add_minus_cancel add_mono add_mono_thms_linordered_semiring(1) add_mono_thms_linordered_semiring(2) add_mono_thms_linordered_semiring(3) add_mono_thms_linordered_semiring(4) add_mult_distrib add_mult_distrib2 add_neg_numeral_special(7) add_neg_numeral_special(8) add_nonneg_eq_0_iff add_nonneg_nonneg add_nonpos_eq_0_iff add_nonpos_nonpos add_right_cancel add_right_imp_eq add_right_mono add_scale_eq_noteq antisym_conv antisym_conv1 antisym_conv2 assms bot_nat_0.extremum bot_nat_0.extremum_unique bot_nat_0.extremum_uniqueI bot_nat_0.not_eq_extremum combine_common_factor comm_monoid_add_class.add_0 comm_monoid_mult_class.mult_1 comm_semiring_class.distrib conj_le_cong convex_bound_le crossproduct_eq crossproduct_noteq dbl_def dbl_inc_def dbl_inc_simps(2) dbl_inc_simps(4) dbl_simps(2) distrib_left distrib_right divisors_zero double_add_le_zero_iff_single_add_le_zero double_add_less_zero_iff_single_add_less_zero double_zero double_zero_sym dual_order.antisym dual_order.eq_iff dual_order.order_iff_strict dual_order.refl dual_order.strict_iff_not dual_order.strict_iff_order dual_order.strict_implies_order dual_order.strict_trans1 dual_order.strict_trans2 dual_order.trans dup_code(1) dup_def eq_imp_le eq_refl equal_neg_zero gr0I gr_implies_not0 group_cancel.add1 group_cancel.add2 imp_le_cong int_distrib(1) int_distrib(2) int_ge_induct is_num_normalize(1) le0 le_0_eq le_Suc_ex le_add1 le_add2 le_add_same_cancel1 le_add_same_cancel2 le_antisym le_cases le_cases3 le_cube le_eq_less_or_eq le_iff_add le_imp_less_or_eq le_less_linear le_less_trans le_neq_implies_less le_neq_trans le_numeral_extra(3) le_numeral_extra(4) le_refl le_square le_trans le_zero_eq left_add_mult_distrib less_add_eq_less less_add_same_cancel1 less_add_same_cancel2 less_eqE less_eq_int_code(1) less_eq_nat.simps(1) less_eq_neg_nonpos less_imp_le less_imp_le_nat less_le_not_le less_le_trans less_mono_imp_le_mono less_nat_zero_code less_neg_neg less_one less_or_eq_imp_le less_zeroE linear linorder_wlog linordered_nonzero_semiring_class.zero_le_one minus_add_cancel minus_add_distrib minus_mult_minus mult.assoc mult.comm_monoid_axioms mult.comm_neutral mult.commute mult.left_commute mult.left_neutral mult.monoid_axioms mult.right_neutral mult_0 mult_0_right mult_cancel1 mult_cancel2 mult_cancel_left mult_cancel_left1 mult_cancel_left2 mult_cancel_right mult_cancel_right1 mult_cancel_right2 mult_eq_0_iff mult_eq_self_implies_10 mult_is_0 mult_le_0_iff mult_le_cancel2 mult_le_mono mult_le_mono1 mult_le_mono2 mult_le_one mult_left_cancel mult_left_le mult_left_le_one_le mult_left_mono mult_left_mono_neg mult_less_cancel2 mult_minus1 mult_minus1_right mult_minus_left mult_minus_right mult_mono mult_mono' mult_nonneg_nonneg mult_nonneg_nonpos mult_nonneg_nonpos2 mult_nonpos_nonneg mult_nonpos_nonpos mult_not_zero mult_of_int_commute mult_right_cancel mult_right_le_one_le mult_right_mono mult_right_mono_neg mult_zero_left mult_zero_right nat.exhaust_disc nat_0_less_mult_iff nat_1_eq_mult_iff nat_add_left_cancel_le nat_add_left_cancel_less nat_le_iff_add nat_le_linear nat_less_le nat_mult_1 nat_mult_1_right nat_mult_eq_1_iff nat_mult_eq_cancel_disj nat_mult_le_cancel_disj nat_mult_less_cancel_disj neg_0_equal_iff_equal neg_0_le_iff_le neg_0_less_iff_less neg_equal_0_iff_equal neg_equal_zero neg_le_0_iff_le neg_le_iff_le neg_less_0_iff_less neg_less_eq_nonneg neg_less_iff_less neg_less_pos neq0_conv nle_le no_zero_divisors not_add_less1 not_add_less2 not_gr0 not_gr_zero not_le not_le_imp_less not_less not_less0 not_one_le_zero odd_nonzero of_int_0 of_int_0_eq_iff of_int_0_le_iff of_int_0_less_iff of_int_1 of_int_1_le_iff of_int_1_less_iff of_int_add of_int_eq_0_iff of_int_eq_1_iff of_int_le_0_iff of_int_le_1_iff of_int_le_iff of_int_less_0_iff of_int_less_1_iff of_int_less_iff of_int_mult of_int_nonneg one_reorient ord_eq_le_subst ord_eq_le_trans ord_le_eq_subst ord_le_eq_trans order.antisym order.eq_iff order.not_eq_order_implies_strict order.order_iff_strict order.strict_iff_not order.strict_iff_order order.strict_implies_order order.strict_trans1 order.strict_trans2 order.trans order_antisym order_class.order_eq_iff order_refl order_subst1 order_subst2 order_trans ordered_comm_semiring_class.comm_mult_left_mono plus_int_code(1) plus_int_code(2) plus_nat.add_0 push_bit_add push_bit_eq_0_iff push_bit_negative_int_iff push_bit_nonnegative_int_iff push_bit_of_0 push_bit_push_bit ring_class.ring_distribs(1) ring_class.ring_distribs(2) split_mult_neg_le split_mult_pos_le sum_squares_eq_zero_iff sum_squares_ge_zero sum_squares_le_zero_iff times_int_code(1) times_int_code(2) trans_le_add1 trans_le_add2 trans_less_add1 trans_less_add2 verit_comp_simplify1(2) verit_la_disequality verit_la_generic verit_sum_simplify zero_eq_add_iff_both_eq_0 zero_le zero_le_double_add_iff_zero_le_single_add zero_le_mult_iff zero_le_square zero_less_double_add_iff_zero_less_single_add zero_less_one_class.zero_le_one zero_neq_one zero_reorient zle_add1_eq_le)
*)
    fun step_of_assume i ((_, role), th) =
      let
        val th = Thm.prop_of th
        fun matching (_, th') = cvc_matching_assms ctxt rewrite_rules ll_defs th th'
      in
        case List.find matching assms of
          NONE => []
        | SOME (k, _) =>
          Lethe_Proof.Lethe_Step 
           {id = SMTLIB_Interface.assert_name_of_role_and_index role (id_of_index i),
            rule = input_rule, prems = [], proof_ctxt = [], concl = th, fixes = []}
          |> single
      end

    val (actual_steps, _) = Lethe_Proof.parse typs terms output ctxt
    val used_assert_ids = fold add_used_asserts_in_step actual_steps []
    val used_assm_js =
      map_filter (fn id => let val i = index_of_id id in if i >= 0 then SOME i else NONE end)
        used_assert_ids
    val used_assms = map (nth assms) used_assm_js
    val assm_steps = map2 step_of_assume used_assm_js used_assms
        |> flat
    val steps = assm_steps @ actual_steps

    val conjecture_i = 0
    val prems_i = conjecture_i + 1
    val num_prems = length prems
    val facts_i = prems_i + num_prems
    val num_facts = length xfacts
    val helpers_i = facts_i + num_facts

    val conjecture_id = id_of_index conjecture_i
    val prem_ids = map id_of_index (prems_i upto prems_i + num_prems - 1)
    val fact_ids' =
      map_filter (fn j =>
        let val ((i, _), _) = nth assms j in
          try (apsnd (nth xfacts)) (id_of_index j, i - facts_i)
        end) used_assm_js
    val helper_ids' =
      map_filter (fn ((i, _), thm) => if i >= helpers_i then SOME (i, thm) else NONE) used_assms

    val fact_helper_ts =
      map (fn (_, th) => (ATP_Util.short_thm_name ctxt th, Thm.prop_of th)) helper_ids' @
      map (fn (_, ((s, _), th)) => (s, Thm.prop_of th)) fact_ids'
    val fact_helper_ids' =
      map (apsnd (ATP_Util.short_thm_name ctxt)) helper_ids' @ map (apsnd (fst o fst)) fact_ids'
  in
    {outcome = NONE, fact_ids = SOME fact_ids',
     atp_proof = fn () => atp_proof_of_veriT_proof ctxt ll_defs rewrite_rules prems concl
       fact_helper_ts prem_ids conjecture_id fact_helper_ids' steps}
  end

fun parse_proof (rep as {context = ctxt, ...}) =
  if SMT_Config.use_lethe_proof_from_cvc ctxt
  then parse_proof_unsatcore rep
  else parse_proof_unsatcore rep

end;
