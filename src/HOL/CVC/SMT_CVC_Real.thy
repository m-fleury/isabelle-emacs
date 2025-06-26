theory SMT_CVC_Real
  imports "cvc5_dsl_rewrites/Extra_Rewrites" "HOL.Real"
begin

cvc5_rare "Extra_Rewrites.rewrite_ite_eq"
cvc5_rare "Extra_Rewrites.rewrite_quant_var_elim_eq"


cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_leq"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_leq_left_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_leq_right_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_leq_both_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_geq"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_geq_left_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_geq_right_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_geq_both_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_lt"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_lt_left_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_lt_right_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_lt_both_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_gt"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_gt_left_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_gt_right_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_gt_both_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_equal"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_equal_left_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_equal_right_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_poly_norm_rel_equal_both_to_real"


cvc5_rare "Extra_Rewrites.rewrite_arith_to_int_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_to_real_distrib_uminus"
cvc5_rare "Extra_Rewrites.rewrite_arith_to_real_distrib_add"
cvc5_rare "Extra_Rewrites.rewrite_arith_to_real_distrib_minus"
cvc5_rare "Extra_Rewrites.rewrite_arith_to_real_distrib_mult"
cvc5_rare "Extra_Rewrites.rewrite_arith_distrib_add"
cvc5_rare "Extra_Rewrites.rewrite_arith_distrib_mult"
cvc5_rare "Extra_Rewrites.rewrite_arith_to_real_distrib_uminus_rev"


cvc5_rare "Extra_Rewrites.rewrite_arith_geq_norm1_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_geq_norm2"
cvc5_rare "Extra_Rewrites.rewrite_arith_eq_elim_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_to_int_elim_to_real"
cvc5_rare "Extra_Rewrites.rewrite_arith_div_elim_to_real1"
cvc5_rare "Extra_Rewrites.rewrite_arith_div_elim_to_real2"
cvc5_rare "Extra_Rewrites.rewrite_arith_int_eq_conflict"
cvc5_rare "Extra_Rewrites.rewrite_arith_int_geq_tighten"
cvc5_rare "Extra_Rewrites.rewrite_arith_geq_ite_lift"
cvc5_rare "Extra_Rewrites.rewrite_arith_gt_ite_lift"
cvc5_rare "Extra_Rewrites.rewrite_arith_leq_ite_lift"
cvc5_rare "Extra_Rewrites.rewrite_arith_lt_ite_lift"

cvc5_rare "Extra_Rewrites.rewrite_arith_to_int_to_real2"

cvc5_rare "Extra_Rewrites.or_not_refl"

lemma temp: "((0 < - a) = (0 < - (b::real))) = ((0 > (a::real)) = (0 > b))"
  by simp

lemmas cvc_evaluate = of_rat_add of_rat_minus of_rat_diff of_rat_mult of_rat_divide of_rat_eq_iff
of_rat_divide nonzero_of_rat_divide of_rat_neg_numeral_eq temp

lemmas [alethe_poly_norm] =
  ab_group_add_class.minus_add_distrib
  add_uminus_conv_diff add.inverse_inverse
  uminus_add_conv_diff right_diff_distrib_numeral
  mult_minus_left distrib_left_numeral mult_num_simps add_num_simps
  numeral_mult[symmetric] minus_diff_eq of_int_diff of_int_numeral of_int_add
  of_int_mult of_int_numeral mult_minus_left of_int_1 add.inverse_neutral
  diff_0 minus_diff_eq add.left_neutral mult.left_neutral of_int_0 divide_minus_left
  times_divide_eq_left add_divide_distrib divide_eq_eq_numeral1 eq_numeral_simps
  if_True if_False distrib_right_numeral left_diff_distrib_numeral times_divide_eq_left
  of_int_neg_numeral ring_1_class.of_int_diff ring_1_class.of_int_numeral ring_1_class.of_int_mult
  mult_numeral_left_semiring_numeral mult_num_simps of_int_minus mult_minus_right times_divide_eq_right
  of_int_of_nat_eq diff_divide_distrib add.right_neutral diff_cancel mult_minus_right
  mult_zero_left mult_zero_right div_0 div_by_1 add_uminus_conv_diff numeral_times_numeral
  mult_numeral_left_semiring_numeral mult_num_simps mult_numeral_left uminus_add_conv_diff
   div_by_1 divide_numeral_1 divide_divide_eq_right neg_equal_iff_equal numeral_One divide_divide_eq_left
  divide_self_if if_True if_False one_neq_zero more_arith_simps
  division_ring_class.times_divide_eq_right divide_cancel_left

ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open>real_of_int (- 3 * (- 2 - (- (v0 + v1) + 1))) = 9 / 1 + - 3 / 1 * real_of_int v0 + - 3 / 1 * real_of_int v1\<close>}\<close>

ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open> real_of_int (- 2 * (v0 - (2 + - 1 * v1))) = 4 / 1 + - 2 / 1 * real_of_int v0 + - 2 / 1 * real_of_int v1\<close>}
\<close>

ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open> real_of_int (- 1 * (- 0 - (- v0 + 1))) = 1 / 1 + - 1 / 1 * real_of_int v0 \<close>}\<close>
ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open>- 1 / 2 * (y + (if 0 \<le> y then y else - y)) = - 1 / 2 * (y::real) + - 1 / 2 * (if 0 \<le> y then y else - y)\<close>}\<close>

ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open>real_of_int (- 4) = - 4\<close>}\<close>

thm alethe_poly_norm
ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open>3 / 2 * real_of_int (3 - 2 * x) = 9 / 2 + - 3 / 1 * real_of_int x\<close>}\<close>

ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open>3 / 1 * (real_of_int (- 1 * x) - - 3 / 2) = 9 / 2 + - 3 / 1 * real_of_int x \<close>}\<close>

ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open>- ((2 * real_of_int (int x) - 1) / 2) = 1 / 2 - real_of_int (int x)  \<close>}\<close>

ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open>d / 2 + 0 + 0 - (d::real) / 2 = 0\<close> }\<close>
ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open>1 / 1 * (2 / 1 * (1 / 1 / (2 / 1)) * (t1 / (1 / 1 / (2 / 1))) - 2 / 1 * (1 / 1 / (2 / 1) * ((t1::real) / (1 / 1 / (2 / 1))))) =
    2 / 1 * (1 / 1 / (2 / 1)) * (t1 / (1 / 1 / (2 / 1))) + - 2 / 1 * (1 / 1 / (2 / 1) * (t1 / (1 / 1 / (2 / 1)))) \<close>}\<close>

context
  fixes powr :: \<open>real \<Rightarrow> real \<Rightarrow> real\<close> (infix "powr" 80)
begin

declare [[simp_trace=false]]
ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open>(2::real) / 1 *
         (2 / 1 * (1 / 1 / (2 / 1)) * ((2 / 1) powr real_of_int p / (1 / 1 / (2 / 1))) +
          2 / 1 * (- 1 / 1 * (1 / 1 / (2 / 1)) * ((2 / 1) powr real_of_int p / (1 / 1 / (2 / 1)))) -
          0 / 1) =
         4 / 1 * (- 1 / 1 * (1 / 1 / (2 / 1)) * ((2 / 1) powr real_of_int p / (1 / 1 / (2 / 1)))) +
         2 / 1 * (2 / 1 * (1 / 1 / (2 / 1)) * ((2 / 1) powr real_of_int p / (1 / 1 / (2 / 1))))\<close>}\<close>
end
ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open>- v1 = - (Numeral1 * (v1::real) / Numeral1) \<close>}\<close>

ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open>1 / 1 * (t1 - - 1 / 1 * t2) = t1 + (t2::real)   \<close>}\<close>

declare [[simp_trace=false,simp_trace_depth_limit=3]]
ML \<open>
Alethe_Replay_RARE_Simplify_Methods.arith_poly_norm @{context}
@{term \<open>1 / 1 * ((t1::real) - 1 / 1 / t2) = t1 + - 1 / 1 * (1 / 1 / t2) \<close>}\<close>
end