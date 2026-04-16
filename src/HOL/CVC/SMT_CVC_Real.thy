theory SMT_CVC_Real
  imports "cvc5_dsl_rewrites/Rare_Interface_Real" "HOL.Real"
begin

cvc5_rare "Rare_Interface_Real.rewrite_arith_geq_norm1_real"
cvc5_rare "Rare_Interface_Real.rewrite_arith_eq_elim_real"
cvc5_rare "Rare_Interface_Real.rewrite_arith_to_int_to_real"
cvc5_rare "Rare_Interface_Real.rewrite_arith_int_eq_conflict"
cvc5_rare "Rare_Interface_Real.rewrite_arith_int_geq_tighten"
cvc5_rare "Rare_Interface_Real.rewrite_arith_geq_ite_lift"
cvc5_rare "Rare_Interface_Real.rewrite_arith_leq_ite_lift"



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

(*TODO: These could be organized better to make sure we are not missing any*)
lemma [alethe_poly_simp_rel]:
  fixes x1::"real" and x2 y1 y2 cx cy
  shows "cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 = x2) = (y1 = y2))"
  by force

lemma [alethe_poly_simp_rel]:
  fixes x1::"real" and x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 < x2) = (y1 < y2))"
  by (metis less_iff_diff_less_0 mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1::"real" and x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<le> x2) = (y1 \<le> y2))"
  by (metis diff_gt_0_iff_gt linorder_not_le mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1::"real" and x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 > x2) = (y1 > y2))"
  by (metis le_iff_diff_le_0 linorder_not_le mult_less_0_iff nless_le zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1::"real" and x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<ge> x2) = (y1 \<ge> y2))"
  by (metis diff_ge_0_iff_ge linorder_not_le mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1 and x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * real_of_int (x1 - x2)) = (cy * ((real_of_int y1) - (real_of_int y2)))) \<longrightarrow> ((x1 \<le> x2) = (real_of_int y1 \<le> real_of_int y2))"
  apply (cases "x1 \<le> x2")
   apply (cases "(0 < cx)")
    apply simp_all
    apply (metis le_iff_diff_le_0 mult_le_cancel_left mult_zero_right not_less_iff_gr_or_eq of_int_le_iff)
  apply (metis diff_ge_0_iff_ge eq_iff_diff_eq_0 linorder_not_le mult_zero_right no_zero_divisors of_int_diff of_int_less_0_iff order_le_less zero_less_mult_iff)
  by (metis (no_types, opaque_lifting) cvc_arith_rewrite_defs(5) diff_gt_0_iff_gt mult_less_0_iff not_less_iff_gr_or_eq of_int_less_iff zero_less_mult_iff)
  
lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * real_of_int (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<ge> x2) = ((real_of_int y1) \<ge> (real_of_int y2)))"
  apply (cases "x1 \<ge> x2")
   apply (cases "(0 < cx)")
  apply (metis diff_ge_0_iff_ge dual_order.strict_iff_not of_int_0_le_iff of_int_diff zero_le_mult_iff)
   apply (metis cvc_arith_rewrite_defs(5) less_iff_diff_less_0 of_int_diff of_int_less_0_iff order_le_less zero_less_mult_iff)
  apply simp
  by (metis cvc_arith_rewrite_defs(5) less_iff_diff_less_0 mult_less_0_iff of_int_less_iff order_le_less zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (real_of_int (x1 - x2))) = (cy * ((real_of_int y1) - (real_of_int y2)))) \<longrightarrow> ((x1 < x2) = ((real_of_int y1) < (real_of_int y2)))"
  by (metis less_iff_diff_less_0 mult_less_0_iff not_less_iff_gr_or_eq of_int_less_0_iff zero_less_mult_iff)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (real_of_int (x2 - x1))) = (cy * ((real_of_int y2) - y1))) \<longrightarrow> ((x1 \<le> x2) = (y1 \<le> (real_of_int y2)))"
  apply (cases "x1 \<le> x2")
   apply (case_tac [!] "(0 < cx)")
    apply simp_all
  apply (metis diff_ge_0_iff_ge mult.commute mult_left_le_imp_le mult_zero_left of_int_0_le_iff of_int_diff split_mult_pos_le zero_le_square)
   apply (metis cvc_arith_rewrite_defs(5) diff_ge_0_iff_ge mult_le_0_iff of_int_0_le_iff of_int_diff order_le_less)
   apply (metis (no_types, lifting) diff_ge_0_iff_ge linorder_not_less mult_eq_0_iff mult_le_0_iff nle_le of_int_le_iff)
   by (metis diff_ge_0_iff_ge leI mult_le_0_iff of_int_le_iff order_antisym_conv)

lemma [alethe_poly_simp_rel]:
  fixes x1 x2 y1 y2 cx cy
  shows "((cx > 0) = (cy > 0)) \<Longrightarrow> cx \<noteq> 0 \<Longrightarrow> cy \<noteq> 0 \<Longrightarrow>
((cx * (real_of_int (x1 - x2))) = (cy * ((real_of_int y1) - (real_of_int y2)))) \<longrightarrow> ((x1 = x2) = ((real_of_int y1) = (real_of_int y2)))"
  by auto

end