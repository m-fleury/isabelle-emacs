theory SMT_CVC_Real
  imports "cvc5_dsl_rewrites/Extra_Rewrites" "HOL.Real"
begin

cvc5_rare "Extra_Rewrites.rewrite_ite_eq"
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

lemma temp: "((0 < - a) = (0 < - (b::real))) = ((0 > (a::real)) = (0 > b))"
  by simp

lemmas cvc_evaluate = of_rat_add of_rat_minus of_rat_diff of_rat_mult of_rat_divide of_rat_eq_iff
of_rat_divide nonzero_of_rat_divide of_rat_neg_numeral_eq temp
end