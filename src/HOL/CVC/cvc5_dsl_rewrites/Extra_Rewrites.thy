theory Extra_Rewrites
  imports "HOL.Real"
begin (*Since this needs real operators it is not included in RARE_interface*)

(*TODO: has nothing to do with reals should be moved?*)
named_theorems rewrite_ite_eq \<open>\<close>

lemma [rewrite_ite_eq]:
  fixes C::"bool" and t1::"'a::type" and t2::"'a::type"
  shows "NO_MATCH cvc_a (undefined C t1 t2) \<Longrightarrow> 
(if C then ((if C then t1 else t2) = t1)
      else ((if C then t1 else t2) = t2)) = True"
  by simp

named_theorems rewrite_quant_var_elim_eq \<open>\<close>

lemma [rewrite_quant_var_elim_eq]:
  fixes x::bool and y::"bool"
  shows "NO_MATCH cvc_a (undefined x y)
 \<Longrightarrow> ((\<forall>x. x \<noteq> t) = False)"
  by auto

named_theorems rewrite_arith_poly_norm_rel_leq \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_leq]:
  fixes x1::"'a::linordered_idom" and x2 and y1 and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<le> x2) = (y1 \<le> y2))) = True"
  by (metis (no_types, opaque_lifting) diff_gt_0_iff_gt linorder_not_le mult_le_0_iff mult_less_0_iff nle_le)

named_theorems rewrite_arith_poly_norm_rel_leq_left_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_leq_left_to_real]:
  fixes x1::"int" and x2::"int" and y1::"real" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (of_int (x1 - x2)::real)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<le> x2) = (y1 \<le> y2))) = True"
  by (metis diff_gt_0_iff_gt linorder_not_le mult_less_0_iff not_less_iff_gr_or_eq of_int_0_less_iff zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_leq_right_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_leq_right_to_real]:
  fixes x1::"real" and x2::"real" and y1::"int" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy *  (of_int (y1 - y2)::real))) \<longrightarrow> ((x1 \<le> x2) = (y1 \<le> y2))) = True"
  by (metis diff_gt_0_iff_gt linorder_not_le mult_less_0_iff not_less_iff_gr_or_eq of_int_0_less_iff zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_leq_both_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_leq_both_to_real]:
  fixes x1::"int" and x2::"int" and y1::"int" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (of_int (x1 - x2))) = (cy *  (of_int (y1 - y2)::real))) \<longrightarrow> ((x1 \<le> x2) = (y1 \<le> y2))) = True"
  by (metis diff_gt_0_iff_gt linorder_not_le mult_less_0_iff not_less_iff_gr_or_eq of_int_0_less_iff zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_geq \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_geq]:
  fixes x1::"'a::linordered_idom" and x2 and y1 and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<Longrightarrow>  cx \<noteq>0 \<Longrightarrow>  cy \<noteq>0 \<Longrightarrow> 
(((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<ge> x2) = (y1 \<ge> y2))) = True"
  by (metis eq_iff_diff_eq_0 linorder_linear mult_eq_0_iff order_antisym_conv rewrite_arith_poly_norm_rel_leq)

named_theorems rewrite_arith_poly_norm_rel_geq_left_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_geq_left_to_real]:
  fixes x1::"int" and x2::"int" and y1::"real" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (of_int (x1 - x2)::real)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<ge> x2) = (y1 \<ge> y2))) = True"
  by (metis diff_ge_0_iff_ge linorder_not_le mult_less_0_iff not_less_iff_gr_or_eq of_int_less_0_iff zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_geq_right_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_geq_right_to_real]:
  fixes x1::"real" and x2::"real" and y1::"int" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy *  (of_int (y1 - y2)::real))) \<longrightarrow> ((x1 \<ge> x2) = (y1 \<ge> y2))) = True"
  by (metis diff_ge_0_iff_ge linorder_not_le mult_less_0_iff not_less_iff_gr_or_eq of_int_less_0_iff zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_geq_both_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_geq_both_to_real]:
  fixes x1::"int" and x2::"int" and y1::"int" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (of_int (x1 - x2))) = (cy *  (of_int (y1 - y2)::real))) \<longrightarrow> ((x1 \<ge> x2) = (y1 \<ge> y2))) = True"
  by (metis diff_ge_0_iff_ge linorder_not_le mult_less_0_iff not_less_iff_gr_or_eq of_int_less_0_iff zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_gt \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_gt]:
  fixes x1::"'a::linordered_idom" and x2 and y1 and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 > x2) = (y1 > y2))) = True"
  by (metis diff_gt_0_iff_gt mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_gt_left_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_gt_left_to_real]:
  fixes x1::"int" and x2::"int" and y1::"real" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (of_int (x1 - x2)::real)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 > x2) = (y1 > y2))) = True"
  by (metis le_iff_diff_le_0 linorder_not_le mult_less_0_iff nless_le of_int_le_0_iff zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_gt_right_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_gt_right_to_real]:
  fixes x1::"real" and x2::"real" and y1::"int" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy *  (of_int (y1 - y2)::real))) \<longrightarrow> ((x1 > x2) = (y1 > y2))) = True"
  by (metis le_iff_diff_le_0 linorder_not_le mult_less_0_iff nless_le of_int_le_0_iff zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_gt_both_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_gt_both_to_real]:
  fixes x1::"int" and x2::"int" and y1::"int" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (of_int (x1 - x2))) = (cy *  (of_int (y1 - y2)::real))) \<longrightarrow> ((x1 > x2) = (y1 > y2))) = True"
  by (metis le_iff_diff_le_0 linorder_not_le mult_less_0_iff nless_le of_int_le_0_iff zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_lt \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_lt]:
  fixes x1::"'a::linordered_idom" and x2 and y1 and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 < x2) = (y1 < y2))) = True"
  apply (rule impI)+
  by (metis less_iff_diff_less_0 mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_lt_left_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_lt_left_to_real]:
  fixes x1::"int" and x2::"int" and y1::"real" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (of_int (x1 - x2)::real)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 < x2) = (y1 < y2))) = True"
  by (metis less_iff_diff_less_0 mult_less_0_iff not_less_iff_gr_or_eq of_int_less_0_iff zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_lt_right_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_lt_right_to_real]:
  fixes x1::"real" and x2::"real" and y1::"int" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy *  (of_int (y1 - y2)::real))) \<longrightarrow> ((x1 < x2) = (y1 < y2))) = True"
  by (metis less_iff_diff_less_0 mult_less_0_iff not_less_iff_gr_or_eq of_int_less_0_iff zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_lt_both_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_lt_both_to_real]:
  fixes x1::"int" and x2::"int" and y1::"int" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (of_int (x1 - x2))) = (cy *  (of_int (y1 - y2)::real))) \<longrightarrow> ((x1 < x2) = (y1 < y2))) = True"
  by (metis less_iff_diff_less_0 mult_less_0_iff not_less_iff_gr_or_eq of_int_less_0_iff zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_equal \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_equal]:
  fixes x1::"'a::linordered_idom" and x2 and y1 and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 = x2) = (y1 = y2))) = True"
  apply (rule impI)+
  by auto

named_theorems rewrite_arith_poly_norm_rel_equal_left_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_equal_left_to_real]:
  fixes x1::"int" and x2::"int" and y1::"real" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (of_int (x1 - x2)::real)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 = x2) = (y1 = y2))) = True"
  by force

named_theorems rewrite_arith_poly_norm_rel_equal_right_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_equal_right_to_real]:
  fixes x1::"real" and x2::"real" and y1::"int" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy *  (of_int (y1 - y2)::real))) \<longrightarrow> ((x1 = x2) = (y1 = y2))) = True"
  by force

named_theorems rewrite_arith_poly_norm_rel_equal_both_to_real \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_equal_both_to_real]:
  fixes x1::"int" and x2::"int" and y1::"int" and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (of_int (x1 - x2))) = (cy *  (of_int (y1 - y2)::real))) \<longrightarrow> ((x1 = x2) = (y1 = y2))) = True"
  by force

named_theorems rewrite_arith_to_int_to_real \<open>\<close>

lemma [rewrite_arith_to_int_to_real]:
  fixes x::"int"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> floor (of_int x ::real) = x"
  by simp

named_theorems rewrite_arith_to_real_distrib_uminus \<open>\<close>

lemma [rewrite_arith_to_real_distrib_uminus]:
  fixes x::"int"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> -(of_int x ::real) = (of_int (-x) ::real)"
  by simp

named_theorems rewrite_arith_to_real_distrib_add \<open>\<close>

lemma [rewrite_arith_to_real_distrib_add]:
  fixes x::"int" and y::"int"
  shows "NO_MATCH cvc_a (undefined (x,y)) \<Longrightarrow> (of_int (x + y) ::real) = (of_int x ::real) + (of_int y ::real)"
  by simp

named_theorems rewrite_arith_to_real_distrib_minus \<open>\<close>

lemma [rewrite_arith_to_real_distrib_minus]:
  fixes x::"int" and y::"int"
  shows "NO_MATCH cvc_a (undefined (x,y)) \<Longrightarrow> (of_int (x - y) ::real) = (of_int x ::real) - (of_int y ::real)"
  by simp

named_theorems rewrite_arith_to_real_distrib_mult \<open>\<close>

lemma [rewrite_arith_to_real_distrib_mult]:
  fixes x::"int" and y::"int"
  shows "NO_MATCH cvc_a (undefined (x,y)) \<Longrightarrow> (of_int (x * y) ::real) = (of_int x ::real) * (of_int y ::real)"
  by simp


named_theorems rewrite_arith_distrib_add \<open>\<close>

lemma temp2:
  fixes x::"'a::{ab_group_add}" and  y::"'a::{ab_group_add}" and xss::"'a ::{ab_group_add} list"
  shows "foldr (+) xss 0 + x = foldr (+) xss x"
  apply (induction xss)
   apply simp
  by simp

lemma [rewrite_arith_distrib_add]:
  fixes x::"'a::{ab_group_add}" and xs::"'a::{ab_group_add} cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined x xs)
 \<Longrightarrow> ((cvc_list_left (+) xs 0) + x) = (cvc_list_left (+) xs x)"
  apply (cases xs)
  subgoal for xss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (simp add: temp2[of xss x])
    done
  done

(*
named_theorems rewrite_arith_distrib_add \<open>\<close>

lemma temp2:
  fixes x::"'a::{ab_group_add}" and  y::"'a::{ab_group_add}" and xss::"'a ::{ab_group_add} list"
  shows "foldr (+) xss x + y = foldr (+) xss (x + y)"
  apply (induction xss)
   apply simp
  by simp

lemma [rewrite_arith_distrib_add]:
  fixes x::"'a::{ab_group_add}" and y::"'a::{ab_group_add}" and xs::"'a::{ab_group_add} cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined x y xs)
 \<Longrightarrow> ((cvc_list_left (+) xs x) + y) = (cvc_list_left (+) xs (x + y))"
  apply (cases xs)
  subgoal for xss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (simp add: temp2)
    done
  done
*)

named_theorems rewrite_arith_distrib_mult \<open>\<close>

lemma temp3:
  fixes x::"'a::{ring}" and  y::"'a::{ring}" and xss::"'a ::{ring} list"
  shows "foldr (*) xss x * y = foldr (*) xss (x * y)"
  apply (induction xss)
   apply simp
  by (simp add: mult.assoc)

lemma [rewrite_arith_distrib_mult]:
  fixes x::"'a::{ring}"  and  y::"'a::{ring}" and xs::"'a::{ring} cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined x xs)
 \<Longrightarrow> ((cvc_list_left (*) xs x) * y) = (cvc_list_left (*) xs (x * y))"
  apply (cases xs)
  subgoal for xss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (simp add: temp3[of xss x y])
    done
  done

named_theorems rewrite_arith_to_real_distrib_uminus_rev \<open>\<close>

lemma [rewrite_arith_to_real_distrib_uminus_rev]:
  fixes t::int
  shows "NO_MATCH cvc_a (undefined t)
 \<Longrightarrow> ((of_int (-t) ::real) = -(of_int t))"
  by auto


named_theorems rewrite_arith_geq_norm1_real \<open>\<close> (*TODO: Find examples*)

lemma [rewrite_arith_geq_norm1_real]:
  fixes t::"real"  and  s::"real" 
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((t \<ge> s) = ((t - s) \<ge> 0/1))"
  by simp

named_theorems rewrite_arith_geq_norm2 \<open>\<close>

lemma [rewrite_arith_geq_norm2]:
  fixes t::"'a::linordered_idom"  and  s::"'a::linordered_idom" 
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((t \<ge> s) = (-t \<le> -s))"
  by simp

named_theorems rewrite_arith_eq_elim_real \<open>\<close>

lemma [rewrite_arith_eq_elim_real]:
  fixes t::"'a::linordered_idom"  and  s::"'a::linordered_idom" 
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((t = s) = (t \<ge> s \<and> t \<le> s))"
  by auto

named_theorems rewrite_arith_to_int_elim_to_real \<open>\<close>

lemma [rewrite_arith_to_int_elim_to_real]:
  fixes x::int
  shows "NO_MATCH cvc_a (undefined x)
 \<Longrightarrow> (floor (of_int x ::real) = floor x)"
  by auto

named_theorems rewrite_arith_div_elim_to_real1 \<open>\<close>

lemma [rewrite_arith_div_elim_to_real1]:
  fixes x::int and y::real
  shows "NO_MATCH cvc_a (undefined x y)
 \<Longrightarrow> (((of_int x ::real) / y) = (x / y))"
  by auto

named_theorems rewrite_arith_div_elim_to_real2 \<open>\<close>

lemma [rewrite_arith_div_elim_to_real2]:
  fixes x::real and y::int
  shows "NO_MATCH cvc_a (undefined x y)
 \<Longrightarrow> ((x / (of_int y ::real)) = (x / y))"
  by auto

named_theorems rewrite_arith_int_eq_conflict \<open>\<close>

lemma [rewrite_arith_int_eq_conflict]:
  fixes t::int and c::real
  shows "NO_MATCH cvc_a (undefined t c)
 \<Longrightarrow> \<not>((of_int (floor c)::real) = c) \<Longrightarrow> (((of_int t ::real) = c) = False)"
  by auto

named_theorems rewrite_arith_int_geq_tighten \<open>\<close>

lemma [rewrite_arith_int_geq_tighten]:
  fixes t::int and c::real and cc::int
  shows "NO_MATCH cvc_a (undefined t c cc)
 \<Longrightarrow> (\<not>((of_int (floor c)) = c) \<and> (cc = (floor c) + 1)) \<Longrightarrow> (((of_int t ::real) \<ge> c) = (t \<ge> cc))"
  by linarith

named_theorems rewrite_arith_geq_ite_lift \<open>\<close>

lemma [rewrite_arith_geq_ite_lift]:
  fixes c::real and t::"'a::linordered_idom" and r::"'a::linordered_idom" and s::"'a::linordered_idom"  
  shows "NO_MATCH cvc_a (undefined C t s r)
 \<Longrightarrow> (((if C then t else s) \<ge> r) = (if C then (t \<ge> r) else (s \<ge> r)))"
  by auto

named_theorems rewrite_arith_gt_ite_lift \<open>\<close>

lemma [rewrite_arith_geq_ite_lift]:
  fixes c::real and t::"'a::linordered_idom" and r::"'a::linordered_idom" and s::"'a::linordered_idom"  
  shows "NO_MATCH cvc_a (undefined C t s r)
 \<Longrightarrow> (((if C then t else s) > r) = (if C then (t > r) else (s > r)))"
  by auto

named_theorems rewrite_arith_leq_ite_lift \<open>\<close>

lemma [rewrite_arith_leq_ite_lift]:
  fixes c::real and t::"'a::linordered_idom" and r::"'a::linordered_idom" and s::"'a::linordered_idom"  
  shows "NO_MATCH cvc_a (undefined C t s r)
 \<Longrightarrow> (((if C then t else s) \<le> r) = (if C then (t \<le> r) else (s \<le> r)))"
  by auto

named_theorems rewrite_arith_lt_ite_lift \<open>\<close>

lemma [rewrite_arith_leq_ite_lift]:
  fixes c::real and t::"'a::linordered_idom" and r::"'a::linordered_idom" and s::"'a::linordered_idom"  
  shows "NO_MATCH cvc_a (undefined C t s r)
 \<Longrightarrow> (((if C then t else s) < r) = (if C then (t < r) else (s < r)))"
  by auto


named_theorems rewrite_or_not_refl_empty \<open>added in postprocessing\<close>
(* (define-rule or-not-refl-empty ((t ?) (x Bool)) (or (not (= t t)) x) x) *)

lemma [rewrite_or_not_refl_empty]:
  fixes t::'a and x::bool
  shows "NO_MATCH cvc_a (undefined t x) \<Longrightarrow> (\<not>(t = t) \<or> x) = x"
  by simp


named_theorems rewrite_or_not_refl \<open>added in postprocessing\<close>
(* (define-rule or-not-refl ((t ?) (x Bool) (xs Bool :list) (or (not (= t t)) x xs) (or x xs)) *)

lemma [rewrite_or_not_refl]:
  fixes t::'a and xs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined t x xs) \<Longrightarrow>  
   ((\<not>(t = t)) \<or> (cvc_list_right (\<or>) x xs)) = (cvc_list_right (\<or>) x xs)"
  by simp


(*Performance addition*)
named_theorems rewrite_arith_to_int_to_real2 \<open>\<close>
lemmas [rewrite_arith_to_int_to_real2] = floor_of_int
end