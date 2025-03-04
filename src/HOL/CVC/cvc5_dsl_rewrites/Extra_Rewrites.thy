theory Extra_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops" "HOL.Real" "HOL-CVC.Dsl_Nary_Ops"
begin (*Since this needs real operators it is not included in RARE_interface*)

(*TODO: has nothing to do with reals should be moved?*)
named_theorems rewrite_ite_eq \<open>\<close>

lemma [rewrite_ite_eq]:
  fixes C::"bool" and t1::"'a::type" and t2::"'a::type"
  shows "NO_MATCH cvc_a (undefined C t1 t2) \<Longrightarrow> 
(if C then ((if C then t1 else t2) = t1)
      else ((if C then t1 else t2) = t2)) = True"
  by simp

named_theorems rewrite_arith_poly_norm_rel_leq \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_leq]:
  fixes x1::"'a::linordered_idom" and x2 and y1 and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<le> x2) = (y1 \<le> y2))) = True"
  by (metis (no_types, opaque_lifting) diff_gt_0_iff_gt linorder_not_le mult_le_0_iff mult_less_0_iff nle_le)

named_theorems rewrite_arith_poly_norm_rel_geq \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_geq]:
  fixes x1::"'a::linordered_idom" and x2 and y1 and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<Longrightarrow>  cx \<noteq>0 \<Longrightarrow>  cy \<noteq>0 \<Longrightarrow> 
(((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 \<ge> x2) = (y1 \<ge> y2))) = True"
  by (metis eq_iff_diff_eq_0 linorder_linear mult_eq_0_iff order_antisym_conv rewrite_arith_poly_norm_rel_leq)

named_theorems rewrite_arith_poly_norm_rel_gt \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_gt]:
  fixes x1::"'a::linordered_idom" and x2 and y1 and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 > x2) = (y1 > y2))) = True"
  by (metis diff_gt_0_iff_gt mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_lt \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_lt]:
  fixes x1::"'a::linordered_idom" and x2 and y1 and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> ((cx > 0) = (cy > 0)) \<longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 < x2) = (y1 < y2))) = True"
  apply (rule impI)+
  by (metis less_iff_diff_less_0 mult_less_0_iff not_less_iff_gr_or_eq zero_less_mult_iff)

named_theorems rewrite_arith_poly_norm_rel_equal \<open>\<close>

lemma [rewrite_arith_poly_norm_rel_equal]:
  fixes x1::"'a::linordered_idom" and x2 and y1 and y2 and cx and cy
  shows "NO_MATCH cvc_a (undefined cx cy x1 x2 y1 y2) \<Longrightarrow> cx \<noteq>0 \<longrightarrow> cy \<noteq>0 \<longrightarrow> 
(((cx * (x1 - x2)) = (cy * (y1 - y2))) \<longrightarrow> ((x1 = x2) = (y1 = y2))) = True"
  apply (rule impI)+
  by auto

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


end