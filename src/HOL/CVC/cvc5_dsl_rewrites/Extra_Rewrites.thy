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


named_theorems rewrite_arith_abs_real_gt \<open>\<close>

lemma [rewrite_arith_abs_real_gt]:
  fixes x::"real" and y::"real"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> 
(abs x > abs y) =
 (if (x \<ge> 0/1) then
   (if (y \<ge> 0/1) then (x > y) else (x > -y))
 else
   (if (y \<ge> 0/1) then (-x > y) else (-x > -y)))"
  by simp


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

named_theorems rewrite_arith_to_int_elim \<open>\<close>

lemma [rewrite_arith_to_int_elim]:
  fixes x::int
  shows "NO_MATCH cvc_a (undefined x)
 \<Longrightarrow> floor x = x"
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

(*
(define-rule arith-min-lt1 ((t ?) (s ?))
  (<= (ite (< t s) t s) t)
  true)
*)
named_theorems rewrite_arith_min_lt1 \<open>\<close>

lemma [rewrite_arith_min_lt1]:
  fixes t::"'a::linordered_idom" and s::"'a::linordered_idom"  
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((if (t < s) then t else s) \<le> t) = True"
  by auto

named_theorems rewrite_arith_min_lt2 \<open>\<close>

lemma [rewrite_arith_min_lt2]:
  fixes t::"'a::linordered_idom" and s::"'a::linordered_idom"  
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((if (t < s) then t else s) \<le> s) = True"
  by auto

named_theorems rewrite_arith_max_geq2 \<open>\<close>

lemma [rewrite_arith_max_geq2]:
  fixes t::"'a::linordered_idom" and s::"'a::linordered_idom"  
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((if (t \<ge> s) then t else s) \<ge> s) = True"
  by auto


named_theorems rewrite_or_not_refl_empty \<open>added in postprocessing\<close>
(* (define-rule or-not-refl-empty ((t ?) (x Bool)) (or (not (= t t)) x) x) *)

lemma [rewrite_or_not_refl_empty]:
  fixes t::'a and x::bool
  shows "NO_MATCH cvc_a (undefined t x) \<Longrightarrow> (\<not>(t = t) \<or> x) = x"
  by simp


named_theorems rewrite_or_not_refl \<open>added in postprocessing\<close>
(* (define-rule or-not-refl ((t ?) (x Bool) (xs Bool :list) (or (not (= t t)) xs) (or xs))) *)

lemma [rewrite_or_not_refl]:
  fixes t::'a and xs::"bool cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined t xs) \<Longrightarrow>
   ((\<not>(t = t)) \<or> (cvc_list_right (\<or>) x xs)) = (cvc_list_right (\<or>) x xs)"
  by simp

(*Alethe proofs produced by cvc5 only. Can be moved before reals*)
(*TODO: We hardcoded to use simp for this*)
named_theorems rewrite_distinct_false \<open>added in postprocessing\<close>



(*Performance addition*)
named_theorems rewrite_arith_to_int_to_real2 \<open>\<close>
lemmas [rewrite_arith_to_int_to_real2] = floor_of_int
end
