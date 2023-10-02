theory Arith_Rewrites
  imports Dsl_Nary_Ops "HOL.Real"
begin

(* This is a theory automatically created from a rare file! All that remains to do is to prove
any lemma whose provided proof fails and to to import this file in SMT.thy. 
If your rare statements use nary operators over lists that would be binarised by Isabelle 
you have to add it in Dsl_Nary_Ops.thy. Currently already supported are the operators:
and,
or,
plus,
times,
append,
re_concat,
str_concat,
*)

named_theorems rewrite_arith_plus_zero \<open>automatically_generated\<close>

lemma [rewrite_arith_plus_zero]:
  fixes t::"int cvc_ListVar" and s::"int cvc_ListVar"
  shows "cvc_list_right (+) (cvc_list_left (+) t (0::int)) s =
   cvc_list_both (+) (0::int) t s"
  apply (cases s)
  apply (cases t)
  subgoal for ss ts 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction ts arbitrary: t)
    by simp_all
  done

named_theorems rewrite_arith_mul_one \<open>automatically_generated\<close>

lemma [rewrite_arith_mul_one]:
  fixes t::"int cvc_ListVar" and s::"int cvc_ListVar"
  shows "cvc_list_right (*) (cvc_list_left (*) t (1::int)) s =
   cvc_list_both (*) (1::int) t s"
  apply (cases s)
  apply (cases t)
  subgoal for ss ts 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction ts arbitrary: t)
    by simp_all
  done

named_theorems rewrite_arith_mul_zero \<open>automatically_generated\<close>

lemma [rewrite_arith_mul_zero]:
  fixes t::"int cvc_ListVar" and s::"int cvc_ListVar"
  shows "cvc_list_right (*) (cvc_list_left (*) t (0::int)) s = (0::int)"
  apply (cases s)
  apply (cases t)
  subgoal for ss ts 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction ts arbitrary: t)
    by simp_all
  done

named_theorems rewrite_arith_neg_neg_one \<open>automatically_generated\<close>

lemma [rewrite_arith_neg_neg_one]:
  fixes t::"nat"
  shows "- (1::int) * (- (1::int) * t) = t"
  by auto

named_theorems rewrite_arith_elim_uminus \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_uminus]:
  fixes t::"int"
  shows "- t = - (1::int) * t"
  by auto

named_theorems rewrite_arith_elim_minus \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_minus]:
  fixes t::"int" and s::"int"
  shows "t - s = t + - (1::int) * s"
  by auto

named_theorems rewrite_arith_elim_gt \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_gt]:
  fixes t::"'a::linorder" and s::"'a::linorder"
  shows "(s < t) = (\<not> t \<le> s)"
  using linorder_not_less by blast

named_theorems rewrite_arith_elim_lt \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_lt]:
  fixes t::"'a::linorder" and s::"'a::linorder"
  shows "(t < s) = (\<not> s \<le> t)"
    using linorder_not_less by blast


named_theorems rewrite_arith_elim_leq \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_leq]:
  fixes t::"'a::ord" and s::"'a::ord"
  shows "(t \<le> s) = (t \<le> s)"
  by auto

named_theorems rewrite_arith_leq_norm \<open>automatically_generated\<close>

lemma [rewrite_arith_leq_norm]:
  fixes t::"int" and s::"int"
  shows "(t \<le> s) = (\<not> s + (1::int) \<le> t)"
  by auto

named_theorems rewrite_arith_geq_tighten \<open>automatically_generated\<close>

lemma [rewrite_arith_geq_tighten]:
  fixes t::"int" and s::"int"
  shows "(\<not> s \<le> t) = (t + (1::int) \<le> s)"
  by auto

named_theorems rewrite_arith_geq_norm \<open>automatically_generated\<close>

lemma [rewrite_arith_geq_norm]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH a (undefined t s) ==> (s \<le> t) = ((0::int) \<le> t - s)"
  by auto

named_theorems rewrite_arith_refl_leq \<open>automatically_generated\<close>

lemma [rewrite_arith_refl_leq]:
  fixes t::"'a::linorder"
  shows "(t \<le> t) = True"
  by auto

named_theorems rewrite_arith_refl_lt \<open>automatically_generated\<close>

lemma [rewrite_arith_refl_lt]:
  fixes t::"'a::linorder"
  shows "(t < t) = False"
  by auto

named_theorems rewrite_arith_refl_geq \<open>automatically_generated\<close>

lemma [rewrite_arith_refl_geq]:
  fixes t::"'a::linorder"
  shows "(t \<le> t) = True"
  by auto

named_theorems rewrite_arith_refl_gt \<open>automatically_generated\<close>

lemma [rewrite_arith_refl_gt]:
  fixes t::"'a::linorder"
  shows "(t < t) = False"
  by auto

named_theorems rewrite_arith_plus_flatten \<open>automatically_generated\<close>

lemma [rewrite_arith_plus_flatten]:
  fixes xs::"'a::linordered_ab_group_add cvc_ListVar" and w::"'a::linordered_ab_group_add" and ys::"'a::linordered_ab_group_add cvc_ListVar" and zs::"'a::linordered_ab_group_add cvc_ListVar"
  shows "cvc_list_right (+) (cvc_list_left (+) xs (cvc_list_right (+) w ys)) zs =
   cvc_list_right (+) (cvc_list_right (+) (cvc_list_left (+) xs w) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction xss arbitrary: xs)
    by simp_all
  done

named_theorems rewrite_arith_mult_flatten \<open>automatically_generated\<close>

lemma [rewrite_arith_mult_flatten]:
  fixes xs::"'a::ab_semigroup_mult cvc_ListVar" and w::"'a::ab_semigroup_mult" and ys::"'a::ab_semigroup_mult cvc_ListVar" and zs::"'a::ab_semigroup_mult cvc_ListVar"
  shows "cvc_list_right (*) (cvc_list_left (*) xs (cvc_list_right (*) w ys)) zs =
   cvc_list_right (*) (cvc_list_right (*) (cvc_list_left (*) xs w) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (simp add: cvc_list_right_Nil)
     apply (induction zss arbitrary: zs)
    apply (simp add: cvc_list_right_Nil cvc_list_right_transfer mult.assoc)
     apply (simp add: ab_semigroup_mult_class.mult_ac(1) cvc_list_right_Cons)
    by (simp add: cvc_list_right_Cons mult.assoc)
  done

named_theorems rewrite_arith_mult_dist \<open>automatically_generated\<close>

lemma [rewrite_arith_mult_dist]:
  fixes x::"'a::{ring}" and y::"'a" and z::"'a" and w::"'a cvc_ListVar"
  shows "x * cvc_list_right (+) (y + z) w = x * y + x * cvc_list_right (+) z w"
  apply (cases w)
  subgoal for ws 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction ws arbitrary: w)
     apply simp_all
    unfolding cvc_list_right_def
     apply (simp add: ring_class.ring_distribs(1))
    by (simp add: ring_class.ring_distribs(1))
  done

named_theorems rewrite_arith_plus_cancel1 \<open>automatically_generated\<close>

lemma [rewrite_arith_plus_cancel1]:
  fixes t::"('a::{zero,plus,one,times,uminus}) cvc_ListVar" and x::"'a::{zero,plus,one,times,uminus}" and s::"'a::{zero,plus,one,times,uminus} cvc_ListVar" 
and r::"'a::{zero,plus,one,times,uminus} cvc_ListVar"
  shows "cvc_list_right (+)
    (cvc_list_right (+) (cvc_list_left (+) t x) s + - 1 * x) r =
   cvc_list_right (+) (cvc_list_both (+) 0 t s) r"
  apply (cases r)
  apply (cases s)
  apply (cases t)
  subgoal for rs ss ts 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction rs)
     apply simp_all
    apply (induction ts)
     apply simp_all
    apply (induction ss)
     apply simp_all
    
    sorry
  done

named_theorems rewrite_arith_plus_cancel2 \<open>automatically_generated\<close>

lemma [rewrite_arith_plus_cancel2]:
  fixes t::"int cvc_ListVar" and x::"int" and s::"int cvc_ListVar" and r::"int cvc_ListVar"
  shows "cvc_list_right (+)
    (cvc_list_right (+) (cvc_list_left (+) t (- (1::int) * x)) s + x) r =
   cvc_list_right (+) (cvc_list_both (+) (0::int) t s) r"
  apply (cases r)
  apply (cases s)
  apply (cases t)
  subgoal for rs ss ts 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    sorry
  done

end