theory Arith_Rewrites
  imports "Arith_Rewrites_Lemmas"
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)


named_theorems rewrite_arith_elim_gt \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_gt]:
  fixes t::"'a::linorder" and s::"'a::linorder"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (s < t) = (\<not> t \<le> s)"
  by auto


named_theorems rewrite_arith_elim_lt \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_lt]:
  fixes t::"'a::linorder" and s::"'a::linorder"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t < s) = (\<not> s \<le> t)"
  by auto


named_theorems rewrite_arith_elim_int_gt \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_int_gt]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t > s) = (t \<ge> (s+1))"
  by auto


named_theorems rewrite_arith_elim_int_lt \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_int_lt]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t < s) = (s \<ge> (t+1))"
  by auto


named_theorems rewrite_arith_elim_leq \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_leq]:
  fixes t::"'a::linorder" and s::"'a::linorder"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t \<le> s) = (t \<le> s)"
  by auto


named_theorems rewrite_arith_leq_norm \<open>automatically_generated\<close>

lemma [rewrite_arith_leq_norm]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t \<le> s) = (\<not> s + (1::int) \<le> t)"
  by auto


named_theorems rewrite_arith_geq_tighten \<open>automatically_generated\<close>

lemma [rewrite_arith_geq_tighten]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (\<not> s \<le> t) = (t + (1::int) \<le> s)"
  by auto


named_theorems rewrite_arith_geq_norm1_int \<open>automatically_generated\<close>

lemma [rewrite_arith_geq_norm1_int]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (s \<le> t) = ((0::int) \<le> t - s)"
  by auto


(*rewrite_arith_geq_norm1_real is in Extra_Rewrites*)



named_theorems rewrite_arith_refl_leq \<open>automatically_generated\<close>

lemma [rewrite_arith_refl_leq]:
  fixes t::"'a::linorder"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t \<le> t) = True"
  by auto


named_theorems rewrite_arith_refl_lt \<open>automatically_generated\<close>

lemma [rewrite_arith_refl_lt]:
  fixes t::"'a::linorder"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t < t) = False"
  by auto


named_theorems rewrite_arith_refl_geq \<open>automatically_generated\<close>

lemma [rewrite_arith_refl_geq]:
  fixes t::"'a::linorder"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t \<le> t) = True"
  by auto


named_theorems rewrite_arith_refl_gt \<open>automatically_generated\<close>

lemma [rewrite_arith_refl_gt]:
  fixes t::"'a::linorder"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t < t) = False"
  by auto


named_theorems rewrite_arith_eq_elim_int \<open>automatically_generated\<close>

lemma [rewrite_arith_eq_elim_int]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((t = s) = (t \<ge> s \<and> t \<le> s))"
  by auto


named_theorems rewrite_arith_abs_eq \<open>\<close>

lemma [rewrite_arith_abs_eq]:
  fixes x::"int" and y::"int"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (abs x = abs y) = ((x = y) \<or> (x = -y))"
  apply simp
  by (simp add: abs_eq_iff)


named_theorems rewrite_arith_abs_int_gt \<open>\<close>

lemma [rewrite_arith_abs_int_gt]:
  fixes x::"int" and y::"int"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> 
(abs x > abs y) =
 (if (x \<ge> 0) then
   (if (y \<ge> 0) then (x > y) else (x > -y))
 else
   (if (y \<ge> 0) then (-x > y) else (-x > -y)))"
  by simp

(*Old*)

named_theorems rewrite_arith_neg_neg_one \<open>automatically_generated\<close>

lemma [rewrite_arith_neg_neg_one]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> - (1::int) * (- (1::int) * t) = t"
  by auto


named_theorems rewrite_arith_elim_uminus \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_uminus]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> - t = - (1::int) * t"
  by auto


named_theorems rewrite_arith_elim_minus \<open>automatically_generated\<close>

lemma [rewrite_arith_elim_minus]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> t - s = t + - (1::int) * s"
  by auto


named_theorems rewrite_arith_plus_flatten \<open>automatically_generated\<close>

lemma [rewrite_arith_plus_flatten]:
  fixes xs::"int cvc_ListVar" and w::"int" and ys::"int cvc_ListVar" and zs::"int cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs w ys zs) \<Longrightarrow> cvc_list_right (+) (cvc_list_left (+) xs (cvc_list_right (+) w ys)) zs =
   cvc_list_right (+) (cvc_list_right (+) (cvc_list_left (+) xs w) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss)
    apply simp_all
    apply (induction yss)
    apply simp_all
    apply (induction xss)
    apply simp_all
    by (simp_all add: arith_plus_flatten_lemma)
  done


named_theorems rewrite_arith_mult_flatten \<open>automatically_generated\<close>

lemma [rewrite_arith_mult_flatten]:
  fixes xs::"int cvc_ListVar" and w::"int" and ys::"int cvc_ListVar" and zs::"int cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs w ys zs) \<Longrightarrow> cvc_list_right (*) (cvc_list_left (*) xs (cvc_list_right (*) w ys)) zs =
   cvc_list_right (*) (cvc_list_right (*) (cvc_list_left (*) xs w) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss)
    apply simp_all
    apply (induction yss)
    apply simp_all
    apply (induction xss)
    apply simp_all
    by (simp_all add: arith_mult_flatten_lemma)
  done


named_theorems rewrite_arith_mult_dist \<open>automatically_generated\<close>

lemma [rewrite_arith_mult_dist]:
  fixes x::"int" and y::"int" and z::"int" and w::"int cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined x y z w) \<Longrightarrow> x * cvc_list_right (+) (y + z) w = x * y + x * cvc_list_right (+) z w"
  apply (cases w)
  subgoal for ws 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction ws)
    apply simp_all
    by (simp_all add: arith_mult_dist_lemma)
  done


named_theorems rewrite_arith_plus_cancel1 \<open>automatically_generated\<close>

lemma [rewrite_arith_plus_cancel1]:
  fixes t::"int cvc_ListVar" and x::"int" and s::"int cvc_ListVar" and r::"int cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined t x s r) \<Longrightarrow> cvc_list_right (+)
    (cvc_list_right (+) (cvc_list_left (+) t x) s + - (1::int) * x) r =
   cvc_list_right (+) (cvc_list_both (+) (0::int) t s) r"
  apply (cases r)
  apply (cases s)
  apply (cases t)
  subgoal for rs ss ts 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction rs)
    apply simp_all
    apply (induction ss)
    apply simp_all
    apply (induction ts)
    apply simp_all
    by (simp_all add: arith_plus_cancel1_lemma)
  done


named_theorems rewrite_arith_plus_cancel2 \<open>automatically_generated\<close>

lemma [rewrite_arith_plus_cancel2]:
  fixes t::"int cvc_ListVar" and x::"int" and s::"int cvc_ListVar" and r::"int cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined t x s r) \<Longrightarrow> cvc_list_right (+)
    (cvc_list_right (+) (cvc_list_left (+) t (- (1::int) * x)) s + x) r =
   cvc_list_right (+) (cvc_list_both (+) (0::int) t s) r"
  apply (cases r)
  apply (cases s)
  apply (cases t)
  subgoal for rs ss ts 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction rs)
    apply simp_all
    apply (induction ss)
    apply simp_all
    apply (induction ts)
    apply simp_all
    by (simp_all add: arith_plus_cancel2_lemma)
  done

named_theorems rewrite_arith_int_gt \<open>manually added, will autogenerate later\<close>

lemma [rewrite_arith_int_gt]:
  fixes t::int and s::int
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t > s) = (t \<ge> (s + 1))"
  by auto


named_theorems rewrite_arith_int_lt \<open>manually added, will autogenerate later\<close>

lemma [rewrite_arith_int_lt]:
  fixes t::int and s::int
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t < s) = (s \<ge> (t + 1))"
  by auto


named_theorems rewrite_arith_max_geq1 \<open>\<close>

lemma [rewrite_arith_max_geq1]:
  fixes t::"'a::linordered_idom" and s::"'a::linordered_idom"  
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> (t \<le> (if (s \<le> t) then t else s)) = True"
  by auto

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



end