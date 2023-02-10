theory Arith_Rewrites
  imports Dsl_Nary_Ops
begin

(* This is a theory automatically created from a rare file! All that remains to do is to prove
any lemma whose auto proof fails and to to import this file in SMT.thy. 
If your rare statements use nary operators over lists that would be binarised by Isabelle 
you have to add it in Dsl_Nary_Ops.thy. Currently supported are the operators:
and,or*)

named_theorems arith_plus_cancel2 \<open>automatically_generated\<close>

lemma h1: "(foldr (+) ts 0) + (foldr (+) ss (0::int)) = foldr (+) ts (foldr (+) ss 0)"
  apply (induction ts)
   apply simp
  apply (induction ss)
  by simp_all

lemma h2: "(foldr (+) ts x) = (foldr (+) ts (0::int)) + x"
  apply (induction ts)
  by simp_all

lemma h3: "foldr (+) ts (- (x::int)) + foldr (+) ss 0 + x = foldr (+) ts (foldr (+) ss 0)"
proof-
  have "foldr (+) ts (- (x::int)) + foldr (+) ss 0 + x = 
        foldr (+) ts 0 + (- (x::int)) + foldr (+) ss 0 + x"
    by (metis h2)
  also have "... = foldr (+) ts 0 + foldr (+) ss 0"
    by simp
  also have "... = foldr (+) ts (foldr (+) ss 0)"
    by (simp add: h1)
  finally show ?thesis 
    by simp
qed

lemma [arith_plus_cancel2]:
  fixes r::"int cvc_ListVar" and s::"int cvc_ListVar" and x::"int" and t::"int cvc_ListVar"
  shows "((cvc_list_right (+)
 (cvc_list_right (+) (cvc_list_left (+) t (- 1 * x)) s + x) r) = (cvc_list_right (+) (cvc_list_both (+) 0 t s) r))"
  apply (cases r)
  apply (cases s)
  apply (cases t)
  subgoal for rs ss ts
    apply (cases "ts = [] \<and> ss = []")
    apply simp_all
    apply (simp_all add: cvc_list_right_transfer)
    apply (simp_all add: cvc_list_left_transfer)
    apply (simp_all add: cvc_list_both_transfer)
    apply (induction rs)
    apply (induction ss)
      apply simp_all
      apply (induction ts)
       apply simp_all
    apply (metis add.commute add_minus_cancel h2)
    apply (metis add.assoc add.left_commute h2 h3)
    using h3 by force
  done

named_theorems arith_plus_cancel1 \<open>automatically_generated\<close>

lemma [arith_plus_cancel1]:
  fixes r::"int cvc_ListVar" and s::"int cvc_ListVar" and x::"int" and t::"int cvc_ListVar"
  shows "((cvc_list_right (+) (cvc_list_right (+) (cvc_list_left (+) t x) s + - 1 * x)
 r) = (cvc_list_right (+) (cvc_list_both (+) 0 t s) r))"
 apply (cases r)
  apply (cases s)
  apply (cases t)
  subgoal for rs ss ts
    apply (cases "ts = [] \<and> ss = []")
    apply simp_all
    apply (simp_all add: cvc_list_right_transfer)
    apply (simp_all add: cvc_list_left_transfer)
    apply (simp_all add: cvc_list_both_transfer)
    apply (induction rs)
    apply (induction ss)
      apply simp_all
      apply (induction ts)
       apply simp_all
    apply (metis eq_diff_eq h2)
     apply (metis diff_add_cancel diff_add_eq h2)
    by (metis add_0 diff_minus_eq_add h3 minus_diff_eq)
  done

named_theorems arith_eq_equiv \<open>automatically_generated\<close>

lemma [arith_eq_equiv]:
  fixes q::"int" and r::"int" and s::"int" and t::"int"
  shows "(((t = s) = (r = q)) = (t + - 1 * s = r + - 1 * q))"
  oops  

named_theorems mult_dist \<open>automatically_generated\<close>

lemma [mult_dist]:
  fixes w::"int cvc_ListVar" and z::"int" and y::"int" and x::"int"
  shows "((x * cvc_list_right (+) (y + z) w) = (x * y + x * cvc_list_right (+) z w))"
  apply (cases w)
  subgoal for ws
    apply (simp_all add: cvc_list_right_transfer)
    by (simp add: distrib_left)
  done

named_theorems mult_flatten \<open>automatically_generated\<close>

lemma h4: "foldr (*) xs (w * (a::int)) = foldr (*) xs w * a"
  by (metis (no_types, opaque_lifting) foldr.simps(1) foldr.simps(2) foldr_append id_apply mult.right_neutral o_apply prod_list.append prod_list.eq_foldr)


lemma [mult_flatten]:
  fixes zs::"int cvc_ListVar" and ys::"int cvc_ListVar" and w::"int" and xs::"int cvc_ListVar"
  shows "((cvc_list_right (*) (cvc_list_left (*) xs (cvc_list_right (*) w ys)) zs) = (cvc_list_right (*) (cvc_list_right (*) (cvc_list_left (*) xs w) ys) zs))"
 apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss
    apply simp_all
    apply (simp_all add: cvc_list_left_transfer)
    apply (simp add: cvc_ListOp_neutral cvc_list_right_transfer[of "(*)" 1 w yss])
    apply (simp add: cvc_ListOp_neutral cvc_list_right_transfer[of "(*)" 1 "(foldr (*) xss (w * foldr (*) yss 1))" zss])
    apply (simp add: cvc_ListOp_neutral cvc_list_right_transfer[of "(*)" 1 "(foldr (*) xss w)" yss])
    apply (simp add: cvc_ListOp_neutral cvc_list_right_transfer[of "(*)" 1 "(foldr (*) xss w * foldr (*) yss 1)" zss])
    apply (induction zss)
    apply simp_all
    apply (induction yss)
    apply simp_all
    apply (induction xss)
      apply simp_all
     apply (simp add: h4)
    using h4 by auto
  done

named_theorems plus_flatten \<open>automatically_generated\<close>

lemma [plus_flatten]:
  fixes zs::"int cvc_ListVar" and ys::"int cvc_ListVar" and w::"int" and xs::"int cvc_ListVar"
  shows "((cvc_list_right (+) (cvc_list_left (+) xs (cvc_list_right (+) w ys)) zs) = (cvc_list_right (+) (cvc_list_right (+) (cvc_list_left (+) xs w) ys) zs))"
 apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss
    apply simp_all
    apply (simp_all add: cvc_list_left_transfer)
    apply (simp_all add: cvc_list_right_transfer)
    apply (induction zss)
    apply simp_all
     apply (induction xss)
    apply simp_all
    apply (induction yss)
      apply simp_all
    apply (metis add.commute add.left_commute h2)
    by (metis add.assoc h2)
  done

named_theorems arith_refl_gt \<open>automatically_generated\<close>

lemma [arith_refl_gt]:
  fixes t::"int"
  shows "((t < t) = (False))"
  by auto

named_theorems arith_refl_geq \<open>automatically_generated\<close>

lemma [arith_refl_geq]:
  fixes t::"int"
  shows "((t \<le> t) = (True))"
  by auto

named_theorems arith_refl_lt \<open>automatically_generated\<close>

lemma [arith_refl_lt]:
  fixes t::"int"
  shows "((t < t) = (False))"
  by auto

named_theorems arith_refl_leq \<open>automatically_generated\<close>

lemma [arith_refl_leq]:
  fixes t::"int"
  shows "((t \<le> t) = (True))"
  by auto

named_theorems arith_geq_norm \<open>automatically_generated\<close>

lemma [arith_geq_norm]:
  fixes s::"int" and t::"int"
  shows "((s \<le> t) = (0 \<le> t - s))"
  by auto

named_theorems arith_geq_tighten \<open>automatically_generated\<close>

lemma [arith_geq_tighten]:
  fixes s::"int" and t::"int"
  shows "((\<not> s \<le> t) = (t + 1 \<le> s))"
  by auto

named_theorems arith_elim_leq \<open>automatically_generated\<close>

lemma [arith_elim_leq]:
  fixes s::"int" and t::"int"
  shows "((t \<le> s) = (\<not> s + 1 \<le> t))"
  by auto

named_theorems arith_elim_lt \<open>automatically_generated\<close>

lemma [arith_elim_lt]:
  fixes s::"int" and t::"int"
  shows "((t < s) = (\<not> s \<le> t))"
  by auto

named_theorems arith_elim_gt \<open>automatically_generated\<close>

lemma [arith_elim_gt]:
  fixes s::"int" and t::"int"
  shows "((s < t) = (\<not> t \<le> s))"
  by auto

named_theorems arith_elim_minus \<open>automatically_generated\<close>

lemma [arith_elim_minus]:
  fixes s::"int" and t::"int"
  shows "((t - s) = (t + - 1 * s))"
  by auto

named_theorems arith_neg_neg_one \<open>automatically_generated\<close>

lemma [arith_neg_neg_one]:
  fixes t::"int"
  shows "((- 1 * (- 1 * t)) = (t))"
  by auto

named_theorems arith_uminus_elim \<open>automatically_generated\<close>

lemma [arith_uminus_elim]:
  fixes t::"int"
  shows "((- t) = (- 1 * t))"
  by auto

named_theorems arith_mul_zero \<open>automatically_generated\<close>

lemma [simp]: "foldr (*) ts (0::int) = 0"
  apply (induction ts)
  by simp_all

lemma [arith_mul_zero]:
  fixes s::"int cvc_ListVar" and t::"int cvc_ListVar"
  shows "((cvc_list_right (*) (cvc_list_left (*) t 0) s) = (0))"
  apply (cases t)
  apply (cases s)
  apply (simp_all add: cvc_list_left_transfer)
  subgoal for ts ss
    using cvc_ListOp_neutral cvc_list_right_transfer[of "(*)" 1 "(foldr (*) ts 0)" ss] by simp
  done

named_theorems arith_mul_one \<open>automatically_generated\<close>

lemma [arith_mul_one]:
  fixes s::"int cvc_ListVar" and t::"int cvc_ListVar"
  shows "((cvc_list_right (*) (cvc_list_left (*) t 1) s) = (cvc_list_both (*) 1 t s))"
  apply (cases t)
  apply (cases s)
  apply (simp_all add: cvc_list_left_transfer)
  subgoal for ts ss
  apply (simp_all add: cvc_ListOp_neutral cvc_list_right_transfer[of "(*)" 1 "(foldr (*) ts 1)" ss])
    apply (cases "ts =[] \<and> ss =[]")
  apply (simp_all add: cvc_list_both_transfer)
    by (metis foldr_append prod_list.append prod_list.eq_foldr)
  done

named_theorems arith_plus_zero \<open>automatically_generated\<close>

lemma [arith_plus_zero]:
  fixes s::"int cvc_ListVar" and t::"int cvc_ListVar"
  shows "((cvc_list_right (+) (cvc_list_left (+) t 0) s) = (cvc_list_both (+) 0 t s))"
  apply (cases t)
  apply (cases s)
  apply (simp_all add: cvc_list_left_transfer)
  subgoal for ts ss
  apply (simp_all add: cvc_ListOp_neutral cvc_list_right_transfer[of "(+)" 0 " (foldr (+) ts 0)" ss])
    apply (cases "ts =[] \<and> ss =[]")
  apply (simp_all add: cvc_list_both_transfer)
    using h1 by blast
    done

named_theorems arith_eq_symm_int \<open>automatically_generated\<close>

lemma [arith_eq_symm_int]:
  fixes s::"int" and t::"int"
  shows "((t = s) = (s = t))"
  by auto

named_theorems arith_eq_refl_int \<open>automatically_generated\<close>

lemma [arith_eq_refl_int]:
  fixes t::"int"
  shows "((t = t) = (True))"
  by auto

end