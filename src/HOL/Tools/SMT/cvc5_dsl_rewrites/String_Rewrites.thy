theory String_Rewrites
  imports Dsl_Nary_Ops String_Rewrites_Lemmas
begin

(*All proven except: *)
(*
str_substr_combine \<rightarrow> MISSING CONDITION
*)


(* This is a theory automatically created from a rare file! All that remains to do is to prove
any lemma whose auto proof fails and to to import this file in SMT.thy. 
If your rare statements use nary operators over lists that would be binarised by Isabelle 
you have to add it in Dsl_Nary_Ops.thy. Currently supported are the operators:
and,or*)

named_theorems re_concat_star_swap \<open>automatically_generated\<close>

lemma [re_concat_star_swap]:
  fixes ys::"char list set cvc_ListVar" and r::"char list set" and xs::"char list set cvc_ListVar"
  shows "((cvc_list_right smtlib_re_concat
 (smtlib_re_concat (cvc_list_left smtlib_re_concat xs (smtlib_re_star r)) r)
 ys) = (cvc_list_right smtlib_re_concat
 (smtlib_re_concat (cvc_list_left smtlib_re_concat xs r) (smtlib_re_star r))
 ys))"
  apply (cases ys)
  apply (cases xs)
  subgoal for ys xs 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: re_concat_star_swap_lemma)
  done

named_theorems re_concat_flatten \<open>automatically_generated\<close>

lemma [re_concat_flatten]:
  fixes zs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar" and s::"char list set" and xs::"char list set cvc_ListVar"
  shows "((cvc_list_right smtlib_re_concat
 (cvc_list_left smtlib_re_concat xs (cvc_list_right smtlib_re_concat s ys))
 zs) = (cvc_list_right smtlib_re_concat
 (cvc_list_right smtlib_re_concat (cvc_list_left smtlib_re_concat xs s) ys)
 zs))"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zs ys xs 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: re_concat_flatten_lemma)
  done

named_theorems re_concat_emp \<open>automatically_generated\<close>

value " (cvc_str_to_re [])"

(*TODO: *)
(*(define-rule re-concat-emp ((xs RegLan :list) (ys RegLan :list)) (re.++ xs (str.to_re "") ys) (re.++ xs ys))*)
lemma [re_concat_emp]:
  fixes ys::"char list set cvc_ListVar" and xs::"char list set cvc_ListVar"
  shows "((cvc_list_right smtlib_re_concat
 (cvc_list_left smtlib_re_concat xs (smtlib_str_to_re '''')) ys) = (cvc_list_both smtlib_re_concat {''''} xs ys))"
 apply (cases ys)
  apply (cases xs)
  subgoal for ys xs 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: re_concat_emp_lemma)
  done

named_theorems str_concat_emp \<open>automatically_generated\<close>

lemma [str_concat_emp]:
  fixes ys::"char list cvc_ListVar" and xs::"char list cvc_ListVar"
  shows "((cvc_list_right smtlib_str_concat (cvc_list_left smtlib_str_concat xs '''')
 ys) = (cvc_list_both smtlib_str_concat [] xs ys))"
   apply (cases ys)
  apply (cases xs)
  subgoal for ys xs 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: str_concat_emp_lemma)
  done

named_theorems str_contains_split_char \<open>automatically_generated\<close>

lemma [str_contains_split_char]:
  fixes w::"char list" and z::"char list cvc_ListVar" and y::"char list" and x::"char list"
  assumes "smtlib_str_len w = 1"
  shows "((smtlib_str_contains
 (cvc_list_right smtlib_str_concat (smtlib_str_concat x y) z) w) = (smtlib_str_contains x w \<or>
smtlib_str_contains (cvc_list_right smtlib_str_concat y z) w))"
  apply (cases z)
  subgoal for z 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: str_contains_split_char_lemma assms)
  done

named_theorems str_contains_refl \<open>automatically_generated\<close>

lemma [str_contains_refl]:
  fixes x::"char list"
  shows "((smtlib_str_contains x x) = (True))"
  using smtlib_str_contains_def 
  by (metis prefix_def prefix_order.order_refl smtlib_str_contains2_def smtlib_str_contains_equal suffix_def suffix_to_prefix)

named_theorems substr_concat1 \<open>automatically_generated\<close>

lemma [substr_concat1]:
  fixes m::"int" and n::"int" and s2::"char list cvc_ListVar" and s1::"char list"
  assumes "0 \<le> n \<and> n + m \<le> smtlib_str_len s1"
  shows "((smtlib_str_substr (cvc_list_right smtlib_str_concat s1 s2) n m) = (smtlib_str_substr s1 n m))"
  apply (cases s2)
  subgoal for s2 
    using assms
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: substr_concat1_lemma)
  done

named_theorems str_substr_combine \<open>automatically_generated\<close>

lemma [str_substr_combine]:
  fixes m2::"int" and n2::"int" and m1::"int" and n1::"int" and s::"char list"
  assumes "0 \<le> n2 \<and> 0 \<le> n2 + m2 - m1 \<and> m1 \<ge> 0 \<and> m2 \<le> m1"
  shows "((smtlib_str_substr (smtlib_str_substr s n1 m1) n2 m2)
        = (smtlib_str_substr s (n1 + n2) m2))"
  nitpick



named_theorems str_suffixof_one \<open>automatically_generated\<close>

lemma [str_suffixof_one]:
  fixes t::"char list" and s::"char list"
  assumes "smtlib_str_len t = 1"
  shows "((smtlib_str_suffixof s t) = (smtlib_str_contains t s))"
  using assms
  unfolding smtlib_str_suffixof_def smtlib_str_len_def
  using str_suffixof_one_lemma smtlib_str_contains_equal
  using smtlib_str_contains2_def by auto

named_theorems str_prefixof_one \<open>automatically_generated\<close>

lemma [str_prefixof_one]:
  fixes t::"char list" and s::"char list"
  assumes "smtlib_str_len t = 1"
  shows "((smtlib_str_prefixof s t) = (smtlib_str_contains t s))"
  using assms
  unfolding smtlib_str_prefixof_def smtlib_str_contains_def smtlib_str_len_def
  using str_prefixof_one_lemma smtlib_str_contains_equal
  using smtlib_str_contains2_def smtlib_str_contains_def by auto

named_theorems str_suffixof_elim \<open>automatically_generated\<close>

lemma [str_suffixof_elim]:
  fixes t::"char list" and s::"char list"
  shows "((smtlib_str_suffixof s t) = (s = smtlib_str_substr t (smtlib_str_len t - smtlib_str_len s) (smtlib_str_len s)))"
    unfolding smtlib_str_suffixof_def smtlib_str_substr_def smtlib_str_len_def
    using str_suffixof_elim_lemma by simp

named_theorems str_prefixof_elim \<open>automatically_generated\<close>

lemma [str_prefixof_elim]:
  fixes t::"char list" and s::"char list"
  shows "((smtlib_str_prefixof s t) = (s = smtlib_str_substr t 0 (smtlib_str_len s)))"
  unfolding smtlib_str_prefixof_def smtlib_str_substr_def smtlib_str_len_def
  apply simp
  by (metis append_eq_append_conv append_take_drop_id length_take min.commute min_def prefix_def prefix_length_le)

named_theorems concat_clash_char_rev \<open>automatically_generated\<close>

lemma [concat_clash_char_rev]:
  fixes t3::"char list cvc_ListVar" and t2::"char list cvc_ListVar" and t1::"char list" and s3::"char list cvc_ListVar" and s2::"char list cvc_ListVar" and s1::"char list"
  assumes "\<not> s1 = t1 \<and> smtlib_str_len s1 = smtlib_str_len t1"
  shows "((cvc_list_left smtlib_str_concat s3 (cvc_list_left smtlib_str_concat s2 s1) =
cvc_list_left smtlib_str_concat t3 (cvc_list_left smtlib_str_concat t2 t1)) = (False))"
  apply (cases t3)
  apply (cases t2)
  apply (cases s3)
  apply (cases s2)
  subgoal for t3 t2 s3 s2
    using assms
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: concat_clash_char_rev_lemma)
  done

named_theorems concat_clash_char \<open>automatically_generated\<close>

lemma [concat_clash_char]:
  fixes t3::"char list cvc_ListVar" and t2::"char list cvc_ListVar" and t1::"char list" and s3::"char list cvc_ListVar" and s2::"char list cvc_ListVar" and s1::"char list"
  assumes "\<not> s1 = t1 \<and> smtlib_str_len s1 = smtlib_str_len t1"
  shows "((cvc_list_right smtlib_str_concat (cvc_list_right smtlib_str_concat s1 s2) s3 =
cvc_list_right smtlib_str_concat (cvc_list_right smtlib_str_concat t1 t2) t3) = (False))"
  apply (cases t3)
  apply (cases t2)
  apply (cases s3)
  apply (cases s2)
  subgoal for t3 t2 s3 s2
    using assms
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: concat_clash_char_lemma)
  done

named_theorems concat_unify_rev \<open>automatically_generated\<close>

lemma [concat_unify_rev]:
  fixes t3::"char list cvc_ListVar" and t2::"char list" and s3::"char list cvc_ListVar" and s2::"char list" and s1::"char list"
  shows "((smtlib_str_concat (cvc_list_right smtlib_str_concat s2 s3) s1 =
smtlib_str_concat (cvc_list_right smtlib_str_concat t2 t3) s1) = (cvc_list_right smtlib_str_concat s2 s3 = cvc_list_right smtlib_str_concat t2 t3))"
  apply (cases t3)
  apply (cases s3)
  subgoal for t3 s3 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: concat_unify_rev_lemma)
  done

named_theorems concat_unify \<open>automatically_generated\<close>

lemma [concat_unify]:
  fixes t3::"char list cvc_ListVar" and t2::"char list" and s3::"char list cvc_ListVar" and s2::"char list" and s1::"char list"
  shows "((cvc_list_right smtlib_str_concat (smtlib_str_concat s1 s2) s3 =
cvc_list_right smtlib_str_concat (smtlib_str_concat s1 t2) t3) = (cvc_list_right smtlib_str_concat s2 s3 = cvc_list_right smtlib_str_concat t2 t3))"
  apply (cases t3)
  apply (cases s3)
  subgoal for t3 s3 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: concat_unify_lemma)
  done

named_theorems concat_clash2_rev \<open>automatically_generated\<close>

lemma [concat_clash2_rev]:
  fixes t2::"char list cvc_ListVar" and t1::"char list" and s1::"char list"
  assumes "\<not> s1 = t1 \<and> smtlib_str_len s1 = smtlib_str_len t1"
  shows "((s1 = cvc_list_left smtlib_str_concat t2 t1) = (False))"
  apply (cases t2)
  subgoal for t2 
    using assms
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: concat_clash2_rev_lemma)
  done

named_theorems concat_clash2 \<open>automatically_generated\<close>

lemma [concat_clash2]:
  fixes t2::"char list cvc_ListVar" and t1::"char list" and s1::"char list"
  assumes "\<not> s1 = t1 \<and> smtlib_str_len s1 = smtlib_str_len t1"
  shows "((s1 = cvc_list_right smtlib_str_concat t1 t2) = (False))"
  apply (cases t2)
  subgoal for t2 
    using assms
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: concat_clash2_lemma)
  done

named_theorems concat_clash_rev \<open>automatically_generated\<close>

lemma [concat_clash_rev]:
  fixes t2::"char list cvc_ListVar" and t1::"char list" and s2::"char list cvc_ListVar" and s1::"char list"
  assumes "\<not> s1 = t1 \<and> smtlib_str_len s1 = smtlib_str_len t1"
  shows "((cvc_list_left smtlib_str_concat s2 s1 = cvc_list_left smtlib_str_concat t2 t1) = (False))"
  apply (cases t2)
  apply (cases s2)
  subgoal for t2 s2 
    using assms
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: concat_clash_rev_lemma)
  done

named_theorems concat_clash \<open>automatically_generated\<close>

lemma [concat_clash]:
  fixes t2::"char list cvc_ListVar" and t1::"char list" and s2::"char list cvc_ListVar" and s1::"char list"
  assumes "\<not> s1 = t1 \<and> smtlib_str_len s1 = smtlib_str_len t1"
  shows "((cvc_list_right smtlib_str_concat s1 s2 = cvc_list_right smtlib_str_concat t1 t2) = (False))"
  apply (cases t2)
  apply (cases s2)
  subgoal for t2 s2 
    using assms
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: concat_clash_lemma)
  done

named_theorems re_in_comp \<open>automatically_generated\<close>

lemma [re_in_comp]:
  fixes r::"char list set" and t::"char list"
  shows "((smtlib_str_in_re t (smtlib_re_comp r)) = (\<not> smtlib_str_in_re t r))"
  unfolding smtlib_str_in_re_def smtlib_re_comp_def
  by auto

named_theorems re_in_cstring \<open>automatically_generated\<close>

lemma [re_in_cstring]:
  fixes s::"char list" and t::"char list"
  shows "((smtlib_str_in_re t (smtlib_str_to_re s)) = (t = s))"
  unfolding smtlib_str_in_re_def smtlib_str_to_re_def
  by auto

named_theorems re_in_sigma_star \<open>automatically_generated\<close>

lemma [re_in_sigma_star]:
  fixes t::"char list"
  shows "((smtlib_str_in_re t (smtlib_re_star smtlib_re_allchar)) = (True))"
  unfolding smtlib_re_allchar_def smtlib_str_in_re_def smtlib_re_star_def
            smtlib_re_concat_def
  by (metis UNIV_I smtlib_re_allchar_def smtlib_re_star_smtlib_re_allchar smtlib_re_star_def)

named_theorems re_in_sigma \<open>automatically_generated\<close>

lemma [re_in_sigma]:
  fixes t::"char list"
  shows "((smtlib_str_in_re t smtlib_re_allchar) = (smtlib_str_len t = 1))"
  unfolding smtlib_str_in_re_def smtlib_re_allchar_def smtlib_str_len_def
  by simp

named_theorems re_in_empty \<open>automatically_generated\<close>

lemma [re_in_empty]:
  fixes t::"char list"
  shows "((smtlib_str_in_re t smtlib_re_none) = (False))"
  unfolding smtlib_re_none_def smtlib_str_in_re_def
  by simp

named_theorems str_len_substr_in_range \<open>automatically_generated\<close>

lemma [str_len_substr_in_range]:
  fixes m::"int" and n::"int" and s::"char list"
  assumes "0 \<le> n \<and> n + m \<le> smtlib_str_len s \<and> m \<ge> 0 "
  shows "((smtlib_str_len (smtlib_str_substr s n m)) = (m))"
  using assms
  unfolding smtlib_str_len_def smtlib_str_substr_def
  by auto

named_theorems str_len_replace_inv \<open>automatically_generated\<close>

lemma [str_len_replace_inv]:
  fixes r::"char list" and s::"char list" and t::"char list"
  assumes "smtlib_str_len s = smtlib_str_len r"
  shows "((smtlib_str_len (smtlib_str_replace t s r)) = (smtlib_str_len t))"
  using assms
  by (simp add: smtlib_str_replace_def smtlib_str_replace_length_h2)


named_theorems substr_eq_empty \<open>automatically_generated\<close>

lemma [substr_eq_empty]:
  fixes m::"int" and n::"int" and s::"char list"
  assumes "n = 0 \<and> n < m"
  shows "((smtlib_str_substr s n m = '''') = (s = ''''))"
  using assms
  by (simp add: smtlib_str_substr_def)

named_theorems substr_empty_start \<open>automatically_generated\<close>

lemma [substr_empty_start]:
  fixes m::"int" and n::"int" and x::"char list"
  assumes "smtlib_str_len x \<le> n"
  shows "((smtlib_str_substr x n m) = (''''))"
  using assms
  by (simp add: smtlib_str_substr_def smtlib_str_len_def)

named_theorems substr_empty_range \<open>automatically_generated\<close>

lemma [substr_empty_range]:
  fixes m::"int" and n::"int" and x::"char list"
  assumes "m \<le> 0"
  shows "((smtlib_str_substr x n m) = (''''))"
  by (simp add: smtlib_str_substr_def assms)

named_theorems substr_empty_str \<open>automatically_generated\<close>

lemma [substr_empty_str]:
  fixes m::"int" and n::"int"
  shows "((smtlib_str_substr '''' n m) = (''''))"
  by (simp add: smtlib_str_substr_def)

named_theorems str_concat_flatten_eq_rev \<open>automatically_generated\<close>

lemma [str_concat_flatten_eq_rev]:
  fixes y::"char list" and x2::"char list cvc_ListVar" and x1::"char list cvc_ListVar" and x::"char list"
  shows "((cvc_list_left smtlib_str_concat x2 (cvc_list_left smtlib_str_concat x1 x) = y) = (y = smtlib_str_concat (cvc_list_both smtlib_str_concat [] x2 x1) x))"
  apply (cases x2)
  apply (cases x1)
  subgoal for x2 x1 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: str_concat_flatten_eq_rev_lemma)
  done

named_theorems str_concat_flatten_eq \<open>automatically_generated\<close>

lemma [str_concat_flatten_eq]:
  fixes y::"char list" and x2::"char list cvc_ListVar" and x1::"char list cvc_ListVar" and x::"char list"
  shows "((cvc_list_right smtlib_str_concat (cvc_list_right smtlib_str_concat x x1) x2 = y) = (y = cvc_list_right smtlib_str_concat (cvc_list_right smtlib_str_concat x x1) x2))"
  apply (cases x2)
  apply (cases x1)
  subgoal for x2 x1 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: str_concat_flatten_eq_lemma)
  done

named_theorems str_concat_flatten \<open>automatically_generated\<close>

lemma [str_concat_flatten]:
  fixes zs::"char list cvc_ListVar" and ys::"char list cvc_ListVar" and s::"char list" and xs::"char list cvc_ListVar"
  shows "((cvc_list_right smtlib_str_concat
 (cvc_list_left smtlib_str_concat xs (cvc_list_right smtlib_str_concat s ys)) zs) = (cvc_list_right smtlib_str_concat
 (cvc_list_right smtlib_str_concat (cvc_list_left smtlib_str_concat xs s) ys) zs))"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zs ys xs 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: str_concat_flatten_lemma)
  done

named_theorems str_ite_not_cond \<open>automatically_generated\<close>

lemma [str_ite_not_cond]:
  fixes y::"char list" and x::"char list" and c::"bool"
  shows "((if \<not> c then x else y) = (if c then y else x))"
  by auto

named_theorems str_ite_false_cond \<open>automatically_generated\<close>

lemma [str_ite_false_cond]:
  fixes y::"char list" and x::"char list"
  shows "((if False then x else y) = (y))"
  by auto

named_theorems str_ite_true_cond \<open>automatically_generated\<close>

lemma [str_ite_true_cond]:
  fixes y::"char list" and x::"char list"
  shows "((if True then x else y) = (x))"
  by auto

named_theorems str_eq_symm \<open>automatically_generated\<close>

lemma [str_eq_symm]:
  fixes s::"char list" and t::"char list"
  shows "((t = s) = (s = t))"
  by auto

named_theorems str_eq_refl \<open>automatically_generated\<close>

lemma [str_eq_refl]:
  fixes t::"char list"
  shows "((t = t) = (True))"
  by auto

named_theorems rewrite_str_len_concat_rec \<open>automatically_generated\<close>

lemma [rewrite_str_len_concat_rec]:
  fixes s1::"char list" and s2::"char list" and s3::"char list cvc_ListVar"
  shows "smtlib_str_len
    (cvc_list_right smtlib_str_concat (smtlib_str_concat s1 s2) s3) =
   smtlib_str_len s1 +
   smtlib_str_len (cvc_list_right smtlib_str_concat s2 s3)"
  apply (cases s3)
  subgoal for s3s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: str_len_concat_rec_lemma)
  done

end