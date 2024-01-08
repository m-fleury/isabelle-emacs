theory String_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops"  "String_Rewrites_Lemmas"
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

named_theorems rewrite_str_eq_ctn_false \<open>automatically_generated\<close>

lemma [rewrite_str_eq_ctn_false]:
  fixes x1::"char list cvc_ListVar" and x::"char list" and x2::"char list cvc_ListVar" and y::"char list"
  shows "NO_MATCH cvc_a (undefined x1 x x2 y) \<Longrightarrow> smtlib_str_contains y x = False \<longrightarrow>
   (cvc_list_right smtlib_str_concat (cvc_list_left smtlib_str_concat x1 x)
     x2 =
    y) =
   False"
  apply (cases x2)
  apply (cases x1)
  subgoal for x2s x1s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction x2s arbitrary: x2)
    apply simp_all
    apply (induction x1s arbitrary: x1)
    apply simp_all
    apply (simp_all add: cvc_string_rewrite_defs)
      apply (simp_all add: cvc_rewrites_fold)
    by (simp_all add: str_eq_ctn_false_lemma)
  done


named_theorems rewrite_str_concat_flatten \<open>automatically_generated\<close>

lemma [rewrite_str_concat_flatten]:
  fixes xs::"char list cvc_ListVar" and s::"char list" and ys::"char list cvc_ListVar" and zs::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs s ys zs) \<Longrightarrow> cvc_list_right smtlib_str_concat
    (cvc_list_left smtlib_str_concat xs
      (cvc_list_right smtlib_str_concat s ys))
    zs =
   cvc_list_right smtlib_str_concat
    (cvc_list_right smtlib_str_concat (cvc_list_left smtlib_str_concat xs s)
      ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss arbitrary: zs)
    apply simp_all
    apply (induction yss arbitrary: ys)
    apply simp_all
    apply (induction xss arbitrary: xs)
    apply simp_all
    apply (simp_all add: cvc_string_rewrite_defs)
    by (simp_all add: cvc_rewrites_fold)
  done


named_theorems rewrite_str_concat_flatten_eq \<open>automatically_generated\<close>

lemma [rewrite_str_concat_flatten_eq]:
  fixes x::"char list" and x1::"char list cvc_ListVar" and x2::"char list cvc_ListVar" and y::"char list"
  shows "NO_MATCH cvc_a (undefined x x1 x2 y) \<Longrightarrow> (cvc_list_right smtlib_str_concat (cvc_list_right smtlib_str_concat x x1)
     x2 =
    y) =
   (y =
    cvc_list_right smtlib_str_concat (cvc_list_right smtlib_str_concat x x1)
     x2)"
  apply (cases x2)
  apply (cases x1)
  subgoal for x2s x1s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction x2s arbitrary: x2)
    apply simp_all
    apply (induction x1s arbitrary: x1)
    apply simp_all
    apply (simp_all add: cvc_string_rewrite_defs)
    apply (simp_all add: cvc_rewrites_fold)
    by (simp_all add: str_concat_flatten_eq_lemma)
  done


named_theorems rewrite_str_concat_flatten_eq_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_flatten_eq_rev]:
  fixes x::"char list" and x1::"char list cvc_ListVar" and x2::"char list cvc_ListVar" and y::"char list"
  shows "NO_MATCH cvc_a (undefined x x1 x2 y) \<Longrightarrow> (cvc_list_left smtlib_str_concat x2
     (cvc_list_left smtlib_str_concat x1 x) =
    y) =
   (y = smtlib_str_concat (cvc_list_both smtlib_str_concat [] x2 x1) x)"
  apply (cases x2)
  apply (cases x1)
  subgoal for x2s x1s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction x2s arbitrary: x2)
    apply simp_all
    apply (induction x1s arbitrary: x1)
    apply simp_all
    apply (simp_all add: cvc_string_rewrite_defs)
    apply (simp_all add: cvc_rewrites_fold)
    by auto
  done


named_theorems rewrite_str_substr_empty_str \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_str]:
  fixes n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined n m) \<Longrightarrow> smtlib_str_substr (''''::char list) n m = ''''"
    by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_str_substr_empty_range \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_range]:
  fixes x::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x n m) \<Longrightarrow> m \<le> (0::int) \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
    by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_str_substr_empty_start \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_start]:
  fixes x::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x n m) \<Longrightarrow> smtlib_str_len x \<le> n \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
    by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_str_substr_empty_start_neg \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_start_neg]:
  fixes x::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined x n m) \<Longrightarrow> n < (0::int) \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
    by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_str_substr_eq_empty \<open>automatically_generated\<close>

lemma [rewrite_str_substr_eq_empty]:
  fixes s::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined s n m) \<Longrightarrow> n = (0::int) \<and> n < m \<longrightarrow>
   (smtlib_str_substr s n m = (''''::char list)) = (s = '''')"
    by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_str_len_replace_inv \<open>automatically_generated\<close>

lemma [rewrite_str_len_replace_inv]:
  fixes t::"char list" and s::"char list" and r::"char list"
  shows "NO_MATCH cvc_a (undefined t s r) \<Longrightarrow> smtlib_str_len s = smtlib_str_len r \<longrightarrow>
   smtlib_str_len (smtlib_str_replace t s r) = smtlib_str_len t"
  using smtlib_str_len_def smtlib_str_replace_def smtlib_str_replace_length by presburger

named_theorems rewrite_str_len_update_inv \<open>automatically_generated\<close>

lemma [rewrite_str_len_update_inv]:
  fixes t::"char list" and n::"int" and r::"char list"
  shows "NO_MATCH cvc_a (undefined t n r) \<Longrightarrow> smtlib_str_len (smtlib_str_update t n r) = smtlib_str_len t"
  apply (simp add: cvc_string_rewrite_defs)
  by auto

named_theorems rewrite_str_len_substr_in_range \<open>automatically_generated\<close>

lemma [rewrite_str_len_substr_in_range]:
  fixes s::"char list" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined s n m) \<Longrightarrow> (0::int) \<le> n \<and>
   (0::int) \<le> m \<and> n + m \<le> smtlib_str_len s \<longrightarrow>
   smtlib_str_len (smtlib_str_substr s n m) = m"
  apply (simp add: cvc_string_rewrite_defs)
  by auto

named_theorems rewrite_str_len_substr_ub1 \<open>automatically_generated\<close>

lemma [rewrite_str_len_substr_ub1]:
  fixes s::"char list" and n::"int" and m::"int" and k::"int"
  shows "NO_MATCH cvc_a (undefined s n m k) \<Longrightarrow> (0::int) \<le> k \<and> m \<le> k \<longrightarrow>
   (smtlib_str_len (smtlib_str_substr s n m) \<le> k) = True"
  apply (simp add: cvc_string_rewrite_defs)
  by auto

named_theorems rewrite_str_len_substr_ub2 \<open>automatically_generated\<close>

lemma [rewrite_str_len_substr_ub2]:
  fixes s::"char list" and n::"int" and m::"int" and k::"int"
  shows "NO_MATCH cvc_a (undefined s n m k) \<Longrightarrow> (0::int) \<le> k \<and> smtlib_str_len s - n \<le> k \<longrightarrow>
   (smtlib_str_len (smtlib_str_substr s n m) \<le> k) = True"
  apply (simp add: cvc_string_rewrite_defs)
  by auto

named_theorems rewrite_re_in_empty \<open>automatically_generated\<close>

lemma [rewrite_re_in_empty]:
  fixes t::"char list"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> smtlib_str_in_re t smtlib_re_none = False"
    by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_re_in_sigma \<open>automatically_generated\<close>

lemma [rewrite_re_in_sigma]:
  fixes t::"char list"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> smtlib_str_in_re t smtlib_re_allchar = (smtlib_str_len t = (1::int))"
    by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_re_in_sigma_star \<open>automatically_generated\<close>

lemma [rewrite_re_in_sigma_star]:
  fixes t::"char list"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> smtlib_str_in_re t (smtlib_re_star smtlib_re_allchar) = True"
  by (simp add: smtlib_str_in_re_def)

named_theorems rewrite_re_in_cstring \<open>automatically_generated\<close>

lemma [rewrite_re_in_cstring]:
  fixes t::"char list" and s::"char list"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> smtlib_str_in_re t (smtlib_str_to_re s) = (t = s)"
    by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_re_in_comp \<open>automatically_generated\<close>

lemma [rewrite_re_in_comp]:
  fixes t::"char list" and r::"char list set"
  shows "NO_MATCH cvc_a (undefined t r) \<Longrightarrow> smtlib_str_in_re t (smtlib_re_comp r) = (\<not> smtlib_str_in_re t r)"
    by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_str_concat_clash \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and t1::"char list" and t2::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 t1 t2) \<Longrightarrow> s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (cvc_list_right smtlib_str_concat s1 s2 =
    cvc_list_right smtlib_str_concat t1 t2) =
   False"
  apply (cases t2)
  apply (cases s2)
  subgoal for t2s s2s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction t2s arbitrary: t2)
    apply simp_all
    apply (induction s2s arbitrary: s2)
    apply simp_all
    apply (simp_all add: cvc_string_rewrite_defs)
    apply (simp_all add: cvc_rewrites_fold)
    by auto
  done


named_theorems rewrite_str_concat_clash_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash_rev]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and t1::"char list" and t2::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 t1 t2) \<Longrightarrow> s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (cvc_list_left smtlib_str_concat s2 s1 =
    cvc_list_left smtlib_str_concat t2 t1) =
   False"
  apply (cases t2)
  apply (cases s2)
  subgoal for t2s s2s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction t2s arbitrary: t2)
    apply simp_all
    apply (induction s2s arbitrary: s2)
    apply simp_all
    apply (simp_all add: cvc_string_rewrite_defs)
     apply (simp_all add: cvc_rewrites_fold)
     apply auto
    by (metis append.assoc append_eq_append_conv)
  done


named_theorems rewrite_str_concat_clash2 \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash2]:
  fixes s1::"char list" and t1::"char list" and t2::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 t1 t2) \<Longrightarrow> s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (s1 = cvc_list_right smtlib_str_concat t1 t2) = False"
  apply (cases t2)
  subgoal for t2s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction t2s arbitrary: t2)
    apply simp_all
    apply (simp_all add: cvc_string_rewrite_defs)
    apply (simp_all add: cvc_rewrites_fold)
    by auto
  done


named_theorems rewrite_str_concat_clash2_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash2_rev]:
  fixes s1::"char list" and t1::"char list" and t2::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 t1 t2) \<Longrightarrow> s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (s1 = cvc_list_left smtlib_str_concat t2 t1) = False"
  apply (cases t2)
  subgoal for t2s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction t2s arbitrary: t2)
    apply simp_all
    apply (simp_all add: cvc_string_rewrite_defs)
    apply (simp_all add: cvc_rewrites_fold)
    by auto
  done


named_theorems rewrite_str_concat_unify \<open>automatically_generated\<close>

lemma [rewrite_str_concat_unify]:
  fixes s1::"char list" and s2::"char list" and s3::"char list cvc_ListVar" and t2::"char list" and t3::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 s3 t2 t3) \<Longrightarrow> (cvc_list_right smtlib_str_concat (smtlib_str_concat s1 s2) s3 =
    cvc_list_right smtlib_str_concat (smtlib_str_concat s1 t2) t3) =
   (cvc_list_right smtlib_str_concat s2 s3 =
    cvc_list_right smtlib_str_concat t2 t3)"
  apply (cases t3)
  apply (cases s3)
  subgoal for t3s s3s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction t3s arbitrary: t3)
    apply simp_all
    apply (induction s3s arbitrary: s3)
    apply simp_all
    by (simp_all add: cvc_string_rewrite_defs)
  done


named_theorems rewrite_str_concat_unify_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_unify_rev]:
  fixes s1::"char list" and s2::"char list" and s3::"char list cvc_ListVar" and t2::"char list" and t3::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 s3 t2 t3) \<Longrightarrow> (smtlib_str_concat (cvc_list_right smtlib_str_concat s2 s3) s1 =
    smtlib_str_concat (cvc_list_right smtlib_str_concat t2 t3) s1) =
   (cvc_list_right smtlib_str_concat s2 s3 =
    cvc_list_right smtlib_str_concat t2 t3)"
  apply (cases t3)
  apply (cases s3)
  subgoal for t3s s3s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction t3s arbitrary: t3)
    apply simp_all
    apply (induction s3s arbitrary: s3)
    apply simp_all
    by (simp_all add: cvc_string_rewrite_defs)
  done


named_theorems rewrite_str_concat_clash_char \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash_char]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and s3::"char list cvc_ListVar" and t1::"char list" and t2::"char list cvc_ListVar" and t3::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 s3 t1 t2 t3) \<Longrightarrow> s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (cvc_list_right smtlib_str_concat
     (cvc_list_right smtlib_str_concat s1 s2) s3 =
    cvc_list_right smtlib_str_concat
     (cvc_list_right smtlib_str_concat t1 t2) t3) =
   False"
  apply (cases t3)
  apply (cases t2)
  apply (cases s3)
  apply (cases s2)
  subgoal for t3s t2s s3s s2s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction t3s arbitrary: t3)
    apply simp_all
    apply (induction t2s arbitrary: t2)
    apply simp_all
    apply (induction s3s arbitrary: s3)
    apply simp_all
    apply (induction s2s arbitrary: s2)
    apply simp_all
    apply (simp_all add: cvc_string_rewrite_defs)
     apply (simp_all add: cvc_rewrites_fold)
     apply (simp add: append_eq_conv_conj)
    by (simp add: append_eq_conv_conj)
  done


named_theorems rewrite_str_concat_clash_char_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash_char_rev]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and s3::"char list cvc_ListVar" and t1::"char list" and t2::"char list cvc_ListVar" and t3::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 s3 t1 t2 t3) \<Longrightarrow> s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (cvc_list_left smtlib_str_concat s3
     (cvc_list_left smtlib_str_concat s2 s1) =
    cvc_list_left smtlib_str_concat t3
     (cvc_list_left smtlib_str_concat t2 t1)) =
   False"
  apply (cases t3)
  apply (cases t2)
  apply (cases s3)
  apply (cases s2)
  subgoal for t3s t2s s3s s2s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: concat_clash_char_rev_lemma)
  done


named_theorems rewrite_str_prefixof_elim \<open>automatically_generated\<close>

lemma [rewrite_str_prefixof_elim]:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_prefixof s t =
   (s = smtlib_str_substr t (0::int) (smtlib_str_len s))"
   by (simp add: rewrite_str_prefixof_elim_lemma)

named_theorems rewrite_str_suffixof_elim \<open>automatically_generated\<close>

lemma [rewrite_str_suffixof_elim]:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_suffixof s t =
   (s =
    smtlib_str_substr t (smtlib_str_len t - smtlib_str_len s)
     (smtlib_str_len s))"
  by (simp add: smtlib_str_len_def smtlib_str_substr_def smtlib_str_suffixof_def str_suffixof_elim_lemma)

named_theorems rewrite_str_prefixof_one \<open>automatically_generated\<close>

lemma [rewrite_str_prefixof_one]:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_len t = (1::int) \<longrightarrow>
   smtlib_str_prefixof s t = smtlib_str_contains t s"
  by (simp add: smtlib_str_contains2_def smtlib_str_contains_equal smtlib_str_len_def smtlib_str_prefixof_def str_prefixof_one_lemma)

named_theorems rewrite_str_suffixof_one \<open>automatically_generated\<close>

lemma [rewrite_str_suffixof_one]:
  fixes s::"char list" and t::"char list"
  shows "NO_MATCH cvc_a (undefined s t) \<Longrightarrow> smtlib_str_len t = (1::int) \<longrightarrow>
   smtlib_str_suffixof s t = smtlib_str_contains t s"
  by (simp add: smtlib_str_contains2_def smtlib_str_contains_equal smtlib_str_len_def smtlib_str_suffixof_def str_suffixof_one_lemma)

named_theorems rewrite_str_substr_combine1 \<open>automatically_generated\<close>

lemma [rewrite_str_substr_combine1]:
  fixes s::"char list" and n1::"int" and m1::"int" and n2::"int" and m2::"int"
  shows "NO_MATCH cvc_a (undefined s n1 m1 n2 m2) \<Longrightarrow> (0::int) \<le> n1 \<and>
   (0::int) \<le> n2 \<and> (0::int) \<le> m2 - (m1 - n2) \<longrightarrow>
   smtlib_str_substr (smtlib_str_substr s n1 m1) n2 m2 =
   smtlib_str_substr s (n1 + n2) (m1 - n2)"
unfolding smtlib_str_substr_def[of s n1 m1]
  apply (cases "n1 < int (length s)")
   apply simp_all
   apply (cases "0 < m1 ")
    apply simp_all
  unfolding smtlib_str_substr_def[of "[]"]
    apply simp_all
  unfolding smtlib_str_substr_def[of s "(n1 + n2)" "(m1 - n2)"]
    apply simp_all
  apply (cases "n1 + n2 < int (length s)")
   apply simp_all
  apply (cases "n2 < m1")
    apply simp_all
    apply (cases "(nat m1)\<le> (length s - nat n1)")  
     apply simp_all
     apply (cases "(nat (m1 - n2)) \<le> (length s - nat (n1 + n2))")
      apply simp_all
  unfolding  smtlib_str_substr_def[of "(take (nat m1) (drop (nat n1) s))" n2 m2]
      apply simp
  apply (smt (verit, ccfv_threshold) add_diff_cancel_left' drop_drop drop_take le_add_diff_inverse2 min_absorb2 nat_diff_distrib' nat_mono take_take)
    using nat_int_comparison(3) apply force
    apply (smt (verit, ccfv_SIG) \<open>smtlib_str_substr (take (nat m1) (drop (nat n1) s)) n2 m2 \<equiv> if 0 \<le> n2 \<and> n2 < int (length (take (nat m1) (drop (nat n1) s))) \<and> 0 < m2 then take (min (nat m2) (length (take (nat m1) (drop (nat n1) s)) - nat n2)) (drop (nat n2) (take (nat m1) (drop (nat n1) s))) else []\<close> add_diff_cancel_left' drop_drop drop_take le_add_diff_inverse2 le_diff_iff length_drop min_absorb2 nat_diff_distrib' nat_le_linear nat_less_iff nat_mono order_less_le take_all_iff take_take)
    apply (simp add: \<open>smtlib_str_substr (take (nat m1) (drop (nat n1) s)) n2 m2 \<equiv> if 0 \<le> n2 \<and> n2 < int (length (take (nat m1) (drop (nat n1) s))) \<and> 0 < m2 then take (min (nat m2) (length (take (nat m1) (drop (nat n1) s)) - nat n2)) (drop (nat n2) (take (nat m1) (drop (nat n1) s))) else []\<close> nat_le_iff of_nat_diff)
    by (simp add: int_ops(6) of_nat_min smtlib_str_substr_def)



named_theorems rewrite_str_substr_combine2 \<open>automatically_generated\<close>

lemma [rewrite_str_substr_combine2]:
  fixes s::"char list" and n1::"int" and m1::"int" and n2::"int" and m2::"int"
  shows "NO_MATCH cvc_a (undefined s n1 m1 n2 m2) \<Longrightarrow> (0::int) \<le> n1 \<and>
   (0::int) \<le> n2 \<and> (0::int) \<le> m1 - n2 - m2 \<longrightarrow>
   smtlib_str_substr (smtlib_str_substr s n1 m1) n2 m2 =
   smtlib_str_substr s (n1 + n2) m2"
  unfolding smtlib_str_substr_def[of s n1 m1] apply simp
  apply (cases "n1 < int (length s)")
  apply simp_all
  unfolding smtlib_str_substr_def[of "[]"]
    apply simp_all
   apply (cases "0 < m1 ")
  apply simp_all
  unfolding smtlib_str_substr_def[of s "n1+n2" m2] apply simp
  apply (cases "(nat m1) \<le> (length s - nat n1)")
     apply simp_all
   apply (cases "n1 + n2 < int (length s) ")
    apply simp_all
  apply (cases "0 < m2")
     apply simp_all
  unfolding smtlib_str_substr_def[of "(take (nat m1) (drop (nat n1) s))" n2 m2]
     apply simp
  apply (smt (verit, del_insts) drop_drop drop_take min_absorb1 nat_0_le nat_add_distrib nat_diff_distrib' nat_int_comparison(3) take_take)
  apply presburger
  using int_ops(6) nat_le_iff apply force
  by (smt (verit) drop_drop length_drop nat_add_distrib nat_less_iff smtlib_str_substr_def zero_less_diff)

named_theorems rewrite_str_substr_concat1 \<open>automatically_generated\<close>

lemma [rewrite_str_substr_concat1]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and n::"int" and m::"int"
  shows "NO_MATCH cvc_a (undefined s1 s2 n m) \<Longrightarrow> (0::int) \<le> n \<and> n + m \<le> smtlib_str_len s1 \<longrightarrow>
   smtlib_str_substr (cvc_list_right smtlib_str_concat s1 s2) n m =
   smtlib_str_substr s1 n m"
   apply (cases s2)
  subgoal for s2s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: substr_concat1_lemma)
  done


named_theorems rewrite_str_substr_full \<open>automatically_generated\<close>

lemma [rewrite_str_substr_full]:
  fixes s::"char list" and n::"int"
  shows "NO_MATCH cvc_a (undefined s n) \<Longrightarrow> smtlib_str_len s \<le> n \<longrightarrow>
   smtlib_str_substr s (0::int) n = s"
  apply (simp add: cvc_string_rewrite_defs)
  using order_le_less by fastforce

named_theorems rewrite_str_contains_refl \<open>automatically_generated\<close>

lemma [rewrite_str_contains_refl]:
  fixes x::"char list"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> smtlib_str_contains x x = True"
  apply (simp add: cvc_string_rewrite_defs)
  by (metis append.left_neutral append_Nil2)

named_theorems rewrite_str_contains_concat_find \<open>automatically_generated\<close>

lemma [rewrite_str_contains_concat_find]:
  fixes xs::"char list cvc_ListVar" and y::"char list" and zs::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs y zs) \<Longrightarrow> smtlib_str_contains
    (cvc_list_right smtlib_str_concat (cvc_list_left smtlib_str_concat xs y)
      zs)
    y =
   True"
  apply (cases zs)
  apply (cases xs)
  subgoal for zss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss arbitrary: zs)
    apply simp_all
    apply (induction xss arbitrary: xs)
    apply simp_all
    apply (simp_all add: cvc_string_rewrite_defs)
      apply (simp_all add: cvc_rewrites_fold)
      apply (metis append.left_neutral append_Nil2)
    apply (metis append.assoc)
    by blast
  done


named_theorems rewrite_str_contains_split_char \<open>automatically_generated\<close>

lemma [rewrite_str_contains_split_char]:
  fixes x::"char list" and y::"char list" and z::"char list cvc_ListVar" and w::"char list"
  shows "NO_MATCH cvc_a (undefined x y z w) \<Longrightarrow> smtlib_str_len w = (1::int) \<longrightarrow>
   smtlib_str_contains
    (cvc_list_right smtlib_str_concat (smtlib_str_concat x y) z) w =
   (smtlib_str_contains x w \<or>
    smtlib_str_contains (cvc_list_right smtlib_str_concat y z) w)"
  apply (cases z)
  subgoal for zs 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: str_contains_split_char_lemma)
  done


named_theorems rewrite_str_contains_leq_len_eq \<open>automatically_generated\<close>

lemma [rewrite_str_contains_leq_len_eq]:
  fixes x::"char list" and y::"char list"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> smtlib_str_len x \<le> smtlib_str_len y \<longrightarrow>
   smtlib_str_contains x y = (x = y)"
  apply (induction x)
  using smtlib_str_contains2_def smtlib_str_contains_equal apply force
  using smtlib_str_contains_def smtlib_str_len_def by force

named_theorems rewrite_str_concat_emp \<open>automatically_generated\<close>

lemma [rewrite_str_concat_emp]:
  fixes xs::"char list cvc_ListVar" and ys::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_str_concat
    (cvc_list_left smtlib_str_concat xs (''''::char list)) ys =
   cvc_list_both smtlib_str_concat [] xs ys"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: str_concat_emp_lemma)
  done


named_theorems rewrite_str_at_elim \<open>automatically_generated\<close>

lemma [rewrite_str_at_elim]:
  fixes x::"char list" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> smtlib_str_at x n = smtlib_str_substr x n (1::int)"
    by (simp add: cvc_string_rewrite_defs)

named_theorems rewrite_re_all_elim \<open>automatically_generated\<close>

lemma [rewrite_re_all_elim]:
  shows "NO_MATCH cvc_a (undefined ) \<Longrightarrow> smtlib_re_all = smtlib_re_star smtlib_re_allchar"
  by (simp add: smtlib_re_all_def)

named_theorems rewrite_re_opt_elim \<open>automatically_generated\<close>

lemma [rewrite_re_opt_elim]:
  fixes x::"char list set"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> smtlib_re_opt x = smtlib_re_union (smtlib_str_to_re (''''::char list)) x"
  using smtlib_re_opt_def smtlib_re_union_def by auto

named_theorems rewrite_re_concat_emp \<open>automatically_generated\<close>

lemma [rewrite_re_concat_emp]:
  fixes xs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_re_concat
    (cvc_list_left smtlib_re_concat xs (smtlib_str_to_re (''''::char list)))
    ys =
   cvc_list_both smtlib_re_concat ({''''}::char list set) xs ys"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: re_concat_emp_lemma)
  done


named_theorems rewrite_re_concat_none \<open>automatically_generated\<close>

lemma [rewrite_re_concat_none]:
  fixes xs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_re_concat
    (cvc_list_left smtlib_re_concat xs smtlib_re_none) ys =
   smtlib_re_none"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss
    by (metis cvc_ListVar.exhaust cvc_bin_op2.simps cvc_list_left_transfer cvc_list_right_def ex_in_conv smtlib_re_concat_foldr smtlib_re_concat_ind.cases smtlib_re_concat_smtlib_re_concat_induct smtlib_re_none_def)
  done


named_theorems rewrite_re_concat_flatten \<open>automatically_generated\<close>

lemma [rewrite_re_concat_flatten]:
  fixes xs::"char list set cvc_ListVar" and s::"char list set" and ys::"char list set cvc_ListVar" and zs::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs s ys zs) \<Longrightarrow> cvc_list_right smtlib_re_concat
    (cvc_list_left smtlib_re_concat xs
      (cvc_list_right smtlib_re_concat s ys))
    zs =
   cvc_list_right smtlib_re_concat
    (cvc_list_right smtlib_re_concat (cvc_list_left smtlib_re_concat xs s)
      ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: re_concat_flatten_lemma)
  done


named_theorems rewrite_re_concat_star_swap \<open>automatically_generated\<close>

lemma [rewrite_re_concat_star_swap]:
  fixes xs::"char list set cvc_ListVar" and r::"char list set" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs r ys) \<Longrightarrow> cvc_list_right smtlib_re_concat
    (smtlib_re_concat (cvc_list_left smtlib_re_concat xs (smtlib_re_star r))
      r)
    ys =
   cvc_list_right smtlib_re_concat
    (smtlib_re_concat (cvc_list_left smtlib_re_concat xs r)
      (smtlib_re_star r))
    ys"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: re_concat_star_swap_lemma)
  done


named_theorems rewrite_re_union_all \<open>automatically_generated\<close>

lemma [rewrite_re_union_all]:
  fixes xs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_re_union
    (cvc_list_left smtlib_re_union xs (smtlib_re_star smtlib_re_allchar))
    ys =
   smtlib_re_star smtlib_re_allchar"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply simp
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction yss arbitrary: ys)
    apply simp_all
        apply (induction xss arbitrary: xs)
    apply simp_all
      apply (simp add: smtlib_re_union_def)
    apply (simp add: smtlib_re_union_def)
    using smtlib_re_union_def by auto
  done

named_theorems rewrite_re_union_flatten \<open>automatically_generated\<close>

lemma [rewrite_re_union_flatten]:
  fixes xs::"char list set cvc_ListVar" and b::"char list set" and ys::"char list set cvc_ListVar" and zs::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs b ys zs) \<Longrightarrow> cvc_list_right smtlib_re_union
    (cvc_list_left smtlib_re_union xs (cvc_list_right smtlib_re_union b ys))
    zs =
   cvc_list_right smtlib_re_union
    (cvc_list_right smtlib_re_union (cvc_list_left smtlib_re_union xs b) ys)
    zs"
 apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
      apply (induction zss arbitrary: zs)
     apply simp_all
      apply (induction yss arbitrary: ys)
     apply simp_all
    using cvc_ListOp_neutral_re_union apply force
         apply (induction xss arbitrary: xs)
      apply simp_all
    subgoal
  proof -
    fix a :: "char list set" and xssa :: "char list set list" and aa :: "char list set" and yssa :: "char list set list" and ysa :: "char list set cvc_ListVar" and xsa :: "char list set cvc_ListVar"
    assume a1: "smtlib_re_union (smtlib_re_union a (foldr smtlib_re_union xssa (smtlib_re_union b (foldr smtlib_re_union yssa {})))) {} = smtlib_re_union (smtlib_re_union (smtlib_re_union a (foldr smtlib_re_union xssa b)) (foldr smtlib_re_union yssa {})) {}"
    assume a2: "\<And>a yss ys xs. \<lbrakk>smtlib_re_union (foldr smtlib_re_union xssa (smtlib_re_union b (foldr smtlib_re_union yss {}))) {} = smtlib_re_union (smtlib_re_union (foldr smtlib_re_union xssa b) (foldr smtlib_re_union yss {})) {}; ys = ListVar (a # yss); xs = ListVar xssa\<rbrakk> \<Longrightarrow> smtlib_re_union (foldr smtlib_re_union xssa (smtlib_re_union b (smtlib_re_union a (foldr smtlib_re_union yss {})))) {} = smtlib_re_union (smtlib_re_union (foldr smtlib_re_union xssa b) (smtlib_re_union a (foldr smtlib_re_union yss {}))) {}"
    have f3: "\<And>C Ca. smtlib_re_union C Ca = C \<union> Ca"
      using smtlib_re_union_def by auto
    then have f4: "a \<union> foldr smtlib_re_union xssa b \<union> foldr smtlib_re_union yssa {} = a \<union> foldr smtlib_re_union xssa (b \<union> foldr smtlib_re_union yssa {})"
      using a1 by simp
    have "\<And>f C. foldr f ([]::char list set list) (C::char list set) = C"
      by auto
    then have "\<And>C. foldr smtlib_re_union xssa b \<union> C = foldr smtlib_re_union xssa (b \<union> C)"
      using f3 a2 by (metis sup_bot.right_neutral)
    then have "a \<union> (aa \<union> foldr smtlib_re_union xssa (b \<union> foldr smtlib_re_union yssa {})) = a \<union> foldr smtlib_re_union xssa (b \<union> (aa \<union> foldr smtlib_re_union yssa {}))"
      by (smt (z3) sup_aci(3))
    then show "smtlib_re_union (smtlib_re_union a (foldr smtlib_re_union xssa (smtlib_re_union b (smtlib_re_union aa (foldr smtlib_re_union yssa {}))))) {} = smtlib_re_union (smtlib_re_union (smtlib_re_union a (foldr smtlib_re_union xssa b)) (smtlib_re_union aa (foldr smtlib_re_union yssa {}))) {}"
      using f4 f3 by (simp add: sup_aci(3))
  qed
  using smtlib_re_union_def by auto
  done


named_theorems rewrite_re_union_dup \<open>automatically_generated\<close>

lemma [rewrite_re_union_dup]:
  fixes xs::"char list set cvc_ListVar" and b::"char list set" and ys::"char list set cvc_ListVar" and zs::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs b ys zs) \<Longrightarrow> cvc_list_right smtlib_re_union
    (smtlib_re_union
      (cvc_list_right smtlib_re_union (cvc_list_left smtlib_re_union xs b)
        ys)
      b)
    zs =
   cvc_list_right smtlib_re_union
    (cvc_list_right smtlib_re_union (cvc_list_left smtlib_re_union xs b) ys)
    zs"
 apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss arbitrary: zs)
     apply simp_all
      apply (induction yss arbitrary: ys)
      apply simp_all
        apply (induction xss arbitrary: xs)
      apply simp_all
    apply (simp add: smtlib_re_union_def)
    using smtlib_re_union_def apply auto[1]
    using smtlib_re_union_def apply auto[1]
    using smtlib_re_union_def by auto
  done

lemma rewrite_re_inter_all_h1: "smtlib_re_inter (foldr smtlib_re_inter xss UNIV) A = foldr smtlib_re_inter xss A"
  apply (induction xss)
  apply (simp add: smtlib_re_inter_def)
  apply simp
  by (smt (verit, ccfv_SIG) Collect_cong mem_Collect_eq smtlib_re_inter_def)


named_theorems rewrite_re_inter_all \<open>automatically_generated\<close>

lemma [rewrite_re_inter_all]:
  fixes xs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_re_inter
    (cvc_list_left smtlib_re_inter xs (smtlib_re_star smtlib_re_allchar))
    ys =
   cvc_list_both smtlib_re_inter (UNIV::char list set) xs ys"
 apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    using rewrite_re_inter_all_h1 by auto
  done


named_theorems rewrite_re_inter_none \<open>automatically_generated\<close>

lemma [rewrite_re_inter_none]:
  fixes xs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs ys) \<Longrightarrow> cvc_list_right smtlib_re_inter
    (cvc_list_left smtlib_re_inter xs smtlib_re_none) ys =
   smtlib_re_none"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction yss arbitrary: ys)
    apply simp_all
        apply (induction xss arbitrary: xs)
      apply simp_all
    using cvc_ListOp_neutral_re_inter apply force
    apply (simp add: smtlib_re_inter_def smtlib_re_none_def)
    using smtlib_re_inter_def smtlib_re_none_def by auto
  done


named_theorems rewrite_re_inter_flatten \<open>automatically_generated\<close>

lemma rewrite_re_inter_flatten_h1: "smtlib_re_inter (foldr smtlib_re_inter xss (smtlib_re_inter b (foldr smtlib_re_inter yss UNIV))) A =
    smtlib_re_inter (smtlib_re_inter (foldr smtlib_re_inter xss b) (foldr smtlib_re_inter yss UNIV)) A"
  apply (induction xss)
   apply simp_all
  by (smt (verit) Int_commute Int_def Int_left_commute smtlib_re_inter_def)


lemma [rewrite_re_inter_flatten]:
  fixes xs::"char list set cvc_ListVar" and b::"char list set" and ys::"char list set cvc_ListVar" and zs::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs b ys zs) \<Longrightarrow> cvc_list_right smtlib_re_inter
    (cvc_list_left smtlib_re_inter xs (cvc_list_right smtlib_re_inter b ys))
    zs =
   cvc_list_right smtlib_re_inter
    (cvc_list_right smtlib_re_inter (cvc_list_left smtlib_re_inter xs b) ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: rewrite_re_inter_flatten_h1)
  done


named_theorems rewrite_re_inter_dup \<open>automatically_generated\<close>

lemma [rewrite_re_inter_dup]:
  fixes xs::"char list set cvc_ListVar" and b::"char list set" and ys::"char list set cvc_ListVar" and zs::"char list set cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined xs b ys zs) \<Longrightarrow> cvc_list_right smtlib_re_inter
    (smtlib_re_inter
      (cvc_list_right smtlib_re_inter (cvc_list_left smtlib_re_inter xs b)
        ys)
      b)
    zs =
   cvc_list_right smtlib_re_inter
    (cvc_list_right smtlib_re_inter (cvc_list_left smtlib_re_inter xs b) ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss arbitrary: zs)
     apply simp_all
      apply (induction yss arbitrary: ys)
      apply simp_all
        apply (induction xss arbitrary: xs)
      apply simp_all
    apply (simp add: smtlib_re_inter_def)
    using smtlib_re_inter_def apply auto[1]
    using smtlib_re_inter_def apply auto[1]
    using smtlib_re_inter_def by auto
  done


named_theorems rewrite_str_len_concat_rec \<open>automatically_generated\<close>

lemma [rewrite_str_len_concat_rec]:
  fixes s1::"char list" and s2::"char list" and s3::"char list cvc_ListVar"
  shows "NO_MATCH cvc_a (undefined s1 s2 s3) \<Longrightarrow> smtlib_str_len
    (cvc_list_right smtlib_str_concat (smtlib_str_concat s1 s2) s3) =
   smtlib_str_len s1 +
   smtlib_str_len (cvc_list_right smtlib_str_concat s2 s3)"
  apply (cases s3)
  subgoal for s3s 
    by (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
  done


named_theorems rewrite_str_in_re_range_elim \<open>automatically_generated\<close>

lemma h1: "(of_char c1::int) \<ge> -1"
  unfolding of_char_def by simp

lemma h2: "(of_char c1::int) > -1"
  unfolding of_char_def by simp


lemma [rewrite_str_in_re_range_elim]:
  fixes s::"char list" and c1::"char list" and c2::"char list"
  shows "smtlib_str_len c1 = (1::int) \<Longrightarrow>
   smtlib_str_len c2 = (1::int) \<Longrightarrow>
   smtlib_str_in_re s (smtlib_re_range c1 c2) =
   (smtlib_str_to_code c1 \<le> smtlib_str_to_code s \<and>
    smtlib_str_to_code s \<le> smtlib_str_to_code c2)"
  apply (rule iffI)
  unfolding smtlib_str_to_code_def smtlib_str_len_def
  apply simp
  unfolding smtlib_str_in_re_def smtlib_re_range_def smtlib_str_leq_def smtlib_str_less_def
  apply simp
  apply (case_tac [!] "length s")
   apply simp_all
   apply (case_tac [!] c2)
     apply simp_all
   apply (case_tac [!] c1)
   apply simp_all
  using order_le_less string_comp.elims(2) apply fastforce
  subgoal for c2' c2s c1'
    apply (cases "c2' = CHR 0x00")
     apply simp_all
    apply (cases "c1' = CHR 0x00")
      apply (simp_all add: h1)
    using String_Rewrites.h2 linorder_not_le apply blast
    using String_Rewrites.h2 linorder_not_le by blast
  by (smt (verit, ccfv_SIG) String_Rewrites.h2 Suc_length_conv char_of_char length_greater_0_conv list.size(3) nth_Cons_0 string_comp.simps(3))

end