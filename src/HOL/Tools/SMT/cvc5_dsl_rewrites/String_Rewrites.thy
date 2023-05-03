theory String_Rewrites
  imports Dsl_Nary_Ops String_Rewrites_Lemmas
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

named_theorems rewrite_str_eq_ctn_false \<open>automatically_generated\<close>

lemma [rewrite_str_eq_ctn_false]:
  fixes x1::"char list cvc_ListVar" and x::"char list" and x2::"char list cvc_ListVar" and y::"char list"
  shows "smtlib_str_contains y x = False \<longrightarrow>
   (cvc_list_right smtlib_str_concat (cvc_list_left smtlib_str_concat x1 x)
     x2 =
    y) =
   False"
  apply (cases x2)
  apply (cases x1)
  subgoal for x2s x1s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: str_eq_ctn_false_lemma)
  done

named_theorems rewrite_str_concat_flatten \<open>automatically_generated\<close>

lemma [rewrite_str_concat_flatten]:
  fixes xs::"char list cvc_ListVar" and s::"char list" and ys::"char list cvc_ListVar" and zs::"char list cvc_ListVar"
  shows "cvc_list_right smtlib_str_concat
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
    by (simp add: str_concat_flatten_lemma)
  done

named_theorems rewrite_str_concat_flatten_eq \<open>automatically_generated\<close>

lemma [rewrite_str_concat_flatten_eq]:
  fixes x::"char list" and x1::"char list cvc_ListVar" and x2::"char list cvc_ListVar" and y::"char list"
  shows "(cvc_list_right smtlib_str_concat (cvc_list_right smtlib_str_concat x x1)
     x2 =
    y) =
   (y =
    cvc_list_right smtlib_str_concat (cvc_list_right smtlib_str_concat x x1)
     x2)"
  apply (cases x2)
  apply (cases x1)
  subgoal for x2s x1s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: str_concat_flatten_eq_lemma)
  done

named_theorems rewrite_str_concat_flatten_eq_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_flatten_eq_rev]:
  fixes x::"char list" and x1::"char list cvc_ListVar" and x2::"char list cvc_ListVar" and y::"char list"
  shows "(cvc_list_left smtlib_str_concat x2
     (cvc_list_left smtlib_str_concat x1 x) =
    y) =
   (y = smtlib_str_concat (cvc_list_both smtlib_str_concat [] x2 x1) x)"
  apply (cases x2)
  apply (cases x1)
  subgoal for x2s x1s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: str_concat_flatten_eq_rev_lemma)
  done

named_theorems rewrite_str_substr_empty_str \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_str]:
  fixes n::"int" and m::"int"
  shows "smtlib_str_substr (''''::char list) n m = ''''"
  unfolding smtlib_str_substr_def
  by simp

named_theorems rewrite_str_substr_empty_range \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_range]:
  fixes x::"char list" and n::"int" and m::"int"
  shows "m \<le> (0::int) \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
  unfolding smtlib_str_substr_def
  by simp

named_theorems rewrite_str_substr_empty_start \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_start]:
  fixes x::"char list" and n::"int" and m::"int"
  shows "smtlib_str_len x \<le> n \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
  unfolding smtlib_str_substr_def smtlib_str_len_def
  by simp

named_theorems rewrite_str_substr_empty_start_neg \<open>automatically_generated\<close>

lemma [rewrite_str_substr_empty_start_neg]:
  fixes x::"char list" and n::"int" and m::"int"
  shows "n < (0::int) \<longrightarrow>
   smtlib_str_substr x n m = (''''::char list)"
  unfolding smtlib_str_substr_def smtlib_str_len_def
  by simp

named_theorems rewrite_str_substr_eq_empty \<open>automatically_generated\<close>

lemma [rewrite_str_substr_eq_empty]:
  fixes s::"char list" and n::"int" and m::"int"
  shows "n = (0::int) \<and> n < m \<longrightarrow>
   (smtlib_str_substr s n m = (''''::char list)) = (s = '''')"
  unfolding smtlib_str_substr_def smtlib_str_len_def
  by simp

named_theorems rewrite_str_len_replace_inv \<open>automatically_generated\<close>

lemma [rewrite_str_len_replace_inv]:
  fixes t::"char list" and s::"char list" and r::"char list"
  shows "smtlib_str_len s = smtlib_str_len r \<longrightarrow>
   smtlib_str_len (smtlib_str_replace t s r) = smtlib_str_len t"
  using smtlib_str_len_def smtlib_str_replace_def smtlib_str_replace_length by presburger

named_theorems rewrite_str_len_substr_in_range \<open>automatically_generated\<close>

lemma [rewrite_str_len_substr_in_range]:
  fixes s::"char list" and n::"int" and m::"int"
  shows "(0::int) \<le> n \<and>
   (0::int) \<le> m \<and> n + m \<le> smtlib_str_len s \<longrightarrow>
   smtlib_str_len (smtlib_str_substr s n m) = m"
  using smtlib_str_len_def smtlib_str_substr_length by force

named_theorems rewrite_str_len_substr_ub1 \<open>automatically_generated\<close>

lemma [rewrite_str_len_substr_ub1]:
  fixes s::"char list" and n::"int" and m::"int" and k::"int"
  shows "m \<le> k \<longrightarrow> k \<ge> 0 \<longrightarrow>
   (smtlib_str_len (smtlib_str_substr s n m) \<le> k) = True"
  by (simp add: min_def nat_le_iff)

named_theorems rewrite_str_len_substr_ub2 \<open>automatically_generated\<close>

lemma [rewrite_str_len_substr_ub2]:
  fixes s::"char list" and n::"int" and m::"int" and k::"int"
  shows "smtlib_str_len s - n \<le> k \<longrightarrow> k \<ge> 0 \<longrightarrow>
   (smtlib_str_len (smtlib_str_substr s n m) \<le> k) = True"
  using smtlib_str_substr_length[of s n m]
  unfolding smtlib_str_len_def
  by auto

named_theorems rewrite_re_in_empty \<open>automatically_generated\<close>

lemma [rewrite_re_in_empty]:
  fixes t::"char list"
  shows "smtlib_str_in_re t smtlib_re_none = False"
  by (simp add: smtlib_re_none_def smtlib_str_in_re_def)

named_theorems rewrite_re_in_sigma \<open>automatically_generated\<close>

lemma [rewrite_re_in_sigma]:
  fixes t::"char list"
  shows "smtlib_str_in_re t smtlib_re_allchar = (smtlib_str_len t = (1::int))"
  by (simp add: smtlib_re_allchar_def smtlib_str_in_re_def smtlib_str_len_def)

named_theorems rewrite_re_in_sigma_star \<open>automatically_generated\<close>

lemma [rewrite_re_in_sigma_star]:
  fixes t::"char list"
  shows "smtlib_str_in_re t (smtlib_re_star smtlib_re_allchar) = True"
  by (simp add: smtlib_str_in_re_def)

named_theorems rewrite_re_in_cstring \<open>automatically_generated\<close>

lemma [rewrite_re_in_cstring]:
  fixes t::"char list" and s::"char list"
  shows "smtlib_str_in_re t (smtlib_str_to_re s) = (t = s)"
  by (simp add: smtlib_str_in_re_def smtlib_str_to_re_def)

named_theorems rewrite_re_in_comp \<open>automatically_generated\<close>

lemma [rewrite_re_in_comp]:
  fixes t::"char list" and r::"char list set"
  shows "smtlib_str_in_re t (smtlib_re_comp r) = (\<not> smtlib_str_in_re t r)"
  by (simp add: smtlib_re_comp_def smtlib_str_in_re_def)

named_theorems rewrite_str_concat_clash \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and t1::"char list" and t2::"char list cvc_ListVar"
  shows "s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (cvc_list_right smtlib_str_concat s1 s2 =
    cvc_list_right smtlib_str_concat t1 t2) =
   False"
  apply (cases t2)
  apply (cases s2)
  subgoal for t2s s2s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: concat_clash_lemma)
  done

named_theorems rewrite_str_concat_clash_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash_rev]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and t1::"char list" and t2::"char list cvc_ListVar"
  shows "s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (cvc_list_left smtlib_str_concat s2 s1 =
    cvc_list_left smtlib_str_concat t2 t1) =
   False"
  apply (cases t2)
  apply (cases s2)
  subgoal for t2s s2s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: concat_clash_rev_lemma)
  done

named_theorems rewrite_str_concat_clash2 \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash2]:
  fixes s1::"char list" and t1::"char list" and t2::"char list cvc_ListVar"
  shows "s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (s1 = cvc_list_right smtlib_str_concat t1 t2) = False"
  apply (cases t2)
  subgoal for t2s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: concat_clash2_lemma)
  done

named_theorems rewrite_str_concat_clash2_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash2_rev]:
  fixes s1::"char list" and t1::"char list" and t2::"char list cvc_ListVar"
  shows "s1 \<noteq> t1 \<and>
   smtlib_str_len s1 = smtlib_str_len t1 \<longrightarrow>
   (s1 = cvc_list_left smtlib_str_concat t2 t1) = False"
  apply (cases t2)
  subgoal for t2s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: concat_clash2_rev_lemma)
  done

named_theorems rewrite_str_concat_unify \<open>automatically_generated\<close>

lemma [rewrite_str_concat_unify]:
  fixes s1::"char list" and s2::"char list" and s3::"char list cvc_ListVar" and t2::"char list" and t3::"char list cvc_ListVar"
  shows "(cvc_list_right smtlib_str_concat (smtlib_str_concat s1 s2) s3 =
    cvc_list_right smtlib_str_concat (smtlib_str_concat s1 t2) t3) =
   (cvc_list_right smtlib_str_concat s2 s3 =
    cvc_list_right smtlib_str_concat t2 t3)"
  apply (cases t3)
  apply (cases s3)
  subgoal for t3s s3s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: concat_unify_lemma)
  done

named_theorems rewrite_str_concat_unify_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_unify_rev]:
  fixes s1::"char list" and s2::"char list" and s3::"char list cvc_ListVar" and t2::"char list" and t3::"char list cvc_ListVar"
  shows "(smtlib_str_concat (cvc_list_right smtlib_str_concat s2 s3) s1 =
    smtlib_str_concat (cvc_list_right smtlib_str_concat t2 t3) s1) =
   (cvc_list_right smtlib_str_concat s2 s3 =
    cvc_list_right smtlib_str_concat t2 t3)"
  apply (cases t3)
  apply (cases s3)
  subgoal for t3s s3s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: concat_unify_rev_lemma)
  done

named_theorems rewrite_str_concat_clash_char \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash_char]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and s3::"char list cvc_ListVar" and t1::"char list" and t2::"char list cvc_ListVar" and t3::"char list cvc_ListVar"
  shows "s1 \<noteq> t1 \<and>
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
    by (simp add: concat_clash_char_lemma)
  done

named_theorems rewrite_str_concat_clash_char_rev \<open>automatically_generated\<close>

lemma [rewrite_str_concat_clash_char_rev]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and s3::"char list cvc_ListVar" and t1::"char list" and t2::"char list cvc_ListVar" and t3::"char list cvc_ListVar"
  shows "s1 \<noteq> t1 \<and>
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
  shows "smtlib_str_prefixof s t =
   (s = smtlib_str_substr t (0::int) (smtlib_str_len s))"
  unfolding smtlib_str_prefixof_def smtlib_str_substr_def smtlib_str_len_def
  apply simp
  by (metis append_eq_conv_conj min_def prefixE prefix_length_le take_is_prefix)

named_theorems rewrite_str_suffixof_elim \<open>automatically_generated\<close>

lemma [rewrite_str_suffixof_elim]:
  fixes s::"char list" and t::"char list"
  shows "smtlib_str_suffixof s t =
   (s =
    smtlib_str_substr t (smtlib_str_len t - smtlib_str_len s)
     (smtlib_str_len s))"
  by (simp add: smtlib_str_len_def smtlib_str_substr_def smtlib_str_suffixof_def str_suffixof_elim_lemma)

named_theorems rewrite_str_prefixof_one \<open>automatically_generated\<close>

lemma [rewrite_str_prefixof_one]:
  fixes s::"char list" and t::"char list"
  shows "smtlib_str_len t = (1::int) \<longrightarrow>
   smtlib_str_prefixof s t = smtlib_str_contains t s"
   by (simp add: smtlib_str_contains2_def smtlib_str_contains_equal smtlib_str_len_def smtlib_str_prefixof_def str_prefixof_one_lemma)

named_theorems rewrite_str_suffixof_one \<open>automatically_generated\<close>

lemma [rewrite_str_suffixof_one]:
  fixes s::"char list" and t::"char list"
  shows "smtlib_str_len t = (1::int) \<longrightarrow>
   smtlib_str_suffixof s t = smtlib_str_contains t s"
   by (simp add: smtlib_str_contains2_def smtlib_str_contains_equal smtlib_str_len_def smtlib_str_suffixof_def str_suffixof_one_lemma)

named_theorems rewrite_str_substr_combine \<open>automatically_generated\<close>

lemma [rewrite_str_substr_combine]:
  fixes s::"char list" and n1::"int" and m1::"int" and n2::"int" and m2::"int"
  shows "(0::int) \<le> n2 \<and> (0::int) \<le> n2 + m2 - m1 \<longrightarrow>
   smtlib_str_substr (smtlib_str_substr s n1 m1) n2 m2 =
   smtlib_str_substr s (n1 + n2) m2"
  oops


named_theorems rewrite_str_substr_concat1 \<open>automatically_generated\<close>

lemma [rewrite_str_substr_concat1]:
  fixes s1::"char list" and s2::"char list cvc_ListVar" and n::"int" and m::"int"
  shows "(0::int) \<le> n \<and> n + m \<le> smtlib_str_len s1 \<longrightarrow>
   smtlib_str_substr (cvc_list_right smtlib_str_concat s1 s2) n m =
   smtlib_str_substr s1 n m"
  apply (cases s2)
  subgoal for s2s 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: substr_concat1_lemma)
  done

named_theorems rewrite_str_contains_refl \<open>automatically_generated\<close>

lemma [rewrite_str_contains_refl]:
  fixes x::"char list"
  shows "smtlib_str_contains x x = True"
  by (metis append.right_neutral append_self_conv2 smtlib_str_contains2_def smtlib_str_contains_equal)

named_theorems rewrite_str_contains_split_char \<open>automatically_generated\<close>

lemma [rewrite_str_contains_split_char]:
  fixes x::"char list" and y::"char list" and z::"char list cvc_ListVar" and w::"char list"
  shows "smtlib_str_len w = (1::int) \<longrightarrow>
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
  shows "smtlib_str_len x \<le> smtlib_str_len y \<longrightarrow>
   smtlib_str_contains x y = (x = y)"
  apply (induction x)
  using smtlib_str_contains2_def smtlib_str_contains_equal apply force
  using smtlib_str_contains_def smtlib_str_len_def by force


named_theorems rewrite_str_concat_emp \<open>automatically_generated\<close>

lemma [rewrite_str_concat_emp]:
  fixes xs::"char list cvc_ListVar" and ys::"char list cvc_ListVar"
  shows "cvc_list_right smtlib_str_concat
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
  shows "smtlib_str_at x n = smtlib_str_substr x n (1::int)"
    by (simp add: smtlib_str_at_def)


named_theorems rewrite_re_concat_emp \<open>automatically_generated\<close>

lemma [rewrite_re_concat_emp]:
  fixes xs::"char list set cvc_ListVar" and ys::"char list set cvc_ListVar"
  shows "cvc_list_right smtlib_re_concat
    (cvc_list_left smtlib_re_concat xs (smtlib_str_to_re (''''::char list)))
    ys =
   cvc_list_both smtlib_re_concat ({''''}::char list set) xs ys"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: re_concat_emp_lemma)
  done

named_theorems rewrite_re_concat_flatten \<open>automatically_generated\<close>

lemma [rewrite_re_concat_flatten]:
  fixes xs::"char list set cvc_ListVar" and s::"char list set" and ys::"char list set cvc_ListVar" and zs::"char list set cvc_ListVar"
  shows "cvc_list_right smtlib_re_concat
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
  shows "cvc_list_right smtlib_re_concat
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

named_theorems rewrite_str_in_re_range_elim \<open>automatically_generated\<close>

lemma [rewrite_str_in_re_range_elim]:
  fixes s::"char list" and c1::"char list" and c2::"char list"
  shows "smtlib_str_len c1 = (1::int) \<Longrightarrow>
   smtlib_str_len c2 = (1::int) \<Longrightarrow>
   smtlib_str_in_re s (smtlib_re_range c1 c2) =
   (smtlib_str_to_code c1 \<le> smtlib_str_to_code s \<and>
    smtlib_str_to_code s \<le> smtlib_str_to_code c2)"
  unfolding smtlib_str_to_code_def smtlib_str_len_def
  apply simp
  unfolding smtlib_str_in_re_def smtlib_re_range_def smtlib_str_leq_def smtlib_str_less_def
  apply simp
  apply (induction s)
  apply simp_all
   apply (cases c1)
    apply simp
   apply simp
   apply (cases c2)
    apply simp_all
  unfolding of_char_def
  




end