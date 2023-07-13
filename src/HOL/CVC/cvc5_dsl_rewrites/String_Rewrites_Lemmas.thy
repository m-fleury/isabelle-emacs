theory String_Rewrites_Lemmas
  imports Dsl_Nary_Ops
begin


lemma str_eq_ctn_false_lemma:
"\<not> smtlib_str_contains y x \<Longrightarrow> smtlib_str_concat (foldr smtlib_str_concat x1s x) (foldr smtlib_str_concat x2s []) \<noteq> y"
    unfolding smtlib_str_concat_def
    by (metis append.assoc fold_append_concat_rev foldr_conv_fold smtlib_str_contains2_def smtlib_str_contains_equal)

lemma str_concat_flatten_lemma:
  "smtlib_str_concat (foldr smtlib_str_concat xs (smtlib_str_concat s (foldr smtlib_str_concat ys []))) (foldr smtlib_str_concat zs []) =
    smtlib_str_concat (smtlib_str_concat (foldr smtlib_str_concat xs s) (foldr smtlib_str_concat ys [])) (foldr smtlib_str_concat zs [])"
  unfolding smtlib_str_concat_def
  apply (induction xs)
  by simp_all

lemma str_concat_flatten_eq_lemma: 
"(smtlib_str_concat (smtlib_str_concat x (foldr smtlib_str_concat x1 [])) (foldr smtlib_str_concat x2 []) = y) =
    (y = smtlib_str_concat (smtlib_str_concat x (foldr smtlib_str_concat x1 [])) (foldr smtlib_str_concat x2 []))"
  by blast

lemma str_concat_flatten_eq_rev_lemma:
"(foldr smtlib_str_concat x2 (foldr smtlib_str_concat x1 x) = y) = (y = smtlib_str_concat (foldr smtlib_str_concat x2 (foldr smtlib_str_concat x1 [])) x)"
  unfolding smtlib_str_concat_def
  apply (induction x1)
  apply (induction x2)
    apply simp_all
    apply blast
  apply (metis append.right_neutral fold_append_concat_rev foldr_conv_fold)
  by (metis append.assoc append.monoid_axioms fold_append_concat_rev foldr_conv_fold monoid.right_neutral)

lemma concat_clash_lemma:
  "s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<Longrightarrow>
    smtlib_str_concat s1 (foldr smtlib_str_concat s2 []) \<noteq>
    smtlib_str_concat t1 (foldr smtlib_str_concat t2 [])"
  unfolding smtlib_str_len_def smtlib_str_concat_def
  by simp

lemma concat_clash_rev_lemma:
  "s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<Longrightarrow>
    foldr smtlib_str_concat s2 s1 \<noteq> foldr smtlib_str_concat t2 t1"
  unfolding smtlib_str_len_def smtlib_str_concat_def
  apply simp
  apply (induction s1)
   apply simp_all
   apply (induction t1)
    apply simp_all
  by (simp add: fold_append_concat_rev foldr_conv_fold)

lemma concat_clash2_lemma:
"s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<Longrightarrow>
    s1 \<noteq> smtlib_str_concat t1 (foldr smtlib_str_concat t2 [])"
  unfolding smtlib_str_concat_def smtlib_str_len_def
  apply simp
  apply (induction s1)
   apply simp_all
   apply (induction t1)
    apply simp_all
  by (metis Suc_length_conv append_Nil2 append_eq_append_conv)


lemma concat_clash2_rev_lemma:
"s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<Longrightarrow> s1 \<noteq> foldr smtlib_str_concat t2 t1"
  unfolding smtlib_str_concat_def smtlib_str_len_def
  oops 

lemma concat_unify_lemma:
"    (smtlib_str_concat (smtlib_str_concat s1 s2) (foldr smtlib_str_concat s3 []) =
     smtlib_str_concat (smtlib_str_concat s1 t2) (foldr smtlib_str_concat t3 [])) =
    (smtlib_str_concat s2 (foldr smtlib_str_concat s3 []) =
     smtlib_str_concat t2 (foldr smtlib_str_concat t3 []))"
  unfolding smtlib_str_concat_def
  by simp

lemma concat_unify_rev_lemma:
"(smtlib_str_concat (smtlib_str_concat s2 (foldr smtlib_str_concat s3 [])) s1 =
     smtlib_str_concat (smtlib_str_concat t2 (foldr smtlib_str_concat t3 [])) s1) =
    (smtlib_str_concat s2 (foldr smtlib_str_concat s3 []) =
     smtlib_str_concat t2 (foldr smtlib_str_concat t3 []))"
  unfolding smtlib_str_concat_def
  by simp

lemma concat_clash_char_lemma:
"  s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<Longrightarrow>
    smtlib_str_concat (smtlib_str_concat s1 (foldr smtlib_str_concat s2 []))
     (foldr smtlib_str_concat s3 []) \<noteq>
    smtlib_str_concat (smtlib_str_concat t1 (foldr smtlib_str_concat t2 []))
     (foldr smtlib_str_concat t3 [])"
  unfolding smtlib_str_concat_def smtlib_str_len_def
  by simp

lemma concat_clash_char_rev_lemma: 
"s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<Longrightarrow>
    foldr smtlib_str_concat s3 (foldr smtlib_str_concat s2 s1) \<noteq>
    foldr smtlib_str_concat t3 (foldr smtlib_str_concat t2 t1)"
  unfolding smtlib_str_concat_def smtlib_str_len_def
  apply (induction s1)
  apply simp_all
   apply (induction t1)
  apply simp_all
  by (metis concat_clash_rev_lemma smtlib_str_concat_def smtlib_str_len_def foldr_append length_Cons of_nat_Suc)

lemma rewrite_str_prefixof_elim_lemma:
  fixes s::"char list" and t::"char list"
  shows "smtlib_str_prefixof s t =
   (s = smtlib_str_substr t (0::int) (smtlib_str_len s))"
  unfolding smtlib_str_prefixof_def smtlib_str_substr_def smtlib_str_len_def
  apply simp
  by (metis append_eq_conv_conj min_def prefixE prefix_length_le take_is_prefix)

lemma str_suffixof_elim_lemma:
"(length s \<le> length t \<and> s \<noteq> [] \<longrightarrow>
     suffix s t = (s = drop (nat (int (length t) - int (length s))) t)) \<and>
    ((length s \<le> length t \<longrightarrow> s = []) \<longrightarrow> suffix s t = (s = []))"
    apply (cases "length s \<le> length t \<and> s \<noteq> [] ")
     apply simp_all
  apply (metis (no_types, lifting) append_eq_append_conv diff_diff_cancel length_drop nat_diff_distrib' nat_int of_nat_0_le_iff suffix_def suffix_drop)
  using suffix_bot.bot_least suffix_length_le by blast

lemma str_prefixof_one_lemma:
" int (length t) = 1 \<Longrightarrow>  prefix s t = (\<exists>w1 w3. t = w1 @ s @ w3)"
  apply (cases "length s = 1")
   apply simp_all
  apply (metis (no_types, lifting) add_is_1 append_eq_append_conv2 append_self_conv2 length_append length_greater_0_conv prefix_def)
  by (metis add_is_1 append_self_conv2 length_append length_greater_0_conv prefix_append prefix_def)

lemma str_suffixof_one_lemma:
"  int (length t) = 1 \<Longrightarrow> suffix s t = (\<exists>w1 w3. t = w1 @ s @ w3)"
  apply (cases "length s = 1")
   apply simp_all
  apply (metis Nil_is_append_conv add_is_1 append.right_neutral length_append length_greater_0_conv suffix_def)
  by (metis Nil_is_append_conv add_is_1 append_Nil2 length_0_conv length_append suffixE suffixI)

lemma
"0 \<le> n \<and> n + m \<le> smtlib_str_len s1 \<Longrightarrow> smtlib_str_substr (smtlib_str_concat s1 (foldr smtlib_str_concat s2 [])) n m = smtlib_str_substr s1 n m"
  unfolding smtlib_str_substr_def smtlib_str_concat_def smtlib_str_len_def
  apply simp
  by (simp add: linorder_not_less nat_le_iff nat_minus_as_int take_eq_Nil2 zero_less_diff)

lemma re_concat_flatten_lemma:
  "smtlib_re_concat (foldr smtlib_re_concat xs (smtlib_re_concat s (foldr smtlib_re_concat ys {[]}))) (foldr smtlib_re_concat zs {[]}) =
    smtlib_re_concat (smtlib_re_concat (foldr smtlib_re_concat xs s) (foldr smtlib_re_concat ys {[]})) (foldr smtlib_re_concat zs {[]})"
  using smtlib_re_concat_foldr by simp

lemma 
  "smtlib_re_concat (foldr smtlib_re_concat xs (smtlib_str_to_re []))
     (foldr smtlib_re_concat ys {[]}) =
    foldr smtlib_re_concat xs (foldr smtlib_re_concat ys {[]})"
  apply (induction xs)
   apply simp
  apply (meson cvc_ListOp_neutral_re_concat cvc_isListOp.simps)
  by (metis cvc_list_left_Cons cvc_list_left_transfer smtlib_re_concat_foldr)

lemma re_concat_star_swap_lemma:
"    smtlib_re_concat
     (smtlib_re_concat (foldr smtlib_re_concat xs (smtlib_re_star r)) r)
     (foldr smtlib_re_concat ys {[]}) =
    smtlib_re_concat
     (smtlib_re_concat (foldr smtlib_re_concat xs r) (smtlib_re_star r))
     (foldr smtlib_re_concat ys {[]})"
  apply (rule HOL.arg_cong[of "(smtlib_re_concat (foldr smtlib_re_concat xs (smtlib_re_star r)) r)"])
  by (metis re_concat_star_swap smtlib_re_concat_foldr smtlib_re_star_def)

lemma re_concat_emp_lemma:
"smtlib_re_concat (foldr smtlib_re_concat xs {[]}) (foldr smtlib_re_concat ys {[]}) = foldr smtlib_re_concat xs (foldr smtlib_re_concat ys {[]})"
  apply (induction xs)
   apply simp_all
    apply (simp add: smtlib_re_concat_def)
   apply (induction ys)
    apply (simp add: smtlib_re_concat_def)
      apply (simp add: smtlib_re_concat_def)
  apply (induction ys)
  using cvc_ListOp_neutral_re_concat apply auto[1]
  by (metis cvc_list_left_Cons cvc_list_left_transfer smtlib_re_concat_foldr)

lemma str_concat_emp_lemma:
  "smtlib_str_concat (foldr smtlib_str_concat xs []) (foldr smtlib_str_concat ys []) = foldr smtlib_str_concat xs (foldr smtlib_str_concat ys [])"
  apply (induction xs)
  apply (induction ys)
  apply (simp add: smtlib_str_concat_def)
   apply (simp add: smtlib_str_concat_def)
  apply (induction ys)
  apply (simp add: smtlib_str_concat_def)
  by (simp add: smtlib_str_concat_def)

lemma substr_concat1_lemma:
 "0 \<le> n \<and> n + m \<le> smtlib_str_len s1 \<Longrightarrow> smtlib_str_substr (smtlib_str_concat s1 (foldr smtlib_str_concat s2 [])) n m = smtlib_str_substr s1 n m"
  unfolding smtlib_str_substr_def smtlib_str_concat_def
  apply (induction s2)
   apply simp
  by (simp add: nat_le_iff of_nat_diff smtlib_str_len_def)

lemma concat_clash2_rev_lemma:
"s1 \<noteq> t1 \<and> smtlib_str_len s1 = smtlib_str_len t1 \<Longrightarrow> s1 \<noteq> foldr smtlib_str_concat t2 t1"
  unfolding smtlib_str_len_def smtlib_str_concat_def
  apply (induction t2)
   apply simp_all
  by (metis (mono_tags, opaque_lifting) append_eq_append_conv cvc_list_left_Cons cvc_list_left_transfer fold_append_concat_rev foldr_conv_fold)

lemma str_contains_split_char_lemma:
"smtlib_str_len w = 1 \<Longrightarrow> smtlib_str_contains (smtlib_str_concat (smtlib_str_concat x y) (foldr smtlib_str_concat z [])) w =
    (smtlib_str_contains x w \<or> smtlib_str_contains (smtlib_str_concat y (foldr smtlib_str_concat z [])) w)"
  apply (induction z)
   apply simp_all
   apply (simp add: smtlib_str_concat_def)
  apply (simp add: smtlib_str_contains_append_Singleton)
  by (simp add: smtlib_str_concat_def smtlib_str_contains_append_Singleton)

lemma str_len_concat_rec_lemma:
" smtlib_str_len (smtlib_str_concat (smtlib_str_concat s1 s2) (foldr smtlib_str_concat s3s [])) =
    smtlib_str_len s1 + smtlib_str_len (smtlib_str_concat s2 (foldr smtlib_str_concat s3s []))"
  apply (induction s3s)
   apply simp_all
  using smtlib_str_concat_length apply auto[1]
  using smtlib_str_concat_length by presburger

end