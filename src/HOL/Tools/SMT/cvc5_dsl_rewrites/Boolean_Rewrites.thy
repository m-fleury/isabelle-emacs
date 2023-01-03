theory Boolean_Rewrites
  imports Dsl_Nary_Ops
begin

(* This is a theory automatically created from a rare file! All that remains to do is to prove
any lemma whose auto proof fails and to to import this file in SMT.thy. *)
named_theorems bool_or_taut \<open>automatically_generated\<close>

lemma help1: "cvc_isListOp (ListOp (\<or>) False)"
  sorry

lemma [bool_or_taut]:
  fixes zs::cvc_ListVar and ys::cvc_ListVar and w::bool and xs::cvc_ListVar
  shows "((cvc_list_left (\<or>) xs
 (w \<or> cvc_list_left (\<or>) ys (cvc_list_right (\<or>) (\<not> w) zs))) = (True))"
  apply (cases xs)
  apply (cases ys)
  apply (cases zs)
  apply simp_all
  unfolding cvc_list_left_transfer
  subgoal for xss yss zss
  using cvc_list_right_transfer[of "(\<or>)" False "\<not> w" zss] help1
  apply simp

  sorry
  sorry

named_theorems bool_and_conf \<open>automatically_generated\<close>

lemma [bool_and_conf]:
  fixes zs::cvc_ListVar and ys::cvc_ListVar and w::bool and xs::cvc_ListVar
  shows "((cvc_list_left (\<and>) xs
 (w \<and>
  cvc_list_left (\<and>) ys (cvc_list_right (\<and>) (\<not> w) zs))) = (False))"
  sorry

named_theorems bool_ite_not_cond \<open>automatically_generated\<close>

lemma [bool_ite_not_cond]:
  fixes y::bool and x::bool and c::bool
  shows "((if \<not> c then x else y) = (if c then y else x))"
  by auto

named_theorems bool_ite_false_cond \<open>automatically_generated\<close>

lemma [bool_ite_false_cond]:
  fixes y::bool and x::bool
  shows "((if False then x else y) = (y))"
  by auto

named_theorems bool_ite_true_cond \<open>automatically_generated\<close>

lemma [bool_ite_true_cond]:
  fixes y::bool and x::bool
  shows "((if True then x else y) = (x))"
  by auto

named_theorems bool_and_dup \<open>automatically_generated\<close>

lemma [bool_and_dup]:
  fixes zs::cvc_ListVar and ys::cvc_ListVar and b::bool and xs::cvc_ListVar
  shows "((cvc_list_left (\<and>) xs
 (b \<and> cvc_list_left (\<and>) ys (cvc_list_right (\<and>) b zs))) = (cvc_list_left (\<and>) xs (b \<and> cvc_list_both (\<and>) ys zs)))"
  sorry

named_theorems bool_and_flatten \<open>automatically_generated\<close>

lemma [bool_and_flatten]:
  fixes zs::cvc_ListVar and ys::cvc_ListVar and b::bool and xs::cvc_ListVar
  shows "((cvc_list_left (\<and>) xs
 (cvc_list_right (\<and>) (cvc_list_right (\<and>) b ys) zs)) = (cvc_list_left (\<and>) xs
 (cvc_list_left (\<and>) zs (cvc_list_right (\<and>) b ys))))"
  sorry

named_theorems bool_and_false \<open>automatically_generated\<close>

lemma [bool_and_false]:
  fixes ys::cvc_ListVar and xs::cvc_ListVar
  shows "((cvc_list_left (\<and>) xs (cvc_list_right (\<and>) False ys)) = (False))"
  sorry

named_theorems bool_and_true \<open>automatically_generated\<close>

lemma [bool_and_true]:
  fixes ys::cvc_ListVar and xs::cvc_ListVar
  shows "((cvc_list_left (\<and>) xs (cvc_list_right (\<and>) True ys)) = (cvc_list_both (\<and>) xs ys))"
  sorry

named_theorems bool_or_dup \<open>automatically_generated\<close>

lemma [bool_or_dup]:
  fixes zs::cvc_ListVar and ys::cvc_ListVar and b::bool and xs::cvc_ListVar
  shows "((cvc_list_left (\<or>) xs
 (b \<or> cvc_list_left (\<or>) ys (cvc_list_right (\<or>) b zs))) = (cvc_list_left (\<or>) xs (b \<or> cvc_list_both (\<or>) ys zs)))"
  sorry

named_theorems bool_or_flatten \<open>automatically_generated\<close>

lemma [bool_or_flatten]:
  fixes zs::cvc_ListVar and ys::cvc_ListVar and b::bool and xs::cvc_ListVar
  shows "((cvc_list_left (\<or>) xs
 (cvc_list_right (\<or>) (cvc_list_right (\<or>) b ys) zs)) = (cvc_list_left (\<or>) xs
 (cvc_list_left (\<or>) zs (cvc_list_right (\<or>) b ys))))"
  sorry

named_theorems bool_or_false \<open>automatically_generated\<close>

lemma [bool_or_false]:
  fixes ys::cvc_ListVar and xs::cvc_ListVar
  shows "((cvc_list_left (\<or>) xs (cvc_list_right (\<or>) False ys)) = (cvc_list_both (\<or>) xs ys))"
  sorry

named_theorems bool_or_true \<open>automatically_generated\<close>

lemma [bool_or_true]:
  fixes ys::cvc_ListVar and xs::cvc_ListVar
  shows "((cvc_list_left (\<or>) xs (cvc_list_right (\<or>) True ys)) = (True))"
  sorry

named_theorems bool_impl_true2 \<open>automatically_generated\<close>

lemma [bool_impl_true2]:
  fixes t::bool
  shows "((True \<longrightarrow> t) = (t))"
  by auto

named_theorems bool_impl_true1 \<open>automatically_generated\<close>

lemma [bool_impl_true1]:
  fixes t::bool
  shows "((t \<longrightarrow> True) = (True))"
  by auto

named_theorems bool_impl_false2 \<open>automatically_generated\<close>

lemma [bool_impl_false2]:
  fixes t::bool
  shows "((False \<longrightarrow> t) = (True))"
  by auto

named_theorems bool_impl_false1 \<open>automatically_generated\<close>

lemma [bool_impl_false1]:
  fixes t::bool
  shows "((t \<longrightarrow> False) = (\<not> t))"
  by auto

named_theorems bool_eq_false \<open>automatically_generated\<close>

lemma [bool_eq_false]:
  fixes t::bool
  shows "((t = False) = (\<not> t))"
  by auto

named_theorems bool_eq_true \<open>automatically_generated\<close>

lemma [bool_eq_true]:
  fixes t::bool
  shows "((t = True) = (t))"
  by auto

named_theorems bool_double_neg_elim \<open>automatically_generated\<close>

lemma [bool_double_neg_elim]:
  fixes t::bool
  shows "((\<not> \<not> t) = (t))"
  by auto

named_theorems bool_eq_symm \<open>automatically_generated\<close>

lemma [bool_eq_symm]:
  fixes s::bool and t::bool
  shows "((t = s) = (s = t))"
  by auto

named_theorems bool_eq_refl \<open>automatically_generated\<close>

lemma [bool_eq_refl]:
  fixes t::bool
  shows "((t = t) = (True))"
  by auto

end