theory Boolean_Rewrites
  imports Main
begin

(* This is a theory automatically created from a rare file! All that remains to do is to prove
any lemma whose auto proof fails and to to import this file in SMT.thy. *)
named_theorems bool_or_taut \<open>automatically_generated\<close>

lemma [bool_or_taut]:
  fixes zs::bool and ys::bool and w::bool and xs::bool
  shows "((xs \<or> w \<or> ys \<or> \<not> w \<or> zs) = (True))"
  by auto

named_theorems bool_and_conf \<open>automatically_generated\<close>

lemma [bool_and_conf]:
  fixes zs::bool and ys::bool and w::bool and xs::bool
  shows "((xs \<and> w \<and> ys \<and> \<not> w \<and> zs) = (False))"
  by auto

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
  fixes zs::bool and ys::bool and b::bool and xs::bool
  shows "((xs \<and> b \<and> ys \<and> b \<and> zs) = (xs \<and> b \<and> ys \<and> zs))"
  by auto

named_theorems bool_and_flatten \<open>automatically_generated\<close>

lemma [bool_and_flatten]:
  fixes zs::bool and ys::bool and b::bool and xs::bool
  shows "((xs \<and> (b \<and> ys) \<and> zs) = (xs \<and> zs \<and> b \<and> ys))"
  by auto

named_theorems bool_and_false \<open>automatically_generated\<close>

lemma [bool_and_false]:
  fixes ys::bool and xs::bool
  shows "((xs \<and> False \<and> ys) = (False))"
  by auto

named_theorems bool_and_true \<open>automatically_generated\<close>

lemma [bool_and_true]:
  fixes ys::bool and xs::bool
  shows "((xs \<and> True \<and> ys) = (xs \<and> ys))"
  by auto

named_theorems bool_or_dup \<open>automatically_generated\<close>

lemma [bool_or_dup]:
  fixes zs::bool and ys::bool and b::bool and xs::bool
  shows "((xs \<or> b \<or> ys \<or> b \<or> zs) = (xs \<or> b \<or> ys \<or> zs))"
  by auto

named_theorems bool_or_flatten \<open>automatically_generated\<close>

lemma [bool_or_flatten]:
  fixes zs::bool and ys::bool and b::bool and xs::bool
  shows "((xs \<or> (b \<or> ys) \<or> zs) = (xs \<or> zs \<or> b \<or> ys))"
  by auto

named_theorems bool_or_false \<open>automatically_generated\<close>

lemma [bool_or_false]:
  fixes ys::bool and xs::bool
  shows "((xs \<or> False \<or> ys) = (xs \<or> ys))"
  by auto

named_theorems bool_or_true \<open>automatically_generated\<close>

lemma [bool_or_true]:
  fixes ys::bool and xs::bool
  shows "((xs \<or> True \<or> ys) = (True))"
  by auto

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