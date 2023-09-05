theory Set_Rewrites
  imports Dsl_Nary_Ops
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


named_theorems rewrite_sets_member_singleton \<open>automatically_generated\<close>

lemma [rewrite_sets_member_singleton]:
  fixes x::"'a::type" and y::"'a::type"
  shows "(x \<in> {y}) = (x = y)"
  by auto

named_theorems rewrite_sets_subset_elim \<open>automatically_generated\<close>

lemma [rewrite_sets_subset_elim]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "(x \<subseteq> y) = (x \<union> y = y)"
  by auto

named_theorems rewrite_sets_union_comm \<open>automatically_generated\<close>

lemma [rewrite_sets_union_comm]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "x \<union> y = y \<union> x"
  by auto

named_theorems rewrite_sets_inter_comm \<open>automatically_generated\<close>

lemma [rewrite_sets_inter_comm]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "x \<inter> y = y \<inter> x"
  by auto

named_theorems rewrite_sets_inter_member \<open>automatically_generated\<close>

lemma [rewrite_sets_inter_member]:
  fixes x::"'a::type" and y::"'a::type set" and z::"'a::type set"
  shows "(x \<in> y \<inter> z) = (x \<in> y \<and> x \<in> z)"
  by auto

named_theorems rewrite_sets_minus_member \<open>automatically_generated\<close>

lemma [rewrite_sets_minus_member]:
  fixes x::"'a::type" and y::"'a::type set" and z::"'a::type set"
  shows "(x \<in> y - z) = (x \<in> y \<and> x \<notin> z)"
  by auto

named_theorems rewrite_sets_union_member \<open>automatically_generated\<close>

lemma [rewrite_sets_union_member]:
  fixes x::"'a::type" and y::"'a::type set" and z::"'a::type set"
  shows "(x \<in> y \<union> z) = (x \<in> y \<or> x \<in> z)"
  by auto

end