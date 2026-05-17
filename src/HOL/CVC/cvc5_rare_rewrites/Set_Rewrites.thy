theory Set_Rewrites
  imports Dsl_Nary_Ops
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

named_theorems rewrite_sets_eq_singleon_emp \<open>automatically_generated\<close>

lemma [rewrite_sets_eq_singleon_emp]:
  fixes x::"'a::type set" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> x = ({}::'a::type set) \<Longrightarrow> (x = {y}) = False"
  by auto


named_theorems rewrite_sets_card_union \<open>automatically_generated\<close>

lemma [rewrite_sets_card_union]:
  fixes x::"'a::type" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<in> ({y}::'a::type set)) = (x = y)"
  by auto


named_theorems rewrite_sets_member_emp \<open>automatically_generated\<close>

lemma [rewrite_sets_member_emp]:
  fixes x::"'a::type" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y = ({}::'a::type set)) \<Longrightarrow> (x \<in> y = False)"
  by auto


named_theorems rewrite_sets_subset_elim \<open>automatically_generated\<close>

lemma [rewrite_sets_subset_elim]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<subset> y) \<Longrightarrow> (x \<union> y  = y)"
  by auto


named_theorems rewrite_sets_union_comm \<open>automatically_generated\<close>

lemma [rewrite_sets_union_comm]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<union> y) = (y \<union> x)"
  by auto


named_theorems rewrite_sets_inter_comm \<open>automatically_generated\<close>

lemma [rewrite_sets_inter_comm]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<inter> y) = (y \<inter> x)"
  by auto


named_theorems rewrite_sets_inter_emp1 \<open>automatically_generated\<close>

lemma [rewrite_sets_inter_emp1]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x = ({}::'a set)) \<Longrightarrow> (x \<inter> y = x)"
  by auto


named_theorems rewrite_sets_inter_emp2 \<open>automatically_generated\<close>

lemma [rewrite_sets_inter_emp2]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y = ({}::'a set)) \<Longrightarrow> (x \<inter> y = y)"
  by auto


named_theorems rewrite_sets_minus_emp1 \<open>automatically_generated\<close>

lemma [rewrite_sets_minus_emp1]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x = ({}::'a set)) \<Longrightarrow> (x - y = x)"
  by auto


named_theorems rewrite_sets_minus_emp2 \<open>automatically_generated\<close>

lemma [rewrite_sets_minus_emp2]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y = ({}::'a set)) \<Longrightarrow> (x - y = x)"
  by auto


named_theorems rewrite_sets_union_emp1 \<open>automatically_generated\<close>

lemma [rewrite_sets_union_emp1]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x = ({}::'a set)) \<Longrightarrow> (x \<union> y = y)"
  by auto


named_theorems rewrite_sets_union_emp2 \<open>automatically_generated\<close>

lemma [rewrite_sets_union_emp2]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (y = ({}::'a set)) \<Longrightarrow> (x \<union> y = x)"
  by auto


named_theorems rewrite_sets_inter_member \<open>automatically_generated\<close>

lemma [rewrite_sets_inter_member]:
  fixes x::"'a::type" and y::"'a::type set" and z::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y z) \<Longrightarrow> (x \<in> (y \<inter> z)) = (x \<in> y \<and> x \<in> z)"
  by auto


named_theorems rewrite_sets_minus_member \<open>automatically_generated\<close>

lemma [rewrite_sets_minus_member]:
  fixes x::"'a::type" and y::"'a::type set" and z::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y z) \<Longrightarrow> (x \<in> (y - z)) = (x \<in> y \<and> \<not>(x \<in> z))"
  by auto


named_theorems rewrite_sets_union_member \<open>automatically_generated\<close>

lemma [rewrite_sets_union_member]:
  fixes x::"'a::type" and y::"'a::type set" and z::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y z) \<Longrightarrow> (x \<in> (y \<union> z)) = (x \<in> y \<or> x \<in> z)"
  by auto


named_theorems rewrite_sets_choose_singleton \<open>manually\<close>

lemma [rewrite_sets_choose_singleton]:
  fixes x::"'a::type"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (SOME y. y \<in> {x}) = x"
  by auto


named_theorems rewrite_sets_minus_self \<open>automatically_generated\<close>

lemma [rewrite_sets_minus_self]:
  fixes x::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x - x) = ({}::'a::type set)"
  by auto


named_theorems rewrite_sets_is_empty_elim \<open>automatically_generated\<close>

lemma [rewrite_sets_is_empty_elim]:
  fixes x::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x = {}) = (x = ({}::'a::type set))"
  by auto


named_theorems rewrite_sets_is_singleton_elim \<open>automatically_generated\<close>

lemma [rewrite_sets_is_empty_elim]:
  fixes x::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (card x = 1) = (x = {(SOME y. y \<in> x)})"
  apply simp
  by (metis card_1_singleton_iff some_elem_def some_elem_eq)


end