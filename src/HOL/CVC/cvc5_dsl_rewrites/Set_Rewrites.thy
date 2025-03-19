theory Set_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops" 
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

named_theorems rewrite_sets_member_singleton \<open>automatically_generated\<close>

lemma [rewrite_sets_member_singleton]:
  fixes x::"'a::type" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<in> {y}) = (x = y)"
  by auto


named_theorems rewrite_sets_subset_elim \<open>automatically_generated\<close>

lemma [rewrite_sets_subset_elim]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (x \<subseteq> y) = (x \<union> y = y)"
  by auto


named_theorems rewrite_sets_union_comm \<open>automatically_generated\<close>

lemma [rewrite_sets_union_comm]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> x \<union> y = y \<union> x"
  by auto


named_theorems rewrite_sets_inter_comm \<open>automatically_generated\<close>

lemma [rewrite_sets_inter_comm]:
  fixes x::"'a::type set" and y::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> x \<inter> y = y \<inter> x"
  by auto


named_theorems rewrite_sets_inter_member \<open>automatically_generated\<close>

lemma [rewrite_sets_inter_member]:
  fixes x::"'a::type" and y::"'a::type set" and z::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y z) \<Longrightarrow> (x \<in> y \<inter> z) = (x \<in> y \<and> x \<in> z)"
  by auto


named_theorems rewrite_sets_minus_member \<open>automatically_generated\<close>

lemma [rewrite_sets_minus_member]:
  fixes x::"'a::type" and y::"'a::type set" and z::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y z) \<Longrightarrow> (x \<in> y - z) = (x \<in> y \<and> x \<notin> z)"
  by auto


named_theorems rewrite_sets_union_member \<open>automatically_generated\<close>

lemma [rewrite_sets_union_member]:
  fixes x::"'a::type" and y::"'a::type set" and z::"'a::type set"
  shows "NO_MATCH cvc_a (undefined x y z) \<Longrightarrow> (x \<in> y \<union> z) = (x \<in> y \<or> x \<in> z)"
  by auto

(*Test added by Hanna*)


named_theorems rewrite_sets_union_double \<open>automatically_generated\<close>

lemma [rewrite_sets_union_double]:
  fixes x::"'a::type set" 
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<union> x) = x"
  by auto

cvc5_rare "Set_Rewrites.rewrite_sets_union_double"

end