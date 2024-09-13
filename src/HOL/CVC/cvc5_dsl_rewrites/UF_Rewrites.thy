theory UF_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops" 
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

named_theorems rewrite_eq_refl \<open>automatically_generated\<close>

lemma [rewrite_eq_refl]:
  fixes t::"'a::type"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> (t = t) = True"
  by auto


named_theorems rewrite_eq_symm \<open>automatically_generated\<close>

lemma [rewrite_eq_symm]:
  fixes t::"'a::type" and s::"'a::type"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t = s) = (s = t)"
  by auto


named_theorems rewrite_distinct_binary_elim \<open>automatically_generated\<close>

lemma [rewrite_distinct_binary_elim]:
  fixes t::"'a::type" and s::"'a::type"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> (t \<noteq> s) = (t \<noteq> s)"
  by auto

end