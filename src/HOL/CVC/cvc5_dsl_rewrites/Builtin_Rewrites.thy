theory Builtin_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops" 
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

named_theorems rewrite_ite_true_cond \<open>automatically_generated\<close>

lemma [rewrite_ite_true_cond]:
  fixes x::"'a::type" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (if True then x else y) = x"
  by auto


named_theorems rewrite_ite_false_cond \<open>automatically_generated\<close>

lemma [rewrite_ite_false_cond]:
  fixes x::"'a::type" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (if False then x else y) = y"
  by auto


named_theorems rewrite_ite_not_cond \<open>automatically_generated\<close>

lemma [rewrite_ite_not_cond]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y) \<Longrightarrow> (if \<not> c then x else y) = (if c then y else x)"
  by auto


named_theorems rewrite_ite_eq_branch \<open>automatically_generated\<close>

lemma [rewrite_ite_eq_branch]:
  fixes c::"bool" and x::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x) \<Longrightarrow> (if c then x else x) = x"
  by auto


named_theorems rewrite_ite_then_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_then_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then if c then x else y else z) = (if c then x else z)"
  by auto


named_theorems rewrite_ite_else_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_else_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then x else if c then y else z) = (if c then x else z)"
  by auto


named_theorems rewrite_ite_then_neg_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_then_neg_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then if \<not> c then x else y else z) = (if c then y else z)"
  by auto


named_theorems rewrite_ite_else_neg_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_else_neg_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "NO_MATCH cvc_a (undefined c x y z) \<Longrightarrow> (if c then x else if \<not> c then y else z) = (if c then x else y)"
  by auto

end