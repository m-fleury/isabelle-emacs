theory Builtin_Rewrites
  imports Dsl_Nary_Ops
begin

named_theorems rewrite_ite_true_cond \<open>automatically_generated\<close>

lemma [rewrite_ite_true_cond]:
  fixes x::"'a::type" and y::"'a::type"
  shows "(if True then x else y) = x"
  by auto

named_theorems rewrite_ite_false_cond \<open>automatically_generated\<close>

lemma [rewrite_ite_false_cond]:
  fixes x::"'a::type" and y::"'a::type"
  shows "(if False then x else y) = y"
  by auto

named_theorems rewrite_ite_not_cond \<open>automatically_generated\<close>

lemma [rewrite_ite_not_cond]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type"
  shows "(if \<not> c then x else y) = (if c then y else x)"
  by auto

named_theorems rewrite_ite_eq_branch \<open>automatically_generated\<close>

lemma [rewrite_ite_eq_branch]:
  fixes c::"bool" and x::"'a::type"
  shows "(if c then x else x) = x"
  by auto

named_theorems rewrite_ite_then_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_then_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "(if c then if c then x else y else z) = (if c then x else z)"
  by auto

named_theorems rewrite_ite_else_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_else_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "(if c then x else if c then y else z) = (if c then x else z)"
  by auto

named_theorems rewrite_ite_then_neg_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_then_neg_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "(if c then if \<not> c then x else y else z) = (if c then y else z)"
  by auto

named_theorems rewrite_ite_else_neg_lookahead \<open>automatically_generated\<close>

lemma [rewrite_ite_else_neg_lookahead]:
  fixes c::"bool" and x::"'a::type" and y::"'a::type" and z::"'a::type"
  shows "(if c then x else if \<not> c then y else z) = (if c then x else y)"
  by auto

(*Generated by hand*)
named_theorems rewrite_bool_double_neg_elim \<open>added by hand\<close>

lemma [rewrite_bool_double_neg_elim]:
  shows "\<not> (\<not>x) = x"
  by auto


end