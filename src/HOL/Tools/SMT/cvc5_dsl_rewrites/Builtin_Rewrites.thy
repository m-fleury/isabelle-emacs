theory Builtin_Rewrites
  imports Dsl_Nary_Ops Dsl_Nary_Ops
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

named_theorems eq_refl \<open>automatically_generated\<close>

lemma [eq_refl]:
  fixes t::"'a"
  shows "(t = t) = True"
  by simp

named_theorems eq_symm \<open>automatically_generated\<close>
declare[[show_types]]
declare[[show_sorts]]

lemma [eq_symm]:
  fixes s::"'a" and t::"'a"
  shows "(t = s) = (s = t)"
  by auto

named_theorems ite_true_cond \<open>automatically_generated\<close>

lemma [ite_true_cond]:
  fixes y::"'a" and x::"'a"
  shows "(if True then x else y) = x"
  by simp

named_theorems ite_false_cond \<open>automatically_generated\<close>

lemma [ite_false_cond]:
  fixes y::"'a" and x::"'a"
  shows "(if False then x else y) = y"
  by simp

named_theorems ite_not_cond \<open>automatically_generated\<close>

lemma [ite_not_cond]:
  fixes y::"'a" and x::"'a" and c::"bool"
  shows "(if \<not> c then x else y) = (if c then y else x)"
  by simp

named_theorems ite_eq_branch \<open>automatically_generated\<close>

lemma [ite_eq_branch]:
  fixes x::"'a" and c::"bool"
  shows "(if c then x else x) = x"
  by simp

end