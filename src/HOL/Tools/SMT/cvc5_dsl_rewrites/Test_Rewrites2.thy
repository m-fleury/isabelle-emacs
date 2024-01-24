theory Test_Rewrites2
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

named_theorems rewrite_re_all_elim \<open>automatically_generated\<close>

lemma [rewrite_re_all_elim]:
  shows "smtlib_re_all = smtlib_re_star smtlib_re_allchar"
  by auto

end