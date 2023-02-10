theory BV_Rewrites
  imports Dsl_Nary_Ops Dsl_Nary_Ops
begin

(* This is a theory automatically created from a rare file! All that remains to do is to prove
any lemma whose auto proof fails and to to import this file in SMT.thy. 
If your rare statements use nary operators over lists that would be binarised by Isabelle 
you have to add it in Dsl_Nary_Ops.thy. Currently supported are the operators:
and,or*)

named_theorems NegIdemp \<open>automatically_generated\<close>


lemma [NegIdemp]:
  fixes x::"'a::len word"
  shows "let n = LENGTH('a) in ((- (- x)) = (x))"
  by auto

lemma
  fixes x::"'a::len word" and n::"int"
  assumes "LENGTH('a) = nat n"
  shows "((- (- x)) = (x))"
  by auto



lemma
  fixes x::"'a::len word" and n::"int" and y::"'b::len word" and m::int
  assumes "LENGTH('a) = nat n" "m = n"
  shows "x + y = 5"
  by auto


end