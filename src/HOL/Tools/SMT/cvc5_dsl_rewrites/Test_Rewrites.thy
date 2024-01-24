theory Test_Rewrites
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

named_theorems rewrite_test1 \<open>automatically_generated\<close>

lemma
  fixes x::"'a::len word"
  shows "(1::(LENGTH('a))::len word) = 1"






lemma [rewrite_test1]:
  fixes x::"'a ::len word" and y::"'b::len word" and z::"'c::len word"  and a::"'d::len word"
    and b::"'e::len word"
  shows "word_cat x y = z \<and> word_cat a b = z \<longrightarrow> word_cat x y = word_cat a b"
proof
  assume a0: "word_cat x y = z \<and> word_cat a b = z"
  then have "LENGTH('a) + LENGTH('b) = LENGTH('c)"
    apply transfer
    




end