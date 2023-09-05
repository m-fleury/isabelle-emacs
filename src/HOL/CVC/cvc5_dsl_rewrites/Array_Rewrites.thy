theory Array_Rewrites
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

named_theorems rewrite_array_read_over_write \<open>automatically_generated\<close>

lemma [rewrite_array_read_over_write]:
  fixes t::"'a::type \<Rightarrow> 'b::type option" and i::"'a::type" and e::"'b::type option"
  shows "(t(i := e)) i = e"
  by auto

named_theorems rewrite_array_read_over_write2 \<open>automatically_generated\<close>

lemma [rewrite_array_read_over_write2]:
  fixes t::"'a::type \<Rightarrow> 'b::type option" and i::"'a::type" and j::"'a::type" and e::"'b::type option"
  shows "i \<noteq> j \<longrightarrow> (t(i := e)) j = t j"
  by auto

named_theorems rewrite_array_store_overwrite \<open>automatically_generated\<close>

lemma [rewrite_array_store_overwrite]:
  fixes t::"'a::type \<Rightarrow> 'b::type option" and i::"'a::type" and e::"'b::type option" and f::"'b::type option"
  shows "t(i := e, i := f) = t(i := f)"
  by auto

named_theorems rewrite_array_store_self \<open>automatically_generated\<close>

lemma [rewrite_array_store_self]:
  fixes t::"'a::type \<Rightarrow> 'b::type option" and i::"'a::type"
  shows "t(i := t i) = t"
  by auto

end