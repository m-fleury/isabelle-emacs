theory Array_Rewrites
  imports Dsl_Nary_Ops
begin

(* Thank you for using IsaRARE. This is a theory automatically created from a RARE file!
All that remains to do is to prove any lemma whose provided proof fails.
If you want to use the lemmas for proof reconstruction you'll also need to import this file in Rare_Interface.thy*)

named_theorems rewrite_array_read_over_write \<open>automatically_generated\<close>

lemma [rewrite_array_read_over_write]:
  fixes t::"'a::type \<Rightarrow> 'b::type option" and i::"'a::type" and e::"'b::type option"
  shows "NO_MATCH cvc_a (undefined t i e) \<Longrightarrow> (t(i := e)) i = e"
  by auto


named_theorems rewrite_array_read_over_write2 \<open>automatically_generated\<close>

lemma [rewrite_array_read_over_write2]:
  fixes t::"'a::type \<Rightarrow> 'b::type option" and i::"'a::type" and j::"'a::type" and e::"'b::type option"
  shows "NO_MATCH cvc_a (undefined t i j e) \<Longrightarrow> i \<noteq> j \<longrightarrow> (t(i := e)) j = t j"
  by auto


named_theorems rewrite_array_store_overwrite \<open>automatically_generated\<close>

lemma [rewrite_array_store_overwrite]:
  fixes t::"'a::type \<Rightarrow> 'b::type option" and i::"'a::type" and e::"'b::type option" and f::"'b::type option"
  shows "NO_MATCH cvc_a (undefined t i e f) \<Longrightarrow> t(i := e, i := f) = t(i := f)"
  by auto


named_theorems rewrite_array_store_self \<open>automatically_generated\<close>

lemma [rewrite_array_store_self]:
  fixes t::"'a::type \<Rightarrow> 'b::type option" and i::"'a::type"
  shows "NO_MATCH cvc_a (undefined t i) \<Longrightarrow> t(i := t i) = t"
  by auto


named_theorems rewrite_array_read_over_write_split \<open>automatically_generated\<close>

lemma [rewrite_array_read_over_write_split]:
  fixes t::"'a::type \<Rightarrow> 'b::type option" and i::"'a::type" and j::"'a::type"
  and e::"'b::type option"
  shows "NO_MATCH cvc_a (undefined t i j e) \<Longrightarrow> (t(j := e)) i = (if (i=j) then e else t i)"
  by auto


named_theorems rewrite_array_store_swap \<open>automatically_generated\<close>

lemma [rewrite_array_store_swap]:
  fixes t::"'a::type \<Rightarrow> 'b::type option" and i::"'a::type" and j::"'a::type"
  and e::"'b::type option" and f::"'b::type option"
  shows "NO_MATCH cvc_a (undefined t i j e f) \<Longrightarrow> i \<noteq> j \<Longrightarrow> ((t(i := e)) (j := f)) = ((t(j := f)) (i := e))"
  by auto

end