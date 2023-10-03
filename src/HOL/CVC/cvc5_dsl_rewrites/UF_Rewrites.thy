theory UF_Rewrites
  imports Dsl_Nary_Ops
begin

named_theorems rewrite_eq_symm \<open>added by hand\<close>

lemma [rewrite_eq_symm]:
  shows "NO_MATCH c (undefined a b) ==> a = b \<longleftrightarrow> b = a"
  by auto

named_theorems rewrite_eq_refl \<open>added by hand\<close>

lemma [rewrite_eq_refl]:
  shows "NO_MATCH c (undefined a) ==> (a = a) = True"
  by auto

named_theorems rewrite_distinct_binary_elim \<open>added by hand\<close>

lemma [rewrite_distinct_binary_elim]:
  shows "NO_MATCH c (undefined t s) ==> \<not>(t = s) = (\<not>(t = s))"
  by auto

end