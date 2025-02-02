theory Extra_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops" "HOL.Real" 
begin (*Since this needs real operators it is not included in RARE_interface*)

named_theorems rewrite_arith_to_int_to_real \<open>\<close>

lemma [rewrite_arith_to_int_to_real]:
  fixes x::"int"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> floor (of_int x ::real) = x"
  by simp

named_theorems rewrite_arith_to_real_distrib_uminus \<open>\<close>

lemma [rewrite_arith_to_real_distrib_uminus]:
  fixes x::"int"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> -(of_int x ::real) = (of_int (-x) ::real)"
  by simp

named_theorems rewrite_arith_to_real_distrib_add \<open>\<close>

lemma [rewrite_arith_to_real_distrib_add]:
  fixes x::"int" and y::"int"
  shows "NO_MATCH cvc_a (undefined (x,y)) \<Longrightarrow> (of_int (x + y) ::real) = (of_int x ::real) + (of_int y ::real)"
  by simp

named_theorems rewrite_arith_to_real_distrib_minus \<open>\<close>

lemma [rewrite_arith_to_real_distrib_minus]:
  fixes x::"int" and y::"int"
  shows "NO_MATCH cvc_a (undefined (x,y)) \<Longrightarrow> (of_int (x - y) ::real) = (of_int x ::real) - (of_int y ::real)"
  by simp

named_theorems rewrite_arith_to_real_distrib_mult \<open>\<close>

lemma [rewrite_arith_to_real_distrib_mult]:
  fixes x::"int" and y::"int"
  shows "NO_MATCH cvc_a (undefined (x,y)) \<Longrightarrow> (of_int (x * y) ::real) = (of_int x ::real) * (of_int y ::real)"
  by simp

end