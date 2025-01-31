theory Extra_Rewrites
  imports "HOL-CVC.Dsl_Nary_Ops" "HOL.Real" 
begin (*Since this needs real operators it is not included in RARE_interface*)

named_theorems rewrite_arith_to_int_to_real \<open>\<close>

lemma [rewrite_arith_to_int_to_real]:
  fixes x::"int"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> floor (of_int x ::real) = x"
  by simp

end