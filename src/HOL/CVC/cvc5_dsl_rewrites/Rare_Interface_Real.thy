theory Rare_Interface_Real
  imports "HOL.Real"
begin (*Since this needs real operators it is not included in RARE_interface*)


named_theorems rewrite_arith_geq_norm1_real \<open>\<close>

lemma [rewrite_arith_geq_norm1_real]:
  fixes t::"real"  and  s::"real" 
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((t \<ge> s) = ((t - s) \<ge> 0/1))"
  by simp

named_theorems rewrite_arith_eq_elim_real \<open>\<close>

lemma [rewrite_arith_eq_elim_real]:
  fixes t::"'a::linordered_idom"  and  s::"'a::linordered_idom" 
  shows "NO_MATCH cvc_a (undefined t s)
 \<Longrightarrow> ((t = s) = (t \<ge> s \<and> t \<le> s))"
  by auto

named_theorems rewrite_arith_to_int_to_real \<open>\<close>

lemma [rewrite_arith_to_int_to_real]:
  fixes x::"int"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> floor (of_int x ::real) = x"
  by simp

named_theorems rewrite_arith_int_eq_conflict \<open>\<close>

lemma [rewrite_arith_int_eq_conflict]:
  fixes t::int and c::real
  shows "NO_MATCH cvc_a (undefined t c)
 \<Longrightarrow> \<not>((of_int (floor c)::real) = c) \<Longrightarrow> (((of_int t ::real) = c) = False)"
  by auto

named_theorems rewrite_arith_int_geq_tighten \<open>\<close>

lemma [rewrite_arith_int_geq_tighten]:
  fixes t::int and c::real and cc::int
  shows "NO_MATCH cvc_a (undefined t c cc)
 \<Longrightarrow> (\<not>((of_int (floor c)) = c) \<and> (cc = (floor c) + 1)) \<Longrightarrow> (((of_int t ::real) \<ge> c) = (t \<ge> cc))"
  by linarith

named_theorems rewrite_arith_geq_ite_lift \<open>\<close>

lemma [rewrite_arith_geq_ite_lift]:
  fixes c::real and t::"'a::linordered_idom" and r::"'a::linordered_idom" and s::"'a::linordered_idom"  
  shows "NO_MATCH cvc_a (undefined C t s r)
 \<Longrightarrow> (((if C then t else s) \<ge> r) = (if C then (t \<ge> r) else (s \<ge> r)))"
  by auto

named_theorems rewrite_arith_leq_ite_lift \<open>\<close>

lemma [rewrite_arith_leq_ite_lift]:
  fixes c::real and t::"'a::linordered_idom" and r::"'a::linordered_idom" and s::"'a::linordered_idom"  
  shows "NO_MATCH cvc_a (undefined C t s r)
 \<Longrightarrow> (((if C then t else s) \<le> r) = (if C then (t \<le> r) else (s \<le> r)))"
  by auto

end
