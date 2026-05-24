theory Alethe_Rare_Interface_Real
  imports "HOL.Real"
begin (*Since this theory requires real operators it is not included in RARE_interface*)




named_theorems rewrite_arith_int_div_total \<open>automatically_generated\<close>

lemma [rewrite_arith_int_div_total]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> \<not>(s = 0) \<Longrightarrow> SMT.z3div t s = SMT.z3div t s"
  by (simp add: SMT.z3div_def)


named_theorems rewrite_arith_int_div_total_one \<open>automatically_generated\<close>

lemma [rewrite_arith_int_div_total_one]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> SMT.z3div t (1::int) = t"
  by (simp add: SMT.z3div_def)


named_theorems rewrite_arith_int_div_total_zero \<open>automatically_generated\<close>

lemma [rewrite_arith_int_div_total_zero]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> SMT.z3div t (0::int) = 0"
  by (simp add: SMT.z3div_def)


named_theorems rewrite_arith_int_div_total_neg \<open>automatically_generated\<close>

lemma [rewrite_arith_int_div_total_neg]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> s < 0 \<Longrightarrow> SMT.z3div t s = - (SMT.z3div t (-s))"
  by (simp add: SMT.z3div_def)


named_theorems rewrite_arith_int_mod_total \<open>automatically_generated\<close>

lemma [rewrite_arith_int_mod_total]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> \<not> s = 0 \<Longrightarrow> SMT.z3mod t s = SMT.z3mod t s"
  by simp


named_theorems rewrite_arith_int_mod_total_one \<open>automatically_generated\<close>

lemma [rewrite_arith_int_mod_total_one]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> SMT.z3mod t 1 = 0"
  by (simp add: SMT.z3mod_def)


named_theorems rewrite_arith_int_mod_total_zero \<open>automatically_generated\<close>

lemma [rewrite_arith_int_mod_total_zero]:
  fixes t::"int"
  shows "NO_MATCH cvc_a (undefined t) \<Longrightarrow> SMT.z3mod t 0 = t"
  by (simp add: SMT.z3mod_def)


named_theorems rewrite_arith_int_mod_total_neg \<open>automatically_generated\<close>

lemma [rewrite_arith_int_mod_total_neg]:
  fixes t::"int" and s::"int"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow> s < 0 \<Longrightarrow> SMT.z3mod t s = SMT.z3mod t (-s)"
  by (simp add: SMT.z3mod_def)


named_theorems rewrite_arith_mod_over_mod \<open>automatically_generated\<close>

lemma [rewrite_arith_mod_over_mod]:
  fixes c::int and ts::"int cvc_ListVar" and r::int and ss::"int cvc_ListVar" 
  shows "NO_MATCH cvc_a (undefined c ts r ss)
 \<Longrightarrow> \<not>(c=0) 
 \<Longrightarrow> SMT.z3mod (cvc_list_left (+) ts (cvc_list_right (+) (SMT.z3mod r c) ss)) c
= SMT.z3mod (cvc_list_left (+) ts (cvc_list_right (+) r ss)) c"
  apply (cases ts)
  apply (cases ss)
  subgoal for ts' ss'
    unfolding SMT.z3mod_def
     apply simp_all
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op(3))
     apply (induction ts' arbitrary: ts)
     apply simp_all
     apply (induction ss' arbitrary: ss)
     apply simp_all
     apply (meson mod_add_left_eq)
    by (metis (no_types, lifting) mod_add_right_eq)
  done


named_theorems rewrite_arith_divisible_elim \<open>automatically_generated\<close>

lemma [rewrite_arith_divisible_elim]:
  fixes n::"int" and t::"int"
  shows "NO_MATCH cvc_a (undefined n t)
 \<Longrightarrow> \<not>(n = 0) \<Longrightarrow> ((n dvd t) = (SMT.z3mod t n = 0))"
  apply (simp add: SMT.z3mod_def)
  by auto

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
