theory Rare_Interface
  imports "Boolean_Rewrites" "Builtin_Rewrites" "Arith_Rewrites" "UF_Rewrites" "cvc5_Rewrites"
begin

named_theorems rare_rewrites_simple \<open>RARE rewrites that don't contain lists or are star rules \<close>
named_theorems rare_rewrites_complex \<open>RARE rewrites that contain lists or are star rules \<close>
named_theorems rare_rewrites_all \<open>All RARE rewrites\<close>



(*Arithmetic*)
named_theorems rare_arith_rewrites_simple \<open>Arithmetic RARE rewrites that don't contain lists or are star rules \<close>
named_theorems rare_arith_rewrites_complex \<open>Arithmetic RARE rewrites that contain lists or are star rules \<close>
named_theorems rare_arith_rewrites_all \<open>Arithmetic RARE rewrites\<close>


(*We don't use total operators yet*)
(*ARITH_DIV_TOTAL_ZERO_REAL*)
(*ARITH_DIV_TOTAL_ZERO_INTL*)
(*ARITH_INT_DIV_TOTAL*)
(*ARITH_INT_DIV_TOTAL_ONE*)
(*ARITH_INT_DIV_TOTAL_ZERO*)
(*ARITH_INT_DIV_TOTAL_NEG*)
(*ARITH_INT_MOD_TOTAL*)
(*ARITH_INT_MOD_TOTAL_ONE*)
(*ARITH_INT_MOD_TOTAL_ZERO*)
(*ARITH_INT_MOD_TOTAL_NEG*)

cvc5_rare "Arith_Rewrites.rewrite_arith_elim_gt"
cvc5_rare "Arith_Rewrites.rewrite_arith_elim_lt"
cvc5_rare "Arith_Rewrites.rewrite_arith_elim_int_gt"
cvc5_rare "Arith_Rewrites.rewrite_arith_elim_int_lt"
cvc5_rare "Arith_Rewrites.rewrite_arith_elim_leq"
cvc5_rare "Arith_Rewrites.rewrite_arith_leq_norm"
cvc5_rare "Arith_Rewrites.rewrite_arith_geq_tighten"
cvc5_rare "Arith_Rewrites.rewrite_arith_geq_norm1_int"
(*ARITH_GEQ_NORM1_REAL \<longrightarrow> Rare_Interface_Real.thy*)
(*ARITH_EQ_ELIM_REAL \<longrightarrow> Rare_Interface_Real.thy*)
cvc5_rare "Arith_Rewrites.rewrite_arith_eq_elim_int"
(*ARITH_TO_INT_ELIM_TO_REAL \<longrightarrow> Rare_Interface_Real.thy*)
(*ARITH_MOD_OVER_MOD \<longrightarrow> No support for mod*)
(*ARITH_MOD_OVER_MOD_MULT \<longrightarrow> No support for mod*)
(*ARITH_INT_EQ_CONFLICT \<longrightarrow> Rare_Interface_Real.thy*)
(*ARITH_INT_GEQ_TIGHTEN \<longrightarrow> Rare_Interface_Real.thy*)
(*ARITH_DIVISIBLE_ELIM \<longrightarrow> TODO*)
(*ARITH_ABS_EQ \<longrightarrow> No support for abs*)
(*ARITH_ABS_INT_GT \<longrightarrow> No support for abs*)
(*ARITH_ABS_REAL_GT \<longrightarrow> No support for mod*)
(*ARITH_GEQ_ITE_LIFT \<longrightarrow> Rare_Interface_Real.thy*)
(*ARITH_LEQ_ITE_LIFT \<longrightarrow> Rare_Interface_Real.thy*)
(*ARITH_MIN_LT1 \<longrightarrow> No support for min*)
(*ARITH_MIN_LT2 \<longrightarrow> No support for min*)
(*ARITH_MIN_GEQ1 \<longrightarrow> No support for min*)
(*ARITH_MIN_GEQ2 \<longrightarrow> No support for min*)

lemmas [rare_arith_rewrites_simple] =
"Arith_Rewrites.rewrite_arith_elim_gt"
"Arith_Rewrites.rewrite_arith_elim_lt"
"Arith_Rewrites.rewrite_arith_elim_int_gt"
"Arith_Rewrites.rewrite_arith_elim_int_lt"
"Arith_Rewrites.rewrite_arith_elim_leq"
"Arith_Rewrites.rewrite_arith_leq_norm"
"Arith_Rewrites.rewrite_arith_geq_tighten"
"Arith_Rewrites.rewrite_arith_geq_norm1_int"
"Arith_Rewrites.rewrite_arith_eq_elim_int"
lemmas [rare_arith_rewrites_all] = rare_arith_rewrites_simple


(*Booleans*)
named_theorems rare_bool_rewrites_simple \<open>Boolean RARE rewrites that don't contain lists or are star rules \<close>
named_theorems rare_bool_rewrites_complex \<open>Boolean RARE rewrites that contain lists or are star rules \<close>
named_theorems rare_bool_rewrites_all \<open>Boolean RARE rewrites\<close>

cvc5_rare "Boolean_Rewrites.rewrite_bool_double_not_elim"
cvc5_rare "Boolean_Rewrites.rewrite_bool_not_true"
cvc5_rare "Boolean_Rewrites.rewrite_bool_not_false"
cvc5_rare "Boolean_Rewrites.rewrite_bool_eq_true"
cvc5_rare "Boolean_Rewrites.rewrite_bool_eq_false"
cvc5_rare "Boolean_Rewrites.rewrite_bool_eq_nrefl"
cvc5_rare "Boolean_Rewrites.rewrite_bool_impl_false1"
cvc5_rare "Boolean_Rewrites.rewrite_bool_impl_false2"
cvc5_rare "Boolean_Rewrites.rewrite_bool_impl_true1"
cvc5_rare "Boolean_Rewrites.rewrite_bool_impl_true2"
cvc5_rare "Boolean_Rewrites.rewrite_bool_impl_elim"
cvc5_rare "Boolean_Rewrites.rewrite_bool_dual_impl_eq"
cvc5_rare "Boolean_Rewrites.rewrite_bool_and_conf"
cvc5_rare "Boolean_Rewrites.rewrite_bool_and_conf2"
cvc5_rare "Boolean_Rewrites.rewrite_bool_or_taut"
cvc5_rare "Boolean_Rewrites.rewrite_bool_or_taut2"
cvc5_rare "Boolean_Rewrites.rewrite_bool_or_de_morgan"
cvc5_rare "Boolean_Rewrites.rewrite_bool_implies_de_morgan"
cvc5_rare "Boolean_Rewrites.rewrite_bool_and_de_morgan"
cvc5_rare "Boolean_Rewrites.rewrite_bool_or_and_distrib"
cvc5_rare "Boolean_Rewrites.rewrite_bool_implies_or_distrib"
cvc5_rare "Boolean_Rewrites.rewrite_bool_xor_refl"
cvc5_rare "Boolean_Rewrites.rewrite_bool_xor_nrefl"
cvc5_rare "Boolean_Rewrites.rewrite_bool_xor_false"
cvc5_rare "Boolean_Rewrites.rewrite_bool_xor_true"
cvc5_rare "Boolean_Rewrites.rewrite_bool_xor_comm"
cvc5_rare "Boolean_Rewrites.rewrite_bool_xor_elim"
cvc5_rare "Boolean_Rewrites.rewrite_bool_not_xor_elim"
cvc5_rare "Boolean_Rewrites.rewrite_bool_not_eq_elim1"
cvc5_rare "Boolean_Rewrites.rewrite_bool_not_eq_elim2"
cvc5_rare "Boolean_Rewrites.rewrite_ite_neg_branch"
cvc5_rare "Boolean_Rewrites.rewrite_ite_then_true"
cvc5_rare "Boolean_Rewrites.rewrite_ite_else_false"
cvc5_rare "Boolean_Rewrites.rewrite_ite_then_false"
cvc5_rare "Boolean_Rewrites.rewrite_ite_else_true"
cvc5_rare "Boolean_Rewrites.rewrite_ite_then_lookahead_self"
cvc5_rare "Boolean_Rewrites.rewrite_ite_else_lookahead_self"
cvc5_rare "Boolean_Rewrites.rewrite_ite_then_lookahead_not_self"
cvc5_rare "Boolean_Rewrites.rewrite_ite_else_lookahead_not_self"
cvc5_rare "Boolean_Rewrites.rewrite_ite_expand"
cvc5_rare "Boolean_Rewrites.rewrite_bool_not_ite_elim"
cvc5_rare "Builtin_Rewrites.rewrite_ite_true_cond"
cvc5_rare "Builtin_Rewrites.rewrite_ite_false_cond"
cvc5_rare "Builtin_Rewrites.rewrite_ite_not_cond"
cvc5_rare "Builtin_Rewrites.rewrite_ite_eq_branch"
cvc5_rare "Builtin_Rewrites.rewrite_ite_then_lookahead"
cvc5_rare "Builtin_Rewrites.rewrite_ite_else_lookahead"
cvc5_rare "Builtin_Rewrites.rewrite_ite_then_neg_lookahead"
cvc5_rare "Builtin_Rewrites.rewrite_ite_else_neg_lookahead"

lemmas [rare_bool_rewrites_simple] =
"Boolean_Rewrites.rewrite_bool_double_not_elim"
"Boolean_Rewrites.rewrite_bool_not_true"
"Boolean_Rewrites.rewrite_bool_not_false"
"Boolean_Rewrites.rewrite_bool_eq_true"
"Boolean_Rewrites.rewrite_bool_eq_false"
"Boolean_Rewrites.rewrite_bool_eq_nrefl"
"Boolean_Rewrites.rewrite_bool_impl_false1"
"Boolean_Rewrites.rewrite_bool_impl_false2"
"Boolean_Rewrites.rewrite_bool_impl_true1"
"Boolean_Rewrites.rewrite_bool_impl_true2"
"Boolean_Rewrites.rewrite_bool_impl_elim"
"Boolean_Rewrites.rewrite_bool_dual_impl_eq"
"Boolean_Rewrites.rewrite_bool_implies_de_morgan"
"Boolean_Rewrites.rewrite_bool_xor_refl"
"Boolean_Rewrites.rewrite_bool_xor_nrefl"
"Boolean_Rewrites.rewrite_bool_xor_false"
"Boolean_Rewrites.rewrite_bool_xor_true"
"Boolean_Rewrites.rewrite_bool_xor_comm"
"Boolean_Rewrites.rewrite_bool_xor_elim"
"Boolean_Rewrites.rewrite_bool_not_xor_elim"
"Boolean_Rewrites.rewrite_bool_not_eq_elim1"
"Boolean_Rewrites.rewrite_bool_not_eq_elim2"
"Boolean_Rewrites.rewrite_ite_neg_branch"
"Boolean_Rewrites.rewrite_ite_then_true"
"Boolean_Rewrites.rewrite_ite_else_false"
"Boolean_Rewrites.rewrite_ite_then_false"
"Boolean_Rewrites.rewrite_ite_else_true"
"Boolean_Rewrites.rewrite_ite_then_lookahead_self"
"Boolean_Rewrites.rewrite_ite_else_lookahead_self"
"Boolean_Rewrites.rewrite_ite_then_lookahead_not_self"
"Boolean_Rewrites.rewrite_ite_else_lookahead_not_self"
"Boolean_Rewrites.rewrite_ite_expand"
"Boolean_Rewrites.rewrite_bool_not_ite_elim"
"Builtin_Rewrites.rewrite_ite_true_cond"
"Builtin_Rewrites.rewrite_ite_false_cond"
"Builtin_Rewrites.rewrite_ite_not_cond"
"Builtin_Rewrites.rewrite_ite_eq_branch"
"Builtin_Rewrites.rewrite_ite_then_lookahead"
"Builtin_Rewrites.rewrite_ite_else_lookahead"
"Builtin_Rewrites.rewrite_ite_then_neg_lookahead"
"Builtin_Rewrites.rewrite_ite_else_neg_lookahead"

lemmas [rare_bool_rewrites_complex] =
"Boolean_Rewrites.rewrite_bool_and_conf"
"Boolean_Rewrites.rewrite_bool_and_conf2"
"Boolean_Rewrites.rewrite_bool_or_taut"
"Boolean_Rewrites.rewrite_bool_or_taut2"
"Boolean_Rewrites.rewrite_bool_or_de_morgan"
"Boolean_Rewrites.rewrite_bool_and_de_morgan"
"Boolean_Rewrites.rewrite_bool_or_and_distrib"
"Boolean_Rewrites.rewrite_bool_implies_or_distrib"

lemmas [rare_bool_rewrites_all] = rare_bool_rewrites_simple rare_bool_rewrites_complex


(*Uninterpreted Functions*)
named_theorems rare_uf_rewrites_simple \<open>Uninterpreted Functions rewrites that don't contain lists or are star rules \<close>
named_theorems rare_uf_rewrites_complex \<open>Uninterpreted Functions that contain lists or are star rules \<close>
named_theorems rare_uf_rewrites_all \<open>Uninterpreted Functions rewrites\<close>

cvc5_rare "UF_Rewrites.rewrite_eq_refl"
cvc5_rare "UF_Rewrites.rewrite_eq_symm"
cvc5_rare "UF_Rewrites.rewrite_eq_cond_deq"
cvc5_rare "UF_Rewrites.rewrite_eq_ite_lift"
cvc5_rare "UF_Rewrites.rewrite_distinct_binary_elim"

lemmas [rare_uf_rewrites_simple] =
"UF_Rewrites.rewrite_eq_refl"
"UF_Rewrites.rewrite_eq_symm"
"UF_Rewrites.rewrite_eq_cond_deq"
"UF_Rewrites.rewrite_eq_ite_lift"
"UF_Rewrites.rewrite_distinct_binary_elim"
lemmas [rare_uf_rewrites_all] = rare_uf_rewrites_simple



(*cvc5 only*)
named_theorems rare_cvc5_rewrites_simple \<open>Rewrites only produced by the cvc5 Alethe translation that don't contain lists or are star rules \<close>
named_theorems rare_cvc5_rewrites_complex \<open>Rewrites only produced by the cvc5 Alethe translation that contain lists or are star rules \<close>
named_theorems rare_cvc5_rewrites_all \<open>Rewrites only produced by the cvc5 Alethe translation rewrites\<close>

cvc5_rare "cvc5_Rewrites.rewrite_ite_eq"
cvc5_rare "cvc5_Rewrites.rewrite_or_not_refl"
cvc5_rare "cvc5_Rewrites.rewrite_distinct_binary_elim"
(*MOD_ELIM \<longrightarrow> No support for mod yet *)
(*IS_INT_ELIM \<longrightarrow> Rare_Interface_Real.thy *)
(*ABS_ELIM_INT \<longrightarrow> No support for abs yet *)
(*ABS_ELIM_REAL \<longrightarrow> No support for abs yet *)
(*DISTINCT_FALSE \<longrightarrow> We hardcoded this and use simp for it *)

lemmas [rare_cvc5_rewrites_simple] =
"cvc5_Rewrites.rewrite_ite_eq"
 "cvc5_Rewrites.rewrite_distinct_binary_elim"
lemmas [rare_cvc5_rewrites_complex] =
"cvc5_Rewrites.rewrite_or_not_refl"
lemmas [rare_cvc5_rewrites_all] = rare_cvc5_rewrites_simple rare_cvc5_rewrites_complex


(*All*)

lemmas [rare_rewrites_simple] = rare_bool_rewrites_simple rare_arith_rewrites_simple rare_uf_rewrites_simple rare_cvc5_rewrites_simple
lemmas [rare_rewrites_complex] = rare_bool_rewrites_complex rare_arith_rewrites_complex rare_uf_rewrites_complex rare_cvc5_rewrites_complex
lemmas [rare_rewrites_all] = rare_rewrites_simple rare_rewrites_complex


end