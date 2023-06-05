theory SMT_CVC
  imports SMT "Tools/SMT/cvc5_dsl_rewrites/Boolean_Rewrites" "Tools/SMT/cvc5_dsl_rewrites/Builtin_Rewrites"
begin

ML_file \<open>Tools/SMT/lethe_replay_all_simplify_methods.ML\<close>

thm Builtin_Rewrites.bool_double_neg_elim
ML \<open>

\<close>

declare [[smt_trace=false,smt_timeout=5000000,smt_cvc_lethe = true]]
check_smt "~/Documents/repos/SMTLIB/UFLIA/boogie-unsat/AdvancedTypes_AdvancedTypes.Advanced2_SubLessType_notnull-orderStrength_1.smt2"
  "~/Documents/repos/SMTLIB/UFLIA/boogie-unsat/AdvancedTypes_AdvancedTypes.Advanced2_SubLessType_notnull-orderStrength_1.alethe"
(*
why is 'T' transformed in 't'?
SMT: Successfully checked step t176.t8 
SMT: Goal: "bind"
       assumptions:
         ((IsNotNull_ ?o ?T = Smt__#__true) = (?o \<noteq> nullObject \<and> Is_ ?o ?T = Smt__#__true)) = ((Smt__#__true = IsNotNull_ ?o ?T) = (nullObject \<noteq> ?o \<and> Smt__#__true = Is_ ?o ?T))
       proposition:
         (\<forall>o t. (IsNotNull_ o t = Smt__#__true) = (o \<noteq> nullObject \<and> Is_ o t = Smt__#__true)) = (\<forall>o t. (Smt__#__true = IsNotNull_ o t) = (nullObject \<noteq> o \<and> Smt__#__true = Is_ o t)) 
[("o", "o"), ("T", "T")] (line 571 of "~~/src/HOL/Tools/SMT/lethe_replay_methods.ML") 
*)

(*

declare  [[smt_cvc_lethe = true,smt_trace]]
check_smt_dir "~/Documents/repos/SMTLIB/QF_UF/2018-Goel-hwbench_unsat/"
check_smt ("cvc5") "~/Documents/repos/SMTLIB/QF_UF/2018-Goel-hwbench_unsat/QF_UF_Heap_ab_br_max.smt2"
  "~/Documents/repos/SMTLIB/QF_UF/2018-Goel-hwbench_unsat/QF_UF_Heap_ab_br_max.alethe"
*)

lemma " (\<forall>T. (IsNotNull xxo T = Smt____true) =  (xxo \<noteq> nullObject \<and> Is xxo T = Smt____true)) = 
(\<forall>t. (Smt____true = IsNotNull xxo t) = (nullObject \<noteq> xxo \<and> Smt____true = Is xxo t))"
  apply auto



lemma "(\<forall>pc. pc \<noteq> nullObject \<and> (select2 Heap pc allocated = Smt____true) = True \<and> select2 Heap pc ownerRef = select2 Heap slt_in ownerRef \<and> select2 Heap pc ownerFrame = select2 Heap slt_in ownerFrame \<longrightarrow>
          select2 Heap pc inv = typeof pc \<and> select2 Heap pc localinv = typeof pc) =
    (\<forall>pc. nullObject \<noteq> pc \<and> Smt____true = select2 Heap pc allocated \<and> select2 Heap slt_in ownerRef = select2 Heap pc ownerRef \<and> select2 Heap slt_in ownerFrame = select2 Heap pc ownerFrame \<longrightarrow>
          typeof pc = select2 Heap pc inv \<and> typeof pc = select2 Heap pc localinv)"
  try0
  by auto
lemma True
  apply (smt (verit))
  sorry
ML \<open> 
Config.put SMT_Config.trace true\<close>
end