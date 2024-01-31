theory SMT_CVC \<comment> \<open>More Setup for CVC that should be in HOL eventually\<close>
  imports HOL.SMT "cvc5_dsl_rewrites/Rare_Interface"
  keywords "smt_status" "check_smt_dir" "check_smt" :: diag
begin

named_theorems all_simplify_temp \<open>Theorems to reconstruct bitvector theorems concerning list
                                  functions, e.g. take.\<close>

named_theorems cvc_evaluate \<open>Theorems to reconstruct evaluate steps in cvc5 proofs\<close>

named_theorems arith_simp_cvc5 \<open>Might be temp and integrated into smt_arith_simplify \<close>

lemmas [arith_simp_cvc5] = Groups.monoid_mult_class.mult_1_right Nat.mult_Suc_right
                     Nat.mult_0_right Nat.add_Suc_right Groups.monoid_add_class.add.right_neutral
                     Num.numeral_2_eq_2 Nat.One_nat_def Num.numeral_2_eq_2 Nat.One_nat_def
                     Nat.Suc_less_eq Nat.zero_less_Suc minus_nat.diff_0 Nat.diff_Suc_Suc Nat.le0


ML_file \<open>ML/SMT_set.ML\<close>
ML_file \<open>ML/lethe_replay_all_simplify_methods.ML\<close>

ML_file \<open>ML/smt_parse_problem.ML\<close>
ML_file \<open>ML/smt_check_external.ML\<close>

ML \<open>

(*Call replay from SMT_Solver and add replay_data on your own*)
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>check_smt\<close>
          "parse a file in SMTLIB2 format and check proof. <problem_file,proof_file>"
    (Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.string --| \<^keyword>\<open>)\<close>) "cvc5" --
    (Parse.string -- Parse.string)
    >> (fn (prover, (problem_file_name,proof_file_name)) => fn lthy =>
  let
    val ctxt = Local_Theory.target_of lthy
    fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of
    val _ = SMT_Config.verbose_msg ctxt (pretty "Checking Alethe proof...") []
    (*Replay proof*)
    val _ = SMT_Check_External.check_smt prover problem_file_name proof_file_name NONE lthy
    val _ = SMT_Config.verbose_msg ctxt (pretty "Checked Alethe proof") []
  in
   lthy
  end))

(*Call replay from SMT_Solver and add replay_data on your own*)
(*The problem (name.smt2) and proof files (name.alethe) should be in the same directory.*)
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>check_smt_dir\<close>
         "parse a directory with SMTLIB2 format and check proof. <dir>"
    ((Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.string --| \<^keyword>\<open>)\<close>) "cvc5" -- Parse.string)
    >> (fn (prover, dir_name) => fn lthy =>
  let
    val _ = SMT_Check_External.test_all_benchmarks prover dir_name NONE lthy
  in
   lthy
   end))

\<close>



declare [[smt_trace=false,smt_timeout=5000000,smt_cvc_lethe = true]]

ML \<open> 
Config.put SMT_Config.trace true\<close>
declare[[smt_nat_as_int=true,smt_trace=true,smt_verbose=true,smt_debug_verit]]

declare[[native_set=true]]
lemma
"(A::int set) = {1,2} \<Longrightarrow> card (A::int set) = 2"
  sorry









end
