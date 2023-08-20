theory SMT_CVC
  imports HOL.SMT "cvc5_dsl_rewrites/Rare_Interface"
  keywords "smt_status" "check_smt_dir" "check_smt" :: diag
begin

named_theorems all_simplify_temp \<open>Theorems to reconstruct bitvector theorems concerning list
                                  functions, e.g. take.\<close>
named_theorems arith_simp_cvc5 \<open>Might be temp and integrated into smt_arith_simplify \<close>

lemmas [arith_simp_cvc5] = Groups.monoid_mult_class.mult_1_right Nat.mult_Suc_right
                     Nat.mult_0_right Nat.add_Suc_right Groups.monoid_add_class.add.right_neutral
                     Num.numeral_2_eq_2 Nat.One_nat_def Num.numeral_2_eq_2 Nat.One_nat_def
                     Nat.Suc_less_eq Nat.zero_less_Suc minus_nat.diff_0 Nat.diff_Suc_Suc Nat.le0

ML_file\<open>ML/lethe_replay_all_simplify_methods.ML\<close>
ML_file \<open>ML/SMT_string.ML\<close>
ML_file \<open>ML/SMT_set.ML\<close>
ML_file \<open>ML/SMT_array.ML\<close>
ML_file \<open>ML/smt_parse_problem.ML\<close>
ML_file \<open>ML/smt_check_external.ML\<close>

ML \<open>

(*Call replay from SMT_Solver and add replay_data on your own*)
(*The problem (name.smt2) and proof files (name.alethe) should be in the same directory.*)
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>check_smt_dir\<close>
         "parse a directory with SMTLIB2 format and check proof. <dir>"
    ((Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.string --|
      \<^keyword>\<open>)\<close>)
     "cvc5" -- Parse.string)
    >> (fn (prover, dir_name) => fn lthy =>
  let
    val _ = SMT_Check_External.test_all_benchmarks prover dir_name lthy
in lthy end))

\<close>


ML \<open>
(*Call replay from SMT_Solver and add replay_data on your own*)
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>check_smt\<close> "parse a file in SMTLIB2 format and check proof. <problem_file,proof_file>"
    (Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.string --|
      \<^keyword>\<open>)\<close>)
     "cvc5" --
    (Parse.string -- Parse.string)
    >> (fn (prover, (problem_file_name,proof_file_name)) => fn lthy =>
  let
    (*Get problem and proof file*)
    val ctxt = Local_Theory.target_of lthy
    val problem_file_path = Path.explode problem_file_name
    val proof_file_path = Path.explode proof_file_name
    val problem_lines = (Bytes.split_lines (Bytes.read problem_file_path));
    val proof_lines = (Bytes.split_lines (Bytes.read proof_file_path));
    (*val _ = @{print} ("problem_lines", problem_lines)
    val _ = @{print} ("proof_lines", proof_lines)*)

    (*Output information*)
    fun pretty tag lines = Pretty.string_of (Pretty.big_list tag (map Pretty.str lines))

    val _ = SMT_Config.verbose_msg ctxt (pretty "Checking Alethe proof...") []
(*
    val _ = SMT_Config.verbose_msg ctxt (pretty "Problem:") problem_lines
    val _ = SMT_Config.verbose_msg ctxt (pretty "Proof to be checked:") proof_lines
*)
    (*Replay proof*)
    val _ = SMT_CHECK_EXTERNAL.replay_only prover ctxt problem_lines proof_lines
    val _ = (SMT_Config.verbose_msg ctxt (K ("Checked Alethe proof")) ())
in lthy end))
\<close>

ML \<open>

fun mk_binary' n T U t1 t2 = Const (n, [T, T] ---> U) $ t1 $ t2

fun mk_binary n t1 t2 =
  let val T = fastype_of t1
  in mk_binary' n T T t1 t2 end

fun mk_lassoc f t ts = fold (fn u1 => fn u2 => f u2 u1) ts t

fun mk_lassoc' n = mk_lassoc (mk_binary n)

fun mk_lassoc'' n S t
 = mk_lassoc (mk_binary' n (fastype_of t) (TVar (("?a", serial ()), S))) t 
(*TODO split all this*)
fun cvc_term_parser (SMTLIB.Sym "xor",[t1,t2]) = SOME (HOLogic.mk_not (HOLogic.mk_eq (t1, t2)))
  | cvc_term_parser (SMTLIB.Sym "cvc5_nary_op", ts) = 

(*Plan: If there is some content in ts try to figure out what type it has. If it has no dummy type
use that. Otherwise use ?a from the beginning?*)
    SOME(Const( \<^const_name>\<open>ListVar\<close> , \<^typ>\<open>HOL.bool list \<Rightarrow>  HOL.bool cvc_ListVar \<close>)
      (*$ (HOLogic.mk_list (TVar (("?a", serial ()), [])) ts))*)
      $ (HOLogic.mk_list \<^typ>\<open>HOL.bool\<close> ts))
  | cvc_term_parser (SMTLIB.Sym "emptyString", []) = SOME (Free ("''''", \<^typ>\<open>String.string\<close>))
  | cvc_term_parser (SMTLIB.Sym "distinct", ts)
    =
    let
     fun pairwise [] _ = []
       | pairwise (t1::tss) (_::uss) = (map (fn t2 => HOLogic.mk_not (HOLogic.mk_binrel \<^const_name>\<open>HOL.eq\<close> (t1,t2))) uss) @ pairwise tss uss
    in 
      SOME (mk_lassoc'\<^const_name>\<open>HOL.conj\<close> (hd (pairwise ts ts)) (tl (pairwise ts ts)))
    end
  | cvc_term_parser _ = NONE

 fun cvc_type_parser xs = 
  (case SMT_String.string_type_parser xs of
    SOME x => SOME x |
    NONE => 
      case SMT_Set.set_type_parser xs of
        SOME y => SOME y |
        NONE => SMT_Array.array_type_parser xs)
\<close>

ML \<open>
val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_term_parser cvc_term_parser)
)
val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser cvc_type_parser))
\<close>

declare [[smt_trace=false,smt_timeout=5000000,smt_cvc_lethe = true]]
check_smt "~/Documents/repos/SMTLIB/UFLIA/boogie-unsat/AdvancedTypes_AdvancedTypes.Advanced2_SubLessType_notnull-orderStrength_1.smt2"
  "~/Documents/repos/SMTLIB/UFLIA/boogie-unsat/AdvancedTypes_AdvancedTypes.Advanced2_SubLessType_notnull-orderStrength_1.alethe2"
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
ML \<open> 
Config.put SMT_Config.trace true\<close>
end