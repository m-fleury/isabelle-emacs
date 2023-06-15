theory SMT_CVC
  imports SMT "Tools/SMT/cvc5_dsl_rewrites/Boolean_Rewrites" "Tools/SMT/cvc5_dsl_rewrites/Builtin_Rewrites"
begin

ML_file \<open>Tools/SMT/lethe_replay_all_simplify_methods.ML\<close>

ML_file \<open>Tools/SMT/SMT_string.ML\<close>
ML_file \<open>Tools/SMT/SMT_set.ML\<close>
ML_file \<open>Tools/SMT/SMT_array.ML\<close>

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