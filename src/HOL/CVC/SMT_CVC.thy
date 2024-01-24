theory SMT_CVC
  imports HOL.SMT "HOL-CVC.SMT_Word" "cvc5_dsl_rewrites/Rare_Interface"
  keywords "smt_status" "check_smt_dir" "check_smt" :: diag
begin

lemma cvc_ListOp_neutral_bv_and [cvc_ListOp_neutral]:
 "cvc_isListOp (ListOp (semiring_bit_operations_class.and) (-1::'a::len word))"
  by auto

named_theorems all_simplify_temp \<open>Theorems to reconstruct bitvector theorems concerning list
                                  functions, e.g. take.\<close>
named_theorems arith_simp_cvc5 \<open>Might be temp and integrated into smt_arith_simplify \<close>

lemmas [arith_simp_cvc5] = Groups.monoid_mult_class.mult_1_right Nat.mult_Suc_right
                     Nat.mult_0_right Nat.add_Suc_right Groups.monoid_add_class.add.right_neutral
                     Num.numeral_2_eq_2 Nat.One_nat_def Num.numeral_2_eq_2 Nat.One_nat_def
                     Nat.Suc_less_eq Nat.zero_less_Suc minus_nat.diff_0 Nat.diff_Suc_Suc Nat.le0

ML_file \<open>ML/lethe_replay_all_simplify_methods.ML\<close>
ML_file \<open>ML/SMT_string.ML\<close>
ML_file \<open>ML/SMT_set.ML\<close>
ML_file \<open>ML/SMT_array.ML\<close>
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


ML \<open>

fun mk_binary' n T U t1 t2 = Const (n, [T, T] ---> U) $ t1 $ t2

fun mk_binary n t1 t2 =
  let val T = fastype_of t1
  in mk_binary' n T T t1 t2 end

fun mk_rassoc f ts =
  let val us = rev ts
  in fold f (tl us) (hd us) end

fun mk_rassoc' n = mk_rassoc (mk_binary n)

fun pairwise _ [] = []
  | pairwise f (t1::tss)
           = (map (fn u => f (t1,u)) tss) @ pairwise f tss

(*cvc5 specific terms that are not present in veriT's output*)
fun cvc_term_parser (SMTLIB.Sym "xor",[t1,t2]) = SOME(Const(\<^const_name>\<open>SMT_CVC_Util.xor\<close>, \<^typ>\<open>bool \<Rightarrow> bool \<Rightarrow> bool\<close>)
       $ t1 $ t2)
  | cvc_term_parser (SMTLIB.Sym "cvc5_nary_op", []) =
   (*If there are no elements in the list we cannot know the type at this point*)
    SOME(Const( \<^const_name>\<open>ListVar\<close> ,dummyT --> dummyT)
       $ Const( \<^const_name>\<open>List.Nil\<close>, dummyT))
  | cvc_term_parser (SMTLIB.Sym "cvc5_nary_op", ts) = 
    let
      (*Figure out if types are different, this should only be the case if they have different
        bitwidths*)
      fun remove_duplicates [] = []
        | remove_duplicates (x::xs) = x::remove_duplicates(List.filter (fn y => y <> x) xs)

      val types_eq = map fastype_of ts |> remove_duplicates |> length 
      val new_ts =
         if types_eq > 0
         then ts
         else (map (fn t => Const( \<^const_name>\<open>unsigned\<close>, \<^typ>\<open>'a::len word \<Rightarrow> Nat.nat \<close>) $ t) ts)
      val new_type = if types_eq > 0 then fastype_of (hd ts) else \<^typ>\<open>Nat.nat\<close>

    in
    SOME(Const( \<^const_name>\<open>ListVar\<close>, Type(\<^type_name>\<open>List.list\<close>,[new_type])  --> Type(\<^type_name>\<open>cvc_ListVar\<close>,[new_type]))
      $ (HOLogic.mk_list new_type new_ts))
    end
  | cvc_term_parser (SMTLIB.Sym "emptyString", []) = SOME (Free ("''''", \<^typ>\<open>String.string\<close>))
  | cvc_term_parser (SMTLIB.Sym "distinct", ts)
     = SOME (mk_rassoc' \<^const_name>\<open>HOL.conj\<close> (pairwise (HOLogic.mk_eq #> HOLogic.mk_not) ts))
  | cvc_term_parser xs = (case SMT_String.string_term_parser xs of
    SOME x => SOME x |
    NONE =>
      case SMT_Set.set_term_parser xs of
        SOME y => SOME y |
        NONE => SMT_Array.array_term_parser xs)

 fun cvc_type_parser (SMTLIB.Sym "?", _) = SOME dummyT |
     cvc_type_parser (SMTLIB.Sym "?BitVec", []) = SOME (Type (\<^type_name>\<open>word\<close>, [dummyT])) |
  cvc_type_parser xs =
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

ML \<open> 
Config.put SMT_Config.trace true\<close>

lemma "LENGTH(64) = 64"
  supply [[smt_trace,smt_nat_as_int]]
  sorry

end
