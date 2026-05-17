theory SMT_CVC \<comment> \<open>More Setup for CVC that should be in HOL eventually\<close>
  imports HOL.SMT "cvc5_rare_rewrites/Rare_Interface"
  keywords "smt_status" "check_smt_dir" "check_smt" "check_smt_slice" :: diag
begin

(*lemmas [cvc_evaluate] = arith_simp_cvc5*)


named_theorems word_cat_helper_def \<open>test\<close>

(*Term rewrites*)

ML_file \<open>ML/alethe_replay_rare_simplify_methods.ML\<close>

ML \<open>
fun cvc_term_parser (SMTLIB.Sym "rare-list", []) = (
   (*If there are no elements in the list we cannot know the type at this point*)
    SOME(Const( \<^const_name>\<open>ListVar\<close> ,dummyT --> dummyT)
       $ Const( \<^const_name>\<open>List.Nil\<close>, dummyT)))
  | cvc_term_parser (SMTLIB.Sym "rare-list", ts) =(
    let
      (*OLD: Figure out if types are different, this should only be the case if they have different
        bitwidths*)
      (*fun remove_duplicates [] = []
        | remove_duplicates (x::xs) = x::remove_duplicates(List.filter (fn y => y <> x) xs)
      val types_eq = map fastype_of ts |> remove_duplicates |> length 
      *)

      val has_bv = ((hd ts |> fastype_of |> Term.dest_Type |> fst|> @{print}) = "Word.Word")

      val new_ts =
         (if not has_bv
         then ts
         else (map (fn t => Const("to_bl", fastype_of t -->  \<^typ>\<open>bool list \<close>) $ t) ts))
      val new_type = if not has_bv then fastype_of (hd ts) else \<^typ>\<open>Nat.nat\<close>

    in
    if not has_bv
    then
      SOME(Const( \<^const_name>\<open>ListVar\<close>, Type(\<^type_name>\<open>List.list\<close>,[new_type])  --> Type(\<^type_name>\<open>cvc_ListVar\<close>,[new_type]))
      $ (HOLogic.mk_list new_type new_ts))
    else
      SOME (HOLogic.mk_list new_type new_ts)
    end)
  | cvc_term_parser _ = NONE

 fun power _ _ [t1] =
    let
      val mk = Term.list_comb o pair @{term "pow_2"}
    in SOME ("int.pow2", 1, [t1], mk) end
 | power _ _ _ = NONE

val setup_builtins =
  SMT_Builtin.add_builtin_fun SMTLIB_Interface.smtlibC
    (("int.pow2", Term.dest_Const (\<^Const>\<open>SMT.pow_2\<close>) |> snd), power)

val _ = Theory.setup (Context.theory_map (
  setup_builtins #>
  SMTLIB_Proof.add_term_parser cvc_term_parser)
)
\<close>

(*check that int.pow2 is properly registered*)
ML \<open>
if is_none (SMT_Builtin.dest_builtin_fun @{context}
  ("int.pow2", @{typ "int \<Rightarrow> int"})
   [@{term "2::int"}])
then error "fail to recognize int.pow2" else ()\<close>

(*External proof checking*)
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
    val _ = SMT_Check_External.check_smt (if prover = "cvc5" then "cvc5_proof" else prover)
        problem_file_name proof_file_name NONE lthy
    val _ = SMT_Config.verbose_msg ctxt (pretty "Finished checking Alethe proof!") []
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
    val _ = SMT_Check_External.check_all_benchmarks prover dir_name NONE lthy
  in
   lthy
   end))
val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>check_smt_slice\<close>
          "parse a file in SMTLIB2 format and check proof. <problem_file,proof_file>"
    (Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.string --| \<^keyword>\<open>)\<close>) "cvc5" --
    (Parse.string -- Parse.string)
    >> (fn (prover, (problem_file_name,proof_file_name)) => fn lthy =>
  let
    val ctxt = Local_Theory.target_of lthy
    fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of
    val _ = SMT_Config.verbose_msg ctxt (pretty "Checking Alethe proof...") []
    (*Replay proof*)
    val lthy' = Local_Theory.map_contexts (K (Config.put SMT_Config.slice_only_no_full_proof_attr true)) lthy
    val _ = SMT_Check_External.check_smt (if prover = "cvc5" then "cvc5_proof" else prover)
        problem_file_name proof_file_name NONE lthy'
    val _ = SMT_Config.verbose_msg ctxt (pretty "Finished checking Alethe proof!") []
  in
   lthy
  end))
\<close>

end
