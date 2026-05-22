theory SMT_CVC \<comment> \<open>More Setup for CVC that should be in HOL eventually\<close>
  imports HOL.SMT "HOL.Alethe_Rare_Interface"
  keywords "smt_status" :: diag
begin

(*Term rewrites*)
ML \<open>


(*alethe proofs can contain rare_rewrites. The arguments may use rare-list to express lists.*)
fun alethe_term_parser (SMTLIB.Sym "rare-list", []) = (
   (*If there are no elements in the list we cannot know the type at this point*)
    SOME(Const(\<^const_name>\<open>ListVar\<close> ,dummyT --> dummyT) $ Const(\<^const_name>\<open>List.Nil\<close>, dummyT)))
| alethe_term_parser (SMTLIB.Sym "rare-list", ts) = (
  let
    val new_type = fastype_of (hd ts)
  in
    SOME(Const(\<^const_name>\<open>ListVar\<close>, Type(\<^type_name>\<open>List.list\<close>,[new_type]) --> Type(\<^type_name>\<open>cvc_ListVar\<close>,[new_type]))
    $ (HOLogic.mk_list new_type ts))
  end)
| alethe_term_parser _ = NONE

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_term_parser alethe_term_parser)
)\<close>
ML \<open>

 fun power _ _ [t1] =
    let
      val mk = Term.list_comb o pair @{term "pow_2"}
    in SOME ("int.pow2", 1, [t1], mk) end
 | power _ _ _ = NONE

val setup_builtins =
  SMT_Builtin.add_builtin_fun SMTLIB_Interface.smtlibC
    (("int.pow2", Term.dest_Const (\<^Const>\<open>SMT.pow_2\<close>) |> snd), power)

val _ = Theory.setup (Context.theory_map (
  setup_builtins 
))
\<close>
ML_file \<open>ML/alethe_replay_rare_simplify_methods.ML\<close>

(*check that int.pow2 is properly registered*)
ML \<open>
if is_none (SMT_Builtin.dest_builtin_fun @{context}
  ("int.pow2", @{typ "int \<Rightarrow> int"})
   [@{term "2::int"}])
then error "fail to recognize int.pow2" else ()\<close>

end
