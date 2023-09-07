(*  Title:      HOL/Tools/SMT/lethe_replay_methods.ML
    Author:     Mathias Fleury, MPII, JKU, University Freiburg
    Author:     Hanna Lachnitt, Standford

Proof method for replaying Alethe proofs for all-simplify
*)

signature LETHE_REPLAY_ALL_SIMPLIFY_METHODS =
sig
  val all_rewrite_thys : theory list
  val all_simplify: Lethe_Replay_Methods.lethe_tac_args
end;

structure Lethe_Replay_All_Simplify_Methods: LETHE_REPLAY_ALL_SIMPLIFY_METHODS =
struct

val TRY' = Lethe_Replay_Methods.TRY'
val simplify_tac = Lethe_Replay_Methods.simplify_tac

val all_rewrite_thys =
let
 (*This is a little hacky; get theory HOL-CVC.Rare_Interface without registering it (which would 
   involve registering all parents)*)
 val SMT_CVC_parent_thys = Theory.parents_of @{theory}
 val Rare_Interface_thy =
   nth (filter (fn thy => Context.theory_long_name thy = "HOL-CVC.Rare_Interface") SMT_CVC_parent_thys) 0
in
 Theory.parents_of Rare_Interface_thy
end

fun dsl_tac_initialize rewrite_name args ctxt t th =
let
 fun find_Thy [] = Lethe_Replay_Methods.replay_error ctxt
  "No corresponding rewrite lemma found, add yours manually in RARE_Interface.thy or use IsaRARE for automatic support.. "
   Lethe_Replay_Methods.All_Simplify th t |
 find_Thy (thy::thys) =
  let
   val thy_name = (Context.theory_base_name thy)
  in (* Long-term might change named_theorem to normal theorem *)
   case try (Named_Theorems.get ctxt) (thy_name ^ ".rewrite_" ^ rewrite_name) of
    NONE => find_Thy thys |
    (SOME thm) => nth thm 0
  end

 val rewrite_lemma = find_Thy all_rewrite_thys

 val get_types = map snd (rev (Term.add_vars (Thm.full_prop_of rewrite_lemma) []))

 fun rewrite_lemma_inst [] _  = rewrite_lemma |
  rewrite_lemma_inst _ []  = rewrite_lemma | (*TODO: throw error*)
  rewrite_lemma_inst (a :: args') (t::typs') = 
    if (Const ("Dsl_Nary_Ops.cvc_ListVar.ListVar", dummyT --> dummyT) $ Const ("List.list.Nil", dummyT) = a)
    then
      let
        val t' = dest_Type t |> snd |> hd
        val new_a = Const ( \<^const_name>\<open>ListVar\<close>, Type(\<^type_name>\<open>List.list\<close>,[t']) --> Type(\<^type_name>\<open>cvc_ListVar\<close>,[t']))
                  $ Const ("List.list.Nil", Type(\<^type_name>\<open>List.list\<close>,[t']))
      in
        Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [new_a]) (rewrite_lemma_inst args' typs') 
      end
    else
      Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [a]) (rewrite_lemma_inst args' typs')

 val cvc_list_defs = @{thms cvc_list_right_Nil cvc_list_left_Nil cvc_list_both_Singleton
                            cvc_list_right_Cons cvc_list_left_Cons cvc_list_both_Cons}
 val inst_lemma = rewrite_lemma_inst (rev args) (rev get_types)

in (*TODO: fixed-point rules*)
 (SMT_Replay_Methods.prove ctxt t (fn _ => Method.insert_tac ctxt
 [Simplifier.simplify ((put_simpset HOL_basic_ss (empty_simpset ctxt)) addsimps cvc_list_defs) inst_lemma]
  THEN' K (print_tac ctxt ("all-simplify did not resolve after instantiation "))
  THEN' TRY' (simplify_tac ctxt [@{lemma \<open>A = B ==> A = B\<close> by blast}])
  THEN' TRY' (resolve_tac ctxt [@{thm refl}])

))
end

fun try_simp ctxt t = 
  SMT_Replay_Methods.prove ctxt t (fn _ =>
     TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems all_simplify_temp})))))
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt @{thms arith_simps verit_minus_simplify})))
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))))
     THEN' TRY' (K (Clasimp.auto_tac ctxt))
     THEN' K (print_tac ctxt "debug in try simp")
  )

local 
 fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of
in 
 fun all_simplify ctxt (th : thm list) (Free (rewrite_name, _) :: args) t =
  if rewrite_name = "evaluate"
  then
   (SMT_Config.verbose_msg ctxt (pretty ("Found evaluate, try to simplify")) []; try_simp ctxt t)
  else
    (SMT_Config.verbose_msg ctxt (pretty ("Found rewrite rule " ^ rewrite_name)) []; dsl_tac_initialize rewrite_name args ctxt t th) |
 all_simplify ctxt (_ : thm list) args t =
  (SMT_Config.verbose_msg ctxt (pretty ("No dsl rule found, try to simplify" ^
  List.foldr op^ "" (map ML_Syntax.print_term args))) []; try_simp ctxt t)
end

val rules = [
   ("all_simplify", all_simplify)]

val _ = Theory.setup (Context.theory_map (
   fold (uncurry Lethe_Replay_Methods.declare_alethe_rule) rules))

end