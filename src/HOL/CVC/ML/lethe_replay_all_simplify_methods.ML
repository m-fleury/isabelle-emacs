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

val TRY' = Lethe_Replay_Methods.TRY'
val simplify_tac = Lethe_Replay_Methods.simplify_tac
val REPEAT_CHANGED = Lethe_Replay_Methods.REPEAT_CHANGED
val replay_error = Lethe_Replay_Methods.replay_error

fun dsl_tac_initialize rewrite_name args ctxt t =
let

 fun test_lemma theory_name rewrite_name = try (Named_Theorems.get ctxt) (theory_name ^ ".rewrite_" ^ rewrite_name) |> Option.isSome

 fun rewrite_lemma rewrite_name =
let

fun find_Thy []  = nth (Named_Theorems.get ctxt ("Builtin_Rewrites.rewrite_"^rewrite_name)) 0 | (*TODO: Error*)
    find_Thy (thy::thys) =
      let
        val thy_name = (Context.theory_base_name thy)
        val _= @{print} ("name",(thy_name ^ "."^rewrite_name))
        val _= @{print} ("test lemma",test_lemma thy_name rewrite_name)

      in
      if test_lemma thy_name rewrite_name (*TODO: Don't do this twice*)
      then nth (Named_Theorems.get ctxt (thy_name^".rewrite_"^rewrite_name)) 0 (*TODO: Do we need named theorems anymore?*)
(*If we do we can just map to names above and not work on theory list here*)
      else find_Thy thys
end

in 
find_Thy all_rewrite_thys

end

 fun rewrite_lemma_inst rewrite_name [t]  =
    (Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [t]) (rewrite_lemma rewrite_name)) |
 rewrite_lemma_inst rewrite_name (t :: ts) =
     Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [t]) (rewrite_lemma_inst rewrite_name ts)
(*
val _ = @{print}("rewrite_lemma_inst",(rewrite_lemma_inst rewrite_name (rev args)))

fun testm i = NO_CONTEXT_TACTIC ctxt
 ((Method.unfold @{thms cvc_list_right_Nil cvc_list_left_Nil cvc_list_right_Cons cvc_list_left_Cons} ctxt) 
[(rewrite_lemma_inst rewrite_name (rev args))])

val test2 = Seq.list_of
((unfold_tac ctxt @{thms cvc_list_right_Nil cvc_list_left_Nil cvc_list_right_Cons cvc_list_left_Cons})
 (rewrite_lemma_inst rewrite_name (rev args)))


val test3 = 
Seq.list_of ((HEADGOAL (simplify_tac ctxt @{thms cvc_list_right_Nil cvc_list_left_Nil cvc_list_right_Cons cvc_list_left_Cons}))
 (rewrite_lemma_inst rewrite_name (rev args)))


fun test4 thm = Seq.list_of ((NO_CONTEXT_TACTIC ctxt
 ((Method.unfold @{thms cvc_list_right_Nil cvc_list_left_Nil cvc_list_right_Cons cvc_list_left_Cons} ctxt) 
[(rewrite_lemma_inst rewrite_name (rev args))])) thm)
*)
in
 ((*@{print} ("rewrite_name with initialization given", rewrite_name);*)
   SMT_Replay_Methods.prove ctxt t (fn a =>
       (*K (print_tac ctxt ("all-simplify at the beginning "))*
       THEN'*)  Method.insert_tac ctxt
[Simplifier.simplify ((put_simpset HOL_basic_ss (empty_simpset ctxt)) addsimps @{thms cvc_list_right_Nil cvc_list_left_Nil cvc_list_right_Cons cvc_list_left_Cons}) (rewrite_lemma_inst rewrite_name (rev args))]
       (*THEN' (Method.insert_tac ctxt test2)*)
       (*THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] test3))*)
      (*THEN' K (HEADGOAL (EqSubst.eqsubst_tac ctxt [1] test4))*)
      (*THEN' TRY' (Method.assm_tac ctxt)*)
      THEN' TRY' (simplify_tac ctxt [@{lemma \<open>A = B ==> A = B\<close> by blast}])
      THEN' TRY' (resolve_tac ctxt [@{thm refl}])

(*((d::bool) \<and> ((b::bool) \<and> (c::bool)) \<and> (a::bool)) = (d \<and> (b \<and> c) \<and> a)*)
    (*THEN' TRY' (K (Clasimp.auto_tac ctxt)*)
))
end


local 

fun try_simp ctxt t = 
  SMT_Replay_Methods.prove ctxt t (fn a =>
     TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems all_simplify_temp})))))
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt @{thms arith_simps verit_minus_simplify})))
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))))
     THEN' TRY' (K (Clasimp.auto_tac ctxt))
     THEN' K (print_tac ctxt "debug in try simp")
  )

fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of

in 

 fun all_simplify ctxt (_ : thm list) (Free (rewrite_name, _) :: args) t =
  if rewrite_name = "evaluate"
  then
   (SMT_Config.verbose_msg ctxt (pretty ("Found evaluate, try to simplify")) []; try_simp ctxt t)
  else
    dsl_tac_initialize rewrite_name args ctxt t |
 all_simplify ctxt (_ : thm list) args t =
  (SMT_Config.verbose_msg ctxt (pretty ("No dsl rule found, try to simplify" ^
  List.foldr op^ "" (map ML_Syntax.print_term args))) []; try_simp ctxt t)

end

val rules = [
   ("all_simplify", all_simplify)]

val _ = Theory.setup (Context.theory_map (
   fold (uncurry Lethe_Replay_Methods.declare_alethe_rule) rules))

end