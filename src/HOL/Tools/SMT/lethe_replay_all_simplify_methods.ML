(*  Title:      HOL/Tools/SMT/lethe_replay_methods.ML
    Author:     Mathias Fleury, MPII, JKU, University Freiburg
    Author:     Hanna Lachnitt, Standford

Proof method for replaying Alethe proofs for all-simplify
*)

signature LETHE_REPLAY_ALL_SIMPLIFY_METHODS =
sig
  val all_simplify: Lethe_Replay_Methods.lethe_tac_args

end;


structure Lethe_Replay_All_Simplify_Methods: LETHE_REPLAY_ALL_SIMPLIFY_METHODS =
struct

val TRY' = Lethe_Replay_Methods.TRY'
val simplify_tac = Lethe_Replay_Methods.simplify_tac
val REPEAT_CHANGED = Lethe_Replay_Methods.REPEAT_CHANGED
val replay_error = Lethe_Replay_Methods.replay_error

fun dsl_tac_initialize rewrite_name args ctxt t =
let

(*Get all parent theories of Rare_Interface. TODO: Maybe do this somewhere else so it doesn't has to be redone every time*)
(*Need to get the theory Rare_Interface for this? How? Only way seems to use a context?*)
(*val rewrite_theories = Theory.parents_of (Proof_Context.theory_of (Proof_Context.get_global (Theory.get_pure ()) "Rare_Interface.thy"))
val _ = @{print}("rewrite_theories",rewrite_theories)*)

(*This is completely WTF and has no change to work even remotely*)
fun is_BV rewrite_name = Named_Theorems.exists ctxt ("BV_Rewrites."^rewrite_name) (*have exist already give out the thm list? I don't want to change named_theorem so much*)
fun is_Bool rewrite_name = Named_Theorems.exists ctxt ("Boolean_Rewrites."^rewrite_name)
fun is_Arith rewrite_name = Named_Theorems.exists ctxt ("Arith_Rewrites."^rewrite_name)
fun is_String rewrite_name = Named_Theorems.exists ctxt ("String_Rewrites."^rewrite_name)

 fun rewrite_lemma rewrite_name =
       if rewrite_name = "bool_double_not_elim" then nth (Named_Theorems.get ctxt ("Boolean_Rewrites.rewrite_"^rewrite_name)) 0
       else if is_BV rewrite_name then nth (Named_Theorems.get ctxt ("BV_Rewrites."^rewrite_name)) 0
       else if is_Bool rewrite_name then nth (Named_Theorems.get ctxt ("Boolean_Rewrites."^rewrite_name)) 0
       else if is_Arith rewrite_name then nth (Named_Theorems.get ctxt ("Arith_Rewrites."^rewrite_name)) 0
       else if is_String rewrite_name then nth (Named_Theorems.get ctxt ("String_Rewrites."^rewrite_name)) 0
       else nth (Named_Theorems.get ctxt ("Builtin_Rewrites."^rewrite_name)) 0
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
THEN' K (print_tac ctxt "stuff 1")
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt @{thms arith_simps verit_minus_simplify})))
THEN' K (print_tac ctxt "stuff 10")
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))))
THEN' K (print_tac ctxt "stuff 20")
     THEN' TRY' (K (Clasimp.auto_tac ctxt))
  THEN' K (print_tac ctxt "stuff 30")
  )



fun get_tac (Free (rewrite_name, _) :: args) ctxt t =
   if rewrite_name = "evaluate" then (@{print} "Found evaluate, try to simplify"; try_simp ctxt t)
    else dsl_tac_initialize rewrite_name args ctxt t |
 get_tac x ctxt t = (@{print} "No dsl rule found, try to simplify"; @{print} x; try_simp ctxt t)

in 
  fun all_simplify ctxt (_ : thm list) args t = (
warning (@{make_string} (" found all-simplify with args",args)); get_tac args ctxt t)
end

val rules = [
   ("all_simplify", all_simplify)]

val _ = Theory.setup (Context.theory_map (
   fold (uncurry Lethe_Replay_Methods.declare_alethe_rule) rules))

end