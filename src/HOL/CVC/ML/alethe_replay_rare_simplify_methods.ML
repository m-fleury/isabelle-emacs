(*  Title:      HOL/CVC/ML/alethe_replay_rare_simplify_methods.ML
    Author:     Mathias Fleury, MPII, JKU, University Freiburg
    Author:     Hanna Lachnitt, Stanford University

Proof method for replaying Alethe proofs for rare-simplify
*)

signature ALETHE_REPLAY_RARE_SIMPLIFY_METHODS =
sig
  val rare_rewrite: Alethe_Replay_Methods.alethe_tac_step_args
  exception RARE_REPLAY of string
end;

structure Alethe_Replay_RARE_Simplify_Methods: ALETHE_REPLAY_RARE_SIMPLIFY_METHODS =
struct

exception RARE_REPLAY of string

val TRY' = Alethe_Replay_Methods.TRY'
val simplify_tac = Alethe_Replay_Methods.simplify_tac

fun debug_msg ctxt = SMT_Config.alethe_debug_msg ctxt "alethe_replay_rare"
val low = SMT_Config.low
val middle = SMT_Config.middle
val high = SMT_Config.high


(*Tactics for experiments*)
fun try_auto_solo ctxt t = 
  SMT_Replay_Methods.prove ctxt t (fn _ => TRY' (K (Clasimp.auto_tac ctxt)))


(* Evaluation of constants *)
(* Any additional lemmas should be added to cvc_evaluate *)
fun try_evaluate ctxt t =
  SMT_Replay_Methods.prove ctxt t (fn _ =>
  TRY' (Code_Simp.dynamic_tac ctxt )
  THEN' TRY' (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems cvc_evaluate})))
 )

(* Rare rewrite reconstruction *)
fun dsl_tac_initialize rewrite_name args ctxt t _ =
let
  val _ = (if is_none (CVC5_Rare.rare_lookup (Context.Proof ctxt) ("rewrite_" ^ rewrite_name)) 
         then raise RARE_REPLAY ("undeclared RARE rule:" ^ rewrite_name ^ ". Use cvc5_rare \"full_name\".") else ())

  val rewrite_lemma = CVC5_Rare.rare_rule (Context.Proof ctxt) ("rewrite_" ^ rewrite_name) |> try hd |> the
    handle Option.Option => raise RARE_REPLAY ("Found more then one lemma corresponding to RARE rule" ^ rewrite_name)

  val get_types = map snd (rev (Term.add_vars (Thm.full_prop_of rewrite_lemma) []))

  fun is_list_arg (Const ("Dsl_Nary_Ops.cvc_ListVar.ListVar", _) $ Const ("List.list.Nil", _)) = true |
    is_list_arg _ = false

  fun instantiate_with_arg a t =
    if is_list_arg a
    then
      let
        val _ = debug_msg ctxt high (fn () => @{print} ("Detected List Argument", a));
        val t' = dest_Type t |> snd |> hd
        val new_a = Const ( \<^const_name>\<open>ListVar\<close>, Type(\<^type_name>\<open>List.list\<close>,[t']) --> Type(\<^type_name>\<open>cvc_ListVar\<close>,[t']))
                  $ Const ("List.list.Nil", Type(\<^type_name>\<open>List.list\<close>,[t']))
      in
        (map (SOME o Thm.cterm_of ctxt) [new_a])
      end
    else
     (map (SOME o Thm.cterm_of ctxt) [a])


  fun rewrite_lemma_inst [] []  = rewrite_lemma
   | rewrite_lemma_inst [] (_::_)  =
      raise RARE_REPLAY("Too few arguments for RARE rewrite " ^ rewrite_name)
   | rewrite_lemma_inst _ []  =
      raise RARE_REPLAY("Too many arguments for RARE rewrite " ^ rewrite_name)
   | rewrite_lemma_inst (a :: args') (t :: typs') = 
      Drule.infer_instantiate' ctxt (instantiate_with_arg a t) (rewrite_lemma_inst args' typs') 

  val inst_lemma = 
    rewrite_lemma_inst ( (rev args@[Const ("Groups.zero_class.zero",@{typ int})])) (rev get_types)
  val _ = debug_msg ctxt middle (fn () => @{print} ("Instantiated lemma",inst_lemma));

  val cvc_list_defs = @{thms cvc_list_right_Nil cvc_list_left_Nil cvc_list_both_Singleton
    cvc_list_right_Cons cvc_list_left_Cons cvc_list_both_Cons
    cvc_list_both_Cons_0 cvc_list_both_Cons_1 NO_MATCH_def}
  val inst_lemma_without_list = (Local_Defs.unfold ctxt) cvc_list_defs inst_lemma

  (*Should only happen if we have the extra argument*)
  val inst_lemma_without_true
    = Basic_Tactic.rule_by_tactic ctxt (resolve_tac ctxt [@{thm TrueI}] 1) inst_lemma_without_list

in
 (SMT_Replay_Methods.prove ctxt t (fn _ =>
  TRY' (EqSubst.eqsubst_tac ctxt [0] [inst_lemma_without_true])
  THEN' (resolve_tac ctxt [@{thm refl}])
 ))
end

(*TODO: Have different method based on theory rewrite is in*)
fun try_simp ctxt t = 
  SMT_Replay_Methods.prove ctxt t (fn _ =>
     TRY' (K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems cvc_evaluate})))))
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems rare_simplify_temp})))))
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt @{thms arith_simps verit_minus_simplify})))  
     THEN' TRY'(K (HEADGOAL (simplify_tac ctxt ((Named_Theorems.get ctxt @{named_theorems arith_simp_cvc5})))))
     THEN' TRY' (K (Clasimp.auto_tac ctxt))
  )

local 
 fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of
in 

 fun rare_rewrite ctxt (th : thm list) (Free (rewrite_name, _) :: args) t =
 (
  if rewrite_name = "evaluate"
  then
   (debug_msg ctxt low (fn () => @{print} "Found evaluate, try to simplify");
    try_evaluate ctxt t)
  else if rewrite_name = "arith_poly_norm"
  then
   (debug_msg ctxt low (fn () => @{print} "Found arith_poly_norm, try to simplify");
    try_simp ctxt t)
  else
   (debug_msg ctxt low (fn () => @{print} "Found rare rewrite " ^ rewrite_name);
    dsl_tac_initialize rewrite_name args ctxt t th)
 )
 | rare_rewrite ctxt _ args t =
   ((SMT_Config.verbose_msg ctxt (pretty ("No dsl rule found, try to simplify" ^
     List.foldr op^ "" (map ML_Syntax.print_term args))) []; try_simp ctxt t))
end

val rules = [
   ("rare_rewrite", rare_rewrite)]

val _ = Theory.setup (Context.theory_map (
   fold (uncurry Alethe_Replay_Methods.declare_alethe_rule) rules))

end
