(*  Title:      HOL/Tools/SMT/alethe_replay.ML
    Author:     Mathias Fleury, JKU
    Author:     Hanna Lachnitt, Stanford University

Proof parsing and replay for cvc5.
*)

signature ALETHE_REPLAY =
sig
  val replay: (string -> Proof.context -> thm list -> term list -> term list -> term -> tactic_args option -> thm) -> 
     Proof.context -> SMT_Translate.replay_data -> string list -> thm
end;

structure Alethe_Replay: ALETHE_REPLAY =
struct

val trace = true
datatype debugging_verbosity = low | middle | high
fun debug_to_int low = 0 |
    debug_to_int middle = 1 |
    debug_to_int high = 2
val debug = true
val debugging_level = high (*0 low, 1 middle, 2 high verbosity*)

fun replay_trace_msg cond (x : unit -> 'a) = if cond then ignore(x ()) else ()
fun rtrace v = (replay_trace_msg trace v; v)
fun debug_crtrace c i v = (replay_trace_msg (debug andalso debug_to_int i <= debug_to_int debugging_level andalso c) v; v)
fun debug_rtrace i v = debug_crtrace true i v
val simplify_spaces = ATP_Util.strip_spaces false (K true)

fun filter_split _ [] = ([], [])
  | filter_split f (a :: xs) =
     (if f a then apfst (curry op :: a) else apsnd (curry op :: a)) (filter_split f xs)

fun subst_only_free pairs =
  let
     fun substf u =
        (case Termtab.lookup pairs u of
          SOME u' => u'
        | NONE =>
          (case u of
            (Abs(a,T,t)) => Abs(a, T, substf t)
          | (t$u') => substf t $ substf u'
          | u => u))
  in substf end;

val is_input_rule = curry (op =) Alethe_Proof.input_rule


fun under_fixes f unchanged_prems (prems, prems_as_thms_with_context_assms) names step_args context_assignments (concl, ctxt) tactic_args =
  let
    val thms1 = unchanged_prems @ map (SMT_Replay.varify ctxt) prems(* |> @{print}*)
    val thms2 = map snd prems_as_thms_with_context_assms(* |> @{print}*)
    (*val _ = @{print}("decls",decls)*)
  in (f ctxt (thms1 @ thms2) step_args context_assignments concl tactic_args) end


(** Replaying **)

fun replay_thm method_for rewrite_rules ll_defs ctxt assumed unchanged_prems prems prems_as_thms_with_context_assms
    concl_transformation global_transformation step_args context_assignments args
    (Alethe_Node.Alethe_Replay_Node {id, rule, concl, ...}) =
  let
    val rewrite = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_rules []
        #> not (null ll_defs andalso Alethe_Proof.keep_raw_lifting rule) ? SMTLIB_Isar.unlift_term ll_defs
      end
    val rewrite_concl = (if Alethe_Proof.keep_app_symbols rule then
          filter (curry Term.could_unify (Thm.concl_of @{thm SMT.fun_app_def}) o Thm.concl_of) rewrite_rules
        else rewrite_rules) |> @{print}
    val post = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_concl []
        #> Object_Logic.atomize_term ctxt
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
        #> SMTLIB_Isar.unskolemize_names ctxt
        #> HOLogic.mk_Trueprop
      end
(*val _ = @{print}("rule",rule )
val _ = @{print}("rule",not (Alethe_Proof.keep_raw_lifting rule ))
val _ = @{print}("rule",not (null ll_defs ))

val _ = @{print}("here",(not (null ll_defs) andalso not (Alethe_Proof.keep_raw_lifting rule) ))*)
    val concl = concl
      |> Term.subst_free concl_transformation
      |> subst_only_free global_transformation
      |> post

    val args = if rule = "refl" then SOME (Solver_Name "cvc5") else args

  in
    if rule = Alethe_Proof.input_rule then
      (case Symtab.lookup assumed id of
        SOME (_, thm) => thm
      | _ => raise Fail ("assumption " ^ @{make_string} id ^ " not found"))
    else
      under_fixes (method_for rule) unchanged_prems
        (prems, prems_as_thms_with_context_assms) []
        (map rewrite step_args)
        (map rewrite context_assignments)
        (concl, ctxt)
        args (*(Symtab.map (K rewrite) insts)*)
      |> Simplifier.simplify (empty_simpset ctxt addsimps rewrite_rules)
    handle (*temp for testing*)
     (ERROR msg) =>
       if Config.get ctxt SMT_Config.rec_evaluation
       then (raise SMT_Failure.SMT (SMT_Failure.Replay(rule,(ERROR (msg |> YXML.content_of)))))
       else Exn.reraise (ERROR msg) |
     (Fail msg)=>
       if Config.get ctxt SMT_Config.rec_evaluation
       then (raise SMT_Failure.SMT (SMT_Failure.Replay(rule,ERROR "failure")))
       else Exn.reraise (Fail msg) |
      err =>
       if Config.get ctxt SMT_Config.rec_evaluation
       then (raise SMT_Failure.SMT (SMT_Failure.Replay(rule,err)))
       else Exn.reraise err
  end
 | replay_thm _ _ _ _ _ _ _ _ _ _ _ _ _ _  = raise (Fail "TODO")



fun add_used_asserts_in_step (Alethe_Node.Alethe_Replay_Node {prems,
    subproof = (_, _, _, subproof), ...}) =
  union (op =) (map_filter (try (snd o SMTLIB_Interface.role_and_index_of_assert_name)) prems @
     flat (map (fn x => add_used_asserts_in_step x []) subproof)) |
  add_used_asserts_in_step (Alethe_Node.Alethe_Definition_Node _) = (fn x => x)

fun remove_rewrite_rules_from_rules n =
  (fn Alethe_Node.Alethe_Replay_Node {id, ...} =>
    (case try (snd o SMTLIB_Interface.role_and_index_of_assert_name) id of
      NONE => true
    | SOME a => (a >= n)))

(*
ll_defs: lambda_lifting defs

__ in variablen Namen wenn der Term im falschen Kontext ist
*)
fun replay_theorem_step method_for rewrite_rules all_assms ll_defs assumed (inputs : thm list) (all_local_assumptions : thm list)
  (step as Alethe_Node.Alethe_Replay_Node {id, rule, prems, step_args, context_assignments, 
     subproof = (fixes, assms, input, subproof), concl, args, ...})
  (globally_known_facts, stats, ctxt, concl_tranformation, global_transformation) =
  let
    val _ = rtrace (fn () => @{print} ("Replaying theorem step: ", id))
    val _ = @{print} prems

    val ctxt = Variable.variant_fixes [] ctxt
      |> (fn (_, ctxt) => fold Variable.declare_term [SMTLIB_Isar.unskolemize_names ctxt concl] ctxt)
    val (names, sub_ctxt) = Variable.variant_fixes (map fst fixes) ctxt
       ||> fold Variable.declare_term (map Free fixes)
    val export_vars = concl_tranformation @ (*TODO: Sollte keine __ auf der rechten Seite haben*)
       (ListPair.zip (map Free fixes, map Free (ListPair.zip (names, map snd fixes))))
    val _ = debug_crtrace (fixes <> []) low (fn () => @{print} ("Neuen Variablen vom Subproof (e.g., im Subproof neue Variablen):",fixes))
    val _ = debug_rtrace high (fn () => @{print} ("Add names from the step's conclusion to context"))
    val _ = debug_crtrace (names <> []) high (fn () => @{print} ("Add variables from fixes to subcontext.",names))
    val _ = debug_crtrace (export_vars <> []) middle (fn () => @{print} ("Mapping from variable names to the possibly new names that Isabelle chose",export_vars))
        (*Fixes machen dann whrs die neuen Vars*)

 
    (* Rewriting and Transforming Util *)       
    val remove_lambdas =
      let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy ((if (Alethe_Proof.keep_raw_lifting rule) andalso not (null rewrite_rules) then tl rewrite_rules else rewrite_rules)) []
        #> Object_Logic.atomize_term ctxt
        #> not (null ll_defs orelse Alethe_Proof.keep_raw_lifting rule) ? SMTLIB_Isar.unlift_term ll_defs
        #> SMTLIB_Isar.unskolemize_names ctxt
        #> HOLogic.mk_Trueprop
      end
val _ = if null ll_defs orelse Alethe_Proof.keep_raw_lifting rule then ignore (@{print} "not keeping") else
 ignore (@{print} "keeping")
    val term_rewriter2 = (subst_only_free global_transformation o Term.subst_free (export_vars) o remove_lambdas)
    val term_rewriter = (SMTLIB_Isar.unskolemize_names ctxt o term_rewriter2)

    fun is_refl thm = Thm.concl_of thm |> (fn (_ $ t) => t | _ => raise TERM ("",[])) |> HOLogic.dest_eq |> (op =) handle TERM _=> false
    fun mk_thms sctxt t = Assumption.add_assumes (map (Thm.cterm_of sctxt) t) sctxt |>> filter_out is_refl
    fun is_mapping (\<^term>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _ )) = true |
        is_mapping _ = false
    val remove_mappings = List.filter is_mapping

    (* Rewrite and Transform Components *)
    val _ = debug_crtrace (not (null (assms @ input @ context_assignments @ step_args))) middle
      (fn () => @{print} ("Rewrite components of the step (delete lets," ^
      " reflexivity and fixed variables in context assignments) and transform them to thms"))
    val rewritten_assms = map term_rewriter assms
    val rewritten_input = map term_rewriter input
    val rewritten_context_assignments = context_assignments |> remove_mappings |> map term_rewriter2
    val rewritten_step_args = map term_rewriter step_args
    val _ = debug_crtrace (not (null step_args)) high (fn () => @{print} ("Rewritten step arguments",(step_args,rewritten_step_args)))

    (* Build up Context sub_ctxt2 using (Context) Assumptions *)
    val _ = debug_rtrace high (fn () => @{print} ("Build up new subcontext from context assertions and assumes"))
    val (assms_as_thm, sub_ctxt2) = mk_thms sub_ctxt rewritten_assms
    val (input_as_thm, sub_ctxt2) = mk_thms sub_ctxt2 rewritten_input
    val (context_assignments_as_thm, sub_ctxt2) = mk_thms sub_ctxt2 rewritten_context_assignments 
    val updated_local_assumptions = all_local_assumptions @ assms_as_thm @ context_assignments_as_thm
val _ = @{print} assms_as_thm
val _ = @{print} updated_local_assumptions

    val _ = debug_crtrace (not (null rewritten_assms)) middle (fn () => @{print} ("Transformed assumptions, i.e. top-level assumes (before,after)",(assms,assms_as_thm)))
    val _ = debug_crtrace (not (null rewritten_input)) middle (fn () => @{print} ("Transformed input, i.e. assumes in subproofs (before,after)",(input,input_as_thm)))
    val _ = debug_crtrace (not (null rewritten_context_assignments)) middle (fn () => @{print} ("Transformed context assignments (before,after)",(context_assignments,context_assignments_as_thm)))
    val _ = debug_crtrace (not (null updated_local_assumptions)) low (fn () => @{print} ("All assumptions holding after the current step:", updated_local_assumptions))
 
    (* Processing Subproof *)
    val _ = debug_crtrace (not (null subproof)) low (fn () => @{print} ("Interrupting the replay of the current step " ^ id ^ " to replay its subproof"))
    (*val _ = @{print}("input",input)*)
    val replay = replay_theorem_step method_for rewrite_rules all_assms ll_defs assumed (input_as_thm @ inputs) updated_local_assumptions
    val (locally_known_facts, stats, _, _, sub_global_rew) =                                       
       fold replay subproof (globally_known_facts, stats, sub_ctxt2, export_vars, global_transformation)
    val _ = debug_crtrace (not (null subproof)) high (fn () => @{print} ("Filled table with mapping from names (id or for skolems var_def) to " ^
      "theorems with all steps the current step can access."))
    val _ = debug_crtrace (not (null subproof)) low (fn () => @{print} ("Finished processing the subproof, returning the original step",id))

    (* Processing Components with new Context *)
    val export_thm = singleton (Proof_Context.export sub_ctxt2 ctxt)
    val subst_transform = (Raw_Simplifier.rewrite_term (Proof_Context.theory_of (empty_simpset ctxt)) ((if (Alethe_Proof.keep_raw_lifting rule) andalso not (null rewrite_rules) then tl rewrite_rules else rewrite_rules)) []
         o @{print} o SMTLIB_Isar.unlift_term ll_defs o @{print} o Term.subst_free concl_tranformation o subst_only_free global_transformation o @{print})
    (*val _ = @{print}("concl_tranformation",global_transformation)*)
    val id_to_thm = (Symtab.lookup (if (null subproof) then globally_known_facts else locally_known_facts))
    val (prems_skolem_def,non_skolem_prems) = filter_split Alethe_Proof.is_skolem_def prems
    val prems_as_thms_with_context_assms =
      non_skolem_prems
      |> map_filter id_to_thm
      |> map (apsnd export_thm)
|> @{print}
    val skolem_rule_prems_as_thms_with_context_assms = 
      (if Alethe_Proof.is_skolemization rule (*Choice terms only appear in sko_forall and exists*)
       then prems_skolem_def |> map_filter (Symtab.lookup globally_known_facts) (*Skolem definitionen sind immer im auesseren Kontext*)
       else [])
    val step_args = map subst_transform step_args (*TODO*)
    val args =
      (case args of
        SOME (Alethe_Node.Insts tab) => SOME (Alethe_Node.Insts (Symtab.map (K subst_transform) tab)) |
        _ => args)
    val context_assignments = map subst_transform context_assignments
    val  _ = debug_crtrace (length non_skolem_prems <> length prems_as_thms_with_context_assms) low (fn () => 
      @{print} ("Warning, there were premises that are not accessible to the current step (i.e., that are not in the context). This should not happen. These were ignored."))
    val _ = debug_crtrace (not (null prems)) middle (fn () =>
      @{print} ("Export premises that are not skolem definitions, to the current context." ^
        "This will automatically add context assertions and assumes to the goal.",(prems,prems_as_thms_with_context_assms)))
    val _ = debug_crtrace (not (null step_args)) middle (fn () => @{print} ("Processed step_args",step_args))
    val _ = debug_crtrace (not (null context_assignments)) middle (fn () => @{print} ("Processed context_assignments", context_assignments))

    val missing_assumptions =
       if SMT_Config.alethe_no_provided_assms ctxt andalso
         (rule = Alethe_Proof.local_input_rule orelse is_input_rule rule)
       then all_assms else [] (*Bei externen Problemen wissen wir nicht welche assumptions benutzt wurden, also fuegen wir alle hinzu*)
    val all_local_assumptions =
       if Alethe_Replay_Methods.requires_subproof_assms prems rule then updated_local_assumptions else []
    val local_inputs =
       if Alethe_Replay_Methods.requires_local_input prems rule then input_as_thm @ inputs else []
    val _ = debug_crtrace (not (null missing_assumptions)) low (fn () => @{print} ("Added missing assumptions TODO",missing_assumptions))
    val _ = debug_crtrace (not (null all_local_assumptions)) low (fn () => @{print} ("Added mapping from context_assignment as premises to steps (refl,sko_forall,sko_ex,cong)",all_local_assumptions))
    val _ = debug_crtrace (not (null local_inputs)) low (fn () => @{print} ("local_inputs: subproof rule assumptions",local_inputs))


    (*val _ = @{print}("concl_tranformation",concl_tranformation)*)
(*Counter of what concl_trans is supposed to do?*)
 (*   fun remove_skolem_names (Free (a,b)) = Free(if String.isSuffix "__" a then Library.unsuffix "__" a else a,b) |
     remove_skolem_names x = x
    val concl_tranformation = map (fn (a,b) => (a,remove_skolem_names b)) concl_tranformation
    val _ = @{print}("concl_tranformation",concl_tranformation)
*)
    (*val _ = @{print}("(nthms @ skolem_prems_as_thms_with_context_assms)",(nthms @ skolem_prems_as_thms_with_context_assms))*)
    val _ = rtrace (fn () => @{print} ("Calling reconstruction method"))
    val replay = (Timing.timing (replay_thm method_for rewrite_rules ll_defs
       ctxt assumed [] (missing_assumptions @ all_local_assumptions @ local_inputs)
       (prems_as_thms_with_context_assms @ skolem_rule_prems_as_thms_with_context_assms) concl_tranformation
       global_transformation step_args context_assignments args))

    val ({elapsed, ...}, thm) =
      SMT_Config.with_time_limit ctxt SMT_Config.reconstruction_step_timeout replay step (*Welche Felder von Step benutzt replay_thm? Nur die conclusion?*)
        handle Timeout.TIMEOUT _ => raise SMT_Failure.SMT SMT_Failure.Time_Out (*TODO: Maybe add flag so this is only output when checking an external proof, although I feel it would be useful even when not*)
    val _ = (SMT_Config.verbose_msg ctxt (K ("Successfully checked step " ^ id)) ())

    val stats' = Symtab.cons_list (rule, Time.toNanoseconds elapsed) stats
    val globally_known_facts = Symtab.update (id, ([], thm)) globally_known_facts
    val _ = debug_rtrace low (fn () => @{print} ("Add resulting theorem to globabally known facts", (id,thm)))

  in (globally_known_facts, stats', ctxt,
       concl_tranformation, sub_global_rew) end
 | replay_theorem_step _ _ _ _ _ _ _ _ _  = raise (Fail "TODO")


fun replay_definition_step rewrite_rules ll_defs _ _ _
  (Alethe_Node.Alethe_Definition_Node {id, skolem_name, skolem_term, ...}) state =
  let
    val (proofs, stats, ctxt, concl_tranformation, global_transformation) = state

    val global_transformer = subst_only_free global_transformation
    val rewrite = let val thy = Proof_Context.theory_of ctxt in
        Raw_Simplifier.rewrite_term thy (rewrite_rules) []
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
      end
    val start0 = Timing.start ()
    val declaration = (rewrite o global_transformer) skolem_term
    val ([name], ctxt) = Variable.variant_fixes [skolem_name] ctxt
       ||> Variable.declare_term (Free (skolem_name, fastype_of declaration))
    val old_names = (Free (skolem_name, fastype_of declaration))
    val new_names = (Free (name, fastype_of declaration))
    fun update_mapping (a, b) tab =
          if a <> b andalso Termtab.lookup tab a = NONE
          then Termtab.update_new (a, b) tab else tab
    val global_transformation = global_transformation
     |> update_mapping (old_names, new_names)
    val global_transformer = subst_only_free global_transformation

    val generate_definition =
      (fn (name, term) => (HOLogic.mk_Trueprop
        (Const(\<^const_name>\<open>HOL.eq\<close>, fastype_of term --> fastype_of term --> @{typ bool}) $
            Free (name, fastype_of term) $ term)))
      #> global_transformer
      #> Thm.cterm_of ctxt
    val decls = generate_definition (skolem_name,declaration)
    val ([def], ctxt) = Assumption.add_assumes [decls] ctxt
    val thms_with_old_name = (declaration, def)
    val proofs = 
      (fn (name, thm) => Symtab.update (id, ([name], @{thm sym} OF [thm])))
      thms_with_old_name proofs
    val total = Time.toNanoseconds (#elapsed (Timing.result start0))
    val stats = Symtab.cons_list ("choice", total) stats
  in (proofs, stats, ctxt, concl_tranformation, global_transformation) end
 | replay_definition_step _ _ _ _ _ _ _   = raise (Fail "TODO")


fun replay_assumed assms ll_defs rewrite_rules stats ctxt term =
  let
    val rewrite = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_rules [] (*TODO: Figure out what rewrite_rules do*)
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs (*Lambda definitions werden unfolded*)
      end
    val replay = Timing.timing (SMT_Replay_Methods.prove ctxt (rewrite term)) (*Dasselbe fuer alle solver*)
    val ({elapsed, ...}, thm) =
      SMT_Config.with_time_limit ctxt SMT_Config.reconstruction_step_timeout replay
         (fn _ => Method.insert_tac ctxt assms THEN' Classical.fast_tac ctxt) (*Wissen den Grund nicht warum fast_tac verwendet wird, vielleicht nur zur Sicherheit*)
        handle Timeout.TIMEOUT _ => raise SMT_Failure.SMT SMT_Failure.Time_Out
    val stats' = Symtab.cons_list (Alethe_Proof.input_rule, Time.toNanoseconds elapsed) stats
  in
    (thm, stats')
  end

fun replay_step method_for rewrite_rules all_assms ll_defs assumed inputs all_local_assumptions
    (step as Alethe_Node.Alethe_Replay_Node {...}) state =
     replay_theorem_step method_for rewrite_rules all_assms ll_defs assumed inputs all_local_assumptions step state
  | replay_step method_for rewrite_rules _ ll_defs assumed inputs all_local_assumptions
    (step as Alethe_Node.Alethe_Definition_Node {...}) state =
     replay_definition_step rewrite_rules ll_defs assumed inputs all_local_assumptions step state
 

fun replay method_for outer_ctxt
    ({ctxt = ctxt, typs, terms, rewrite_rules, assms, ll_defs, ...} : SMT_Translate.replay_data)
     raw_proof_steps =
  let
    val _ = if not (SMT_Config.use_alethe_proof_from_cvc ctxt)
       then (raise SMT_Failure.SMT (SMT_Failure.Other_Failure ("reconstruction with CVC is experimental.\n" ^
         "You must activate it with [[smt_cvc_alethe = true]] and use cvc5 (not included as component) .")))
       else ()
    val _ = rtrace (fn () => @{print} ("Replaying proof"))

    (* Rewriting Util *)
    val rewrite_rules =
      filter_out (fn thm => Term.could_unify (Thm.prop_of @{thm verit_eq_true_simplify},
          Thm.prop_of thm))
        rewrite_rules
    val num_ll_defs = length ll_defs
    val index_of_id = Integer.add (~ num_ll_defs)

    (* Parse Proof *)
    val start0 = Timing.start ()
    val (parsed_proof_steps, ctxt_after_parsing) =
      Alethe_Proof.parse_replay typs terms raw_proof_steps ctxt
    val parsing_time = Time.toNanoseconds (#elapsed (Timing.result start0))
    val _ = debug_rtrace low (fn () => @{print} ("Finished parsing proof steps"))

    (*Find used and non lambda lifting definition assumptions *)
    val used_assert_ids = fold add_used_asserts_in_step parsed_proof_steps []
    val real_assms =
      map_filter (fn id => let val i = index_of_id id in if i >= 0 then
            let val concl = Thm.prop_of (snd (nth assms i))
              |> Raw_Simplifier.rewrite_term (Proof_Context.theory_of
               (empty_simpset ctxt addsimps rewrite_rules)) rewrite_rules []
            in SOME (SMTLIB_Interface.assert_name_of_role_and_index SMT_Util.Axiom id, Alethe_Proof.input_rule, concl, []) end
          else NONE end) used_assert_ids
    val _ = debug_rtrace high (fn () => @{print} ("real_assms ",real_assms))

    (* Process Lambda Lifting Definitions *)
    fun normalize_tac ctxt = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
      Raw_Simplifier.rewrite_term thy rewrite_rules [] end
    val used_lldefs =
      map_filter (fn id => let val i = index_of_id id in if i < 0
          then SOME (id, normalize_tac ctxt (nth ll_defs id))  else NONE end)
        used_assert_ids
    val _ = debug_rtrace high (fn () => @{print} ("used_lldefs ",used_lldefs))

    (* Add Assumptions to Context *)
    fun extract (Alethe_Node.Alethe_Replay_Node {id, rule, concl, ...}) = (id, rule, concl, [])
    val add_assert = SMT_Replay.add_asserted Symtab.update Symtab.empty (fn x => x) is_input_rule
    val ((_, _), (ctxt_with_asserts, assumed)) = (*assumed tabelle mit real assumptins*)
      add_assert outer_ctxt rewrite_rules (map (apfst fst) assms)
        (real_assms) ctxt_after_parsing (*TODO: Ask Mathias, why do we filter?*)
    val _ = debug_rtrace high (fn () => @{print} ("Alle assumptions sind in assumed ",assumed)) (*TODO: Understand better*)

    val ctxt_with_asserts =
      ctxt_with_asserts
   (* |> put_simpset (empty_simpset ctxt_with_asserts [])*) (*FIXME: commented out for easier development but should be added again since it will make auto faster (but also know less simplification rules)*)
      |> Config.put SAT.solver (Config.get ctxt_after_parsing SMT_Config.sat_solver)
    val _ = rtrace (fn () => @{print} ("num_ll_defs",num_ll_defs))

    (* Replay Assumption *)
    val (assumed, stats) = fold (fn ((id, thm)) => fn (assumed, stats) =>
      let
        val (thm, stats) = replay_assumed (map snd assms) ll_defs rewrite_rules stats ctxt thm (*replay assumptions*)
        val name = SMTLIB_Interface.assert_name_of_role_and_index SMT_Util.Axiom id
      in
        (Symtab.update (name, ([], thm)) assumed, stats) (*Das Replay hat das Theorem veraendert? (vllt wegen monomorphisierung?)*)
      end) (*TODO: Look at a few examples to see what it does, not sure if needed*)
      used_lldefs (assumed, Symtab.cons_list ("parsing", parsing_time) Symtab.empty)
    val _ = debug_rtrace high (fn () => @{print} ("Alle assumptions sind in assumed ",assumed)) (*TODO: Understand better*)

    (* Lineralize Step Ids *)
    val len = Alethe_Proof.number_of_steps parsed_proof_steps
    fun steps_with_depth _ [] = []
      | steps_with_depth i (p :: ps) =
        let val i' = i + Alethe_Proof.number_of_steps [p] in (i', p) :: steps_with_depth i' ps end
    val actual_steps = steps_with_depth 0 parsed_proof_steps
    val _ = debug_rtrace middle (fn () => @{print} ("Add indices to steps"))

    (*Set-up Statistics*)
    val start = Timing.start ()
    val print_runtime_statistics = SMT_Replay.intermediate_statistics ctxt_with_asserts start len
    fun blockwise f (i, x) (next, y) =
      (if i > next then print_runtime_statistics i else ();
       (if i > next then i + 10 else next, f x y))

    (*Replay Steps*)
    val global_transformation : term Termtab.table = Termtab.empty
    val (_, (proofs, stats, ctxt5, _, _)) =
      fold (blockwise (replay_step method_for rewrite_rules (map snd assms) ll_defs assumed [] [])) actual_steps
        (1, (assumed, stats, ctxt_with_asserts, [], global_transformation))
    val total = Time.toMilliseconds (#elapsed (Timing.result start))
    val (_, (_, Alethe_Node.Alethe_Replay_Node {id, ...})) = split_last actual_steps
    val thm_with_defs = Symtab.lookup proofs id |> the |> snd
      |> singleton (Proof_Context.export ctxt5 outer_ctxt)
    val _ = debug_rtrace middle (fn () => @{print} ("Last step (id " ^ id ^ ")", thm_with_defs))
(*TODO: Schaue mit beispiel mit skolems an*)

    (*Statistics*)
    val _ = print_runtime_statistics len
    val _ = SMT_Config.statistics_msg ctxt5
      (Pretty.string_of o SMT_Replay.pretty_statistics "cvc" total) stats
    fun print_stats stats =
    let
      fun print_list xs = fold (fn x => fn msg => msg ^ string_of_int x ^ ",") xs "" |> Library.unsuffix ","
    in
      fold (fn (x,y) => fn msg => msg ^ "\"" ^  x ^ "\": [" ^ print_list y ^ "],\n") stats "" |> Library.unsuffix ",\n"
    end
    (*TEMP*)
    val _ = 
      if Config.get ctxt SMT_Config.rec_evaluation
      then File.append (Path.explode ("$ISABELLE_HOME_USER/" ^
        (Config.get ctxt SMT_Config.statistics_file))) (string_of_int total
       ^ ",\"detail\": {" ^ print_stats (Symtab.dest stats) ^"}}]},\n")
      else ()

    val _ = SMT_Replay.spying (SMT_Config.spy_verit ctxt) ctxt
      (fn () => SMT_Replay.print_stats (Symtab.dest stats)) "spy_cvc"

  in
    CVC5_Replay_Methods.discharge ctxt [thm_with_defs] @{term False}
  end

end
