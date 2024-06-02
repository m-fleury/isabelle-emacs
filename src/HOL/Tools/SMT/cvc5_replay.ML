(*  Title:      HOL/Tools/SMT/cvc5_replay.ML
    Author:     Mathias Fleury, JKU
    Author:     Hanna Lachnitt, Stanford University

Proof parsing and replay for cvc5.
*)

signature CVC5_REPLAY =
sig
  val replay: Proof.context -> SMT_Translate.replay_data -> string list -> thm
end;

structure CVC5_Replay: CVC5_REPLAY =
struct

val trace = true
fun cvc5_replay_trace ctxt (x : unit -> 'a) = if trace then (@{print} (x ());ignore(x ())) else () (*Eventually, will use option in context, so leaving ctxt as argument*)
fun cvc5_replay_trace' ctxt (str : string) a  =
   let
    val _ = cvc5_replay_trace ctxt (fn () => str)
   in a end

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


fun under_fixes f unchanged_prems (prems, nthms) names step_args context_assignments (concl, ctxt) tactic_args =
  let
    val thms1 = unchanged_prems @ map (SMT_Replay.varify ctxt) prems(* |> @{print}*)
    val thms2 = map snd nthms(* |> @{print}*)
    (*val _ = @{print}("decls",decls)*)
  in (f ctxt (thms1 @ thms2) step_args context_assignments concl tactic_args) end


(** Replaying **)

fun replay_thm method_for rewrite_rules ll_defs ctxt assumed unchanged_prems prems nthms
    concl_transformation global_transformation step_args context_assignments args
    (Lethe_Node.Lethe_Replay_Node {id, rule, concl, ...}) =
  let
    val rewrite = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_rules []
        #> not (null ll_defs andalso Lethe_Proof.keep_raw_lifting rule) ? SMTLIB_Isar.unlift_term ll_defs
      end
    val rewrite_concl = if Lethe_Proof.keep_app_symbols rule then
          filter (curry Term.could_unify (Thm.concl_of @{thm SMT.fun_app_def}) o Thm.concl_of) rewrite_rules
        else rewrite_rules
    val post = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_concl []
        #> Object_Logic.atomize_term ctxt
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
        #> SMTLIB_Isar.unskolemize_names ctxt
        #> HOLogic.mk_Trueprop
      end
    val concl = concl
      |> Term.subst_free concl_transformation
      |> subst_only_free global_transformation
      |> post

    val args = if rule = "refl" then SOME (Solver_Name "cvc5") else args

  in
    if rule = Lethe_Proof.input_rule then
      (case Symtab.lookup assumed id of
        SOME (_, thm) => thm
      | _ => raise Fail ("assumption " ^ @{make_string} id ^ " not found"))
    else
      under_fixes (method_for rule) unchanged_prems
        (prems, nthms) []
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

fun add_used_asserts_in_step (Lethe_Node.Lethe_Replay_Node {prems,
    subproof = (_, _, _, subproof), concl, ...}) =
  union (op =) (map_filter (try (snd o SMTLIB_Interface.role_and_index_of_assert_name)) prems @
     flat (map (fn x => add_used_asserts_in_step x []) subproof))

fun remove_rewrite_rules_from_rules n =
  (fn (step as Lethe_Node.Lethe_Replay_Node {id, ...}) =>
    (case try (snd o SMTLIB_Interface.role_and_index_of_assert_name) id of
      NONE => SOME step
    | SOME a => if a < n then NONE else SOME step))

fun replay_theorem_step rewrite_rules all_assms ll_defs assumed inputs proof_prems
  (step as Lethe_Node.Lethe_Replay_Node {id, rule, prems, step_args, context_assignments, 
     subproof = (fixes, assms, input, subproof), concl,  args, ...}) state =
  let
    val (proofs, stats, ctxt, concl_tranformation, global_transformation) = state
    val _ = cvc5_replay_trace ctxt (fn () => "Replaying theorem step: " ^ \<^make_string> id)

    val (_, ctxt) = Variable.variant_fixes [] ctxt
      |> (fn (names, ctxt) => (names,
        fold Variable.declare_term [SMTLIB_Isar.unskolemize_names ctxt concl] ctxt))
    val _ = cvc5_replay_trace ctxt (fn () => "Build up a new Isabelle context with the term names from the step's conclusion")

    val (names, sub_ctxt) = Variable.variant_fixes (map fst fixes) ctxt
       ||> fold Variable.declare_term (map Free fixes)
    val _ = cvc5_replay_trace ctxt (fn () => "Add variables from fixes to subcontext. There should be no fixes though")
    val export_vars = concl_tranformation @
       (ListPair.zip (map Free fixes, map Free (ListPair.zip (names, map snd fixes))))
    val _ = cvc5_replay_trace' ctxt "Obtained mapping from variable names to the possibly new name that Isabelle chose." export_vars
                
    val remove_lambdas =
      let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy ((if Lethe_Proof.keep_raw_lifting rule andalso not (null rewrite_rules) then tl rewrite_rules else rewrite_rules)) []
        #> Object_Logic.atomize_term ctxt
        #> not (null ll_defs andalso Lethe_Proof.keep_raw_lifting rule) ? SMTLIB_Isar.unlift_term ll_defs
        #> SMTLIB_Isar.unskolemize_names ctxt
        #> HOLogic.mk_Trueprop
      end
    val _ = cvc5_replay_trace ctxt (fn () => "Obtained rewriter to remove lambda expressions from a term")

    val term_rewriter = (SMTLIB_Isar.unskolemize_names ctxt o subst_only_free global_transformation o Term.subst_free (export_vars) o remove_lambdas)
    fun is_refl thm = Thm.concl_of thm |> (fn (_ $ t) => t) |> HOLogic.dest_eq |> (op =) handle TERM _=> false
    (*TODO: Do somewhere else?*)
    fun is_mapping (x as  \<^term>\<open>Trueprop\<close> $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _ )) = true |
        is_mapping _ = false


    fun mk_thms t sctxt = Assumption.add_assumes (map (Thm.cterm_of sctxt) t) sctxt |>> filter_out is_refl
    val _ = cvc5_replay_trace ctxt (fn () => "Obtained rewriter filter out refl steps and transform into theorem")

    val _ = cvc5_replay_trace ctxt (fn () => "Apply rewriter")
    val _ = @{print}("all_proof_prems", assms @ context_assignments)
    val _ = @{print}("prems", proof_prems)

    val assms = map term_rewriter assms
      |> cvc5_replay_trace' ctxt "Rewrite assms"
      |> trace ? @{print}

    val input = map term_rewriter input
      |> cvc5_replay_trace' ctxt "Rewrite input (assumes in subproofs)"
      |> trace ? @{print}

    val step_args = map term_rewriter step_args
      |> cvc5_replay_trace' ctxt "Rewrite step arguments"
      |> trace ? @{print}

    val context_assignments = map term_rewriter context_assignments
      |> cvc5_replay_trace' ctxt "Rewrite context assignments"
      |> trace ? @{print}


    val (assms, sub_ctxt2) = mk_thms assms sub_ctxt
      |> cvc5_replay_trace' ctxt "Filter out refl assms and transform to theorem"
      |> trace ? @{print}

    val (input, sub_ctxt2) = mk_thms input sub_ctxt2
      |> cvc5_replay_trace' ctxt "Filter out refl inputs and transform to theorem"
      |> trace ? @{print}

    val context_assignments = List.filter is_mapping context_assignments
    val _ = @{print}("context_assignments",context_assignments)
      |> trace ? @{print}


    val (context_assignments2, sub_ctxt2) = mk_thms context_assignments sub_ctxt2
      |> cvc5_replay_trace' ctxt "Filter out refl context assigments and transform to theorem"

    val all_proof_prems = proof_prems @ assms @ context_assignments2
    val _ = @{print}("all_proof_prems",all_proof_prems)

    val replay = replay_theorem_step rewrite_rules all_assms ll_defs assumed (input @ inputs) all_proof_prems
    (*Tabelle mit mapping von Namen (id oder fuer skolem var_def) zu theoremen von allen Schritten auf die ich lokal zugreifen kann*)
    val (proofs', stats, _, _, sub_global_rew) =
       fold replay subproof (proofs, stats, sub_ctxt2, export_vars, global_transformation)

    (*Wir waren im Context wo theorem drin war jetzt holen wir das wieder raus. Es hat sich veraendert. v0 wird jetzt implizit fuer alle quantifiziert*)
    (*Wenn ich assumes block im subproof habe dann sollte es erlaubt sein das conclusion vom subproof kann mehrere Schritte referenzieren*)
    val export_thm = singleton (Proof_Context.export sub_ctxt2 ctxt)

    (*for sko_ex and sko_forall, assumptions are in proofs',  but the definition of the skolem
       function is in proofs *)
    val nthms =
      prems
      |> filter_out Lethe_Proof.is_skolem_def (*Alle fakten ausser skolem defs*)
      |> map (apsnd export_thm) o map_filter (Symtab.lookup (if (null subproof) then proofs else proofs'))
 (*
 map_filter (Symtab.lookup (if (null subproof) then proofs else proofs'))
Wir filtern die aus nicht im Kontext existieren (DAS SOLLTE NICHT PASSIEREN!)
Wir mappen Namen zu ihrem Thorem

map (apsnd export_thm) macht dann noch iwleche transformationen
*)


(*proof ist in proof' drin, aber nicht andersrum *)
(*proof' sind mapping von namen zu theoremen fuer den Subproof *)
(*proof sind alle vorherigen *)
    val nthms' = (if Lethe_Proof.is_skolemization rule
         then prems else [])
      |> filter Lethe_Proof.is_skolem_def (*Nur die skolem definitionen aus*)
      |> map_filter (Symtab.lookup proofs) (*Skolem definitionen sind immer im auesseren Kontext*)

    val step_args = map (Term.subst_free concl_tranformation o subst_only_free global_transformation) step_args
    val context_assignments = map (Term.subst_free concl_tranformation o subst_only_free global_transformation) context_assignments

    val missing_assumptions =
       if SMT_Config.alethe_no_provided_assms ctxt andalso
         (rule = Lethe_Proof.local_input_rule orelse rule = Lethe_Proof.input_rule)
       then all_assms else []
(*Wir wollen mappings vom Context assignment als premises an "refl", "sko_forall", "sko_ex", "cong" steps uebergeben*)
    val proof_prems =
       if Lethe_Replay_Methods.requires_subproof_assms prems rule then proof_prems else []
    val local_inputs =
       if Lethe_Replay_Methods.requires_local_input prems rule then input @ inputs else []

    val insts = Symtab.map (K (Term.subst_free concl_tranformation o subst_only_free global_transformation)) Symtab.empty (*insts TODO*)
    

    (*val _ = @{print}("(nthms @ nthms')",(nthms @ nthms'))*)
    val replay = (Timing.timing (replay_thm CVC5_Replay_Methods.method_for rewrite_rules ll_defs
       ctxt assumed [] (missing_assumptions @ proof_prems @ local_inputs) (nthms @ nthms') concl_tranformation
       global_transformation step_args context_assignments args))

    val ({elapsed, ...}, thm) =
      SMT_Config.with_time_limit ctxt SMT_Config.reconstruction_step_timeout replay step
        handle Timeout.TIMEOUT _ => raise SMT_Failure.SMT SMT_Failure.Time_Out
    (*TODO: Maybe add flag so this is only output when checking an external proof, although I feel
      it would be useful even when not*)
    val _ = (SMT_Config.verbose_msg ctxt (K ("Successfully checked step " ^ id)) ())

    val stats' = Symtab.cons_list (rule, Time.toNanoseconds elapsed) stats
    val proofs = Symtab.update (id, ([], thm)) proofs
  in (proofs, stats', ctxt,
       concl_tranformation, sub_global_rew) end

fun replay_definition_step rewrite_rules ll_defs _ _ _
  (Lethe_Node.Lethe_Replay_Node {id, subproof = (_, _, _, subproof), args, ...}) state =
  let
    val _ = if null subproof then ()
          else raise (Fail ("unrecognized cvc5 proof, definition has a subproof"))
    val (proofs, stats, ctxt, concl_tranformation, global_transformation) = state
    val global_transformer = subst_only_free global_transformation
    val rewrite = let val thy = Proof_Context.theory_of ctxt in
        Raw_Simplifier.rewrite_term thy (rewrite_rules) []
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
      end
    val start0 = Timing.start ()
    val declaration = map (apsnd (rewrite o global_transformer)) (case args of SOME (Declarations xs) => xs | _ => []) (*TODO: raw_declarations*)
    val (names, ctxt) = Variable.variant_fixes (map fst declaration) ctxt
       ||> fold Variable.declare_term (map Free (map (apsnd fastype_of) declaration))
    val old_names = map Free (map (fn (a, b) => (a, fastype_of b)) declaration)
    val new_names = map Free (ListPair.zip (names, map (fastype_of o snd) declaration))
    fun update_mapping (a, b) tab =
          if a <> b andalso Termtab.lookup tab a = NONE
          then Termtab.update_new (a, b) tab else tab
    val global_transformation = global_transformation
     |> fold update_mapping (ListPair.zip (old_names, new_names))
    val global_transformer = subst_only_free global_transformation

    val generate_definition =
      (fn (name, term) => (HOLogic.mk_Trueprop
        (Const(\<^const_name>\<open>HOL.eq\<close>, fastype_of term --> fastype_of term --> @{typ bool}) $
            Free (name, fastype_of term) $ term)))
      #> global_transformer
      #> Thm.cterm_of ctxt
    val decls = map generate_definition declaration
    val (defs, ctxt) = Assumption.add_assumes decls ctxt
    val thms_with_old_name = ListPair.zip (map fst declaration, defs)
    val proofs = fold
      (fn (name, thm) => Symtab.update (id, ([name], @{thm sym} OF [thm])))
      thms_with_old_name proofs
    val total = Time.toNanoseconds (#elapsed (Timing.result start0))
    val stats = Symtab.cons_list ("choice", total) stats
  in (proofs, stats, ctxt, concl_tranformation, global_transformation) end


fun replay_assumed assms ll_defs rewrite_rules stats ctxt term =
  let
    val rewrite = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
        Raw_Simplifier.rewrite_term thy rewrite_rules []
        #> not (null ll_defs) ? SMTLIB_Isar.unlift_term ll_defs
      end
    val replay = Timing.timing (SMT_Replay_Methods.prove ctxt (rewrite term))
    val ({elapsed, ...}, thm) =
      SMT_Config.with_time_limit ctxt SMT_Config.reconstruction_step_timeout replay
         (fn _ => Method.insert_tac ctxt assms THEN' Classical.fast_tac ctxt)
        handle Timeout.TIMEOUT _ => raise SMT_Failure.SMT SMT_Failure.Time_Out
    val stats' = Symtab.cons_list (Lethe_Proof.input_rule, Time.toNanoseconds elapsed) stats
  in
    (thm, stats')
  end

val cvc_assms_prefix = "__repeated_assms_" (*FUDGE*)
(*The index k is not unique for monomorphised theorems.*)
fun cvc_assms_name l k = cvc_assms_prefix ^ SMTLIB_Interface.assert_name_of_role_and_index SMT_Util.Axiom k ^ "_" ^ l
(*
fun add_correct_assms_deps ctxt rewrite_rules ll_defs assms steps =
  let
    fun add_correct_assms_deps (st as Lethe_Node.Lethe_Replay_Node {id, rule, step_args, context_assignments, prems,
        concl, subproof, args}) =
     (case try (snd o SMTLIB_Interface.role_and_index_of_assert_name) id of
       NONE => st
     | SOME _ =>
       (case List.find (fn (_, th') =>  CVC_Proof_Parse.cvc_matching_assms ctxt rewrite_rules ll_defs concl th') assms of
         NONE => st
       | SOME ((k,_), _) =>
       let
          val assms_prem = cvc_assms_name id k
       in
        Lethe_Node.mk_replay_node id rule  step_args context_assignments (assms_prem :: prems) concl
         subproof args
       end))
  in
    map add_correct_assms_deps steps
  end
*)
fun replay_step rewrite_rules all_assms ll_defs assumed inputs proof_prems
  (step as Lethe_Node.Lethe_Replay_Node {rule, ...}) state =
  if rule = Lethe_Proof.skolem_def
  then replay_definition_step rewrite_rules ll_defs assumed inputs proof_prems step state
  else replay_theorem_step rewrite_rules all_assms ll_defs assumed inputs proof_prems step state


fun replay outer_ctxt
    ({context = ctxt, typs, terms, rewrite_rules, assms, ll_defs, ...} : SMT_Translate.replay_data)
     output =
  let
    val _ = if not (SMT_Config.use_lethe_proof_from_cvc ctxt)
       then (raise SMT_Failure.SMT (SMT_Failure.Other_Failure ("reconstruction with CVC is experimental.\n" ^
         "You must activate it with [[smt_cvc_lethe = true]] and use cvc5 (not included as component) .")))
       else ()
    val rewrite_rules =
      filter_out (fn thm => Term.could_unify (Thm.prop_of @{thm verit_eq_true_simplify},
          Thm.prop_of thm))
        rewrite_rules
    val num_ll_defs = length ll_defs
    val index_of_id = Integer.add (~ num_ll_defs)
    val id_of_index = Integer.add num_ll_defs

    val start0 = Timing.start ()

    val (actual_steps, ctxt2) =
      Lethe_Proof.parse_replay typs terms output ctxt
    val parsing_time = Time.toNanoseconds (#elapsed (Timing.result start0))

    fun step_of_assume (j, (_, th)) =
      Lethe_Node.Lethe_Replay_Node {
        id = SMTLIB_Interface.assert_name_of_role_and_index SMT_Util.Axiom (id_of_index j),
        rule = Lethe_Proof.input_rule,
        step_args = [],
        context_assignments = [],
        prems = [],
        concl = Thm.prop_of th
          |> Raw_Simplifier.rewrite_term (Proof_Context.theory_of
               (empty_simpset ctxt addsimps rewrite_rules)) rewrite_rules [],
        subproof = ([], [], [], []),
        args = NONE}
       
    val used_assert_ids = fold add_used_asserts_in_step actual_steps []

    fun normalize_tac ctxt = let val thy = Proof_Context.theory_of (empty_simpset ctxt) in
      Raw_Simplifier.rewrite_term thy rewrite_rules [] end
    val used_assm_js =
      map_filter (fn id => let val i = index_of_id id in if i >= 0 then SOME (i, nth assms i)
          else NONE end)
        used_assert_ids

    val assm_steps = map step_of_assume used_assm_js
    fun extract (Lethe_Node.Lethe_Replay_Node {id, rule, concl, ...}) =
         (id, rule, concl, [])
    fun cond rule = rule = Lethe_Proof.input_rule
    val add_asssert = SMT_Replay.add_asserted Symtab.update Symtab.empty extract cond

    val ((_, _), (ctxt3, assumed)) =
      add_asssert outer_ctxt rewrite_rules (map (apfst fst) assms)
        (map_filter (remove_rewrite_rules_from_rules num_ll_defs) assm_steps) ctxt2

    val used_rew_js =
      map_filter (fn id => let val i = index_of_id id in if i < 0
          then SOME (id, normalize_tac ctxt (nth ll_defs id)) else NONE end)
        used_assert_ids

    val (assumed, stats) = fold (fn ((id, thm)) => fn (assumed, stats) =>
      let
        val (thm, stats) = replay_assumed (map snd assms) ll_defs rewrite_rules stats ctxt thm
        val name = SMTLIB_Interface.assert_name_of_role_and_index SMT_Util.Axiom id
      in
        (Symtab.update (name, ([], thm)) assumed, stats)
      end)
      used_rew_js (assumed, Symtab.cons_list ("parsing", parsing_time) Symtab.empty)
    (*val _ = @{print}("assumed",assumed)*)

(*
    val actual_steps = actual_steps
      |> add_correct_assms_deps ctxt rewrite_rules ll_defs assms
*)

    val ctxt4 =
      ctxt3
(*
      |> put_simpset (empty_simpset ctxt3 [])*)
      |> Config.put SAT.solver (Config.get ctxt3 SMT_Config.sat_solver)
    val len = Lethe_Proof.number_of_steps actual_steps
    fun steps_with_depth _ [] = []
      | steps_with_depth i (p :: ps) = (i +  Lethe_Proof.number_of_steps [p], p) ::
          steps_with_depth (i +  Lethe_Proof.number_of_steps [p]) ps
    val actual_steps = steps_with_depth 0 actual_steps
    val start = Timing.start ()
    val print_runtime_statistics = SMT_Replay.intermediate_statistics ctxt4 start len
    fun blockwise f (i, x) (next, y) =
      (if i > next then print_runtime_statistics i else ();
       (if i > next then i + 10 else next, f x y))

    val global_transformation : term Termtab.table = Termtab.empty

    val (_, (proofs, stats, ctxt5, _, _)) =
      fold (blockwise (replay_step rewrite_rules (map snd assms) ll_defs assumed [] [])) actual_steps
        (1, (assumed, stats, ctxt4, [], global_transformation))

    val total = Time.toMilliseconds (#elapsed (Timing.result start))

    val (_, (_, Lethe_Node.Lethe_Replay_Node {id, ...})) = split_last actual_steps

    val _ = print_runtime_statistics len

    val thm_with_defs = Symtab.lookup proofs id |> the |> snd
      |> singleton (Proof_Context.export ctxt5 outer_ctxt)

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
