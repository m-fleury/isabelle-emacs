(*  Title:      HOL/Tools/SMT/alethe/alethe_proof_parse.ML
    Author:     Mathias Fleury, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Alethe proof parsing.
*)

signature ALETHE_PROOF_PARSE =
sig
  val parse_proof: SMT_Translate.replay_data ->
    ((string * ATP_Problem_Generate.stature) * thm) list -> term list -> term -> string list ->
    SMT_Solver.parsed_proof
end;

structure Alethe_Proof_Parse: ALETHE_PROOF_PARSE =
struct

fun parse_proof
    ({ctxt, typs, terms, ll_defs, rewrite_rules, assms} : SMT_Translate.replay_data)
    xfacts prems concl output =
  let
    val num_ll_defs = length ll_defs

    val id_of_index = Integer.add num_ll_defs
    val index_of_id = Integer.add (~ num_ll_defs)

    fun step_of_assume j ((_, role), th) =
      Alethe_Node.Alethe_Step
        {id = SMTLIB_Interface.assert_name_of_role_and_index role (id_of_index j),
        rule = Alethe_Proof.input_rule, prems = [], concl = Thm.prop_of th,
        prop_skeleton = @{term "True"}}

    val (actual_steps, _) = Alethe_Proof.parse typs terms output ctxt
    val used_assert_ids =
        actual_steps
        |> map_filter (fn (Alethe_Node.Alethe_Step { id, ...}) =>
           try (snd o SMTLIB_Interface.role_and_index_of_assert_name) id)
    val used_assm_js =
      map_filter (fn id => let val i = index_of_id id in if i >= 0 then SOME i else NONE end)
        used_assert_ids
    val used_assms = map (nth assms) used_assm_js
    val assm_steps = map2 step_of_assume used_assm_js used_assms
    val steps = assm_steps @ actual_steps

    val conjecture_i = 0
    val prems_i = conjecture_i + 1
    val num_prems = length prems
    val facts_i = prems_i + num_prems
    val num_facts = length xfacts
    val helpers_i = facts_i + num_facts

    val conjecture_id = id_of_index conjecture_i
    val prem_ids = map id_of_index (prems_i upto prems_i + num_prems - 1)
    val fact_ids' =
      map_filter (fn j =>
        let val ((i, _), _) = nth assms j in
          try (apsnd (nth xfacts)) (id_of_index j, i - facts_i)
        end) used_assm_js
    val helper_ids' =
      map_filter (fn ((i, _), thm) => if i >= helpers_i then SOME (i, thm) else NONE) used_assms

    val fact_helper_ts =
      map (fn (_, th) => (ATP_Util.short_thm_name ctxt th, Thm.prop_of th)) helper_ids' @
      map (fn (_, ((s, _), th)) => (s, Thm.prop_of th)) fact_ids'
    val fact_helper_ids' =
      map (apsnd (ATP_Util.short_thm_name ctxt)) helper_ids' @ map (apsnd (fst o fst)) fact_ids'
  in
    {outcome = NONE, fact_ids = SOME fact_ids',
     atp_proof = fn () => Alethe_Isar.atp_proof_of_veriT_proof ctxt ll_defs rewrite_rules prems concl
       fact_helper_ts prem_ids conjecture_id fact_helper_ids' steps}
  end

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
)
end;
