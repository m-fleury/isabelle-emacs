(*  Title:      HOL/Tools/SMT/verit_strategies.ML
    Author:     Mathias Fleury, ENS Rennes, MPI, JKU, Freiburg University

VeriT proofs: parsing and abstract syntax tree.

TODO: Rename
*)

signature VERIT_STRATEGIES =
sig
  (*Strategy related*)
  val smt_solver_strategy : string Config.T
  val smt_solver_current_strategy : string -> Context.generic -> string list
  val veriT_current_strategy : Context.generic -> string list
  val cvc5_current_strategy : Context.generic -> string list
  val all_smt_solver_stgies: string -> Context.generic -> string list;
  val all_veriT_stgies: Context.generic -> string list;
  val all_cvc5_stgies: Context.generic -> string list;

  val select_smt_solver_stgy: string -> string -> Context.generic -> Context.generic;
  val select_veriT_stgy: string -> Context.generic -> Context.generic;
  val valid_smt_solver_stgy: string -> string -> Context.generic -> bool;
  val smt_solver_add_stgy: (string * string) * string list -> Context.generic -> Context.generic
  val smt_solver_rm_stgy: string -> string -> Context.generic -> Context.generic

  (*Global tactic*)
  val verit_tac: Proof.context -> thm list -> int -> tactic
  val verit_tac_stgy: string -> Proof.context -> thm list -> int -> tactic
  val cvc5_tac: Proof.context -> thm list -> int -> tactic
  val cvc5_tac_stgy: string -> Proof.context -> thm list -> int -> tactic
end;

structure Verit_Strategies: VERIT_STRATEGIES =
struct

open SMTLIB_Proof

val verit_strategy_default_name = "default"; (*FUDGE*)
val verit_strategy_del_insts_name = "del_insts"; (*FUDGE*)
val verit_strategy_rm_insts_name = "ccfv_SIG"; (*FUDGE*)
val verit_strategy_ccfv_insts_name = "ccfv_threshold"; (*FUDGE*)
val verit_strategy_best_name = "best"; (*FUDGE*)

val verit_strategy_best = ["--index-sorts", "--index-fresh-sorts", "--triggers-new",
  "--triggers-sel-rm-specific"];
val verit_strategy_del_insts = ["--index-sorts", "--index-fresh-sorts", "--ccfv-breadth",
  "--inst-deletion", "--index-SAT-triggers", "--inst-deletion-loops", "--inst-deletion-track-vars",
  "--inst-deletion", "--index-SAT-triggers"];
val verit_strategy_rm_insts = ["--index-SIG", "--triggers-new", "--triggers-sel-rm-specific"];
val verit_strategy_ccfv_insts = ["--index-sorts", "--index-fresh-sorts", "--triggers-new",
  "--triggers-sel-rm-specific", "--triggers-restrict-combine", "--inst-deletion",
  "--index-SAT-triggers", "--inst-deletion-loops", "--inst-deletion-track-vars", "--inst-deletion",
  "--index-SAT-triggers", "--inst-sorts-threshold=100000", "--ematch-exp=10000000",
  "--ccfv-index=100000", "--ccfv-index-full=1000"]

(*these are the strategies used by default for sledgehammer. We did not try to find good one
and they mostly are useful to improve our mirabelle tests. The main motivation was that we observed
several proofs where cvc5 would find a proof for sledgehammer in one of the slice but none in the
smt tactic.

It is not clear if we should keep that or not.

Die die SMT methode benutzt
*)
val cvc5_stgy_default_name = "best"
val cvc5_stgy_default_insts = []
val cvc5_stgy_trigger_last_name = "trigger_last"
val cvc5_stgy_trigger_last = ["--full-saturate-quant", "--inst-when=full-last-call", "--inst-no-entail", "--term-db-mode=relevant", "--multi-trigger-linear"]
val cvc5_stgy_quant_name = "quant_saturate"
val cvc5_stgy_quant = ["--decision=internal", "--simplification=none", "--full-saturate-quant"]
val cvc5_stgy_trigger_max_name = "trigger_max"
val cvc5_stgy_trigger_max = ["--trigger-sel=max", "--full-saturate-quant"]
val cvc5_stgy_trigger_relevance_name = "trigger_relev"
val cvc5_stgy_trigger_relevance = ["--relevant-triggers", "--full-saturate-quant"]
val cvc5_stgy_term_relevance_name = "term_relev"
val cvc5_stgy_term_relevance = ["--term-db-mode=relevant", "--full-saturate-quant"]
val cvc5_stgy_no_ematch_name ="noematch"
val cvc5_stgy_no_ematch = ["--no-e-matching", "--full-saturate-quant"]
val cvc5_stgy_fmf_name = "fmf"
val cvc5_stgy_fmf_insts = ["--finite-model-find", "--decision=internal"]

val verit_strategy_default = [];

type verit_strategy = {default_strategy: string, strategies: ((string * string) * string list) list}
fun mk_verit_strategy default_strategy strategies : verit_strategy = {default_strategy=default_strategy,strategies=strategies}

val verit_name = "verit"
val cvc5_name = "cvc5_proof"
val empty_data = mk_verit_strategy verit_strategy_best_name
  [((verit_name, verit_strategy_default_name), verit_strategy_default),
   ((verit_name, verit_strategy_del_insts_name), verit_strategy_del_insts),
   ((verit_name, verit_strategy_rm_insts_name), verit_strategy_rm_insts),
   ((verit_name, verit_strategy_ccfv_insts_name), verit_strategy_ccfv_insts),
   ((verit_name, verit_strategy_best_name), verit_strategy_best),

   ((cvc5_name, cvc5_stgy_default_name), cvc5_stgy_default_insts),
   ((cvc5_name, cvc5_stgy_trigger_last_name), cvc5_stgy_trigger_last),
   ((cvc5_name, cvc5_stgy_quant_name),cvc5_stgy_quant),
   ((cvc5_name, cvc5_stgy_trigger_max_name), cvc5_stgy_trigger_max),
   ((cvc5_name, cvc5_stgy_trigger_relevance_name), cvc5_stgy_trigger_relevance),
   ((cvc5_name, cvc5_stgy_term_relevance_name), cvc5_stgy_term_relevance),
   ((cvc5_name, cvc5_stgy_no_ematch_name), cvc5_stgy_no_ematch),
   ((cvc5_name, cvc5_stgy_fmf_name), cvc5_stgy_fmf_insts)
]

fun merge_data ({strategies=strategies1,...}:verit_strategy,
    {default_strategy,strategies=strategies2}:verit_strategy) : verit_strategy =
  mk_verit_strategy default_strategy (AList.merge (op =) (op =) (strategies1, strategies2))

structure Data = Generic_Data
(
  type T = verit_strategy
  val empty = empty_data
  val merge = merge_data
)

fun smt_solver_current_strategy solver ctxt =
  let
    val {default_strategy,strategies} = (Data.get ctxt)
  in
    AList.lookup (op=) strategies (solver, default_strategy)
    |> the
  end

val smt_solver_strategy = Attrib.setup_config_string \<^binding>\<open>smt_verit_strategy\<close> (K verit_strategy_best_name);

fun valid_smt_solver_stgy solver stgy context =
  let
    val {strategies,...} = Data.get context
  in
    AList.defined (op =) strategies (solver, stgy)
  end

fun select_smt_solver_stgy solver stgy context =
  let
    val {strategies,...} = Data.get context
    val upd = Data.map (K (mk_verit_strategy stgy strategies))
  in
    if not (AList.defined (op =) strategies (solver, stgy)) then
      error ("Trying to select unknown " ^ quote solver ^ " strategy: " ^ quote stgy)
    else upd context
  end

val select_veriT_stgy = select_smt_solver_stgy verit_name
val select_cvc5_stgy = select_smt_solver_stgy cvc5_name

fun smt_solver_add_stgy stgy context =
  let
    val {default_strategy,strategies} = Data.get context
  in
    Data.map
      (K (mk_verit_strategy default_strategy (AList.update (op =) stgy strategies)))
      context
  end

fun smt_solver_rm_stgy solver stgy context =
  let
    val {default_strategy,strategies} = Data.get context
  in
    Data.map
      (K (mk_verit_strategy default_strategy (AList.delete (op =) (solver, stgy) strategies)))
      context
  end

fun all_smt_solver_stgies solver context =
  let
    val {strategies,...} = Data.get context
   in
    strategies
    |> map_filter (fn ((solver', name), _) => if solver=solver' then SOME name else NONE)
  end
val all_veriT_stgies = all_smt_solver_stgies verit_name
val all_cvc5_stgies = all_smt_solver_stgies cvc5_name

val veriT_current_strategy = smt_solver_current_strategy verit_name
val cvc5_current_strategy = smt_solver_current_strategy cvc5_name
val select_verit = SMT_Config.select_solver verit_name
fun verit_tac ctxt = SMT_Solver.smt_tac (Context.proof_map select_verit ctxt)
fun verit_tac_stgy stgy ctxt = verit_tac (Context.proof_of (select_veriT_stgy stgy (Context.Proof ctxt)))

val select_cvc5 = SMT_Config.select_solver cvc5_name
fun cvc5_tac ctxt = SMT_Solver.smt_tac (Context.proof_map select_cvc5 ctxt)
fun cvc5_tac_stgy stgy ctxt = cvc5_tac (Context.proof_of (select_cvc5_stgy stgy (Context.Proof ctxt)))

end;
