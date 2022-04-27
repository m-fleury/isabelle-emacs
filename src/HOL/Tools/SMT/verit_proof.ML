(*  Title:      HOL/Tools/SMT/verit_proof.ML
    Author:     Mathias Fleury, JKU

Lethe proofs: parsing and abstract syntax tree.
*)

signature VERIT_PROOF =
sig

  (*Strategy related*)
  val verit_strategy : string Config.T
  val verit_current_strategy : Context.generic -> string list
  val all_verit_stgies: Context.generic -> string list;

  val select_verit_stgy: string -> Context.generic -> Context.generic;
  val valid_verit_stgy: string -> Context.generic -> bool;
  val verit_add_stgy: string * string list -> Context.generic -> Context.generic
  val verit_rm_stgy: string -> Context.generic -> Context.generic

  (*Global tactic*)
  val verit_tac: Proof.context -> thm list -> int -> tactic
  val verit_tac_stgy: string -> Proof.context -> thm list -> int -> tactic
  val cvc_tac: Proof.context -> thm list -> int -> tactic
end;


structure Verit_Proof: VERIT_PROOF =
struct

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

val verit_strategy_default = [];

type verit_strategy = {default_strategy: string, strategies: (string * string list) list}
fun mk_verit_strategy default_strategy strategies : verit_strategy = {default_strategy=default_strategy,strategies=strategies}

val empty_data = mk_verit_strategy verit_strategy_best_name
  [(verit_strategy_default_name, verit_strategy_default),
   (verit_strategy_del_insts_name, verit_strategy_del_insts),
   (verit_strategy_rm_insts_name, verit_strategy_rm_insts),
   (verit_strategy_ccfv_insts_name, verit_strategy_ccfv_insts),
   (verit_strategy_best_name, verit_strategy_best)]

fun merge_data ({strategies=strategies1,...}:verit_strategy,
    {default_strategy,strategies=strategies2}:verit_strategy) : verit_strategy =
  mk_verit_strategy default_strategy (AList.merge (op =) (op =) (strategies1, strategies2))

structure Data = Generic_Data
(
  type T = verit_strategy
  val empty = empty_data
  val merge = merge_data
)

fun verit_current_strategy ctxt =
  let
    val {default_strategy,strategies} = (Data.get ctxt)
  in
    AList.lookup (op=) strategies default_strategy
   |> the
  end

val verit_strategy = Attrib.setup_config_string \<^binding>\<open>smt_verit_strategy\<close> (K verit_strategy_best_name);

fun valid_verit_stgy stgy context =
  let
    val {strategies,...} = Data.get context
  in
    AList.defined (op =) strategies stgy
  end

fun select_verit_stgy stgy context =
  let
    val {strategies,...} = Data.get context
    val upd = Data.map (K (mk_verit_strategy stgy strategies))
  in
    if not (AList.defined (op =) strategies stgy) then
      error ("Trying to select unknown verit strategy: " ^ quote stgy)
    else upd context
  end

fun verit_add_stgy stgy context =
  let
    val {default_strategy,strategies} = Data.get context
  in
    Data.map
      (K (mk_verit_strategy default_strategy (AList.update (op =) stgy strategies)))
      context
  end

fun verit_rm_stgy stgy context =
  let
    val {default_strategy,strategies} = Data.get context
  in
    Data.map
      (K (mk_verit_strategy default_strategy (AList.delete (op =) stgy strategies)))
      context
  end

fun all_verit_stgies context =
  let
    val {strategies,...} = Data.get context
   in
    map fst strategies
  end

val select_verit = SMT_Config.select_solver "verit"
fun verit_tac ctxt = SMT_Solver.smt_tac (Config.put SMT_Config.native_bv false ((Context.proof_map select_verit ctxt)))
fun verit_tac_stgy stgy ctxt = verit_tac (Context.proof_of (select_verit_stgy stgy (Context.Proof ctxt)))
fun cvc_tac ctxt = SMT_Solver.smt_tac (Context.proof_map (SMT_Config.select_solver "cvc4") ctxt)


end;
