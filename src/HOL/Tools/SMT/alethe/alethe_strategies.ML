(*  Title:      HOL/Tools/SMT/alethe/alethe_strategies.ML
    Author:     Mathias Fleury, ENS Rennes, MPI, JKU, University of Freiburg
    Author:     Hanna Lachnitt, Stanford University

Alethe strategies: option portfolio to call solvers with

*)

signature ALETHE_STRATEGIES =
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

structure Alethe_Strategies: ALETHE_STRATEGIES =
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

(*TODO:
We obtained these strategies by asking cvc5 what strategies it would use in the SMT-COMP
for some Isabelle generated problems from the 17 provers paper using the options --portfolio-dry-run --use-portfolio.
This gave 25 strategies.
Running the strategy on a benchmark with the option --safe-mode=safe, we obtain the options that
have a low count of holes, leaving 17.
Then, using Mirabelle we extracted goals that could not be solved by internal proof methods
(i.e., timeout or call to the smt method) and evaluated the strategies. The focus is on having a
good portfolio, not several strategies that are fast on the same goals.

Note: we always use --enum-inst at the moment because otherwise cvc5 will answer unknown too often.
Note: --full-saturate-quant is an alias of --enum-inst, which the cvc5 devs prefer we use.
TODO: We will give them better names once we know which ones to use.

*)
val cvc5_stgy_default_name = "best"
val cvc5_stgy_default_insts = []
val cvc5_stgy_no_simp_name ="no_simp"
val cvc5_stgy_no_simp = ["--simplification=none"]
val cvc5_stgy_no_ematching_name ="no_ematching"
val cvc5_stgy_no_ematching = ["--no-e-matching"]
val cvc5_stgy_trigger_relevance_name = "trigger_relev"
val cvc5_stgy_trigger_relevance = ["--relevant-triggers"]
val cvc5_stgy_trigger_max_name = "trigger_max"
val cvc5_stgy_trigger_max = ["--trigger-sel=max"]
val cvc5_stgy_trigger_multi_name = "trigger_multi"
val cvc5_stgy_trigger_multi = ["--multi-trigger-when-single"]
val cvc5_stgy_trigger_cache_name = "trigger_cache"
val cvc5_stgy_trigger_cache = ["--multi-trigger-cache"]
val cvc5_stgy_trigger_linear_name = "trigger_linear"
val cvc5_stgy_trigger_linear = ["--no-multi-trigger-linear"]
val cvc5_stgy_pre_skolem_quant_name= "pre_skolem_quant"
val cvc5_stgy_pre_skolem_quant = ["--pre-skolem-quant=on"]
val cvc5_stgy_inst_when_full_name= "inst_when_full"
val cvc5_stgy_inst_when_full = ["--inst-when=full"]
val cvc5_stgy_dec_internal_enum_inst_sum_name ="dec_internal_enum_inst_sum"
val cvc5_stgy_dec_internal_enum_inst_sum = ["--decision=internal", "--enum-inst", "--enum-inst-sum"]
val cvc5_stgy_term_db_relevant_name= "term_db_relevant"
val cvc5_stgy_term_db_relevant = ["--term-db-mode=relevant"]
val cvc5_stgy_term_enum_inst_interleave_name= "interleave"
val cvc5_stgy_term_enum_inst_interleave = ["--enum-inst-interleave"]
val cvc5_stgy_term_prereg_lazy_name= "prereg_lazy"
val cvc5_stgy_term_prereg_lazy = ["--preregister-mode=lazy"]
val cvc5_stgy_term_fmf_name= "finite_mode_find"
val cvc5_stgy_term_fmf = ["--finite-model-find"]
val cvc5_stgy_term_fmf_dec_internal_name= "finite_mode_find_dec_internal"
val cvc5_stgy_term_dec_internal_fmf = ["--finite-model-find", "--decision=internal"]
val cvc5_stgy_mbqi_name= "mbqi"
val cvc5_stgy_mbqi = ["--mbqi"]


val cvc5_stgy_trigger_last_name = "trigger_last"
val cvc5_stgy_trigger_last = ["--full-saturate-quant", "--inst-when=full-last-call", "--inst-no-entail", "--term-db-mode=relevant", "--multi-trigger-linear"]
val cvc5_stgy_quant_name = "quant_saturate"
val cvc5_stgy_quant = ["--decision=internal", "--simplification=none", "--full-saturate-quant"]

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
   ((cvc5_name, cvc5_stgy_fmf_name), cvc5_stgy_fmf_insts),
   ((cvc5_name, cvc5_stgy_no_simp_name), cvc5_stgy_no_simp)
(*,
   ((cvc5_name, cvc5_stgy_no_ematching_name), cvc5_stgy_no_ematching),
   ((cvc5_name, cvc5_stgy_trigger_multi_name), cvc5_stgy_trigger_multi),
   ((cvc5_name, cvc5_stgy_trigger_cache_name), cvc5_stgy_trigger_cache),
   ((cvc5_name, cvc5_stgy_trigger_linear_name), cvc5_stgy_trigger_linear),
   ((cvc5_name, cvc5_stgy_pre_skolem_quant_name), cvc5_stgy_pre_skolem_quant),
   ((cvc5_name, cvc5_stgy_inst_when_full_name), cvc5_stgy_inst_when_full),
   ((cvc5_name, cvc5_stgy_dec_internal_enum_inst_sum_name), cvc5_stgy_dec_internal_enum_inst_sum),
   ((cvc5_name, cvc5_stgy_term_db_relevant_name), cvc5_stgy_term_db_relevant),
   ((cvc5_name, cvc5_stgy_term_enum_inst_interleave_name), cvc5_stgy_term_enum_inst_interleave),
   ((cvc5_name, cvc5_stgy_term_prereg_lazy_name), cvc5_stgy_term_prereg_lazy),
   ((cvc5_name, cvc5_stgy_term_fmf_name), cvc5_stgy_term_fmf),
   ((cvc5_name, cvc5_stgy_term_fmf_dec_internal_name), cvc5_stgy_term_dec_internal_fmf),
   ((cvc5_name, cvc5_stgy_mbqi_name), cvc5_stgy_mbqi)*)
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
