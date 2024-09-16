(*  Title:      HOL/Tools/SMT/lethe_node.ML
    Author:     Mathias Fleury, ENS Rennes
    Author:     Sascha Boehme, TU Muenchen
    Author:     Hanna Lachnitt, Stanford University

Lethe: abstract syntax tree utils.
*)

signature LETHE_NODE =
sig

  datatype lethe_step = Lethe_Step of {
    id: string,
    rule: string,
    prems: string list,
    proof_ctxt: term list, (*TODO: Delete? Should be empty?*)
    concl: term}

  val mk_step : string -> string -> string list -> term list -> term -> lethe_step

  (* Pass information added during pre-processing to reconstruction *)
  datatype tactic_args =
    Declarations of (string * term) list | (*only used for sko_definitions*)
    Insts of term Symtab.table | (*only used for forall_inst*)
    Sko_Def_Prems of string list * string list | (*only used for sko_forall and sko_exists*)
    Solver_Name of string | (*used for refl and cong*)
    Index of int (*used for and, not_or, and_pos and or_neg*)

  val transform_tactic_args : (term -> term) -> tactic_args option -> tactic_args option

  datatype lethe_replay_node = Lethe_Replay_Node of {
    id: string,
    rule: string,
    step_args: term list,
    context_assignments: term list,
    prems: string list,
    concl: term,
    subproof: (string * typ) list * term list * term list * lethe_replay_node list,
    args: tactic_args option}
  | Lethe_Definition_Node of {
    id: string,
    rule: string,
    skolem_name : string,
    skolem_term : term
  }


  val mk_replay_node: string -> string -> term list -> term list -> string list -> term ->
   (string * typ) list * term list * term list * lethe_replay_node list -> tactic_args option
   -> lethe_replay_node
        
  datatype raw_lethe_node = Raw_Lethe_Node of {
    id: string,
    rule: string,
    step_args: SMTLIB.tree list,
    context_assignments: SMTLIB.tree list,
    prems: string list,
    concl: SMTLIB.tree,
    subproof: raw_lethe_node list}
  | Raw_Definition_Node of {
    id: string,
    rule: string,
    skolem_name : string,
    skolem_term : SMTLIB.tree
  }

  val mk_raw_node : string ->
      string ->
        SMTLIB.tree list ->
          SMTLIB.tree list ->
            string list ->
                SMTLIB.tree ->
                  raw_lethe_node list -> raw_lethe_node

  val mk_raw_definition_node : string -> string -> string -> SMTLIB.tree -> raw_lethe_node

end;

structure Lethe_Node: LETHE_NODE =
struct

open SMTLIB_Proof

datatype raw_lethe_node = Raw_Lethe_Node of {
    id: string,
    rule: string,
    step_args: SMTLIB.tree list,
    context_assignments: SMTLIB.tree list,
    prems: string list,
    concl: SMTLIB.tree,
    subproof: raw_lethe_node list}
  | Raw_Definition_Node of {
    id: string,
    rule: string,
    skolem_name : string,
    skolem_term : SMTLIB.tree
  }

fun mk_raw_node id rule step_args context_ass prems concl subproof =
  Raw_Lethe_Node {id = id, rule = rule, step_args = step_args,
    context_assignments = context_ass, prems = prems,
    concl = concl, subproof = subproof}

fun mk_raw_definition_node id rule skolem_name skolem_term = Raw_Definition_Node {id=id, rule=rule, skolem_name=skolem_name, skolem_term=skolem_term}


  datatype lethe_step = Lethe_Step of {
    id: string,
    rule: string,
    prems: string list,
    proof_ctxt: term list, (*TODO: Delete?*)
    concl: term}

fun mk_node id rule prems proof_ctxt concl =
  Lethe_Step {id = id, rule = rule, prems = prems, proof_ctxt = proof_ctxt, concl = concl}

(* Sometimes we want to communicate additional information that is gained during parsing or
preprocessing to the reconstruction tactic. *)
datatype tactic_args =
  Declarations of (string * term) list | (*only used for sko_definitions *)
  Insts of term Symtab.table | (*only used for forall_inst*)
  Sko_Def_Prems of string list * string list | (*only used for sko_forall and sko_exists*)
  Solver_Name of string |  (*used for refl and cong*)
  Index of int (*used for and, not_or, and_pos and or_neg*)

fun transform_tactic_args _ NONE = NONE |
  transform_tactic_args f (SOME (Insts insts)) = SOME (Insts (Symtab.map (K f) insts)) |
  transform_tactic_args f (SOME (Declarations xs)) = SOME (Declarations xs) |
  transform_tactic_args f x = x

datatype lethe_replay_node = Lethe_Replay_Node of {
  id: string,
  rule: string,
  step_args: term list,
  context_assignments: term list,
  prems: string list,
  concl: term,
  subproof: (string * typ) list * term list * term list * lethe_replay_node list,
  args: tactic_args option} |
 Lethe_Definition_Node of {
    id: string,
    rule: string,
    skolem_name : string,
    skolem_term : term
  }

fun mk_replay_node id rule step_args context_ass prems concl subproof tactic_args =
  Lethe_Replay_Node {id = id, rule = rule, step_args = step_args,
    context_assignments = context_ass, prems = prems, concl = concl, subproof = subproof,
    args = tactic_args}

datatype lethe_step = Lethe_Step of {
  id: string,
  rule: string,
  prems: string list,
  proof_ctxt: term list,
  concl: term}

fun mk_step id rule prems proof_ctxt concl =
  Lethe_Step {id = id, rule = rule, prems = prems, proof_ctxt = proof_ctxt, concl = concl}


end;