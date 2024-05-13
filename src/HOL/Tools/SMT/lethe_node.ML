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
    proof_ctxt: term list, (*TODO: Delete?*)
    concl: term}

  val mk_step : string -> string -> string list -> term list -> term -> lethe_step

  (* Pass information added during pre-processing to reconstruction  *)
  datatype tactic_args =
    Declarations of (string * term) list | (*only used for sko_definitions *)
    Insts of term Symtab.table | (*only used for forall_inst*)
    Sko_Def_Prems of term list (*only used for sko_forall and sko_exists*)

  datatype lethe_replay_node = Lethe_Replay_Node of {
    id: string,
    rule: string,
    step_args: term list,
    context_assignments: term list,
    prems: string list,
    concl: term,
    subproof: (string * typ) list * term list * term list * lethe_replay_node list,
    args: tactic_args option}

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
    declarations: (string * SMTLIB.tree) list, (*Fuer skolem_def stehen statt in der conclusion die in der declarations drin, koennte man auch in concl machen*)
    subproof: raw_lethe_node list}
 (* | Raw_Definition_Node of {
    concl: SMTLIB.tree
  }*)

  val mk_raw_node : string ->
      string ->
        SMTLIB.tree list ->
          SMTLIB.tree list ->
            string list ->
              (string * SMTLIB.tree) list ->
                SMTLIB.tree ->
                  raw_lethe_node list -> raw_lethe_node


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
    declarations: (string * SMTLIB.tree) list,
    subproof: raw_lethe_node list}

fun mk_raw_node id rule step_args context_ass  prems declarations concl subproof =
  Raw_Lethe_Node {id = id, rule = rule, step_args = step_args,
    context_assignments = context_ass, prems = prems, declarations = declarations,
    concl = concl, subproof = subproof}


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
  Sko_Def_Prems of term list (*only used for sko_forall and sko_exists*)

datatype lethe_replay_node = Lethe_Replay_Node of {
  id: string,
  rule: string,
  step_args: term list,
  context_assignments: term list,
  prems: string list,
  concl: term,
  subproof: (string * typ) list * term list * term list * lethe_replay_node list,
  args: tactic_args option}

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