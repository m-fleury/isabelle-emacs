(*  Title:      HOL/Tools/SMT/lethe_proof.ML
    Author:     Mathias Fleury, University of Freiburg
    Author:     Hanna Lachnitt, Stanford University

Parsing smt problems into lethe nodes
*)

open Lethe_Node

signature LETHE_SMT_PROBLEM =
sig
  exception LETHE_PROBLEM_PARSE of string

  val parse_raw_problem_steps: SMTLIB.tree list -> SMTLIB_Proof.name_bindings ->
     int -> raw_lethe_node list * SMTLIB.tree list * SMTLIB_Proof.name_bindings
end;

structure Lethe_SMT_Problem: LETHE_SMT_PROBLEM =
struct

exception LETHE_PROBLEM_PARSE of string

open SMTLIB_Proof
open Lethe_Node

datatype command_kind = ASSERT | FUN_DEF | FUN_DECL

local

  fun parse_fun_def (SMTLIB.S [SMTLIB.Sym "define-fun", SMTLIB.Sym id,  _, typ,
           SMTLIB.S (SMTLIB.Sym "!" :: t :: [SMTLIB.Key _, SMTLIB.Sym name])]) cx =
         (*replace the name binding by the constant instead of the full term in order to reduce
           the size of the generated terms and therefore the reconstruction time*)
         let val (l, cx) = (fst oo SMTLIB_Proof.extract_and_update_name_bindings) t cx
            |> apsnd (SMTLIB_Proof.update_name_binding (name, SMTLIB.Sym id))
         in
           (*(mk_raw_node (id ^ lethe_def) lethe_def (SMTLIB.S [SMTLIB.Sym id, typ, l]) [] []
              (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym id, l]) [], cx)*)
            (mk_raw_node (id ^ Lethe_Proof.lethe_def) Lethe_Proof.lethe_def [(SMTLIB.S [SMTLIB.Sym id, typ, l])] [] [] []
              (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym id, l]) [], cx)
         end
      | parse_fun_def (SMTLIB.S [SMTLIB.Sym "define-fun", SMTLIB.Sym id,  _, typ, SMTLIB.S l]) cx =
         let val (l, cx) = (fst oo SMTLIB_Proof.extract_and_update_name_bindings) (SMTLIB.S l) cx
         in
           (mk_raw_node (id ^ Lethe_Proof.lethe_def) Lethe_Proof.lethe_def [(SMTLIB.S [SMTLIB.Sym id, typ, l])] [] [] []
              (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym id, l]) [], cx)
         end
      | parse_fun_def t _ = raise Fail ("unrecognized Lethe proof " ^ \<^make_string> t)


in

fun parse_raw_problem_steps (commands : SMTLIB.tree list) (cx : name_bindings) (assms_nbr : int):
     (raw_lethe_node list * SMTLIB.tree list * name_bindings) =
  let
    fun command_kind "assert" = ASSERT
      | command_kind "define-fun" = FUN_DEF
      | command_kind "declare-fun" = FUN_DECL
      | command_kind kind = raise LETHE_PROBLEM_PARSE ("kind of command unrec: " ^ @{make_string} kind)
    
    fun split_commands [] = NONE
      | split_commands ((step as SMTLIB.S (SMTLIB.Sym kind :: _)) :: remaining_steps) =
          SOME (command_kind kind, step, remaining_steps)
      | split_commands steps = raise LETHE_PROBLEM_PARSE ("malformed command: " ^ @{make_string} steps)

    fun parse_fun_decl (SMTLIB.S [SMTLIB.Sym "declare-fun", SMTLIB.Sym id, typ, def]) cx =
         (*replace the name binding by the constant instead of the full term in order to reduce
           the size of the generated terms and therefore the reconstruction time*)
         let val (l, cx) = (fst oo SMTLIB_Proof.extract_and_update_name_bindings) def cx
         in
           (mk_raw_node (id ^ Lethe_Proof.lethe_def) Lethe_Proof.lethe_def [(SMTLIB.S [SMTLIB.Sym id, typ, l])] [] [] []
              (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym id, def]) [], cx)
         end

  in
    case split_commands commands of
     SOME (ASSERT, p, l) => 
          let
            val (id, term) = (case p of
                SMTLIB.S [SMTLIB.Sym "assert", SMTLIB.S [SMTLIB.Sym "!", term, SMTLIB.Key "named", SMTLIB.Sym id]] => (id, term)
              | SMTLIB.S [SMTLIB.Sym "assert", term] => (Int.toString assms_nbr, term))
            val ((t, cx), _) = SMTLIB_Proof.extract_and_update_name_bindings term cx
            val s = mk_raw_node id Lethe_Proof.input_rule [] [] [] [] t []
            val (rp, rl, cx) = parse_raw_problem_steps l cx (assms_nbr + 1)
       in (s :: rp, rl, cx) end
      | SOME (FUN_DEF, p, l) =>
          let
            val (s, cx) = parse_fun_def p cx
            val (rp, rl, cx) = parse_raw_problem_steps l cx assms_nbr
          in (s :: rp, rl, cx) end
      | SOME (FUN_DECL, p, l) =>
          let
            val (s, cx) = parse_fun_decl p cx
            val (rp, rl, cx) = parse_raw_problem_steps l cx assms_nbr
          in (s :: rp, rl, cx) end
      |  NONE => ([],[], cx)
      | x => let val _ = @{print}("x",x) in raise ERROR "" end
    (*  | SOME (FUN_DEF, p, l) => (parse_fun_def p cx,assms_nbr)
      | SOME (FUN_DECL, p, l) => (parse_fun_decl p cx,assms_nbr)
*)

  end
end
end;