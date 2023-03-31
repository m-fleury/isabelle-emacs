signature SMT_PARSE_PROBLEM =
sig
  val parse: string list -> Proof.context -> SMT_Translate.replay_data
end;

structure SMT_Parse_Problem =
struct

(*TODO: This file will eventually be integrated into other files (mainly lethe_proof (parse_raw_proof_steps) and smt_solver).
 It is only used for easier development*)

(* The define-fun functionality is already implemented in lethe-proof and should be reused*)

(* 
To declare a term and put it into the context:
  ||> fold Variable.declare_term (map Free fixes)
This is also used in verit_replay (replay_theorem_step)

It gives the term a new name that is why we also need to do: 

  val export_vars = concl_tranformation @
       (ListPair.zip (map Free fixes, map Free (ListPair.zip (names, map snd fixes))))

The same has to be done for assumptions:

 val (all_proof_prems', sub_ctxt2) = Assumption.add_assumes (map (Thm.cterm_of sub_ctxt) (assms @ input))
      sub_ctxt
*)

(*
Mathias Plan to implement functionality:

Traverse problem:
  - If you see declare-fun add to context and fill up replay-data (probably just put in declare-fun directly into terms and eventually add in typs)
  - If you see assert do the same

Afterwards you should be able to call the replay directly. 

You cannot make a theorem out of it, so use export_theorem

At the end you want to export the theorem from local to global context. For this use 

    val export_thm = singleton (Proof_Context.export sub_ctxt2 ctxt)

Because in the local context you have the assumptions but not in global one

Ich versuche diese Woche, sonst uebernimmt Mathias.

*)

(*"In apply_solver_and_replay" (line 266 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Tools/SMT/smt_solver.ML") 
("assms", [((0, Axiom), "\<not> True"  [.])]) (line 267 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Tools/SMT/smt_solver.ML") 
("terms", {}) (line 268 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Tools/SMT/smt_solver.ML") 
("typs", {}) (line 269 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Tools/SMT/smt_solver.ML") 
("rewrite_rules",
 ["SMT.fun_app (?y::?'a) \<equiv> ?y", "Let (?s::?'a) (?f::?'a \<Rightarrow> ?'b) \<equiv> ?f ?s",
  "(?P::bool) = True \<equiv> ?P"]) (line 270 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Tools/SMT/smt_solver.ML") 
("ll_defs", []*)

fun parse_assert cs ({context,typs,terms,ll_defs,rewrite_rules,assms}: SMT_Translate.replay_data)
 =
let
  val _ = @{print}("cs",implode cs)
  val smtlib_lines_without_qm = (*This also removes pattern usually but I deleted it here for now*)
    [implode cs]
    |> map single
    |> map SMTLIB.parse
  val _ = @{print}("smtlib_lines_without_qm",smtlib_lines_without_qm)

  (*If the assert is not named we can only work with a counter, if we were to need the id*)
  val SMTLIB.S [SMTLIB.Sym "assert", SMTLIB.S [SMTLIB.Sym "!", term, SMTLIB.Key "named", SMTLIB.Sym id]]
    = hd smtlib_lines_without_qm

  val ((t, name_binding), _) = SMTLIB_Proof.extract_and_update_name_bindings (term) (SMTLIB_Proof.empty_name_binding)
  val _ = @{print}("t",t)
  val cx = (SMTLIB_Proof.empty_context context Symtab.empty Symtab.empty)
  val t2 = SMTLIB_Proof.term_of t cx |> fst
  val context = SMTLIB_Proof.ctxt_of cx
  val _ = @{print}("t2",t2)


  val (all_proof_prems', sub_ctxt2) = Assumption.add_assumes (map (Thm.apply \<^cterm>\<open>Trueprop\<close> o Thm.cterm_of context) [@{term "\<not>True"}]) context
  val _ = @{print}("all_proof_prems'",all_proof_prems')

  val test = Thm.assume (Thm.apply \<^cterm>\<open>Trueprop\<close> (Thm.cterm_of context @{term "\<not>True"}))
  val _ = @{print}("test",test)
 (* assms should be:
  ("assms", [((0, Axiom), "\<not> True"  [.])]) (line 267 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Tools/SMT/smt_solver.ML") *)
    val export_thm = singleton (Proof_Context.export sub_ctxt2 context)
 
 val assms2 = ([((0,SMT_Util.Axiom),test)]:((int * SMT_Util.role) * thm) list)

val rewrite_rules2 =  [@{thm SMT.fun_app_def},@{thm HOL.Let_def},
  @{thm verit_eq_true_simplify}]

in
 {context = sub_ctxt2,typs = typs,terms = terms,ll_defs = ll_defs,rewrite_rules = rewrite_rules,assms = assms2}
end

(*This obviously could be done better but since it is only temporary:*)
fun read l ("("::"a"::"s"::"s"::"e"::"r"::"t"::" "::cs) replay_data = parse_assert ("("::"a"::"s"::"s"::"e"::"r"::"t"::" "::cs) replay_data |
    read l cs replay_data = replay_data
(* read l ("("::"d"::"e"::"c"::"l"::"a"::"r"::"e"::"-"::"f"::"u"::"n"::" "::cs) replay_data = parse_declare cs replay_data *)
(* read l ("("::"d"::"e"::"c"::"l"::"a"::"r"::"e"::"-"::"s"::"o"::"r"::"t"::" "::cs) replay_data = parse_declare cs replay_data *)



(* overall parser *)
(*TODO: assertions and declarations can go over multiple lines. For now assume they don't*)
fun add_line line (l, replay_data) =
  let
    val _ = @{print}("current line to parse",line)
    val line_list = (raw_explode line)
  in
    if size line = 0 then (l + 1, replay_data) (*Skip empty lines*)
    else if hd line_list = ";" then (l + 1, replay_data) (*Skip comments*)
    else (l + 1, read l (raw_explode line) replay_data)
  end

fun parse lines ctxt
 = snd (fold add_line lines (1,
 ({context = ctxt, typs = Symtab.empty, terms = Symtab.empty, ll_defs = [], rewrite_rules = [], assms = []}: SMT_Translate.replay_data)))
 (*= print (fst (Lethe_Proof.parse Symtab.empty Symtab.empty lines ctxt))*)



end