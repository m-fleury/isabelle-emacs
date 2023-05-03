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

fun parse_assert cs ({context,typs,terms,ll_defs,rewrite_rules,assms}: SMT_Translate.replay_data, assms_nbr)
 =
let
  val smtlib_lines_without_qm = (*This also removes pattern usually but I deleted it here for now*)
    implode cs
    |> single
    |> SMTLIB.parse
  val ([step], _, cx) =  (Lethe_Proof.parse_raw_proof_steps NONE [smtlib_lines_without_qm]
   SMTLIB_Proof.empty_name_binding 0)

  val (Lethe_Proof.Raw_Lethe_Node {concl, ...} : Lethe_Proof.raw_lethe_node) = step
  (*val _ = @{print}("concl", concl)*)


  val cx = (SMTLIB_Proof.empty_context context typs terms)
  val t2 = SMTLIB_Proof.term_of concl cx |> fst
  (*val _ = @{print}("t2",t2)*)


  val ([all_proof_prems'], sub_ctxt2) = Assumption.add_assumes (map (Thm.apply \<^cterm>\<open>Trueprop\<close> o Thm.cterm_of context) [t2]) context
  (*val _ = @{print}("all_proof_prems'",all_proof_prems')*)
 
 val assm = ((assms_nbr,SMT_Util.Axiom),all_proof_prems'):((int * SMT_Util.role) * thm)

in
 ({context = sub_ctxt2,typs = typs,terms = terms,ll_defs = ll_defs,rewrite_rules = rewrite_rules,
assms = assm :: assms}, assms_nbr+1)
end

(*Taken from stuff*)
fun add_components_of_typ (Type (s, Ts)) =
    cons (Long_Name.base_name s) #> fold_rev add_components_of_typ Ts
  | add_components_of_typ (TFree (s, _)) = cons (perhaps (try (unprefix "'")) s)
  | add_components_of_typ _ = I;

fun suggested_name_of_typ T = space_implode "_" (add_components_of_typ T []);

fun suggested_name_of_term (Const (s, _)) = Long_Name.base_name s
  | suggested_name_of_term (Free (s, _)) = s
  | suggested_name_of_term _ = Name.uu

fun add_typ T proper (cx as (names, typs, terms)) =
  (case Typtab.lookup typs T of
    SOME (name, _) => (name, cx)
  | NONE =>
      let
        val sugg = Name.desymbolize (SOME true) (suggested_name_of_typ T) ^ "$"
        val (name, names') = Name.variant sugg names
        val typs' = Typtab.update (T, (name, proper)) typs
      in (name, (names', typs', terms)) end)
(**)
fun parse_sort (cs: string list) ({context,typs: typ Symtab.table,terms,ll_defs,rewrite_rules,assms}: SMT_Translate.replay_data, assms_nbr)
 =
let
    (*val _ = @{print} ("declaration", cs)*)
  val typ = (*This also removes pattern usually but I deleted it here for now*)
    [implode cs]
    |> map single
    |> map SMTLIB.parse
    |> (fn [SMTLIB.S [SMTLIB.Sym "declare-sort", SMTLIB.Sym typ, SMTLIB.Num 0]] => typ)
    (*|> @{print}*)
    val T = TFree (typ, ["HOL.type"])
    val context = Variable.declare_typ T context

   val typs = Symtab.update (typ, T) typs
(*|> @{print}*)
in
 ({context = context,typs = typs,terms = terms,ll_defs = ll_defs,rewrite_rules = rewrite_rules,assms = assms}, assms_nbr)
end


fun dest_name (SMTLIB.Sym name) = name
  | dest_name t = raise SMTLIB_Proof.SMTLIB_PARSE ("bad name", t)

fun dest_seq (SMTLIB.S ts) = ts
  | dest_seq t = raise SMTLIB_Proof.SMTLIB_PARSE ("bad Z3 proof format", t)

val desymbolize = Name.desymbolize (SOME false) o perhaps (try (unprefix "?"))

fun parse_declare (cs: string list) ({context,typs,terms,ll_defs,rewrite_rules,assms}: SMT_Translate.replay_data, assms_nbr)
   =
  let
    (*val _ = @{print} ("declaration", cs)*)
    val (n, tys, ty) = (*This also removes pattern usually but I deleted it here for now*)
      [implode cs]
      |> map single
      |> map SMTLIB.parse
      |> (fn [SMTLIB.S [SMTLIB.Sym "declare-fun", n, tys, ty]] => (n, tys, ty))
    
     val name = dest_name n
     val ctxt = SMTLIB_Proof.empty_context context typs terms
     val Ts = map (SMTLIB_Proof.type_of ctxt) (dest_seq tys)
     val T = SMTLIB_Proof.type_of ctxt ty

    val ([n'], ctxt') =  Variable.variant_fixes [name] context

    val t = Free (n', Ts ---> T)
    val terms = Symtab.update (name, t) terms
(*|>  @{print} *)
(*
     val Ts = map (SMTLIB_Proof.type_of context) (dest_seq tys)
     val T = type_of cx ty
*)
   (*     in parse' ts (declare_fun name (Ts ---> T) cx) end*)
   (* val _ = @{print} ("declaration", (n, tys, ty))*)
  in
    ({context = context, typs = typs,terms = terms,ll_defs = ll_defs,rewrite_rules = rewrite_rules,assms = assms}, assms_nbr)
  end


(*This obviously could be done better but since it is only temporary:*)
fun read ("("::"a"::"s"::"s"::"e"::"r"::"t"::" "::cs) replay_data = 
      parse_assert ("("::"a"::"s"::"s"::"e"::"r"::"t"::" "::cs) replay_data
  | read (cs as "("::"d"::"e"::"c"::"l"::"a"::"r"::"e"::"-"::"f"::"u"::"n"::" ":: _) replay_data = parse_declare cs replay_data
  | read (cs as "("::"d"::"e"::"c"::"l"::"a"::"r"::"e"::"-"::"s"::"o"::"r"::"t"::" ":: _) replay_data = parse_sort cs replay_data
  | read _ replay_data  = replay_data


(* overall parser *)
(*TODO: assertions and declarations can go over multiple lines. For now assume they don't*)
fun add_line line (l, replay_data) =
  let
    (*val _ = @{print}("current line to parse",line)*)
    val line_list = (raw_explode line)
  in
    if size line = 0 then (l + 1, replay_data) (*Skip empty lines*)
    else if hd line_list = ";" then (l + 1, replay_data) (*Skip comments*)
    else (l + 1, read (raw_explode line) replay_data)
  end


fun count_parenthesis n ("(" :: line)  = count_parenthesis (n+1) line
  | count_parenthesis n (")" :: line)  = count_parenthesis (n-1) line
  | count_parenthesis n (_ :: line)  = count_parenthesis (n) line
  | count_parenthesis n []  = n

(*TODO this is ugly and not very efficient and does not support
(assert ..) (assert ...)


but supports

(assert (or 
   a
   b))


*)
fun fix_lines acc _ [] = [acc]
  | fix_lines acc m (l :: lines) =
    let val n = count_parenthesis m (raw_explode l)
    in 
      if n = 0 then acc ^ l :: fix_lines "" 0 lines
      else fix_lines (acc ^ l) n (lines)
    end

fun parse lines ctxt
 = snd (fold add_line (fix_lines "" 0 lines) (1,
 ({context = ctxt, typs = Symtab.empty, terms = Symtab.empty, ll_defs = [], rewrite_rules = [], assms = []}: SMT_Translate.replay_data, 0)))
 (*= print (fst (Lethe_Proof.parse Symtab.empty Symtab.empty lines ctxt))*)



end