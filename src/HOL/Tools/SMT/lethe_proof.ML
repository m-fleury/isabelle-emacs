(*  Title:      HOL/Tools/SMT/lethe_proof.ML
    Author:     Mathias Fleury, ENS Rennes
    Author:     Sascha Boehme, TU Muenchen

Lethe proofs: parsing and abstract syntax tree.
*)

signature LETHE_PROOF =
sig
  (*proofs*)
  datatype lethe_step = Lethe_Step of {
    id: string,
    rule: string,
    prems: string list,
    proof_ctxt: term list,
    concl: term,
    fixes: string list}

  datatype lethe_replay_node = Lethe_Replay_Node of {
    id: string,
    rule: string,
    args: term list,
    prems: string list,
    proof_ctxt: term list,
    concl: term,
    bounds: (string * typ) list,
    declarations: (string * term) list,
    insts: term Symtab.table,
    subproof: (string * typ) list * term list * term list * lethe_replay_node list}

  val mk_replay_node: string -> string -> term list -> string list -> term list ->
     term -> (string * typ) list -> term Symtab.table -> (string * term) list ->
     (string * typ) list * term list * term list * lethe_replay_node list -> lethe_replay_node

datatype raw_lethe_node = Raw_Lethe_Node of {
  id: string,
  rule: string,
  args: SMTLIB.tree,
  prems: string list,
  concl: SMTLIB.tree,
  declarations: (string * SMTLIB.tree) list,
  subproof: raw_lethe_node list}
 val parse_raw_proof_steps: string option -> SMTLIB.tree list -> SMTLIB_Proof.name_bindings -> int ->
 raw_lethe_node list * SMTLIB.tree list * SMTLIB_Proof.name_bindings

  (*proof parser*)
  val parse: typ Symtab.table -> term Symtab.table -> string list ->
    Proof.context -> lethe_step list * Proof.context
  val parse_replay: typ Symtab.table -> term Symtab.table -> string list ->
    Proof.context -> lethe_replay_node list * Proof.context

  val step_prefix : string
  val input_rule: string
  val keep_app_symbols: string -> bool
  val keep_raw_lifting: string -> bool
  val normalized_input_rule: string
  val la_generic_rule : string
  val rewrite_rule : string
  val simp_arith_rule : string
  val lethe_deep_skolemize_rule : string
  val lethe_def : string
  val is_lethe_def : string -> bool
  val subproof_rule : string
  val local_input_rule : string
  val not_not_rule : string
  val contract_rule : string
  val ite_intro_rule : string
  val eq_congruent_rule : string
  val eq_congruent_pred_rule : string
  val skolemization_steps : string list
  val theory_resolution2_rule: string
  val equiv_pos2_rule: string
  val and_pos_rule: string
  val hole: string
  val th_resolution_rule: string

  val is_skolemization: string -> bool
  val is_skolemization_step: lethe_replay_node -> bool

  val number_of_steps: lethe_replay_node list -> int

end;

structure Lethe_Proof: LETHE_PROOF =
struct

open SMTLIB_Proof

datatype raw_lethe_node = Raw_Lethe_Node of {
  id: string,
  rule: string,
  args: SMTLIB.tree,
  prems: string list,
  concl: SMTLIB.tree,
  declarations: (string * SMTLIB.tree) list,
  subproof: raw_lethe_node list}

fun mk_raw_node id rule args prems declarations concl subproof =
  Raw_Lethe_Node {id = id, rule = rule, args = args, prems = prems, declarations = declarations,
    concl = concl, subproof = subproof}

datatype lethe_node = Lethe_Node of {
  id: string,
  rule: string,
  prems: string list,
  proof_ctxt: term list,
  concl: term}

fun mk_node id rule prems proof_ctxt concl =
  Lethe_Node {id = id, rule = rule, prems = prems, proof_ctxt = proof_ctxt, concl = concl}

datatype lethe_replay_node = Lethe_Replay_Node of { (*Hier wuerde ich was veraendern*)
  id: string,
  rule: string,
  args: term list,
  prems: string list,
  proof_ctxt: term list,
  concl: term,
  bounds: (string * typ) list,
  insts: term Symtab.table, (*nur fuer forall_inst gebraucht*)
  declarations: (string * term) list,
  subproof: (string * typ) list * term list * term list * lethe_replay_node list}

fun mk_replay_node id rule args prems proof_ctxt concl bounds insts declarations subproof =
  Lethe_Replay_Node {id = id, rule = rule, args = args, prems = prems, proof_ctxt = proof_ctxt,
    concl = concl, bounds = bounds, insts = insts, declarations = declarations,
    subproof = subproof}

datatype lethe_step = Lethe_Step of {
  id: string,
  rule: string,
  prems: string list,
  proof_ctxt: term list,
  concl: term,
  fixes: string list}

fun mk_step id rule prems proof_ctxt concl fixes =
  Lethe_Step {id = id, rule = rule, prems = prems, proof_ctxt = proof_ctxt, concl = concl,
    fixes = fixes}

val step_prefix = ".c"
val input_rule = "input"
val la_generic_rule = "la_generic"
val normalized_input_rule = "__normalized_input" (*arbitrary*)
val rewrite_rule = "__rewrite" (*arbitrary*)
val subproof_rule = "subproof"
val local_input_rule = "__local_input" (*arbitrary*)
val simp_arith_rule = "simp_arith"
val lethe_def = "__skolem_definition" (*arbitrary*)
val not_not_rule = "not_not"
val contract_rule = "contraction"
val eq_congruent_pred_rule = "eq_congruent_pred"
val eq_congruent_rule = "eq_congruent"
val ite_intro_rule = "ite_intro"
val default_skolem_rule = "sko_forall" (*arbitrary, but must be one of the skolems*)
val theory_resolution2_rule = "__theory_resolution2" (*arbitrary*)
val equiv_pos2_rule = "equiv_pos2"
val th_resolution_rule = "th_resolution"
val and_pos_rule = "and_pos"
val hole = "hole"

val is_lethe_def = String.isSuffix lethe_def
val skolemization_steps = ["sko_forall", "sko_ex"]
val is_skolemization = member (op =) skolemization_steps
val keep_app_symbols = member (op =) [eq_congruent_pred_rule, eq_congruent_rule, ite_intro_rule, and_pos_rule]
val keep_raw_lifting = member (op =) [eq_congruent_pred_rule, eq_congruent_rule, ite_intro_rule, and_pos_rule]
val is_SH_trivial = member (op =) [not_not_rule, contract_rule]

fun is_skolemization_step (Lethe_Replay_Node {id, ...}) = is_skolemization id

(* Even the lethe developers do not know if the following rule can still appear in proofs: *)
val lethe_deep_skolemize_rule = "deep_skolemize"

fun number_of_steps [] = 0
  | number_of_steps ((Lethe_Replay_Node {subproof = (_, _, _, subproof), ...}) :: pf) =
      1 + number_of_steps subproof + number_of_steps pf

(* proof parser *)

fun node_of p cx =
  ([], cx)
  ||>> `(with_fresh_names (term_of p))
  |>> snd

fun synctactic_var_subst old_name new_name (u $ v) =
    (synctactic_var_subst old_name new_name u $ synctactic_var_subst old_name new_name v)
  | synctactic_var_subst old_name new_name (Abs (v, T, u)) =
    Abs (if String.isPrefix old_name v then new_name else v, T,
      synctactic_var_subst old_name new_name u)
  | synctactic_var_subst old_name new_name (Free (v, T)) =
     if String.isPrefix old_name v then Free (new_name, T) else Free (v, T)
  | synctactic_var_subst _ _ t = t

fun synctatic_rew_in_lhs_subst old_name new_name (Const(\<^const_name>\<open>HOL.eq\<close>, T) $ t1 $ t2) =
     Const(\<^const_name>\<open>HOL.eq\<close>, T) $ synctactic_var_subst old_name new_name t1 $ synctactic_var_subst old_name new_name t2 (*TODO: Change back just want to see what happens*)
  | synctatic_rew_in_lhs_subst old_name new_name (Const(\<^const_name>\<open>Trueprop\<close>, T) $ t1) =
     Const(\<^const_name>\<open>Trueprop\<close>, T) $ (synctatic_rew_in_lhs_subst old_name new_name t1)
  | synctatic_rew_in_lhs_subst _ _ t = t

fun add_bound_variables_to_ctxt cx =
  fold (update_binding o
    (fn (s, SOME typ) => (s, Term (Free (s, type_of cx typ)))))

val add_bound_variables_to_ctxt2 =
  fold (update_binding o
    (fn (s, typ) => (s, Term (Free (s, typ)))))

local

(*
New? syntax:
TODO: Figure out if this is really new or was just broken and introduce flag if so

We want to fix this even earlier actually, so that we don't get S [Sym "=", Sym "veriT_vr6", Sym "veriT_vr6"]
when parsing in (veriT_vr6 S4) 
("bds",
 [(S [Sym "=", Sym "veriT_vr6", Sym "veriT_vr6"], SOME (Sym "S4")), (S [Sym "=", Sym "veriT_vr7", Sym "veriT_vr7"], SOME (Sym "S2")),
  (S [Sym "=", Sym "veriT_vr8", Sym "veriT_vr8"], SOME (Sym "S2")), (S [Sym "=", Sym "v0", Sym "veriT_vr6"], NONE),
  (S [Sym "=", Sym "v1", Sym "veriT_vr7"], NONE),
  (S [Sym "=", Sym "v2", Sym "veriT_vr8"], NONE)])
*)
  fun extract_symbols bds = ((*@{print}("bds",bds);*)
    bds
    |> map (fn (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym x, SMTLIB.Sym y], typ) => [([x, y], typ)]
           | t => raise (Fail ("match error " ^ @{make_string} t))))
    |> flat

  (* onepoint can bind a variable to another variable or to a constant *)
  fun extract_qnt_symbols cx bds =
    bds
    |> map (fn (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym x, SMTLIB.Sym y], typ) =>
                (case node_of (SMTLIB.Sym y) cx of
                  ((_, []), _) => [([x], typ)]
                | _ => [([x, y], typ)])
             | (SMTLIB.S (SMTLIB.Sym "=" :: SMTLIB.S [SMTLIB.Sym x, typ] :: SMTLIB.Sym y :: []), _) => [([x, y], SOME typ)]
             | (SMTLIB.S (SMTLIB.Sym "=" :: SMTLIB.Sym x :: _), typ) => [([x], typ)]
             |  t => raise (Fail ("match error " ^ @{make_string} t)))
    |> flat

  fun extract_symbols_map bds =
    bds
    |> map (fn (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym x, _], typ) => [([x], typ)])
    |> flat
in

fun declared_csts _ "__skolem_definition" [(SMTLIB.S [SMTLIB.Sym x, typ, _], _)] = [(x, typ)]
  | declared_csts _ "__skolem_definition" t = raise (Fail ("unrecognized skolem_definition " ^ @{make_string} t))
  | declared_csts _ _ _ = []

fun skolems_introduced_by_rule (SMTLIB.S bds) =
  fold (fn (SMTLIB.S [SMTLIB.Sym "=", _, SMTLIB.Sym y]) => curry (op ::) y
              | x => (@{print} x; fn x => x)) bds []

(*FIXME there is probably a way to use the information given by onepoint*)
fun bound_vars_by_rule _ "bind" bds = extract_symbols bds
  | bound_vars_by_rule cx "onepoint" bds = extract_qnt_symbols cx bds
  | bound_vars_by_rule _ "sko_forall" bds =  bds
    |> map (fn (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym x, SMTLIB.Sym y], typ) => [([x,y], typ)])
    |> flat
  | bound_vars_by_rule _ "sko_ex" bds = extract_symbols_map bds
  | bound_vars_by_rule _ "__skolem_definition" [(SMTLIB.S [SMTLIB.Sym x, typ, _], _)] = [([x], SOME typ)]
  | bound_vars_by_rule _ "__skolem_definition" [(SMTLIB.S [_, SMTLIB.Sym x, _], _)] = [([x], NONE)]
  | bound_vars_by_rule _ "let" [(SMTLIB.S [_, SMTLIB.Sym x, y], _)] = [([x], NONE)]
  | bound_vars_by_rule _ _ _ = []

end


datatype step_kind = ASSUME | ASSERT | ANCHOR | NO_STEP | NORMAL_STEP | SKOLEM

fun parse_raw_proof_steps (limit : string option) (ls : SMTLIB.tree list) (cx : name_bindings) (assms_nbr : int):
     (raw_lethe_node list * SMTLIB.tree list * name_bindings) =
  let
    fun rotate_pair (a, (b, c)) = ((a, b), c)
    fun step_kind [] = (NO_STEP, SMTLIB.S [], [])
      | step_kind ((p as SMTLIB.S (SMTLIB.Sym "anchor" :: _)) :: l) = (ANCHOR, p, l)
      | step_kind ((p as SMTLIB.S (SMTLIB.Sym "assume" :: _)) :: l) = (ASSUME, p, l)
      | step_kind ((p as SMTLIB.S (SMTLIB.Sym "assert" :: _)) :: l) = (ASSERT, p, l)
      | step_kind ((p as SMTLIB.S (SMTLIB.Sym "step" :: _)) :: l) = (NORMAL_STEP, p, l)
      | step_kind ((p as SMTLIB.S (SMTLIB.Sym "define-fun" :: _)) :: l) = (SKOLEM, p, l)
      | step_kind ((p as SMTLIB.S (SMTLIB.Sym "declare-fun" :: _)) :: l) = (SKOLEM, p, l)
      | step_kind p = raise (Fail ("step_kind unrec: " ^ @{make_string} p))
    fun parse_skolem (SMTLIB.S [SMTLIB.Sym "define-fun", SMTLIB.Sym id,  _, typ,
           SMTLIB.S (SMTLIB.Sym "!" :: t :: [SMTLIB.Key _, SMTLIB.Sym name])]) cx =
         (*replace the name binding by the constant instead of the full term in order to reduce
           the size of the generated terms and therefore the reconstruction time*)
         let val (l, cx) = (fst oo SMTLIB_Proof.extract_and_update_name_bindings) t cx
            |> apsnd (SMTLIB_Proof.update_name_binding (name, SMTLIB.Sym id))
         in
           (mk_raw_node (id ^ lethe_def) lethe_def (SMTLIB.S [SMTLIB.Sym id, typ, l]) [] []
              (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym id, l]) [], cx)
         end
      | parse_skolem (SMTLIB.S [SMTLIB.Sym "define-fun", SMTLIB.Sym id,  _, typ, SMTLIB.S l]) cx =
         let val (l, cx) = (fst oo SMTLIB_Proof.extract_and_update_name_bindings) (SMTLIB.S l) cx
         in
           (mk_raw_node (id ^ lethe_def) lethe_def (SMTLIB.S [SMTLIB.Sym id, typ, l]) [] []
              (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym id, l]) [], cx)
         end
      | parse_skolem (SMTLIB.S [SMTLIB.Sym "declare-fun", SMTLIB.Sym id, typ, def]) cx =
         (*replace the name binding by the constant instead of the full term in order to reduce
           the size of the generated terms and therefore the reconstruction time*)
         let val (l, cx) = (fst oo SMTLIB_Proof.extract_and_update_name_bindings) def cx
         in
           (mk_raw_node (id ^ lethe_def) lethe_def (SMTLIB.S [SMTLIB.Sym id, typ, l]) [] []
              (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym id, def]) [], cx)
         end
      | parse_skolem t _ = raise Fail ("unrecognized Lethe proof " ^ \<^make_string> t)
    fun get_id_cx (SMTLIB.S ((SMTLIB.Sym _) :: (SMTLIB.Sym id) :: l), cx) = (id, (l, cx))
      | get_id_cx t = raise Fail ("unrecognized Lethe proof " ^ \<^make_string> t)
    fun get_id (SMTLIB.S ((SMTLIB.Sym _) :: (SMTLIB.Sym id) :: l)) = (id, l)
      | get_id t = raise Fail ("unrecognized Lethe proof " ^ \<^make_string> t)
    fun parse_source (SMTLIB.Key "premises" :: SMTLIB.S source ::l, cx) =
        (SOME (map (fn (SMTLIB.Sym id) => id) source), (l, cx))
      | parse_source (l, cx) = (NONE, (l, cx))
    fun parse_rule (SMTLIB.Key "rule" :: SMTLIB.Sym r :: l, cx) = (r, (l, cx))
      | parse_rule t = raise Fail ("unrecognized Lethe proof " ^ \<^make_string> t)
    fun parse_anchor_step (SMTLIB.S (SMTLIB.Sym "anchor" :: SMTLIB.Key "step" :: SMTLIB.Sym r :: l), cx) = (r, (l, cx))
      | parse_anchor_step t = raise Fail ("unrecognized Lethe proof " ^ \<^make_string> t)
    fun parse_args (SMTLIB.Key "args" :: args :: l, cx) =
          let val ((args, cx), _) = SMTLIB_Proof.extract_and_update_name_bindings args cx
          in (args, (l, cx)) end
      | parse_args (l, cx) = (SMTLIB.S [], (l, cx))
    fun parse_and_clausify_conclusion (SMTLIB.S (SMTLIB.Sym "cl" :: []) :: l, cx) =
          (SMTLIB.Sym "false", (l, cx))
      | parse_and_clausify_conclusion (SMTLIB.S (SMTLIB.Sym "cl" :: concl) :: l, cx) =
          let val (concl, cx) = fold_map (fst oo SMTLIB_Proof.extract_and_update_name_bindings) concl cx
          in (SMTLIB.S (SMTLIB.Sym "or" :: concl), (l, cx)) end
      | parse_and_clausify_conclusion t = raise Fail ("unrecognized Lethe proof " ^ \<^make_string> t)
    val parse_normal_step =
        get_id_cx
        ##> parse_and_clausify_conclusion
        #> rotate_pair
        ##> parse_rule
        #> rotate_pair
        ##> parse_source
        #> rotate_pair
        ##> parse_args
        #> rotate_pair

    fun to_raw_node subproof ((((id, concl), rule), prems), args) =
        mk_raw_node id rule args (the_default [] prems) [] concl subproof
    fun at_discharge NONE _ = false
      | at_discharge (SOME id) p = p |> get_id |> fst |> (fn id2 => id = id2)
  in
    case step_kind ls of
        (NO_STEP, _, _) => ([],[], cx)
      | (NORMAL_STEP, p, l) =>
          if at_discharge limit p then ([], ls, cx) else
            let
             (*ignores content of "discharge": Isabelle is keeping track of it via the context*)
              val (s, (_, cx)) =  (p, cx)
                |> parse_normal_step
                |>>  (to_raw_node [])
              val (rp, rl, cx) = parse_raw_proof_steps limit l cx assms_nbr
          in (s :: rp, rl, cx) end
      | (ASSUME, p, l) =>
          let
            val (id, t :: []) = p
              |> get_id

            val ((t, cx), _) = SMTLIB_Proof.extract_and_update_name_bindings t cx
            val s = mk_raw_node id input_rule (SMTLIB.S []) [] [] t []
            (*Recursive call to parse rest of the steps.*)
            val (rp, rl, cx) = parse_raw_proof_steps limit l cx (assms_nbr + 1)
          in (s :: rp, rl, cx) end
      | (ASSERT, p, l) => 
          let
            val (id, term) = (case p of
                SMTLIB.S [SMTLIB.Sym "assert", SMTLIB.S [SMTLIB.Sym "!", term, SMTLIB.Key "named", SMTLIB.Sym id]] => (id, term)
              | SMTLIB.S [SMTLIB.Sym "assert", term] => (Int.toString assms_nbr, term))

            val ((t, cx), _) = SMTLIB_Proof.extract_and_update_name_bindings term cx
            val s = mk_raw_node id input_rule (SMTLIB.S []) [] [] t []
            (*Recursive call to parse rest of the steps.*)
            val (rp, rl, cx) = parse_raw_proof_steps limit l cx (assms_nbr+1)
          in (s :: rp, rl, cx) end
      | (ANCHOR, p, l) =>
          let
            val (anchor_id, (anchor_args, (_, cx))) = (p, cx) |> (parse_anchor_step ##> parse_args)
            val (subproof, discharge_step :: remaining_proof, cx) = parse_raw_proof_steps (SOME anchor_id) l cx assms_nbr
            (*val _ = @{print}("I think we would need to add variables of anchor let steps to the context here... In extract_and_update_name_bindings?")
            val _ = @{print}("anchor_id,anchor_args",(anchor_id,anchor_args))*)
            val (curss, (_, cx)) = parse_normal_step (discharge_step, cx)
            val s = to_raw_node subproof (fst curss, anchor_args)
            val (rp, rl, cx) = parse_raw_proof_steps limit remaining_proof cx assms_nbr
            (*val _ = @{print}("finished with this anchor",(anchor_id,s))*)

            (*val _ = @{print}("its name bindings are",(anchor_id,cx))*)

          in (s :: rp, rl, cx) end
      | (SKOLEM, p, l) =>
          let
            val (s, cx) = parse_skolem p cx
            val (rp, rl, cx) = parse_raw_proof_steps limit l cx (assms_nbr)
          in (s :: rp, rl, cx) end
  end

val anchor_rules = ["bind","sko_forall","sko_ex","let","onepoint"]
fun is_anchor_rule rule = List.exists (curry (op =) rule) anchor_rules
val keep_args_rules = ["rare_rewrite","la_generic","bind"]

fun proof_ctxt_of_rule "bind" t = t
  | proof_ctxt_of_rule "sko_forall" t = t
  | proof_ctxt_of_rule "sko_ex" t = t
  | proof_ctxt_of_rule "let" t = t
  | proof_ctxt_of_rule "onepoint" t = t
  | proof_ctxt_of_rule _ _ = []

fun args_of_rule "bind" t = t
  | args_of_rule "la_generic" t = t
  | args_of_rule "rare_rewrite" (SMTLIB.Str s :: xs) = (SMTLIB.Sym s) :: xs (*Not sure if I really want to do this here? I also don't want it transformed to a string term though?*)
  | args_of_rule _ _ = []

fun insts_of_forall_inst "forall_inst" t = map (fn SMTLIB.S [_, SMTLIB.Sym x, a] => (x, a)) t
  | insts_of_forall_inst _ _ = []

fun id_of_last_step prems =
  if null prems then []
  else
    let val Lethe_Replay_Node {id, ...} = List.last prems in [id] end

fun extract_assumptions_from_subproof subproof =
  let fun extract_assumptions_from_subproof (Lethe_Replay_Node {rule, concl, ...}) assms =
    if rule = local_input_rule then concl :: assms else assms
  in
    fold extract_assumptions_from_subproof subproof []
  end

fun normalized_rule_name id rule =
  (case (rule = input_rule, can SMTLIB_Interface.role_and_index_of_assert_name id) of
    (true, true) => normalized_input_rule
  | (true, _) => local_input_rule
  | _ => rule)

fun is_assm_repetition id rule =
  rule = input_rule andalso can SMTLIB_Interface.role_and_index_of_assert_name id

fun extract_skolem ([SMTLIB.Sym var, typ, choice]) = (var, typ, choice)
  | extract_skolem t = raise Fail ("fail to parse type" ^ @{make_string} t)

(* The preprocessing takes care of:
     1. unfolding the shared terms
     2. extract the declarations of skolems to make sure that there are not unfolded
*)
fun preprocess compress step =
  let
    (*val _ = @{print}("Found it! Look here to fix the assumption in bind problem!!!")*)
    fun expand_assms cs =
      map (fn t => case AList.lookup (op =) cs t of NONE => t | SOME a => a)

    fun find_sort _ [] ys = (ys,NONE) |
        find_sort x1 (x::xs) ys =
          case x of
            (SMTLIB.S [SMTLIB.Sym x1', y2]) => if x1' = x1 then (xs @ ys, SOME y2) else  find_sort x1 xs (x::ys)|
             _ => find_sort x1 xs (x::ys)

    fun match_typing_arguments [] [] = [] |
      (*0. Argument already has the right form (= (v0 S) t) *)
        match_typing_arguments ys ((y as SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym _, _], _])::xs)
         = y :: match_typing_arguments ys xs |
      (*1. Single unsorted v0 or sorted_vars (v0 S) that are not matched by any mapping following
        AFTER them. For the old veriT syntax where variables can be unsorted this also works due to
        some transformation applied during parsing*)
      match_typing_arguments ((y as SMTLIB.S [SMTLIB.Sym var, _])::ys) []
        = (SMTLIB.S [SMTLIB.Sym "=", y, SMTLIB.Sym var]) :: match_typing_arguments ys [] |
      (*2. Mapping (:= v0 v1) *)
      match_typing_arguments ys ((SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym x1, t])::xs) =
        (case find_sort x1 ys [] of
          (*2a. Mapping follows after sorted_var (v0 S) or (v1 S) in args list
                If both are in, both need to be deleted from the list but we only need to give x1
                type y2 not x2 as well.*)
          (zs,SOME y2) => (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym x1, y2], t]) :: match_typing_arguments zs xs |
          (*2b. Mapping without any corresponding sorted_var (v0 S) or (v1 S) in args list *)
          (zs,NONE) =>
            (case t of
              SMTLIB.Sym y1 =>
                (case find_sort y1 ys [] of
                  (zs',SOME y2) => ((SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym x1, y2], t]) :: match_typing_arguments zs' xs) |
              _ => (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym x1, t]) :: match_typing_arguments zs xs) |
              _ => (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym x1, t]) :: match_typing_arguments zs xs)
        ) |
      (*3. Sorted variable found (v0 S) *)
      match_typing_arguments ys ((SMTLIB.S [SMTLIB.Sym x1, y2])::xs) = 
        match_typing_arguments ((SMTLIB.S [SMTLIB.Sym x1, y2])::ys) xs |
      (*4. Old veriT syntax where variables can be unsorted v0. During preprocessing we transformed
        them to (v0 v0). Since they don't have a type they are not useful in step 2. However, one could
        argue that if we would not add them to the variable list in case of
        another argument that defines the same variable earlier in the list the matching could use
        the same type. We don't expect this syntax to be matched with sorted variables but still*)
      match_typing_arguments ys ((SMTLIB.S [SMTLIB.Sym x1, SMTLIB.Sym "type"])::xs) = 
        match_typing_arguments ((SMTLIB.S [SMTLIB.Sym x1, SMTLIB.Sym "type"])::ys) xs |
      match_typing_arguments _ ys = (@{print}("this should not be here?");raise Fail ("error parsing in arguments " ^ \<^make_string> ys))


    fun match_typing_arguments2 ys xs =
      let
       (* val _ = @{print}("xs",xs)
        val _ = @{print}("ys",ys)*)
        val temp = match_typing_arguments ys xs
        (*val _ = @{print}("temp",temp)*)

      in temp end

        (* TODO: Should only be activated whenever we check SMT-LIB benchmarks with check_smt *)


fun normalize_name name = if String.explode name |> hd |> Char.isUpper  then "isabelle_internal_" ^ name  else name

fun smtlib_types t = (t="Bool") orelse (t="Int")
fun normalize_tree (SMTLIB.Sym s) = if smtlib_types s then SMTLIB.Sym s else SMTLIB.Sym (normalize_name s) |
    normalize_tree (SMTLIB.S xs) = SMTLIB.S (map normalize_tree xs) |
    normalize_tree x = x


    fun preprocess (Raw_Lethe_Node {id, rule, args, prems, concl, subproof, ...}) (cx, remap_assms)  =
      let
       (*val _ = @{print}("args in pre",args)
       val _ = @{print}("id",id)
       val _ = @{print}("rule",rule)
       val _ = @{print}("cx",cx)
       val _ = @{print}("remap_assms",remap_assms)*)


       (* If we check external proofs we need to change term names starting with an upper character
          since this is not allowed in Isabelle *)
       val ctxt = #ctxt cx
       val args = if Config.get ctxt SMT_Config.check_external then normalize_tree args else args
       val concl = if Config.get ctxt SMT_Config.check_external then normalize_tree concl else concl
       (*val _ = @{print}("args after normalization",args)
       val _ = @{print}("concl after normalization",concl)*)



        val (skolem_names, stripped_args) = args
          |> (fn SMTLIB.S args => args)
          |> map
              (fn SMTLIB.S [SMTLIB.Key "=", x, y] => SMTLIB.S [SMTLIB.Sym "=", x, y]
              | x => x)
              (*TODO: Why did Mathias remove rules here? They are handled in extract_types_of_arg*)
          |>  (rule = "bind" orelse rule = "onepoint" orelse rule="let" orelse rule="sko_forall") ? (match_typing_arguments2 [])
          |> `(if rule = lethe_def then single o extract_skolem else K [])
          ||> SMTLIB.S
       (*val _ = @{print}("stripped_args",stripped_args)*)

        val (subproof, (cx, _)) = fold_map preprocess subproof (cx, remap_assms) |> apfst flat
       (*val _ = @{print}("cx_after sub",cx)*)

        val remap_assms = (if rule = "or" then (id, hd prems) :: remap_assms else remap_assms)
        (* declare variables in the context *)
        val declarations =
           if rule = lethe_def
           then skolem_names |> map (fn (name, _, choice) => (name, choice))
           else []
      in
        if compress andalso rule = "or"
        then ([], (cx, remap_assms))
        else ([Raw_Lethe_Node {id = id, rule = rule, args = stripped_args,
           prems = expand_assms remap_assms prems, declarations = declarations, concl = concl, subproof = subproof}],
          (cx, remap_assms))
      end
  in preprocess step end

fun filter_split _ [] = ([], [])
  | filter_split f (a :: xs) =
     (if f a then apfst (curry op :: a) else apsnd (curry op :: a)) (filter_split f xs)


fun extract_types_of_args (SMTLIB.S [var, typ, t as SMTLIB.S [SMTLIB.Sym "choice", _, _]]) rule_name =
    (SMTLIB.S [var, typ, t], SOME typ)
    |> single
 | extract_types_of_args (SMTLIB.S [var, t as SMTLIB.S [SMTLIB.Sym "choice", SMTLIB.S [SMTLIB.S [_, typ]], _]]) rule_name =
    (SMTLIB.S [var, typ, t], SOME typ)
    |> single
 | extract_types_of_args (SMTLIB.S t) rule_name =
  let
    fun extract_types_of_arg (SMTLIB.S [eq as SMTLIB.Sym "=", SMTLIB.S [var, typ], t]) =
      if is_anchor_rule rule_name
      then (SMTLIB.S [eq, var, t], SOME typ)
      else (SMTLIB.S [eq, SMTLIB.S [var, typ], t], SOME typ)
    | extract_types_of_arg (SMTLIB.S [eq as SMTLIB.Sym "=", var as SMTLIB.Sym _, t as SMTLIB.S [SMTLIB.Sym "choice", SMTLIB.S [SMTLIB.S [_, typ]], _]]) =
       (SMTLIB.S [eq, var, t], SOME typ)
    | extract_types_of_arg t = (t, NONE)

  in
    t
    |> map (extract_types_of_arg)
  end

fun collect_skolem_defs (Raw_Lethe_Node {rule, subproof = subproof, args, ...}) =
  (if is_skolemization rule then map (fn id => id ^ lethe_def) (skolems_introduced_by_rule args) else []) @
  flat (map collect_skolem_defs subproof)

val desymbolize = Name.desymbolize (SOME false) o perhaps (try (unprefix "?"))


(*The postprocessing does:
  1. translate the terms to Isabelle syntax, taking care of free variables
  2. remove the ambiguity in the proof terms:
       x \<leadsto> y |- x = x
    means y = x. To remove ambiguity, we use the fact that y is a free variable and replace the term
    by:
      xy \<leadsto> y |- xy = x.
    This is now does not have an ambiguity and we can safely move the "xy \<leadsto> y" to the proof
    assumptions.
*)
fun postprocess_proof compress ctxt step cx =
  let

    fun postprocess (Raw_Lethe_Node {id, rule, args, prems, declarations, concl, subproof}) (cx, rew) =
    let
      val trace=false
      val _ = if trace then (@{print}("In postprocessing:");()) else ()
      val _ = if trace then (@{print}("id",id);()) else ()
      val _ = if trace then (@{print}("args",args);()) else ()
      val _ = if trace then (@{print}("rew",rew);()) else ()
      val _ = if trace then (@{print}("cx before postprocessing",cx);()) else ()
      val _ = if trace then ((if rew=[] then () else (@{print}("ATTENTION: figure out what this does rew",rew);()))) else ()

      val args_types = extract_types_of_args args rule
      val _ = if trace then (@{print}("args after extract_types_of_args ",args);()) else ()

      (*Only interesting for __skolem_definition rule*)
      val globally_bound_vars = declared_csts cx rule args_types
      val cx = fold (update_binding o (fn (s, typ) => (s, Term (Free (s, type_of cx typ)))))
           globally_bound_vars cx

      (*find rebound variables specific to the LHS of the equivalence symbol*)
      val bound_vars = bound_vars_by_rule cx rule args_types
      val _ = if trace then (@{print}("bound_vars",bound_vars);()) else ()
      val bound_vars_no_typ = map fst bound_vars
      (*TODO: fn x => x muss vielleicht fuer let vllt geloescht werden*)
      val rhs_vars =
        fold (fn [t', t] => t <> t' ? (curry (op ::) t) | _ => fn x => x) bound_vars_no_typ []
      val _ = if trace then (@{print}("rhs_vars",rhs_vars);()) else ()

      fun not_already_bound cx t = SMTLIB_Proof.lookup_binding cx t = None andalso
          not (member (op =) rhs_vars t)
      (* (= v0 y) habe aber schon im Kontext ein anderes y, weil vorher schon (= x y)
         In Alethe ist das egal aber in Isabelle funktioniert das nicht so. 
         	Schon gebundene Variablen muessen umbenannt werden. Collect them rebound_lhs_var

         shadowing_var sind alle die neu sind, weil sie ab jetzt shadowen
      *)
      val (shadowing_vars, rebound_lhs_vars) = bound_vars
        |> filter_split (fn ([t, _], typ) => not_already_bound cx t | _ => true)
        |>> map (apfst (hd))
        |>> (fn vars => vars @ flat (map (fn ([_, t], typ) => [(t, typ)] | _ => []) bound_vars))
      val _ = if trace then (@{print}("shadowing_vars",shadowing_vars);()) else ()
      val _ = if trace then (@{print}("rebound_lhs_vars",rebound_lhs_vars);()) else ()
      val _ = if trace then (@{print}("see",flat (map (fn ([_, t], typ) => [(t, typ)] | _ => []) bound_vars));()) else ()

      (*
        schreibe recursiv subcontexte
        rew sind die die schon hast, die alten rewrites
        
      *)
      val subproof_rew = fold (fn [t, t'] => curry (op ::) (t, t ^ t'))
        (map fst rebound_lhs_vars) rew
      val subproof_rewriter = fold (fn (t, t') => synctatic_rew_in_lhs_subst t t')
         subproof_rew

      val subproof_rewriter_temp = fold (fn (t, t') => synctactic_var_subst t t')
         subproof_rew
      val _ = if trace then (@{print}("rew",rew);()) else ()
      val _ = if trace then (@{print}("subproof_rew",subproof_rew);()) else ()
      val _ = if subproof_rew = [] then () else (if trace then (@{print}("YELL FOUND PROOF with subproof_rew",subproof_rew);()) else ())

      (*concl nur die conclu des bind steps. Foralls haben immer sorted variablen*)

      val _ = if trace then (@{print}("concl",concl);()) else ()

      val ((termified_concl, bounds), cx') = node_of concl cx (*concl is name for both term and SMTLIB.Tree*)  
     
      val _ = if trace then (@{print}("cx'",cx');()) else ()
      val _ = if trace then (@{print}("bounds after node_of",bounds);()) else ()
      val _ = if trace then (@{print}("termified_concl after node_of ",termified_concl);()) else ()
 

      (* Sanity check if conclusion has extra terms *)
      val _ = if bounds <> [] then raise (Fail ("found dangling variable (s) " ^ (@{make_string} bounds) ^
          " in concl " ^ (@{make_string} concl) ^ " of step" ^ id)) else ()



      (*Gebe denen neue Namen, weil sie ja schon im Kontext drin sind und es sonst probleme gaebe
      Namen sind unique, weil a unique ist oder so
      *)
(*TODO: Might be able to simplify not using extra_lhs_vars since that is not used anywhere else *)
      val extra_lhs_vars = map (fn ([a,b], typ) => (a, a^b, typ)) rebound_lhs_vars
      val old_lhs_vars = map (fn (a, _, typ) => (a, typ)) extra_lhs_vars 
      val new_lhs_vars = map (fn (_, newvar, typ) => (newvar, typ)) extra_lhs_vars
      val _ = if trace then (@{print}("extra_lhs_vars",extra_lhs_vars);()) else ()
      val _ = if trace then (@{print}("old_lhs_vars",old_lhs_vars);()) else ()
      val _ = if trace then (@{print}("new_lhs_vars",new_lhs_vars);()) else ()

      (* postprocess conclusion *)
(*unskolemize_names weil Isabelle bei Namen __ macht, wird bei Sledgehammer auch so gemacht. Irgendwie kommen die rein*)
(*Hier werden die rewrites angewendet*)
      val termified_concl = SMTLIB_Isar.unskolemize_names ctxt (subproof_rewriter termified_concl)
      val _ = if trace then (@{print}("termified_concl ",termified_concl);()) else ()


   (*ML: ((string * (string * typ)) list, ''a)
    SMTLIB_Proof.context
cx'
ML: ((string * (string * typ)) list, ''a)
    SMTLIB_Proof.context
*)

(* (string * SMTLIB.tree option) ->  (string * typ) *)

(*Erst sammele alle (string * typ) von den argumenten*)
      fun give_type cx2 (SMTLIB.S [SMTLIB.Sym "=",  SMTLIB.S [SMTLIB.Sym x, typ], t] :: args) =
         let
           val cx2 = add_bound_variables_to_ctxt cx2 [(x, SOME typ)] cx2
           val rhs = (case t of
             SMTLIB.Sym y => [(y,type_of cx2 typ)] |
             _ => [])
         in
            (x,type_of cx2 typ) :: rhs @ give_type cx2 args
         end |
         give_type cx2 (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym x, t] :: args) =
         let
           val (y', cx2) = term_of t cx2
           val cx2 = fold (update_binding o (fn (s, SOME typ) => (s, Term (Free (s, fastype_of y'))))) [(x,SOME (SMTLIB.Sym x))] cx2
           val rhs = (case t of
             SMTLIB.Sym y => [(y,fastype_of y')]  |
             _ => [])   
         in
            (*HOLogic.mk_eq (x',tm) :: give_type cx' args*)
            (x,fastype_of y') :: rhs @ give_type cx2 args
         end |
         give_type _ [] = [] |
         give_type _ (x::_) =[]

(*
("(shadowing_vars @ new_lhs_vars)",
 [("veriT_vr2", NONE), ("veriT_sk0", NONE)]) (line 644 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Tools/SMT/lethe_proof.ML") 
("args_types",
 [("veriT_vr2", "int"), ("veriT_sk0", "int")]) (line 679 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Tools/SMT/lethe_proof.ML") 
exception Fail raised (line 684 of "/home/lach*)
      val args_types2 = give_type cx' ((fn (SMTLIB.S t) => t) args)
      val _ = if trace then (@{print}("args_types2",args_types2);()) else ()

      (*'a * SMTLIB.tree option -> 'a * typ*)
      (*fun give_proper_type (s, SOME typ) = (s, type_of cx typ)*)
      fun give_proper_type (s, SOME typ) = (s, type_of cx typ)
       | give_proper_type (s, NONE) =
          let
            fun findIn [] = NONE |
              findIn ((s2,typ)::xs) = (if s=s2 then SOME typ else findIn xs)
          in
           (case findIn args_types2 of 
            SOME typ => (s, typ) |
            NONE => raise (Fail ("could not find type of var " ^ @{make_string} s ^ " in step " ^ id ^ " in " ^  @{make_string} concl)))
          end
      val bound_tvars = map give_proper_type (shadowing_vars @ new_lhs_vars)
      val _ = if trace then (@{print}("bound_tvars",bound_tvars);()) else ()

      (*val subproof_cx_old =
        add_bound_variables_to_ctxt cx (shadowing_vars @ new_lhs_vars) cx*)
        (*Wir wollen im Kontext, die die neu sind weil sie neu eingefuerht wurden (shadowing) und 
die die umbenannt wurden weil sie neu aber schon mit dem selben Namen existiert haben*)
      val subproof_cx =
        add_bound_variables_to_ctxt2 bound_tvars cx
      (*val _ = @{print}("subproof_cx_old",subproof_cx_old)*)
      val _ = if trace then (@{print}("subproof_cx",subproof_cx);()) else ()


      (*Optimizierung compression: In Isabelle sind alpha umbenennung viel effizienter deswegen wird das hier
        gleich gemacht*)
      (*Wenn es ein Subproof ist der einfach nur umbenennt kann er komplett weg*)
      (*Isabelle benutzt de bruijn umbenennung, statt gebundene Variablen steht 1,2,3,4 *)
      fun could_unify (Bound i, Bound j) = i = j
        | could_unify (Var v, Var v') = v = v'
        | could_unify (Free v, Free v') = v = v'
        | could_unify (Const (v, ty), Const (v', ty')) = v = v' andalso ty = ty'
        | could_unify (Abs (_, ty, bdy), Abs (_, ty', bdy')) = ty = ty' andalso could_unify (bdy, bdy')
        | could_unify (u $ v, u' $ v') = could_unify (u, u') andalso could_unify (v, v')
        | could_unify _ = false
      fun is_alpha_renaming t =
          t
          |> HOLogic.dest_Trueprop
          |> HOLogic.dest_eq
          |> could_unify
        handle TERM _ => false
      val alpha_conversion = rule = "bind" andalso is_alpha_renaming termified_concl

      val can_remove_subproof =
        compress andalso (is_skolemization rule orelse alpha_conversion)
      val _ = if trace then (@{print}("can_remove_subproof ",can_remove_subproof);()) else ()

      (*Wenn nicht comprimiert mache postprocess, rekursiv*)
      val (fixed_subproof : lethe_replay_node list, _) =
         fold_map postprocess (if can_remove_subproof then [] else subproof)
           (subproof_cx, subproof_rew)


      val unsk_and_rewrite = SMTLIB_Isar.unskolemize_names ctxt o subproof_rewriter

      (* postprocess assms *)
      val stripped_args = map fst args_types
      (*Wirf argumente weg wenn nicht bestimmte Regel*)
      val sanitized_args = proof_ctxt_of_rule rule stripped_args
      val _ = if trace then (@{print}("sanitized_args",sanitized_args);()) else ()

      (* y ist schon im Kontext. Jetzt ueberschreiben wir y
         Anstatt y in cx zu ueberschreiben, bennen wir y lieber um
         Jetzt machen wir das ueberschreiben wir subproof_cx
         Warum? 
      *)

      (*Nimmt alte Namen und neue Namen weil wir die orginal argumente uebersetzen und die ja nicht
        die umbenannte namen haben*)
      val arg_cx =
        add_bound_variables_to_ctxt2 (map give_proper_type (shadowing_vars @ old_lhs_vars)) subproof_cx
      val _ = if trace then (@{print}("arg_cx",arg_cx);()) else ()

      val (termified_args, _) = fold_map node_of sanitized_args arg_cx |> apfst (map fst)
      val normalized_args = map unsk_and_rewrite (if rule = "rare_rewrite" then map subproof_rewriter_temp termified_args else termified_args) (*TODO: I added the rewriter here*)
      val _ = if trace then (@{print}("normalized_args",normalized_args);()) else ()

      val subproof_assms = proof_ctxt_of_rule rule normalized_args (*Das ist whrs unoetig, weil es oben ja shon gemacht wird*)

      (* postprocess arguments *)
      (*Fix fuer RARE?*)
      val rule_args = args_of_rule rule stripped_args
      val _ = if trace then (@{print}("rule_args",rule_args);()) else ()

      val (termified_args, _) = fold_map term_of rule_args subproof_cx
      val _ = if trace then (@{print}("termified_args",termified_args);()) else ()

      val normalized_args = map unsk_and_rewrite (if rule = "rare_rewrite" then map subproof_rewriter_temp termified_args else termified_args) (*TODO: I added the rewriter here*)
      val _ = if trace then (@{print}("normalized_args",normalized_args);()) else ()

      val rule_args = map subproof_rewriter normalized_args
      val _ = if trace then (@{print}("rule_args",rule_args);()) else ()

      val raw_insts = insts_of_forall_inst rule stripped_args
      fun termify_term (x, t) cx = let val (t, cx) = term_of t cx in ((x, t), cx) end
      val (termified_args, _) = fold_map termify_term raw_insts subproof_cx
      val _ = if trace then (@{print}("termified_args",termified_args);()) else ()

      val insts = Symtab.empty
        |> fold (fn (x, t) => fn insts => Symtab.update_new (desymbolize x, t) insts) termified_args
        |> Symtab.map (K unsk_and_rewrite)

      (* declarations *)
      val (declarations, _) = fold_map termify_term declarations cx
        |> apfst (map (apsnd unsk_and_rewrite))

      (* fix step *)
      (* Vom subproof *)
      val skolem_defs = (if is_skolemization rule
         then map (fn id => id ^ lethe_def) (skolems_introduced_by_rule (SMTLIB.S (map fst args_types))) else [])
      val _ = if trace then (@{print}("skolem_defs ",skolem_defs);()) else ()

      val skolems_of_subproof = (if compress andalso is_skolemization rule
         then flat (map collect_skolem_defs subproof) else [])
      val _ = if trace then (@{print}("skolems_of_subproof ",skolems_of_subproof);()) else ()

      val _ = if trace then (@{print}("prems ",prems);()) else ()
      val fixed_prems =                                                       
        prems @ (if is_assm_repetition id rule then [id] else []) @
        skolem_defs @ skolems_of_subproof @ (id_of_last_step fixed_subproof) (*TODO: Hier rausnehmen, wo anders reinschreiben*)
      val _ = if trace then (@{print}("fixed_subproof ",fixed_subproof);()) else ()

      val _ = if trace then (@{print}("fixed_prems ",fixed_prems);()) else ()
val _ = @{print}("id",id)
val _ = @{print}("rule",rule)
val _ = @{print}("(id_of_last_step fixed_subproof)",(id_of_last_step fixed_subproof))
val _ = @{print}("fixed_prems",fixed_prems)

      (* fix subproof *)
      val normalized_rule = normalized_rule_name id rule
        |> (if compress andalso alpha_conversion then K "refl" else I)

      val extra_assms2 =
        (if rule = subproof_rule then extract_assumptions_from_subproof fixed_subproof else [])

      val step = mk_replay_node id normalized_rule rule_args fixed_prems subproof_assms termified_concl
        [] insts declarations (bound_tvars, subproof_assms, extra_assms2, fixed_subproof)
      (*val _ = @{print}("step",step)*)
      val _ = if trace then (@{print}("rule_args",rule_args);()) else ()


    in
       (step, (cx', rew))
    end
  in
    postprocess step (cx, [])
    |> (fn (step, (cx, _)) => (step, cx))
  end

fun combine_proof_steps ((step1 : lethe_replay_node) :: step2 :: steps) =
      let
        val (Lethe_Replay_Node {id = id1, rule = rule1, args = args1, prems = prems1,
            proof_ctxt = proof_ctxt1, concl = concl1, bounds = bounds1, insts = insts1,
            declarations = declarations1,
            subproof = (bound_sub1, assms_sub1, assms_extra1, subproof1)}) = step1
        val (Lethe_Replay_Node {id = id2, rule = rule2, args = args2, prems = prems2,
            proof_ctxt = proof_ctxt2, concl = concl2, bounds = bounds2, insts = insts2,
            declarations = declarations2,
            subproof = (bound_sub2, assms_sub2, assms_extra2, subproof2)}) = step2
        val goals1 =
          (case concl1 of
            _ $ (Const (\<^const_name>\<open>HOL.disj\<close>, _) $ _ $
                  (Const (\<^const_name>\<open>HOL.disj\<close>, _) $ (Const (\<^const_name>\<open>HOL.Not\<close>, _) $a) $ b)) => [a,b]
          | _ => [])
        val goal2 = (case concl2 of _ $ a => a)
      in
        if rule1 = equiv_pos2_rule andalso rule2 = th_resolution_rule andalso member (op =) prems2 id1
          andalso member (op =) goals1 goal2
        then
          mk_replay_node id2 theory_resolution2_rule args2 (filter_out (curry (op =) id1) prems2)
            proof_ctxt2 concl2 bounds2 insts2 declarations2
            (bound_sub2, assms_sub2, assms_extra2, combine_proof_steps subproof2) ::
          combine_proof_steps steps
        else
          mk_replay_node id1 rule1 args1 prems1
            proof_ctxt1 concl1 bounds1 insts1 declarations1
            (bound_sub1, assms_sub1, assms_extra1, combine_proof_steps subproof1) ::
          combine_proof_steps (step2 :: steps)
      end
  | combine_proof_steps steps = steps


val linearize_proof =
  let
    fun map_node_concl f (Lethe_Node {id, rule, prems, proof_ctxt, concl}) =
       mk_node id rule prems proof_ctxt (f concl)
    fun linearize (Lethe_Replay_Node {id = id, rule = rule, args = _, prems = prems,
        proof_ctxt = proof_ctxt, concl = concl, bounds = bounds, insts = _, declarations = _,
        subproof = (bounds', assms, inputs, subproof)}) =
      let
        val bounds = distinct (op =) bounds
        val bounds' = distinct (op =) bounds'
        fun mk_prop_of_term concl =
          concl |> fastype_of concl = \<^typ>\<open>bool\<close> ? curry (op $) \<^term>\<open>Trueprop\<close>
        fun remove_assumption_id assumption_id prems =
          filter_out (curry (op =) assumption_id) prems
        fun add_assumption assumption concl =
          \<^Const>\<open>Pure.imp for \<open>mk_prop_of_term assumption\<close> \<open>mk_prop_of_term concl\<close>\<close>
        fun inline_assumption assumption assumption_id
            (Lethe_Node {id, rule, prems, proof_ctxt, concl}) =
          mk_node id rule (remove_assumption_id assumption_id prems) proof_ctxt
            (add_assumption assumption concl)
        fun find_input_steps_and_inline [] = []
          | find_input_steps_and_inline
              (Lethe_Node {id = id', rule, prems, concl, ...} :: steps) =
            if rule = input_rule then
              find_input_steps_and_inline (map (inline_assumption concl id') steps)
            else
              mk_node (id') rule prems [] concl :: find_input_steps_and_inline steps

        fun free_bounds bounds (concl) =
          fold (fn (var, typ) => fn t => Logic.all (Free (var, typ)) t) bounds concl
        val subproof = subproof
          |> flat o map linearize
          |> map (map_node_concl (fold add_assumption (assms @ inputs)))
          |> map (map_node_concl (free_bounds (bounds @ bounds')))
          |> find_input_steps_and_inline
        val concl = free_bounds bounds concl
      in
        subproof @ [mk_node id rule prems proof_ctxt concl]
      end
  in linearize end

fun rule_of (Lethe_Replay_Node {rule,...}) = rule
fun subproof_of (Lethe_Replay_Node {subproof = (_, _, _, subproof),...}) = subproof


(* Massage Skolems for Sledgehammer.

We have to make sure that there is an "arrow" in the graph for skolemization steps.


A. The normal easy case

This function detects the steps of the form
  P \<longleftrightarrow> Q :skolemization
  Q       :resolution with P
and replace them by
  Q       :skolemization
Throwing away the step "P \<longleftrightarrow> Q" completely. This throws away a lot of information, but it does not
matter too much for Sledgehammer.


B. Skolems in subproofs
Supporting this is more or less hopeless as long as the Isar reconstruction of Sledgehammer
does not support more features like definitions. lethe is able to generate proofs with skolemization
happening in subproofs inside the formula.
  (assume "A \<or> P"
   ...
   P \<longleftrightarrow> Q :skolemization in the subproof
   ...)
  hence A \<or> P \<longrightarrow> A \<or> Q :lemma
  ...
  R :something with some rule
and replace them by
  R :skolemization with some rule
Without any subproof
*)
fun remove_skolem_definitions_proof steps =
  let
    fun replace_equivalent_by_imp (judgement $ ((Const(\<^const_name>\<open>HOL.eq\<close>, typ) $ arg1) $ arg2)) =
       judgement $ ((Const(\<^const_name>\<open>HOL.implies\<close>, typ) $ arg1) $ arg2)
     | replace_equivalent_by_imp a = a (*This case is probably wrong*)
    fun remove_skolem_definitions (Lethe_Replay_Node {id = id, rule = rule, args = args,
         prems = prems,
        proof_ctxt = proof_ctxt, concl = concl, bounds = bounds, insts = insts,
        declarations = declarations,
        subproof = (vars, assms', extra_assms', subproof)}) (prems_to_remove, skolems) =
    let
      val prems = prems
        |> filter_out (member (op =) prems_to_remove)
      val trivial_step = is_SH_trivial rule
      fun has_skolem_substep st NONE = if is_skolemization (rule_of st) then SOME (rule_of st)
             else fold has_skolem_substep (subproof_of st) NONE
        | has_skolem_substep _ a = a
      val promote_to_skolem = exists (fn t => member (op =) skolems t) prems
      val promote_from_assms = fold has_skolem_substep subproof NONE <> NONE
      val promote_step = promote_to_skolem orelse promote_from_assms
      val skolem_step_to_skip = is_skolemization rule orelse
        (promote_from_assms andalso length prems > 1)
      val is_skolem = is_skolemization rule orelse promote_step
      val prems = prems
        |> filter_out (fn t => member (op =) skolems t)
        |> is_skolem ? filter_out (String.isPrefix id)
      val rule = (if promote_step then default_skolem_rule else rule)
      val subproof = subproof
        |> (is_skolem ? K []) (*subproofs of skolemization steps are useless for SH*)
        |> map (fst o (fn st => remove_skolem_definitions st (prems_to_remove, skolems)))
             (*no new definitions in subproofs*)
        |> flat
      val concl = concl
        |> is_skolem ? replace_equivalent_by_imp
      val step = (if skolem_step_to_skip orelse rule = lethe_def orelse trivial_step then []
        else mk_replay_node id rule args prems proof_ctxt concl bounds insts declarations
            (vars, assms', extra_assms', subproof)
          |> single)
      val defs = (if rule = lethe_def orelse trivial_step then id :: prems_to_remove
         else prems_to_remove)
      val skolems = (if skolem_step_to_skip then id :: skolems else skolems)
    in
      (step, (defs, skolems))
    end
  in
    fold_map remove_skolem_definitions steps ([], [])
    |> fst
    |> flat
  end

local
  (*TODO useful?*)
  fun remove_pattern (SMTLIB.S (SMTLIB.Sym "!" :: t :: [SMTLIB.Key _, SMTLIB.S _])) = t
    | remove_pattern (SMTLIB.S xs) = SMTLIB.S (map remove_pattern xs)
    | remove_pattern p = p

  (* veriT adds "?" before some variables. *)
  fun remove_all_qm (SMTLIB.Sym v) = SMTLIB.Sym (perhaps (try (unprefix "?")) v)
    | remove_all_qm (SMTLIB.S l) = SMTLIB.S (map remove_all_qm l)
    | remove_all_qm (SMTLIB.Key v) = SMTLIB.Key v
    | remove_all_qm v = v

  fun import_proof_and_post_process typs funs lines ctxt =
    let
      val compress = SMT_Config.compress_verit_proofs ctxt

      val smtlib_lines_without_qm =
        lines
        |> filter_out (fn x => x = "")
        |> map single
        |> map SMTLIB.parse
        |> map remove_all_qm
        |> map remove_pattern
      val (raw_steps, _, _) =
        parse_raw_proof_steps NONE smtlib_lines_without_qm SMTLIB_Proof.empty_name_binding 0
(*args are still "okay" here*)
      (*val _ = @{print}("raw_steps",raw_steps)*)
      fun process step (cx, cx') =
        let fun postprocess step (cx, cx') =
          let val (step, cx) = postprocess_proof compress ctxt step cx
          in (step, (cx, cx')) end
          (*val _ = @{print}("after preprocessing", (preprocess compress step (cx, cx')))*)
        in uncurry (fold_map postprocess) (preprocess compress step (cx, cx')) end
      val step =
        (empty_context ctxt typs funs, [])
        |> fold_map process raw_steps
        |> (fn (steps, (cx, _)) => (flat steps, cx))
        |> compress? apfst combine_proof_steps
    in step end
in

fun parse typs funs lines ctxt =
  let
    val (u, env) = import_proof_and_post_process typs funs lines ctxt
    val t = u
       |> remove_skolem_definitions_proof
       |> flat o (map linearize_proof)
    fun node_to_step (Lethe_Node {id, rule, prems, concl, ...}) =
      mk_step id rule prems [] concl []
  in
    (map node_to_step t, ctxt_of env)
  end

fun parse_replay typs funs lines ctxt =
  let
    val (u, env) = import_proof_and_post_process typs funs lines ctxt
  in
    (u, ctxt_of env)
  end
end

end;
