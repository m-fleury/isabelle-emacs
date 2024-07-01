(*  Title:      HOL/Tools/SMT/lethe_proof.ML
    Author:     Mathias Fleury, ENS Rennes
    Author:     Sascha Boehme, TU Muenchen
    Author:     Hanna Lachnitt, Stanford University

Lethe proofs: parsing into abstract syntax trees
*)

open Lethe_Node

signature LETHE_PROOF =
sig
  exception LETHE_PROOF_PARSE of string

  val parse_raw_proof_steps: string option -> SMTLIB.tree list -> SMTLIB_Proof.name_bindings ->
     raw_lethe_node list * SMTLIB.tree list * SMTLIB_Proof.name_bindings
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
  val skolem_def : string
  val is_skolem_def : string -> bool
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
open Lethe_Node

exception LETHE_PROOF_PARSE of string
fun throw_lethe_ex str = LETHE_PROOF_PARSE ("Error parsing Alethe proof step: " ^ str)

val step_prefix = ".c"
val input_rule = "input"
val la_generic_rule = "la_generic"
val normalized_input_rule = "__normalized_input" (*arbitrary*)
val rewrite_rule = "__rewrite" (*arbitrary*)
val subproof_rule = "subproof"
val local_input_rule = "__local_input" (*arbitrary*)
val simp_arith_rule = "simp_arith"
val skolem_def = "__skolem_definition" (*arbitrary*)
val not_not_rule = "not_not"
val contract_rule = "contraction"
val forall_inst_rule = "forall_inst"
val eq_congruent_pred_rule = "eq_congruent_pred"
val eq_congruent_rule = "eq_congruent"
val ite_intro_rule = "ite_intro"
val default_skolem_rule = "sko_forall" (*arbitrary, but must be one of the skolems*) (*TODO: I don't like this..*)
val theory_resolution2_rule = "__theory_resolution2" (*arbitrary*)
val equiv_pos2_rule = "equiv_pos2"
val th_resolution_rule = "th_resolution"
val and_pos_rule = "and_pos"
val hole = "hole"

val is_skolem_def = String.isSuffix skolem_def
fun get_skolem_def_id id = id ^ skolem_def

val skolemization_steps = ["sko_forall", "sko_ex"]
val is_skolemization = member (op =) skolemization_steps
val keep_app_symbols = member (op =) [eq_congruent_pred_rule, eq_congruent_rule, ite_intro_rule, and_pos_rule]
val keep_raw_lifting = member (op =) [eq_congruent_pred_rule, eq_congruent_rule, ite_intro_rule, and_pos_rule]
val is_SH_trivial = member (op =) [not_not_rule, contract_rule]

fun is_skolemization_step (Lethe_Replay_Node {id, ...}) = is_skolemization id

val trace = true
datatype debugging_verbosity = low | middle | high
fun debug_to_int low = 0 |
    debug_to_int middle = 1 |
    debug_to_int high = 2
val debug = true
val debugging_level = high (*0 low, 1 middle, 2 high verbosity*)

fun lproof_trace_msg cond (x : unit -> 'a) = if cond then ignore(x ()) else ()
fun lptrace v = (lproof_trace_msg trace v; v)
fun debug_lptrace i v = (lproof_trace_msg (debug andalso debug_to_int i <= debug_to_int debugging_level) v; v)


fun number_of_steps [] = 0
  | number_of_steps ((Lethe_Replay_Node {subproof = (_, _, _, subproof), ...}) :: pf) =
      1 + number_of_steps subproof + number_of_steps pf

fun node_of p cx =
  ([], cx)
  ||>> `(with_fresh_names (term_of p))
  |>> snd

fun node_of_term p cx = (term_of p cx)
 
fun synctactic_var_subst old_name new_name (u $ v) =
    (synctactic_var_subst old_name new_name u $ synctactic_var_subst old_name new_name v)
  | synctactic_var_subst old_name new_name (Abs (v, T, u)) =
    Abs (if String.isPrefix old_name v then new_name else v, T,
      synctactic_var_subst old_name new_name u)
  | synctactic_var_subst old_name new_name (Free (v, T)) =
     if String.isPrefix old_name v then Free (new_name, T) else Free (v, T)
  | synctactic_var_subst _ _ t = t

fun syntactic_rew_in_lhs_subst old_name new_name (Const(\<^const_name>\<open>HOL.eq\<close>, T) $ t1 $ t2) =
     Const(\<^const_name>\<open>HOL.eq\<close>, T) $ synctactic_var_subst old_name new_name t1 $ t2
  | syntactic_rew_in_lhs_subst old_name new_name (Const(\<^const_name>\<open>Trueprop\<close>, T) $ t1) =
     Const(\<^const_name>\<open>Trueprop\<close>, T) $ (syntactic_rew_in_lhs_subst old_name new_name t1)
  | syntactic_rew_in_lhs_subst _ _ t = t


(* proof parser *)

local

         (*replace the name binding by the constant instead of the full term in order to reduce
           the size of the generated terms and therefore the reconstruction time*)
  fun parse_fun_def (SMTLIB.S [SMTLIB.Sym "define-fun", SMTLIB.Sym id,  _, typ,
           SMTLIB.S (SMTLIB.Sym "!" :: t :: [SMTLIB.Key _, SMTLIB.Sym name])]) cx =
         let val (l, cx) = (fst oo SMTLIB_Proof.extract_and_update_name_bindings) t cx
            |> apsnd (SMTLIB_Proof.update_name_binding (name, SMTLIB.Sym id))
         in
            (mk_raw_node (id ^ skolem_def) skolem_def [(SMTLIB.S [SMTLIB.Sym id, typ,l])] [] [] []
              (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym id, l]) [], cx)
         end
      | parse_fun_def (SMTLIB.S [SMTLIB.Sym "define-fun", SMTLIB.Sym id,  _, typ, SMTLIB.S l]) cx =
         let val (l, cx) = (fst oo SMTLIB_Proof.extract_and_update_name_bindings) (SMTLIB.S l) cx
         in
           (mk_raw_node (id ^ skolem_def) skolem_def [(SMTLIB.S [SMTLIB.Sym id, typ,l])] [] [] []
              (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym id, l]) [], cx)
         end
      | parse_fun_def t _ = raise Fail ("unrecognized Lethe proof " ^ \<^make_string> t)


in



datatype step_kind = ASSUME | ANCHOR | NO_STEP | NORMAL_STEP | SKOLEM

fun parse_raw_proof_steps (curr_anchor_id : string option) (smtlib_lines : SMTLIB.tree list) (cx : name_bindings):
     (raw_lethe_node list * SMTLIB.tree list * name_bindings) =
  let
    fun step_kind "anchor" = ANCHOR
      | step_kind "assume" = ASSUME
      | step_kind "step" = NORMAL_STEP
      | step_kind "define-fun" = SKOLEM
      | step_kind kind = raise throw_lethe_ex ("step_kind unrec: " ^ @{make_string} kind)

    fun split_step [] = (NO_STEP, SMTLIB.S [], [])
      | split_step ((step as SMTLIB.S (SMTLIB.Sym kind :: _)) :: remaining_steps) =
          (step_kind kind, step, remaining_steps)
      | split_step steps = (@{print}("steps",steps);raise throw_lethe_ex ("malformed step: " ^ @{make_string} steps))

    fun get_id (SMTLIB.S ((SMTLIB.Sym _) :: (SMTLIB.Sym id) :: l)) = (id, l)
      | get_id t = raise throw_lethe_ex ("unrecognized Lethe proof " ^ \<^make_string> t)
    fun get_id_cx (t, cx) = get_id t ||> rpair cx

    fun parse_prems (SMTLIB.Key "premises" :: SMTLIB.S prems :: l, cx) =
        let
          val unwrap_id =
            fn (SMTLIB.Sym id) => id |
            _ => raise throw_lethe_ex ("malformed premises "  ^ \<^make_string> prems)
        in (SOME (map unwrap_id prems), (l, cx)) end
      | parse_prems (l, cx) = (NONE, (l, cx))
    fun parse_rule (SMTLIB.Key "rule" :: SMTLIB.Sym rule_name :: l, cx) = (rule_name, (l, cx))
      | parse_rule t = raise throw_lethe_ex ("unrecognized Alethe proof rule " ^ \<^make_string> t)
    fun parse_anchor_step (SMTLIB.S (SMTLIB.Sym "anchor" :: SMTLIB.Key "step" :: SMTLIB.Sym id :: l), cx) = (id, (l, cx))
      | parse_anchor_step t = raise Fail ("unrecognized Lethe proof " ^ \<^make_string> t)
    fun parse_args (SMTLIB.Key "args" :: args :: l, cx) =
          let val ((args, cx), _) = SMTLIB_Proof.extract_and_update_name_bindings args cx
              val args = args |> (fn SMTLIB.S args => args | _ => raise throw_lethe_ex ("malformed argument"))
          in (args, (l, cx)) end
      | parse_args (l, cx) = ([], (l, cx))

    fun parse_and_clausify_conclusion (SMTLIB.S (SMTLIB.Sym "cl" :: []) :: l, cx) =
          (SMTLIB.Sym "false", (l, cx))
      | parse_and_clausify_conclusion (SMTLIB.S (SMTLIB.Sym "cl" :: concl) :: l, cx) =
          let val (concl, cx) = fold_map (fst oo SMTLIB_Proof.extract_and_update_name_bindings) concl cx
          in (SMTLIB.S (SMTLIB.Sym "or" :: concl), (l, cx)) end
      | parse_and_clausify_conclusion t = raise Fail ("unrecognized Lethe proof " ^ \<^make_string> t)

    fun rotate_pair (a, (b, c)) = ((a, b), c)
    val parse_normal_step =
        get_id_cx
        ##> parse_and_clausify_conclusion
        #> rotate_pair
        ##> parse_rule
        #> rotate_pair
        ##> parse_prems
        #> rotate_pair
        ##> parse_args
        #> rotate_pair

(*TODO: merge*)
    fun to_raw_node subproof ((((id, concl), rule), prems), step_args) =
        mk_raw_node id rule step_args [] (the_default [] prems) [] concl subproof

   fun to_raw_node2 subproof ((((id, concl), rule), prems), context_assignment) = 
        mk_raw_node id rule [] context_assignment (the_default [] prems) [] concl subproof

    fun closes_subproof NONE _ = false
      | closes_subproof (SOME id) step = step |> get_id |> fst |> (curry (op =) id)
  in
    case split_step smtlib_lines of
        (NO_STEP, _, _) => ([],[], cx)
      | (NORMAL_STEP, step, rest) =>
          if closes_subproof curr_anchor_id step
          then ([], smtlib_lines, cx)
          else
            let
             (*ignores content of "discharge": Isabelle is keeping track of it via the context*)
              val (step', (_, cx)) =  (step, cx)
                |> parse_normal_step
                |>>  (to_raw_node [])
              val (rp, rl, cx) = parse_raw_proof_steps curr_anchor_id rest cx
            in (step' :: rp, rl, cx) end
      | (ASSUME, step, rest) =>
          let
            val (id, t) = step |> get_id ||> the_single
            val ((t, cx), _) = SMTLIB_Proof.extract_and_update_name_bindings t cx
            val s = mk_raw_node id input_rule [] [] [] [] t []
            (*Recursive call to parse rest of the steps.*)
            val (rstep, rrest, cx) = parse_raw_proof_steps curr_anchor_id rest cx
          in (s :: rstep, rrest, cx) end
      | (ANCHOR, p, l) =>
          let
            val (anchor_id, (anchor_args, (_, cx))) = (p, cx) |> (parse_anchor_step ##> parse_args)
            val (subproof, discharge_step :: remaining_proof, cx) = parse_raw_proof_steps (SOME anchor_id) l cx
            val (curss, (_, cx)) = parse_normal_step (discharge_step, cx)
            val s = to_raw_node2 subproof (fst curss, anchor_args)
            val (rp, rl, cx) = parse_raw_proof_steps curr_anchor_id remaining_proof cx
          in (s :: rp, rl, cx) end
      | (SKOLEM, p, l) =>
          let
            val (s, cx) = parse_fun_def p cx
            val (rp, rl, cx) = parse_raw_proof_steps curr_anchor_id l cx
          in (s :: rp, rl, cx) end
  end
end

(* context "arguments"
bind,onepoint: fixed_vars list, mapping list
sko_ex, sko_forall, let: mapping list
subgoal: keine Argumente
*)
val anchor_rules = ["bind","sko_forall","sko_ex","let","onepoint","subproof"]
val is_anchor_rule = member (op =) anchor_rules

val context_assignment_rules = ["bind","sko_forall","sko_ex","let","onepoint"]
val allows_context_assignment = member (op =) context_assignment_rules
(*forall_inst has mapping *)

val step_args_rules = ["rare_rewrite","la_generic","forall_inst"] @ [skolem_def]
val allows_step_args = member (op =) step_args_rules


local

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

fun skolems_introduced_by_rule [] = [] |
   skolems_introduced_by_rule bds =
  fold (fn (SMTLIB.S [SMTLIB.Sym "=", _, SMTLIB.Sym y]) => curry (op ::) y
              | x => (@{print} x; fn x => x)) bds [] 


(*FIXME there is probably a way to use the information given by onepoint*)
(*Get substituted variable from a context assignment that is a mapping*)
fun substituted_vars_by_rule _ "bind" bds = extract_symbols bds
  | substituted_vars_by_rule cx "onepoint" bds = extract_qnt_symbols cx bds
  | substituted_vars_by_rule _ "sko_forall" bds = bds
    |> map (fn (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym x, SMTLIB.Sym y], typ) => [([x,y], typ)])
    |> flat
  | substituted_vars_by_rule _ "sko_ex" bds = extract_symbols_map bds
  | substituted_vars_by_rule _ "__skolem_definition" [(SMTLIB.S [SMTLIB.Sym x, typ, _], _)] = [([x], SOME typ)]
  | substituted_vars_by_rule _ "__skolem_definition" [(SMTLIB.S [_, SMTLIB.Sym x, _], _)] = [([x], NONE)]
  | substituted_vars_by_rule _ "let" [(SMTLIB.S [_, SMTLIB.Sym x, y], _)] = [([x], NONE)]
  | substituted_vars_by_rule _ _ _ = []

end

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

fun normalized_input_rule_name id = if can SMTLIB_Interface.role_and_index_of_assert_name id then normalized_input_rule else local_input_rule


fun is_assm_repetition id rule =
  rule = input_rule andalso can SMTLIB_Interface.role_and_index_of_assert_name id

fun extract_skolem ([SMTLIB.S [SMTLIB.Sym var, typ, choice]]) = (var, typ, choice)
  | extract_skolem t = raise Fail ("fail to parse type" ^ @{make_string} t)

(* The preprocessing takes care of:
     1. unfolding the shared terms
     2. extract the declarations of skolems to make sure that there are not unfolded
TODO: Update this comment
*)
fun preprocess compress step =
  let
    fun expand_assms cs =
      map (fn t => case AList.lookup (op =) cs t of NONE => t | SOME a => a)

    (*
      For legacy versions of veriT. If argument list contains (x S) and (= y x) change the latter
      to (= (y S) x). It is possible to have argument lists such as (x S) (x T) (= y x), so we need
      the most up-to-date sort of x
    *)
    fun match_typing_arguments _ [] = [] |
      (*1. Sorted variable found (v0 S) *)
      match_typing_arguments tab ((x as (SMTLIB.S [SMTLIB.Sym x1, y2]))::xs) = 
        x :: match_typing_arguments (Symtab.update (x1,y2) tab) xs  |
      (*2. Mapping without type found (:= v0 v1) *)
      match_typing_arguments tab ((x as (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.Sym x1, t]))::xs) =
        (case Symtab.lookup tab x1 of
          NONE => x :: match_typing_arguments tab xs (*Nothing to be done we have to try later to add the type*) |
          (SOME y2) => (SMTLIB.S [SMTLIB.Sym "=", (SMTLIB.S [SMTLIB.Sym x1, y2]), t]) :: match_typing_arguments tab xs) |
      (*3. All other cases*)
      match_typing_arguments tab (x::xs) = x :: match_typing_arguments tab xs

      fun normalize_name name = if String.explode name |> hd |> Char.isUpper  then "isabelle_internal_" ^ name  else name
      fun smtlib_types t = (t="Bool") orelse (t="Int") orelse (t="Real") orelse (t="String")
      fun normalize_tree (SMTLIB.Sym s) = if smtlib_types s then SMTLIB.Sym s else SMTLIB.Sym (normalize_name s) |
          normalize_tree (SMTLIB.S xs) = SMTLIB.S (map normalize_tree xs) |
          normalize_tree x = x

    (*TODO: Figure out what remap_assms does give comment or better name*)
    fun preprocess (Raw_Lethe_Node {id, rule, step_args, context_assignments, prems, concl, subproof, ...}) (cx : ('a list, 'b) context, remap_assms)  =
      let
        val ctxt = #ctxt cx
        val _ = debug_lptrace high (fn () => \<^print> ("preprocessing started for rule: ", id))
        (* If we check external proofs we need to change term names starting with an upper character
           since this is not allowed in Isabelle *)
        (* I am not too happy about this since it works on all expressions, I want to change this maybe able do in smtlib_proof? *)
        val step_args = if Config.get ctxt SMT_Config.check_external then (map normalize_tree step_args) else step_args
        val context_assignments = if Config.get ctxt SMT_Config.check_external then (map normalize_tree context_assignments) else context_assignments
        val concl = if Config.get ctxt SMT_Config.check_external then normalize_tree concl else concl

        (* Sanity checks *)
        val context_assignments =
          if context_assignments <> [] andalso not (allows_context_assignment rule)
          then
            let val _ = (SMT_Config.verit_msg ctxt) (fn () =>
              \<^print> ("found step with context annotation. Only some of the steps that close a " ^
                      "subproof should have them. Ignoring context argument. Kind is: ", rule))
            in [] end
          else context_assignments
        val step_args =
          if step_args <> [] andalso not (allows_step_args rule)
          then
            let val _ = (SMT_Config.verit_msg ctxt) (fn () =>
              \<^print> ("found step that should not have args but has." ^
                      "Ignoring args. Kind is: ", rule))
            in [] end
          else step_args

        val stripped_context_assignments =
          if context_assignments = [] then []
          else
            let
              val _ = debug_lptrace high (fn () => \<^print> ("rule with context assignment found: ", context_assignments))
              val _ = debug_lptrace high (fn () => \<^print> ("... change assignment symbols (:=) to equalities (=)"))
              val _ = debug_lptrace high (fn () => \<^print> ("... add type information syntactically (for legacy versions of veriT)"))
              val context_assignments'=
                context_assignments
                |> map (fn SMTLIB.S [SMTLIB.Key "=", x, y] => SMTLIB.S [SMTLIB.Sym "=", x, y] | x => x)
                |> match_typing_arguments Symtab.empty
              val _ = debug_lptrace high (fn () => \<^print> ("New context assignments: ", context_assignments'))
            in
             context_assignments'
            end


        val stripped_step_args =
           if rule = forall_inst_rule
           then step_args |> map (fn SMTLIB.S [SMTLIB.Key "=", x, y] => SMTLIB.S [SMTLIB.Sym "=", x, y] | x => x)
           else step_args

        val declarations =
          if rule = skolem_def
          then
            stripped_step_args
            (*|> lethe_proof_parsing_tracing ctxt "... found skolem definition. Transform arguments. "*)
            |> trace ? @{print}
            |> extract_skolem
            |> single
            (*|> lethe_proof_parsing_tracing ctxt "... extracted skolems from skolem definition"*)
            |> trace ? @{print}
            |> map (fn (name, _, choice) => (name, choice)) (*TODO: Could this not be part of extract_skolem? Does not seem to be used anywhere else *)
          else []


        (*val _ = if subproof <> [] then lethe_proof_parsing_trace ctxt (fn () => \<^print> ("... process subproof")) else ()*)
        val (subproof, (cx, _)) = fold_map preprocess subproof (cx, remap_assms) |> apfst flat

        (*Or regeln machen nichts in Isabelle, deshalb werden sie rausgenommen, deshalb muss jede die eine premise hat die eine or regel hat
          ersetzt werden.*)
        (*Ist nur fuer den if case noetig, restrukturiere code*)
        val remap_assms = 
          if rule = "or" andalso compress
          then
           let val _ = debug_lptrace low (fn () => \<^print> ("Compress proof by skipping current 'or' step")) in (id, hd prems) :: remap_assms end
          else remap_assms

        val remap_prems =
          if compress
          then
           let val _ = debug_lptrace low (fn () => \<^print> ("If any premise of the current step has been skipped the premise is updated to that premise's premise"))
           in expand_assms remap_assms prems end
          else prems

      in
        if rule = "or" andalso compress
        then 
          ([], (cx, remap_assms))
        else ([mk_raw_node id rule stripped_step_args stripped_context_assignments remap_prems declarations concl subproof],
          (cx, remap_assms))
      end
  in preprocess step end

fun filter_split _ [] = ([], [])
  | filter_split f (a :: xs) =
     (if f a then apfst (curry op :: a) else apsnd (curry op :: a)) (filter_split f xs)


fun extract_types_of_context_assgnmts [SMTLIB.S [var, typ, t as SMTLIB.S [SMTLIB.Sym "choice", _, _]]] rule_name =
    (SMTLIB.S [var, typ, t], SOME typ)
    |> single (*TODO*)
 | extract_types_of_context_assgnmts [SMTLIB.S [var, t as SMTLIB.S [SMTLIB.Sym "choice", SMTLIB.S [SMTLIB.S [_, typ]], _]]] rule_name =
    (SMTLIB.S [var, typ, t], SOME typ)
    |> single (*TODO*)
 | extract_types_of_context_assgnmts xs rule_name =
  let
    fun extract_types_of_context_ass (mapping as SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [var, typ], t]) = (mapping, SOME typ)
    | extract_types_of_context_ass (fixed as SMTLIB.S [var, typ]) = (fixed, SOME typ)
    | extract_types_of_context_ass (SMTLIB.S [eq as SMTLIB.Sym "=", var as SMTLIB.Sym _, t as SMTLIB.S [SMTLIB.Sym "choice", SMTLIB.S [SMTLIB.S [_, typ]], _]]) =
       (SMTLIB.S [eq, var, t], SOME typ) (*TODO*)
    | extract_types_of_context_ass t = (t, NONE)
  in
    xs
    |> map extract_types_of_context_ass (*TODO: Could do without helper function, lets see where this goes*)
  end

(*Probably merge these three, add types whenever possible *)

fun extract_vars cx (SMTLIB.S [SMTLIB.Sym "=", (SMTLIB.S [SMTLIB.Sym x1, y2]), t]) = (x1, (Free (x1, type_of cx y2))) |
  extract_vars cx (SMTLIB.S [SMTLIB.Sym x1, y2]) = (x1,  (Free (x1, type_of cx y2))) |
  extract_vars _ _ = raise throw_lethe_ex "Not a valid context assignment"

fun split_context_assignment cx [] (fixed : (string * term) list) substituted substitute = (fixed,substituted,substitute) |
    split_context_assignment cx (SMTLIB.S [SMTLIB.Sym x, t] :: xs) (fs : (string * term) list) ss ts = 
      split_context_assignment cx xs ((x, (Free (x, type_of cx t)))::fs) ss ts |
    split_context_assignment cx (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym x, t], y] :: xs) fs ss ts = 
      split_context_assignment cx xs fs ((x, (Free (x, type_of cx t)))::ss) ((y,type_of cx t)::ts) |
    split_context_assignment _ _ _ _ _ = raise throw_lethe_ex ("context assignment malformed ")

fun split_context_ass cx context_assignments = split_context_assignment cx context_assignments [] [] []


fun collect_skolem_defs (Raw_Lethe_Node {rule, subproof = subproof, context_assignments, ...}) =
  (if is_skolemization rule then map get_skolem_def_id (skolems_introduced_by_rule context_assignments) else []) @
  flat (map collect_skolem_defs subproof)

val desymbolize = Name.desymbolize (SOME false) o perhaps (try (unprefix "?"))
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

  fun process_context_assignments context_assignments cx = 
    let
      (*val _ = lethe_proof_parsing_trace ctxt (fn () => \<^print> ("... process context assignments ", context_assignments))*)
    
      val (fixed_vars,substituted_vars,substitute_terms) = split_context_ass cx context_assignments
          (*  |> lethe_proof_parsing_tracing ctxt "... split up context assignments (fixed variables, substituted variables, substitute terms)"
            |> trace ? @{print}*)

      fun not_already_bound cx t = SMTLIB_Proof.lookup_binding cx (fst t) = None

      val (shadowing_vars, rebound_lhs_vars) =
        substituted_vars @ fixed_vars
        |> filter_split (not_already_bound cx)
        (*|>> lethe_proof_parsing_tracing ctxt "... new variables "
        |>> trace ? @{print}
        ||> lethe_proof_parsing_tracing ctxt "... already bound variables "
        ||> trace ? @{print}*)

      (*Urspruenglich war fixed variable immer ein neuer Name*)
      (*TODO: Mache Schleife um zu sehen ob Name schon vergeben (not_already_bound), sonst fuege _isabelle1 hinzu, suche nochmal*)
      (*Sollte nicht wirklich ein Problem sein*)
      val new_variable_names = fold (fn t => curry (op ::) (t, t ^ "_isabelle")) (map fst rebound_lhs_vars) []
          (*  |> lethe_proof_parsing_tracing ctxt "... mapping between new variables introduced in the anchor and their original names"
            |> trace ? @{print}*)

    in ((shadowing_vars, rebound_lhs_vars, substitute_terms), new_variable_names) end


    fun postprocess (Raw_Lethe_Node {id, rule, step_args, context_assignments, prems, declarations, concl, subproof}) (cx, new_variable_names) =
    let
     (* val _ = lethe_proof_parsing_trace ctxt (fn () => \<^print> ("postprocessing started for rule: ", id))*)
      val anchor_rule = is_anchor_rule rule

     (* Update proof context *) 
      val cx = if rule <> skolem_def then cx else
        let
          fun declared_csts [SMTLIB.S [SMTLIB.Sym x, typ,_]] = (x, Term (Free (x, type_of cx typ)))
            | declared_csts t = (@{print}t;raise throw_lethe_ex ("unrecognized skolem_definition " ^ @{make_string} t))
          val globally_bound_vars = declared_csts step_args
            (*|> lethe_proof_parsing_tracing ctxt "... extracted globally bound vars from skolem definition "
            |> trace ? @{print}*)
        in update_binding globally_bound_vars cx end
    
     (* Preprocess context arguments *) 
     val ((shadowing_vars,rebound_lhs_vars,substitute_terms),new_variable_names) =
        (if not anchor_rule then (([],[],[]),[])
         else process_context_assignments context_assignments cx)
         ||> (curry (op @)) new_variable_names

      (* Functions for rewriting terms and the context *)
      val subproof_rewriter = fold (fn (t, t') => syntactic_rew_in_lhs_subst t t') new_variable_names
      fun add_bound_variables_to_cx ts cx = fold update_binding ts cx
      val unsk_and_rewrite = SMTLIB_Isar.unskolemize_names ctxt o subproof_rewriter

      (* Process conclusion *)
     (* val _ = lethe_proof_parsing_trace ctxt (fn () => \<^print> ("... transform conclusion ", concl))*)
      val (cx',termified_concl) =
        let
          val ((termified_concl, extra_var), cx') = node_of concl cx
          (*val _ = lethe_proof_parsing_trace ctxt (fn () => \<^print> ("... transformed conclusion into Isabelle term", termified_concl))*)
          val _ = if extra_var <> []
            then raise ERROR ("found dangling variable (s) " ^ (@{make_string} extra_var) ^
              " in concl " ^ (@{make_string} concl) ^ " of step" ^ id) else ()
          val termified_concl = unsk_and_rewrite termified_concl
             (*|> lethe_proof_parsing_tracing ctxt "... rewrite conclusion with new variable names introduced by prior anchors"
             |> trace ? @{print}*)
        in (cx',termified_concl) end

      (* Process subproof *)
      val alpha_conversion = rule = "bind" andalso is_alpha_renaming termified_concl
      val (subproof_cx,new_subproof) = 
        if not anchor_rule then (cx,[])
        else
          let
           (* val _ = lethe_proof_parsing_trace ctxt (fn () => \<^print> ("... transform subproof "))*)
            val subproof_cx =
              add_bound_variables_to_cx (map (fn (a,b) => (a,Term b)) (shadowing_vars @ rebound_lhs_vars)) cx
              (*|> lethe_proof_parsing_tracing' ctxt "... add new variables to context "
              |> trace ? @{print}*)
            val can_remove_subproof =
              compress andalso (is_skolemization rule orelse alpha_conversion)
            (* |> lethe_proof_parsing_tracing ctxt "... does the subproof only rename variables and therefore can be removed? "
             |> trace ? @{print}*)
            val new_subproof = (if can_remove_subproof then [] else subproof)

            (*TODO: Moved this inside the let. Make sure there are no other rules than anchor rules using subproof atm*)
            val (new_subproof : lethe_replay_node list, _) =
              fold_map postprocess new_subproof (subproof_cx, new_variable_names)
            (*  |> new_subproof <> [] ? lethe_proof_parsing_tracing ctxt ("Finished postprocessing subproofs. Returning to rule with id"  ^ @{make_string} id)*)
         in (subproof_cx,new_subproof) end


      (* Process step and context arguments *)
      val normalized_step_args = if not (allows_step_args rule) orelse rule = skolem_def then [] else
        let
          val (termified_step_args,_) = fold_map node_of_term step_args cx
          val normalized_step_args = map unsk_and_rewrite (map subproof_rewriter termified_step_args)
             (*|> lethe_proof_parsing_tracing ctxt ("Termified and normalized steps args: ")
             |> trace ? @{print}*)
        in normalized_step_args end

     (* We are not sure how step args and context args play together. Can step args use new variables?*)
      (*Original arguments still have the old names, so we need to use the right context.*)
     val context_ass_cx =
        add_bound_variables_to_cx (map (fn (a,b) => (a,Term b)) (shadowing_vars @ rebound_lhs_vars)) cx
         (*|> lethe_proof_parsing_tracing ctxt ("New context for anchor arguments")
         |> trace ? @{print}*)

      val normalized_context_ass = if not (allows_context_assignment rule) then [] else
        let
          fun rm_types [] = [] |
              rm_types (SMTLIB.S [SMTLIB.Sym v,typ]::xs) = SMTLIB.Sym v::rm_types xs |
              rm_types (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym v,typ],t]::xs) = SMTLIB.S [SMTLIB.Sym "=",SMTLIB.Sym v,t]::rm_types xs

          val (termified_context_ass, _) = fold_map node_of (rm_types context_assignments) context_ass_cx |> apfst (map fst)
            (*|> lethe_proof_parsing_tracing ctxt ("termified_context_ass")
            |> trace ? @{print}*)

          val normalized_context_ass = map unsk_and_rewrite (map subproof_rewriter termified_context_ass)
             (*|> lethe_proof_parsing_tracing ctxt ("Termified and normalized normalized_context_ass: ")
             |> trace ? @{print}*)

        in normalized_context_ass end

      (* add arguments *)
      val tactic_args = case rule of
        "forall_inst" =>
         let
           (* special handling: forall_inst *)
           val raw_insts = insts_of_forall_inst rule step_args
           fun termify_term (x, t) cx = let val (t, cx) = term_of t cx in ((x, t), cx) end
           val (termified_inst, _) = fold_map termify_term raw_insts subproof_cx
           val insts = Symtab.empty
            |> fold (fn (x, t) => fn insts => Symtab.update_new (desymbolize x, t) insts) termified_inst
            |> Symtab.map (K unsk_and_rewrite)
         in SOME (Insts insts) end |
        "__skolem_definition" =>
         let
           (* special handling: skolem *)
           fun termify_term (x, t) cx = let val (t, cx) = term_of t cx in ((x, t), cx) end
           val (declarations, _) = fold_map termify_term declarations cx
            |> apfst (map (apsnd unsk_and_rewrite))
         in SOME (Declarations (declarations)) end |
        "sko_exists" =>
       let
          val skolems_of_subproof = (if compress andalso is_skolemization rule
             then flat (map collect_skolem_defs subproof) else []) (*TODO*)
          val skolem_defs = (map (get_skolem_def_id o (fn SMTLIB.Sym x => x) o fst) substitute_terms)

         in SOME (Sko_Def_Prems (skolems_of_subproof,skolem_defs)) end |
        "sko_forall" =>
       let
          val skolems_of_subproof = (if compress andalso is_skolemization rule
             then flat (map collect_skolem_defs subproof) else []) (*TODO*)
          val skolem_defs = (map (get_skolem_def_id o (fn SMTLIB.Sym x => x) o fst) substitute_terms)

         in SOME (Sko_Def_Prems (skolems_of_subproof,skolem_defs)) end |
         _ => NONE

      (* fix assumptions *)
       val assms_from_subproof =
         (if rule = subproof_rule then extract_assumptions_from_subproof new_subproof else [])

      (* fix premises *)
      val normalized_premises =                                                       
        prems @
        (if is_assm_repetition id rule then [id] else []) @
        (if anchor_rule then id_of_last_step new_subproof else [])
        @ (map (get_skolem_def_id o (fn SMTLIB.Sym x => x) o fst) substitute_terms) (*TODO: Not sure yet if I should add them here or in Sko_Def_Prems*)
        (*|> lethe_proof_parsing_tracing ctxt ("New set of premises ")
        |> trace ? @{print}*)

      (* fix rule *)
      val normalized_rule =
        if rule = input_rule
        then normalized_input_rule_name id |> (if compress andalso alpha_conversion then K "refl" else I) (*TODO: Make the compression part better better, maybe move into let above*)
         (* |> lethe_proof_parsing_tracing' ctxt ("New rule: " )
          |> trace ? @{print}*)
        else rule

      val step =
        mk_replay_node id normalized_rule normalized_step_args normalized_context_ass
        normalized_premises termified_concl
        ((map (fn (a,b) => (a, fastype_of b)) (shadowing_vars @ rebound_lhs_vars)), [], assms_from_subproof, new_subproof)
        tactic_args
    in
       (step, (cx', new_variable_names))
    end
  in
    postprocess step (cx, [])
    |> (fn (step, (cx, _)) => (step, cx))
  end

fun combine_proof_steps ((step1 : lethe_replay_node) :: step2 :: steps) =
      let
        val (Lethe_Replay_Node {id = id1, rule = rule1, step_args = step_args1,
            context_assignments = context_assignment1, prems = prems1,
             concl = concl1,
            subproof = (bound_sub1, assms_sub1, assms_extra1, subproof1),args = args1}) = step1
        val (Lethe_Replay_Node {id = id2, rule = rule2, step_args = step_args2,
            context_assignments = context_assignment2, prems = prems2,
            concl = concl2,
            subproof = (bound_sub2, assms_sub2, assms_extra2, subproof2),args = args2}) = step2
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
          mk_replay_node id2 theory_resolution2_rule step_args2 context_assignment2 (filter_out (curry (op =) id1) prems2)
             concl2
            (bound_sub2, assms_sub2, assms_extra2, combine_proof_steps subproof2) args2 ::
          combine_proof_steps steps
        else
          mk_replay_node id1 rule1 step_args1 context_assignment1 prems1
             concl1
            (bound_sub1, assms_sub1, assms_extra1, combine_proof_steps subproof1) args1 ::
          combine_proof_steps (step2 :: steps)
      end
  | combine_proof_steps steps = steps


val linearize_proof =
  let                          
    fun map_node_concl f (Lethe_Step {id, rule, prems, proof_ctxt, concl}) =
       mk_step id rule prems proof_ctxt (f concl)
    fun linearize (Lethe_Replay_Node {id = id, rule = rule, step_args = _, context_assignments = _, prems = prems,
        concl = concl,
        subproof = (bounds', assms, inputs, subproof), args = args}) =
      let
        fun mk_prop_of_term concl =
          concl |> fastype_of concl = \<^typ>\<open>bool\<close> ? curry (op $) \<^term>\<open>Trueprop\<close>
        fun remove_assumption_id assumption_id prems =
          filter_out (curry (op =) assumption_id) prems
        fun add_assumption assumption concl =
          \<^Const>\<open>Pure.imp for \<open>mk_prop_of_term assumption\<close> \<open>mk_prop_of_term concl\<close>\<close>
        fun inline_assumption assumption assumption_id
            (Lethe_Step {id, rule, prems, proof_ctxt, concl}) =
          mk_step id rule (remove_assumption_id assumption_id prems) proof_ctxt
            (add_assumption assumption concl)
        fun find_input_steps_and_inline [] = []
          | find_input_steps_and_inline
              (Lethe_Step {id = id', rule, prems, concl, ...} :: steps) =
            if rule = input_rule then
              find_input_steps_and_inline (map (inline_assumption concl id') steps)
            else
              mk_step (id') rule prems [] concl :: find_input_steps_and_inline steps

        val subproof = subproof
          |> flat o map linearize
          |> map (map_node_concl (fold add_assumption (assms @ inputs)))
          |> find_input_steps_and_inline
      in
        subproof @ [mk_step id rule prems [] concl] (*TODO: proof_ctxt*)
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
    fun remove_skolem_definitions (Lethe_Replay_Node {id = id, rule = rule, step_args = step_args,
        context_assignments = context_assignments,
         prems = prems,
         concl = concl,
        subproof = (vars, assms', extra_assms', subproof), args = args}) (prems_to_remove, skolems) =
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
      val step = (if skolem_step_to_skip orelse rule = skolem_def orelse trivial_step then []
        else mk_replay_node id rule step_args context_assignments prems concl
            (vars, assms', extra_assms', subproof) NONE (*TODO*)
          |> single)
      val defs = (if rule = skolem_def orelse trivial_step then id :: prems_to_remove
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
        parse_raw_proof_steps NONE smtlib_lines_without_qm SMTLIB_Proof.empty_name_binding

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
    fun node_to_step (Lethe_Step {id, rule, prems, concl, ...}) =
      mk_step id rule prems [] concl
  in
    ((*map node_to_step t*)[], ctxt_of env)
  end

fun parse_replay typs funs lines ctxt =
  let
    val (u, env) = import_proof_and_post_process typs funs lines ctxt
  in
    (u, ctxt_of env)
  end
end


end;
