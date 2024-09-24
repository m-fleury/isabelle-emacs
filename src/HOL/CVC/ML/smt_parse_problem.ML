(*TODO: This file will eventually be integrated into other files (mainly alethe_smt_problem.ML)
 It only exists for easier development*)
(*TODO: Spoke to Mathias should be combined with alethe_smt_problem (which will be
renamed smt_parse_problem.*)
signature SMT_PARSE_PROBLEM =
sig
  exception SMT_PROBLEM_PARSE of string

  val parse: string list -> Proof.context -> SMT_Translate.replay_data
end;

structure SMT_Parse_Problem : SMT_PARSE_PROBLEM =
struct

exception SMT_PROBLEM_PARSE of string

(*FIXME: I'd rather not do this this way. If we really need to put it in util class*)
(*TODO: Discussed with Mathias and this can be done in parse_raw_proof_steps (and parse_raw_problem_steps) or after but at least in 
alethe_proof. There I know what a type is and what not. Make separate function after so that we can deactivate it.*)
fun normalize_name name = if String.explode name |> hd |> Char.isUpper  then "isabelle_internal_" ^ name  else name

fun smtlib_types t = (t="Bool") orelse (t="Int") orelse (t="BitVec") orelse (t="String")
fun normalize_tree (SMTLIB.Sym s) = if smtlib_types s then SMTLIB.Sym s else SMTLIB.Sym (normalize_name s) |
    normalize_tree (SMTLIB.S xs) = SMTLIB.S (map normalize_tree xs) |
    normalize_tree x = x


(*         let val (l, cx) = (fst oo SMTLIB_Proof.extract_and_update_name_bindings) t cx
            |> apsnd (SMTLIB_Proof.update_name_binding (name, SMTLIB.Sym id))
         in*)

(*TODO: MAKE SURE REMOVE_PATTERN is done after SMTLIB_Proof.extract_and_update_name_bindings *)
(*!named in problem can be used in proof! \<rightarrow> ASK CESARE if this is really the case*)
(*If so make sure same naming binding is used*)
(*TODO: Merge*)
(*Add named as define-funs*)
fun collect_named ((SMTLIB.S (SMTLIB.Sym "!" :: t :: [SMTLIB.Key "named", name])),collect) = collect_named (t,name::collect)
  | collect_named ((SMTLIB.S (x::xs)),collect) =
    let
     val (x',names) = collect_named (x,collect)
    in
     collect_named (SMTLIB.S (x'::xs),names)
    end
  | collect_named (t',collect) = (t',collect)

fun remove_pattern (SMTLIB.S (SMTLIB.Sym "!" :: t :: [SMTLIB.Key _, SMTLIB.S _])) = t
  | remove_pattern (SMTLIB.S xs) = SMTLIB.S (map remove_pattern xs)
  | remove_pattern p = p

(*This also removes pattern usually but I deleted it here for now*)
(*Should remove pattern, however make sure they are added before to name binding (steht im cx) *)
fun smtlib_lines_without_qm cs =
    implode cs
    |> single
    |> SMTLIB.parse
    |> normalize_tree




fun parse_assert cs ({ctxt,typs,terms,ll_defs,rewrite_rules,assms}: SMT_Translate.replay_data, assms_nbr)
 =
let
  val smtlib_lines_without_qm = smtlib_lines_without_qm cs

  val (assertion,name_bindings) =
   (fn ([step], _, cx) => (step,cx) | _ => raise ERROR "Problem could not be parsed")
   (Alethe_SMT_Problem.parse_raw_problem_steps [smtlib_lines_without_qm] SMTLIB_Proof.empty_name_binding 0)


  val (Alethe_Node.Raw_Alethe_Node {concl, ...} : Alethe_Node.raw_alethe_node) = assertion

  val cx = (SMTLIB_Proof.empty_context ctxt typs terms)
  val t2 = SMTLIB_Proof.term_of concl cx |> fst

  val ([all_proof_prems'], sub_ctxt2) = Assumption.add_assumes (map (Thm.apply \<^cterm>\<open>Trueprop\<close> o Thm.cterm_of ctxt) [t2]) ctxt
 
 val assm = ((assms_nbr,SMT_Util.Axiom),all_proof_prems'):((int * SMT_Util.role) * thm)

in
 ({ctxt = sub_ctxt2,typs = typs,terms = terms,ll_defs = ll_defs,rewrite_rules = rewrite_rules,
assms = assm :: assms}, assms_nbr+1)
end


(*Why is this now called Proof.context and not ctxt? Variable seems to use ctxt

Firm naming conventions:
   thy, thy', thy1, thy2: theory
   ctxt, ctxt', ctxt1, ctxt2: Proof.context
   context: Context.generic

I think this might be a mistake and I can rename it. Yes, replay data should be named ctxt

*)
fun parse_sort (cs: string list)                                              
 ({ctxt,typs: typ Symtab.table,terms,ll_defs,rewrite_rules,assms}: SMT_Translate.replay_data, assms_nbr) =
let
  fun extract_sort_symbol (SMTLIB.S [SMTLIB.Sym "declare-sort", SMTLIB.Sym typ, SMTLIB.Num 0]) = typ |
    extract_sort_symbol (SMTLIB.S [SMTLIB.Sym "declare-sort", SMTLIB.Sym _, SMTLIB.Num _]) =
      raise SMT_PROBLEM_PARSE "we currently only support sorts of arity 0." |
    extract_sort_symbol _ = raise SMT_PROBLEM_PARSE "declare-sort has wrong form"

  val sort_symbol = cs |> smtlib_lines_without_qm |> extract_sort_symbol                                                        
  val T = TFree (sort_symbol, ["HOL.type"])
  val context = Variable.declare_typ T ctxt
  val typs = Symtab.update (sort_symbol, T) typs
in
 ({ctxt = ctxt,typs = typs,terms = terms,ll_defs = ll_defs,rewrite_rules = rewrite_rules,assms = assms}, assms_nbr)
end


fun dest_name (SMTLIB.Sym name) = name
  | dest_name t = raise SMTLIB_Proof.SMTLIB_PARSE ("bad name", t)

fun dest_seq (SMTLIB.S ts) = ts
  | dest_seq t = raise SMTLIB_Proof.SMTLIB_PARSE ("bad Z3 proof format", t)

val desymbolize = Name.desymbolize (SOME false) o perhaps (try (unprefix "?"))

val fix_invalid_name =
  raw_explode
  #> map (fn "." => "__#__" | a => a) (*fudge replacement*)
  #> implode

fun parse_declare (cs: string list) ({ctxt,typs,terms,ll_defs,rewrite_rules,assms}: SMT_Translate.replay_data, assms_nbr)
   =
  let
    (*val _ = @{print} ("declaration", cs)*)
    val (n, tys, ty) = (*This also removes pattern usually but I deleted it here for now*)
      [implode cs]
      |> map single
      |> map SMTLIB.parse
      |> map normalize_tree
      |> (fn [SMTLIB.S [SMTLIB.Sym "declare-fun", n, tys, ty]] => (n, tys, ty) |
             [SMTLIB.S [SMTLIB.Sym "declare-const", n, ty]] => (n, SMTLIB.S [], ty))

     val raw_name = dest_name n
     val name = fix_invalid_name raw_name
     val name = normalize_name name

     val ctxt' = SMTLIB_Proof.empty_context ctxt typs terms
     val Ts = map (SMTLIB_Proof.type_of ctxt') (dest_seq tys)
     val T = SMTLIB_Proof.type_of ctxt' ty

    val ([n'], ctxt') =  Variable.variant_fixes [name] ctxt

    val t = Free (n', Ts ---> T)
    val terms = Symtab.update (raw_name, t) terms
(*|>  @{print} *)
(*
     val Ts = map (SMTLIB_Proof.type_of context) (dest_seq tys)
     val T = type_of cx ty
*)
   (*     in parse' ts (declare_fun name (Ts ---> T) cx) end*)
   (* val _ = @{print} ("declaration", (n, tys, ty))*)
  in
    ({ctxt = ctxt, typs = typs,terms = terms,ll_defs = ll_defs,rewrite_rules = rewrite_rules,assms = assms}, assms_nbr)
  end


fun !!! text scan =
  let
    fun err (syms, msg) = fn () =>
      text ^ (case msg of NONE => "" | SOME m => "\n" ^ m ());
  in Scan.!! err scan end;

val ignore_commands =
 ["check-sat","check-sat_assuming","echo","get-assertions","get-assignment",
  "get-info","get-model","get-option","get-proof","get-unsat-assumptions","get-unsat-core",
  "get-value","set-option","set-logic","exit","set-info"]

val not_supported =
 ["declare-datatype","declare-datatypes","define-fun-rec","define-fun-recs",
  "reset","reset_assertions","pop","push","define-fun"]

fun ignore _ replay_data = replay_data
fun is_not_supported keyword _ _ = raise SMT_PROBLEM_PARSE ("command not supported: " ^ keyword) 

fun method_for "assert" = parse_assert |
 method_for "declare-const" = parse_declare |
 method_for "declare-fun" = parse_declare |
 method_for "declare-sort" = parse_sort |
 method_for keyword =
   if Library.member (op =) not_supported keyword then is_not_supported keyword
   else if Library.member (op =) ignore_commands keyword then ignore
   else (warning ("found garbage when parsing SMT problem, ignoring: " ^ @{make_string} keyword); ignore)

val command_name_scanner = Scan.many1 (fn c => c <> " " andalso c <> ")")

val command_scanner =
  Scan.error (
    !!!  "Could not find opening parenthesis" ($$ "(")
    |-- (Scan.many (curry (op =) " ")) 
    |-- !!!  "Could not find name of command" command_name_scanner
  )

fun current_command cs replay_data =
let
  val command = command_scanner cs |> fst |> implode
in
  method_for command cs replay_data
end

datatype token = None | Unfinished of string list * int | Finished of string list * string list
exception TOKEN of string

fun parse_token s [] = s |
  parse_token None ("("::cs) = parse_token (Unfinished(["("],1)) cs |
  parse_token None (" "::cs) = parse_token None cs |
  parse_token None (")"::cs) = Scan.fail cs |
  parse_token None cs = Finished (Scan.catch Scan.many (fn c => c <> " " andalso c <> ")") cs) |
  parse_token (Unfinished (s,i)) ("("::cs) = parse_token (Unfinished ("("::s,i+1)) cs |
  parse_token (Unfinished (_,0)) (")"::_) = raise TOKEN("too many closing parenthesis") |
  parse_token (Unfinished (s,1)) (")"::xs) = Finished(rev (")"::s),xs) |
  parse_token (Unfinished (s,i)) (")"::cs) = parse_token (Unfinished (")"::s,i-1)) cs |
  parse_token (Unfinished (s,i)) (c::cs) = parse_token (Unfinished (c::s,i)) cs |
  parse_token _ _ = raise TOKEN("error parsing token")

fun lexer_add_line ctxt l line uf =
let
  val trimmed_lines = raw_explode line |> Library.trim (curry (op =) " ")
in
  case trimmed_lines of
    [] => uf | (*skip empty line*)
    (";"::_) => uf | (*skip comment line*)
    _ => 
      let (*non-empty line*)
        (* cut comments in line *)
        val sanitized_lines =
          Library.take (Library.find_index (curry (op =) ";") trimmed_lines) trimmed_lines |> Library.trim (curry (op =) " ")
        val token = parse_token uf sanitized_lines
      in
        case token of
          None => raise SMT_PROBLEM_PARSE ("expected opening parenthesis in line" ^ Int.toString(l)) |
          t => t
       end
end


fun lexer _ [] (Unfinished (s,i)) _ l_start =
    raise SMT_PROBLEM_PARSE ("expected eof but last command (starting at line nr "
      ^ Int.toString(l_start) ^ ") was not closed. Counted " ^ Int.toString(i)
      ^ " opened but not closed parenthesis far. Part already parsed in: \n"
      ^ (rev s |> String.concat)) |
  lexer _ [] _ _ _ = [] | (*Finished lexing*)
  lexer ctxt (line::lines) uf l l_start =
    case lexer_add_line ctxt l line uf of
      Finished (s,[]) => (l_start,String.concat s) :: lexer ctxt lines None (l+1) (l+1) |
      Finished (_,s') => raise SMT_PROBLEM_PARSE ("text after final closing parenthesis found! "
        ^ String.concat s') |
      Unfinished (s,s') => lexer ctxt lines (Unfinished ([" "] @ s,s')) (l+1) l_start |
      None => lexer ctxt lines uf (l+1) (l+1)

fun lex_lines ctxt cs = lexer ctxt cs None 1 1 |> map snd

fun parser_add_line line replay_data = current_command (raw_explode line) replay_data

fun mk_empty_replay_data ctxt =
 ({ctxt = ctxt, typs = Symtab.empty, terms = Symtab.empty, ll_defs = [], rewrite_rules = [], assms = []}: SMT_Translate.replay_data)

(*During parsing we populate a list, so we end up with the wrong order. This functions reverses it
to fix the order.*)
fun reverse_assms_order p =
  let 
    val {ctxt, typs, terms, ll_defs, rewrite_rules, assms} = p
  in {ctxt = ctxt, typs = typs, terms = terms, ll_defs = ll_defs, rewrite_rules = rewrite_rules,
    assms = rev assms} end

fun parse lines ctxt = 
  fst (fold parser_add_line (lex_lines ctxt lines) (mk_empty_replay_data ctxt, 0))
  |> reverse_assms_order

end
