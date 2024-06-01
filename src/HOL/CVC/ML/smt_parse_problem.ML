(*TODO: This file will eventually be integrated into other files (mainly lethe_smt_problem.ML)
 It only exists for easier development*)
(*TODO: Spoke to Mathias should be combined with lethe_smt_problem (which will be
renamed smt_parse_problem.*)
signature SMT_PARSE_PROBLEM =
sig
  exception SMT_PROBLEM_PARSE of string

  val parse: string -> Proof.context -> SMT_Translate.replay_data * int
end;

structure SMT_Parse_Problem : SMT_PARSE_PROBLEM =
struct

exception SMT_PROBLEM_PARSE of string

(*FIXME: I'd rather not do this this way. If we really need to put it in util class*)
(*TODO: Discussed with Mathias and this can be done in parse_raw_proof_steps (and parse_raw_problem_steps) or after but at least in 
lethe_proof. There I know what a type is and what not. Make separate function after so that we can deactivate it.*)
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




fun parse_assert cs ({context,typs,terms,ll_defs,rewrite_rules,assms}: SMT_Translate.replay_data, assms_nbr)
 =
let
  val smtlib_lines_without_qm = smtlib_lines_without_qm cs

  val (step,cx) =
   (fn ([step], _, cx) => (step,cx) | _ => raise ERROR "Problem could not be parsed")
   (Lethe_SMT_Problem.parse_raw_problem_steps [smtlib_lines_without_qm] SMTLIB_Proof.empty_name_binding 0)


  val (Lethe_Node.Raw_Lethe_Node {concl, ...} : Lethe_Node.raw_lethe_node) = step

  val cx = (SMTLIB_Proof.empty_context context typs terms)
  val t2 = SMTLIB_Proof.term_of concl cx |> fst

  val ([all_proof_prems'], sub_ctxt2) = Assumption.add_assumes (map (Thm.apply \<^cterm>\<open>Trueprop\<close> o Thm.cterm_of context) [t2]) context
 
 val assm = ((assms_nbr,SMT_Util.Axiom),all_proof_prems'):((int * SMT_Util.role) * thm)

in
 ({context = sub_ctxt2,typs = typs,terms = terms,ll_defs = ll_defs,rewrite_rules = rewrite_rules,
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
 ({context,typs: typ Symtab.table,terms,ll_defs,rewrite_rules,assms}: SMT_Translate.replay_data, assms_nbr) =
let
  fun extract_sort_symbol (SMTLIB.S [SMTLIB.Sym "declare-sort", SMTLIB.Sym typ, SMTLIB.Num 0]) = typ |
    extract_sort_symbol (SMTLIB.S [SMTLIB.Sym "declare-sort", SMTLIB.Sym _, SMTLIB.Num _]) =
      raise SMT_PROBLEM_PARSE "we currently only support sorts of arity 0." |
    extract_sort_symbol _ = raise SMT_PROBLEM_PARSE "declare-sort has wrong form"

  val sort_symbol = cs |> smtlib_lines_without_qm |> extract_sort_symbol                                                        
  val T = TFree (sort_symbol, ["HOL.type"])
  val context = Variable.declare_typ T context
  val typs = Symtab.update (sort_symbol, T) typs
in
 ({context = context,typs = typs,terms = terms,ll_defs = ll_defs,rewrite_rules = rewrite_rules,assms = assms}, assms_nbr)
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

fun parse_declare (cs: string list) ({context,typs,terms,ll_defs,rewrite_rules,assms}: SMT_Translate.replay_data, assms_nbr)
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

     val ctxt = SMTLIB_Proof.empty_context context typs terms
     val Ts = map (SMTLIB_Proof.type_of ctxt) (dest_seq tys)
     val T = SMTLIB_Proof.type_of ctxt ty

    val ([n'], ctxt') =  Variable.variant_fixes [name] context

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
    ({context = context, typs = typs,terms = terms,ll_defs = ll_defs,rewrite_rules = rewrite_rules,assms = assms}, assms_nbr)
  end

val ignore_commands =
 ["check-sat","check-sat_assuming","echo","get-assertions","get-assignment",
  "get-info","get-model","get-option","get-proof","get-unsat-assumptions","get-unsat-core",
  "get-value","set-option"]
val not_supported =
 ["declare-datatype","declare-datatypes","define-fun-rec","define-fun-recs",
  "exit","reset","reset_assertions","pop","push","set-logic","set-info"]
val supported_commands = ["assert","declare-sort","define-fun","declare-fun","define-sort"]

fun any_prefix list = 
 Scan.first (map (fn l => (fn str => if String.isPrefix l str then  (str,l) else Scan.fail "")) list)
 

fun read_command replay_data =
  $$ "("
  |-- Scan.many (curry (op =) " ")
  (*|-- Scan.ahead (fn cs => any_prefix ignore_commands cs)*)


fun read (cs as "("::"a"::"s"::"s"::"e"::"r"::"t"::" "::_) replay_data = 
      parse_assert cs replay_data
  | read (cs as "("::"d"::"e"::"c"::"l"::"a"::"r"::"e"::"-"::"f"::"u"::"n"::" ":: _) replay_data = parse_declare cs replay_data
  | read (cs as "("::"d"::"e"::"c"::"l"::"a"::"r"::"e"::"-"::"c"::"o"::"n"::"s"::"t"::" ":: _) replay_data = parse_declare cs replay_data
  | read (cs as "("::"d"::"e"::"c"::"l"::"a"::"r"::"e"::"-"::"s"::"o"::"r"::"t"::" ":: _) replay_data = parse_sort cs replay_data
  | read ("("::"s"::"e"::"t"::"-"::"i"::"n"::"f"::"o" :: _) replay_data = replay_data
  | read ("("::"s"::"e"::"t"::"-"::"l"::"o"::"g"::"i"::"c" :: _) replay_data = replay_data
  | read ("("::"c"::"h"::"e"::"c"::"k"::"-"::"s"::"a"::"t"::")" :: _) replay_data = replay_data
  | read ("("::"e"::"x"::"i"::"t"::")" :: _) replay_data = replay_data
  | read ("("::"g"::"e"::"t"::"-"::"p"::"r"::"o"::"o"::"f"::")":: _) replay_data = replay_data
  | read ("("::"s"::"e"::"t"::"-"::"o"::"p"::"t"::"i"::"o"::"n":: _) replay_data = replay_data
  | read x replay_data  = (warning ("found garbage when parsing SMT problem, ignoring: " ^ @{make_string} x); replay_data)


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
          None => raise ERROR ("expected opening parenthesis in line" ^ Int.toString(l)) |
          t => t
       end
end


fun lexer _ [] (Unfinished (s,i)) _ l_start =
    raise ERROR ("expected eof but last command (starting at line nr "
      ^ Int.toString(l_start) ^ ") was not closed. Counted " ^ Int.toString(i)
      ^ " opened but not closed parenthesis far. Part already parsed in: \n"
      ^ (rev s |> String.concat)) |
  lexer _ [] _ _ _ = [] | (*Finished lexing*)
  lexer ctxt (line::lines) uf l l_start =
    case lexer_add_line ctxt l line uf of
      Finished (s,[]) => (l_start,String.concat s) :: lexer ctxt lines None (l+1) (l+1) |
      Finished (_,s') => raise ERROR ("text after final closing parenthesis found! "
        ^ String.concat s') |
      Unfinished (s,s') => lexer ctxt lines (Unfinished ([" "] @ s,s')) (l+1) l_start |
      None => lexer ctxt lines uf (l+1) (l+1)

fun split_up_lines ctxt cs = lexer ctxt [cs] None 1 1 |> map snd

fun parse lines ctxt
 = snd (fold add_line (split_up_lines ctxt lines) (1,
 ({context = ctxt, typs = Symtab.empty, terms = Symtab.empty, ll_defs = [], rewrite_rules = [], assms = []}: SMT_Translate.replay_data, 0)))


end
