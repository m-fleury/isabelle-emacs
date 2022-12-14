signature PARSE_REWRITE =
sig
  exception PARSE of int * string
  datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR

  datatype rewrite_tree = 
    Rule_Type of rule_type |
    Rule_Name of string |
    Par of SMTLIB.tree list | (*TODO: Should par be a SMTLIB.tree rather*)
    Precondition of SMTLIB.tree |
    Match of SMTLIB.tree |
    Target of SMTLIB.tree |
    Context_Expr of SMTLIB.tree |
    Rewrite_Rule of rewrite_tree list

  val parse_rewrites: string list -> rewrite_tree list
  val pretty_rewrite_tree: rewrite_tree -> Pretty.T
  val str_of: rewrite_tree list -> string
end;

structure PARSE_REWRITE: PARSE_REWRITE =
struct

exception PARSE of int * string

datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR
datatype unfinished = None | String of string | Symbol of string

  datatype rewrite_tree = 
    Rule_Type of rule_type |
    Rule_Name of string |
    Par of SMTLIB.tree list |
    Precondition of SMTLIB.tree |
    Match of SMTLIB.tree |
    Target of SMTLIB.tree |
    Context_Expr of SMTLIB.tree |
    Rewrite_Rule of rewrite_tree list


(*While rule type and rule name are parsed in directly the parameter and the expressions are
  given to SMTLIB.parse to efficiently reuse its capabilities:

E.g.,
 For: (define-rule bool-eq-refl ((t Bool)) (= t s) true

 SMTLIB.parse "(t Bool)" and SMTLIB.parse "(= t s) true" result in 

TODO: [[Sym "true", S [Sym "=", Sym "t", Sym "s"],
   S [S [Sym "t",
         Sym "Bool"]]]
*)

(*Parse name*)
fun read_rewrite_name l (c :: cs) None ts =
       if Symbol.is_ascii_blank c then read_rewrite_name l cs None ts (*Ignore leading space*)
       else read_rewrite_name l cs (String c) ts | (*Start of a word*)
    read_rewrite_name l (c :: cs) (String s) ts =
       if Symbol.is_ascii_blank c then (cs, None, (Rule_Name s :: ts)) (*End of a word*)
       else if c = "-" then read_rewrite_name l cs (String (s ^ "_")) ts (*Replace - in name by _ *)
       else read_rewrite_name l cs (String (s ^ c)) ts | (*Word continues*)
    read_rewrite_name l _ _ _ = raise PARSE (l, "rule name could not be parsed in")

local

fun get_smtlib_tree str : SMTLIB.tree list list
  = snd (SMTLIB.read_line 0 (implode str) SMTLIB.None [[]])

(*Call read_par in here?*)
(*TODO: Can there be nested parenthesis in the parameter list?*)
(*TODO: Should target, match etc also be parsed into different components?*)
(*((xs Bool :list) (b Bool) (ys Bool :list) (zs Bool :list))*)
(*TODO: Use unfinished*)
local
  fun rm_list_from_par (")"::cs) cs' _ = (cs, (")"::cs')) |
      rm_list_from_par ("("::cs) cs' false = rm_list_from_par cs ("("::cs') false |
      rm_list_from_par (":"::cs) cs' false = rm_list_from_par cs cs' true |
      rm_list_from_par (c::cs) cs' false = rm_list_from_par cs (c::cs') false |
      rm_list_from_par (_::cs) cs' true = rm_list_from_par cs cs' true

  fun rm_list_from_par_list (")"::cs) cs' l = (cs, cs') | (*very last parenthesis*) 
    rm_list_from_par_list ("("::cs) cs' l  = (*any other parenthesis is a par*)
      let 
        val (new_cs,current_par) = rm_list_from_par ("("::cs) [] false
        val par_as_smtlib = (hd (get_smtlib_tree (rev current_par)))
      in
        rm_list_from_par_list new_cs (par_as_smtlib @ cs') l
      end 
      |
    rm_list_from_par_list (" "::cs) cs' l = rm_list_from_par_list cs cs' l | (*delete spaces between pars*)
    rm_list_from_par_list _ _ l = raise PARSE (l, "error in parsing parameter list")

in
  fun parse_pars ("("::cs) l = 
let val (wth_par, parsed_par) = (rm_list_from_par_list cs [] l)
in
  (wth_par,Par parsed_par)
end

 |
      parse_pars _ l = raise PARSE (l, "parameter list needs to start with an opening parenthesis.")
end


(* [[Sym "t", Sym "s", Sym "="],
  [S [Sym "=", Sym "t",
      Sym "s"]]]*)
  fun read_rule_smtlib_tree l (target :: [match]) = [Match match, Target target] |
      read_rule_smtlib_tree l tree = let val _ = @{print}("treee", tree) in raise PARSE (l, "not a valid instance of a define-rule") end
  fun read_cond_rule_smtlib_tree l (target :: match :: [precondition])
          = [Precondition precondition, Match match, Target target] |
      read_cond_rule_smtlib_tree l _ = raise PARSE (l, "not a valid instance of a define-cond-rule")

  fun read_name l cs = read_rewrite_name l cs None []

  fun parse_rare rule l cs f = 
  let
    val (wth_name, _, name) = read_name l cs
    val _ = @{print}("wth_name",implode wth_name)
    val (wth_par, parsed_par) = parse_pars wth_name l
    val _ = @{print}("wth_par",implode wth_par)
    val wth_last_parenthesis = take (length wth_par - 1) wth_par
    val exprs = f l (hd (get_smtlib_tree wth_last_parenthesis))
    val _ = @{print}("pars",parsed_par)
  in 
    rule :: name @ [parsed_par] @ exprs
  end

in 
(*Soll liste ausgeben nicht liste von listen*)
  fun parse_according_to_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e"::" ":: cs)
        = parse_rare (Rule_Type DEFINE_RULE) l cs read_rule_smtlib_tree | 
      parse_according_to_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"c"::"o"::"n"::"d"::"-"::"r"::"u"::"l"::"e"::" ":: cs)
        = parse_rare (Rule_Type DEFINE_COND_RULE) l cs read_cond_rule_smtlib_tree | 
      parse_according_to_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e"::"*"::" ":: cs)
        = parse_rare (Rule_Type DEFINE_RULE_STAR) l cs read_rule_smtlib_tree | 
      parse_according_to_type l _ = raise PARSE (l, "could not read rule type")
end


(* Overall parser: *)
fun read_tree (l:int) (line:string list) : rewrite_tree
   = ((*@{print} ("current line ",line);*) Rewrite_Rule (parse_according_to_type l line)) 

fun (*add_line (";"::cs) (l,rewrite_trees) = (l + 1, rewrite_trees) | *)(*Skip comments*)
    add_line line (l, rewrite_trees) =
      let
        val _ = @{print}("line",line)
        val line_list = (raw_explode line)
      in 
        if size line = 0 then (l + 1, rewrite_trees) (*Skip empty lines*)
        else if hd line_list = ";" then (l + 1, rewrite_trees) (*Skip comments*)
        else (l + 1, (read_tree l line_list) :: rewrite_trees) (*Get rewrite tree for current line and append*)
      end

fun parse_rewrites lines = (fold add_line lines (1,[])) |> snd

(* pretty printer *)

fun pretty_rewrite_tree (Rule_Type DEFINE_RULE) = Pretty.str ("define-rule ")
  | pretty_rewrite_tree (Rule_Type DEFINE_COND_RULE) = Pretty.str ("define-cond-rule ")
  | pretty_rewrite_tree (Rule_Type DEFINE_RULE_STAR) = Pretty.str ("define-rule* ")
  | pretty_rewrite_tree (Rule_Name s) = Pretty.str s 
  | pretty_rewrite_tree (Par trees) = Pretty.enclose "(" ")" (Pretty.separate "" (map SMTLIB.pretty_tree trees))
  | pretty_rewrite_tree (Precondition tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Match tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Target tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Context_Expr tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Rewrite_Rule trees) =
      Pretty.enclose "(" ")" (Pretty.separate "" (map pretty_rewrite_tree trees))

fun pretty_rewrite_rules cs = Pretty.block (map pretty_rewrite_tree cs)

val str_of = Pretty.unformatted_string_of o pretty_rewrite_rules

end;