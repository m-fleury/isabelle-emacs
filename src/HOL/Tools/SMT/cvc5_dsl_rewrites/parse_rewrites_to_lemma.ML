

(*First parse into datastructure then print*)
(*Try to reuse term parsing/printing infrastructure*)

signature PARSE_REWRITE =
sig
  exception PARSE of int * string
  datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR

  datatype rewrite_tree = 
    Rule_Type of rule_type |
    Rule_Name of string |
    Par of SMTLIB.tree list |
    Precondition of SMTLIB.tree |
    Match of SMTLIB.tree |
    Target of SMTLIB.tree |
    Rewrite_Rule of rewrite_tree list

  val parse_rewrites: string list -> rewrite_tree list
  val pretty_rewrite_tree: rewrite_tree -> Pretty.T
  val str_of: rewrite_tree list -> string
end;


structure PARSE_REWRITE: PARSE_REWRITE =
struct

(* data structures *)

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
    Rewrite_Rule of rewrite_tree list


(*While rule type and rule name are parsed in directly the rest of the string (minus the final
 closing parenthesis is given to SMTLIB.parse to efficiently reuse its capabilities:

E.g.,
 For: (define-rule bool-eq-refl ((t Bool)) (= t s) true

 SMTLIB.parse "((t Bool)) (= t s) true" results in 

 [[Sym "true", S [Sym "=", Sym "t", Sym "s"],
   S [S [Sym "v0",
         Sym "Bool"]]]
*)

(*Parse name*)
fun read_rewrite_name l (c :: cs) None ts =
       if Symbol.is_ascii_blank c then read_rewrite_name l cs None ts (*Ignore leading space*)
       else read_rewrite_name l cs (String c) ts | (*Start of a word*)
    read_rewrite_name l (c :: cs) (String s) ts =
       if Symbol.is_ascii_blank c then (cs, None, (Rule_Name s :: ts)) (*End of a word*)
       else read_rewrite_name l cs (String (s ^ c)) ts | (*Word continues*)
    read_rewrite_name l _ _ _ = raise PARSE (l, "rule name could not be parsed in")


(*read rule type and proceed according to it*)
local 

  fun read_par l (SMTLIB.S cs) = Par cs | (*TODO: What when list is empty still S?*)
      read_par l _ =  raise PARSE (l, "not a valid parameter")
  fun read_rule_smtlib_tree l [target :: match :: [par]] = [read_par l par, Match match, Target target] |
      read_rule_smtlib_tree l _ = raise PARSE (l, "not a valid instance of a define-rule")
  fun read_cond_rule_smtlib_tree l [target :: match :: precondition :: [par]] = [read_par l par, Match match, Target target] |
      read_cond_rule_smtlib_tree l _ = raise PARSE (l, "not a valid instance of a define-cond-rule")

  fun read_name l cs = read_rewrite_name l cs None []
  fun get_smtlib_tree str = snd (SMTLIB.read_line 0 (implode (rev (tl (rev str)))) SMTLIB.None [[]]) (*TODO: Find better way in ML to delete last element*)

  fun print_from_name l cs f = 
  let val (rest, _, name) = read_name l cs in 
    name @ f l (get_smtlib_tree rest)
  end

  fun define_rule l cs = (Rule_Type DEFINE_RULE) :: print_from_name l cs read_rule_smtlib_tree
  fun define_cond_rule l cs = (Rule_Type DEFINE_COND_RULE) :: print_from_name l cs read_cond_rule_smtlib_tree

in 
  fun parse_according_to_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e"::" ":: cs) = define_rule l cs | 
      parse_according_to_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"c"::"o"::"n"::"d"::"-"::"r"::"u"::"l"::"e"::" ":: cs) = define_cond_rule l cs |
      parse_according_to_type l _ = raise PARSE (l, "could not read rule type")
end


(* Overall parser: *)
fun read_tree (l:int) (line:string) : rewrite_tree
   = (@{print} ("current line ",line); Rewrite_Rule (parse_according_to_type l (raw_explode line))) 

fun add_line (line:string) ((l: int), (rewrite_trees: rewrite_tree list))  :  (int * rewrite_tree list) =
      if size line = 0 then (l + 1, rewrite_trees) (*Skip empty lines*)
      else (l + 1, (read_tree l line) :: rewrite_trees) (*Get rewrite tree for current line and append*)
 
(*string list -> rewrite_tree list*)
fun parse_rewrites lines : rewrite_tree list = snd (fold add_line lines (1,[]))

(* pretty printer *)

fun pretty_rewrite_tree (Rule_Type DEFINE_RULE) = Pretty.str ("define-rule ")
  | pretty_rewrite_tree (Rule_Type DEFINE_COND_RULE) = Pretty.str ("define-cond-rule ")
  | pretty_rewrite_tree (Rule_Type DEFINE_RULE_STAR) = Pretty.str ("define-rule* ")
  | pretty_rewrite_tree (Rule_Name s) = Pretty.str s 
  | pretty_rewrite_tree (Par trees) = Pretty.enclose "(" ")" (Pretty.separate "" (map SMTLIB.pretty_tree trees))
  | pretty_rewrite_tree (Precondition tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Match tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Target tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Rewrite_Rule trees) =
      Pretty.enclose "(" ")" (Pretty.separate "" (map pretty_rewrite_tree trees))

fun pretty_rewrite_rules cs = Pretty.block (map pretty_rewrite_tree cs)

val str_of = Pretty.unformatted_string_of o pretty_rewrite_rules


val _ = @{print} ("res",str_of (parse_rewrites ["(define-rule bool-eq-refl ((t Bool)) (= t t) true)"]))
end;