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
    Context_Expr of SMTLIB.tree option | (*Not fully supported yet*)
    Rewrite_Rule of rewrite_tree list

  val parse_rewrites: string list -> rewrite_tree list
  val pretty_rewrite_tree: rewrite_tree -> Pretty.T
  val str_of: rewrite_tree list -> string
end;

structure PARSE_REWRITE: PARSE_REWRITE =
struct

exception PARSE of int * string

datatype rule_type = DEFINE_RULE | DEFINE_COND_RULE | DEFINE_RULE_STAR
datatype unfinished = None | String of string | Symbol of string | TreeList of SMTLIB.tree list

  datatype rewrite_tree = 
    Rule_Type of rule_type |
    Rule_Name of string |
    Par of SMTLIB.tree list |
    Precondition of SMTLIB.tree |
    Match of SMTLIB.tree |
    Target of SMTLIB.tree |
    Context_Expr of SMTLIB.tree option |
    Rewrite_Rule of rewrite_tree list


(*While rule type and rule name are directly parsed in, the parameters and the expressions are
  given to SMTLIB.parse to efficiently reuse its capabilities:

For example,
 For: (define-rule bool-eq-refl ((t Bool)) (= t s) true

 SMTLIB.parse "(t Bool)" and SMTLIB.parse "(= t s) true" result in 

 S [S [Sym "t",Sym "Bool"]] and S [S [Sym "=", Sym "t", Sym "s"], Sym "true"]

TODO: To use SMTLIB.parse we would have to separate "(= t s)" and "true". Is that worth not having 
to add SMTLIB.read_line to that files signature? Requires one more traversal. ASK Matthias

Binarisation of n-ary operators in rare rules:
  Note that for the parameters the type cvc_ListVar is already set here but for the expressions
  this is done in rewrites_to_lemma to reuse the binarisation procedure in SMTLIB_Proof.
*)

(*Parse name*)
fun read_rewrite_name l (c :: cs) None ts =
       if Symbol.is_ascii_blank c then read_rewrite_name l cs None ts (*Ignore leading space*)
       else read_rewrite_name l cs (String c) ts | (*Start of a word*)
    read_rewrite_name l (c :: cs) (String s) ts =
       if Symbol.is_ascii_blank c then (cs, (Rule_Name s :: ts)) (*End of a word*)
       else if c = "-" then read_rewrite_name l cs (String (s ^ "_")) ts (*Replace - in name by _ *)
       else read_rewrite_name l cs (String (s ^ c)) ts | (*Word continues*)
    read_rewrite_name l _ _ _ = raise PARSE (l, "rule name could not be parsed in")

(*
Depricated:
fun get_smtlib_tree str : SMTLIB.tree list list
 = snd (SMTLIB.read_line 0 (implode str) SMTLIB.None [[]])
*)

local (*TODO: Rewrite*)
    fun parse_par (":"::cs) name typ _ _ l = parse_par cs name ("ListVar " ^ typ) true false l
   | parse_par (")"::cs) name typ _ _ _ = (cs, SMTLIB.parse ["("^name^" " ^ typ^")"])
   | parse_par (" "::cs) name typ false _ l = parse_par cs name typ false true l
   | parse_par (c::cs) name typ false false l = parse_par cs (name^c) typ false false l
   | parse_par (c::cs) name typ x true l = parse_par cs name (typ^c) x true l
   | parse_par (_::cs) name typ true _ l = parse_par cs name typ true false l
   | parse_par _ _ _ _ _ l = raise PARSE (l, "parameter is not well-formed.")
in
  fun parse_pars ("("::cs) None l = parse_pars cs (TreeList []) l (*Very first opening parenthesis*) 
 | parse_pars ("("::cs) (TreeList xs) l =
    let
      val (new_cs, par) = parse_par cs "" "" false false l
      (*val _ = @{print} ("Parsed par: ", par)
      val _ = @{print} ("New rest string: ", implode new_cs)*)
    in parse_pars new_cs (TreeList (par::xs)) l end
 | parse_pars (") "::cs) None _ = (cs, []) (*Very last closing parenthesis: Par List was empty*)
 | parse_pars (")"::cs) (TreeList xs) _ = (cs, xs) (*Very last closing parenthesis*)
 | parse_pars (" "::cs) (TreeList xs) l = parse_pars cs (TreeList xs) l (*Skip spaces between pars*)
 | parse_pars _ _ l = raise PARSE (l, "parameter list is not well-formed.")
end

local 
  fun read_rule_smtlib_tree _ (match :: [target])
         = [Match match, Target target] |
      read_rule_smtlib_tree l _ = raise PARSE (l, "not a valid instance of a define-rule")

  fun read_cond_rule_smtlib_tree _ (precondition :: match :: [target])
         = [Precondition precondition, Match match, Target target] |
      read_cond_rule_smtlib_tree l _ = raise PARSE (l, "not a valid instance of a define-cond-rule")

  fun read_star_rule_smtlib_tree _ (match :: [target])
        = [Context_Expr NONE, Match match, Target target] |
      read_star_rule_smtlib_tree _ (target :: match :: [context_expr])
        = [Context_Expr (SOME context_expr), Match match, Target target] |
      read_star_rule_smtlib_tree l _ = raise PARSE (l, "not a valid instance of a define-star-rule")

  fun read_name l cs = read_rewrite_name l cs None []

  fun parse_rare rule l cs f = 
  let
    val (wth_name, name) = read_name l cs
    (*val _ = @{print}("rule name: ", name)*)
    val (wth_par, parsed_par) = parse_pars wth_name None l
    (*val _ = @{print}("parameter list: ", parsed_par)*)
    val wth_last_parenthesis = take (length wth_par - 1) wth_par

    (*TODO: Completely rewrite*)
    (*TODO: Use nested lists instead of counter and then flatten them?*)

    (*A statement is either in between parenthesis or a single token*)
    (*Empty strings cannot be parsed in by the SMTLIB parser. Find out the reason. For now strings are excluded here*)
    fun read_token [] token _ = ([],token) |
        read_token (" "::cs) token _ = (cs,token) |
        read_token ("\""::"\""::cs) token false = read_token cs (token^"(str.const)") true | (*TDOO: replace by ''s?*)
        read_token ("\""::cs) token false = read_token cs (token^"(str.const ") true | (*TDOO: replace by ''s?*)
        read_token ("\""::cs) token true = read_token cs (token^")") false |
        read_token (c::cs) token x = read_token cs (token^c) x

(*TODO: string constants*)
    fun split_up [] _ _ _ = [] |
        split_up (" "::cs) 0 None str_const = split_up cs 0 None str_const | (*Skip blanks in between expressions*)
        split_up ("("::cs) 0 None str_const = split_up cs 1 (String "(") str_const | (*Expression starts with a parenthesis*)
        split_up ("("::cs) i (String str) str_const = split_up cs (i+1) (String (str ^ "(")) str_const | (*Expression starts with a parenthesis*)
        split_up (c::cs) 0 None str_const =
          let 
            val (new_cs,token) = read_token (c::cs) "" false
          in 
            [token]::split_up new_cs 0 None str_const
          end | (*Expression is a token wth parenthesis*)
        split_up (")"::cs) 1 (String str) str_const = [str ^ ")"] :: split_up cs 0 None str_const |
        split_up (")"::cs) i (String str) str_const = split_up cs (i-1) (String (str^")")) str_const |
        split_up ("\""::cs) i (String str) false = split_up cs i (String (str^"str.const(")) true |
        split_up ("\""::cs) i (String str) true = split_up cs i (String (str^")")) false |
        split_up (c::cs) i (String str) str_const = split_up cs i (String (str^c)) str_const |
        split_up _ _ _ _ = raise PARSE (l, "rule cannot be parsed in")

(*TODO: string list instead of string list list*)
    val expr_list = split_up wth_last_parenthesis 0 None false
    (*Separate components (match, target, condition, context) from each other: *)
    val _ = @{print} ("expr_list", expr_list)
   val expr = f l (map SMTLIB.parse expr_list)

  in
    rule :: name @ [Par parsed_par] @ expr
  end

in 
  fun parse_according_to_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e"::" ":: cs)
        = parse_rare (Rule_Type DEFINE_RULE) l cs read_rule_smtlib_tree | 
      parse_according_to_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"c"::"o"::"n"::"d"::"-"::"r"::"u"::"l"::"e"::" ":: cs)
        = parse_rare (Rule_Type DEFINE_COND_RULE) l cs read_cond_rule_smtlib_tree | 
      parse_according_to_type l ("("::"d"::"e"::"f"::"i"::"n"::"e"::"-"::"r"::"u"::"l"::"e"::"*"::" ":: cs)
        = parse_rare (Rule_Type DEFINE_RULE_STAR) l cs read_star_rule_smtlib_tree | 
      parse_according_to_type l _ = raise PARSE (l, "could not read rule type")
end


(* Overall parser: *)
fun read_tree l line
   = parse_according_to_type l line |> Rewrite_Rule

fun add_line line (l, rewrite_trees) =
  let
    val _ = @{print}("current line to parse",line)
    val line_list = (raw_explode line)
  in
    if size line = 0 then (l + 1, rewrite_trees) (*Skip empty lines*)
    else if hd line_list = ";" then (l + 1, rewrite_trees) (*Skip comments*)
    else (l + 1, (read_tree l line_list) :: rewrite_trees) (*Get rewrite tree for current line and append*)
  end

(*TEMP: Figure out how to parse this in a string list automatically, seperating at\n *)

fun parse_rewrites lines = (fold add_line (rev lines) (1,[])) |> snd

(* pretty printer *)

fun pretty_rewrite_tree (Rule_Type DEFINE_RULE) = Pretty.str ("define-rule ")
  | pretty_rewrite_tree (Rule_Type DEFINE_COND_RULE) = Pretty.str ("define-cond-rule ")
  | pretty_rewrite_tree (Rule_Type DEFINE_RULE_STAR) = Pretty.str ("define-rule* ")
  | pretty_rewrite_tree (Rule_Name s) = Pretty.str s 
  | pretty_rewrite_tree (Par trees) = Pretty.enclose "(" ")" (Pretty.separate "" (map SMTLIB.pretty_tree trees))
  | pretty_rewrite_tree (Precondition tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Match tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Target tree) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Context_Expr NONE) = Pretty.str ""
  | pretty_rewrite_tree (Context_Expr (SOME tree)) = SMTLIB.pretty_tree tree
  | pretty_rewrite_tree (Rewrite_Rule trees) =
      Pretty.enclose "(" ")" (Pretty.separate "" (map pretty_rewrite_tree trees))

fun pretty_rewrite_rules cs = Pretty.block (map pretty_rewrite_tree cs)

val str_of = Pretty.unformatted_string_of o pretty_rewrite_rules

end;