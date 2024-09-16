theory SMT_Internals_Regressions
  imports HOL.SMT
begin

(* Test smtlib.ML *)
(* Purely syntactical testing! *)

ML\<open>
exception SMT_Regression of string

(*expects a string, a SMTLIB.tree and a boolean expressing if the string should be parsed into 
the tree or not.*)
fun expect_parsing_error str =
  str |> single |> Timeout.apply (seconds 5.0) SMTLIB.parse |> K (raise (SMT_Regression ("Input expected to raise parsing error but did not: " ^ str)))
  handle SMTLIB.PARSE(_,_) => true

(*expects a string, a SMTLIB.tree and a boolean expressing if the string should be parsed into 
the tree or not.*)
fun check_tree str tree expected_value =
let
  val tree' = [str] |> SMTLIB.parse
  val match = (expected_value = (tree = tree'))
in 
 case match of
  true => true |
  false => raise (SMT_Regression ("SMTLIB.parse does not give expected output for " ^ str ^ " instead resulted in " ^ SMTLIB.str_of tree'))
end



(*Regression Tests*)

val _ = expect_parsing_error "" 
val _ = check_tree "()" (SMTLIB.S []) true


(*Sym*)

val _ = check_tree "x" (SMTLIB.Sym "y") false
val _ = check_tree "x" (SMTLIB.Sym "x") true
val _ = check_tree "(x)" (SMTLIB.Sym "x") false
val _ = check_tree "|x|" (SMTLIB.Sym "x") true
val _ = check_tree "|<|" (SMTLIB.Sym "<") true
val _ = check_tree "@my+var<3" (SMTLIB.Sym "@my+var<3") true
val _ = check_tree "| my test|" (SMTLIB.Sym " my test") true
val _ = check_tree "||" (SMTLIB.Sym "") true

val _ = expect_parsing_error "|s||"


(*Int*)

val _ = check_tree "1" (SMTLIB.Num 1) true
val _ = check_tree "45" (SMTLIB.Num 54) false
val _ = check_tree "00078768" (SMTLIB.Num 78768) true
val _ = check_tree "00078768" (SMTLIB.Num 078768) true
val _ = check_tree "000" (SMTLIB.Num 0) true
val _ = check_tree "-23" (SMTLIB.Num (~23)) true
val _ = check_tree "-23" (SMTLIB.S[SMTLIB.Sym "-", SMTLIB.Num (~23)]) false


(*Dec*)

val _ = check_tree "1/2" (SMTLIB.S [SMTLIB.Sym "/",SMTLIB.Dec (1,0),SMTLIB.Dec (2,0)]) true
val _ = check_tree "01.234" (SMTLIB.Dec (1,234)) true
val _ = check_tree "01.234" (SMTLIB.Dec (01,234)) true
val _ = check_tree "01.234" (SMTLIB.Dec (201,234)) false
val _ = check_tree "47/28" (SMTLIB.S [SMTLIB.Sym "/",SMTLIB.Dec (47,0),SMTLIB.Dec (28,0)]) true
val _ = check_tree "-47/28" (SMTLIB.S [SMTLIB.Sym "/",SMTLIB.S[SMTLIB.Sym "-", SMTLIB.Dec (47,0)],SMTLIB.Dec (28,0)]) false
val _ = check_tree "-47/28" (SMTLIB.S [SMTLIB.Sym "/",SMTLIB.Dec (~47,0),SMTLIB.Dec (28,0)]) true
val _ = check_tree "(- 47/28)" (SMTLIB.S[SMTLIB.Sym "-", SMTLIB.S [SMTLIB.Sym "/",SMTLIB.Dec (47,0),SMTLIB.Dec (28,0)]]) true

val _ = expect_parsing_error "01.234.99"
val _ = expect_parsing_error "01."
val _ = expect_parsing_error "47/-28"
val _ = expect_parsing_error "3.2/5"

(*I guess these are allowed?*)
(*val _ = expect_parsing_error ".38"*)
(*val _ = expect_parsing_error "-." *)

(*Key*)

val _ = check_tree ":hi" (SMTLIB.Key "hi") true
val _ = check_tree ":pattern1" (SMTLIB.Key "hi") false
val _ = expect_parsing_error ": spacebeforepattern"


(*Str*)

val _ = check_tree "\"sdf\"" (SMTLIB.Str "sdf") true
val _ = check_tree "\"\"" (SMTLIB.Str "") true
val _ = check_tree "\" \"" (SMTLIB.Str "") false
val _ = check_tree "\"these should be replaced: \\\\\"" (SMTLIB.Str "these should be replaced: \\") true

val _ = expect_parsing_error "\"notclosed"
val _ = expect_parsing_error "notclosedopen\""


(*BVNum*)

val _ = check_tree "#b00100000101" (SMTLIB.BVNum (261,11)) true



(*S*)
val _ = check_tree "()" (SMTLIB.S []) true
val _ = check_tree "( )" (SMTLIB.S []) true
val _ = check_tree "(op)" (SMTLIB.S [SMTLIB.Sym "op"]) true
val _ = check_tree "(op arg1 arg2)" (SMTLIB.S [SMTLIB.Sym "op",SMTLIB.Sym "arg1",SMTLIB.Sym "arg2"]) true
val _ = expect_parsing_error "(01"

\<close>


(* Test lethe_proof.ML *)
(* Purely syntactical testing! *)


ML\<open>
exception SMT_Regression of string
open SMTLIB
open Lethe_Proof

(*expects 
a SMTLIB.tree list, and a raw_lethe_node list, and a boolean indicating
if the SMTLIB.tree list should be parsed into a the raw_lethe_node or not.
The current_anchor_id is set to NONE and the name bindings to the empty name bindings
SMTLIB_Proof.empty_name_binding*)
fun expect_parsing_error trees =
   (Timeout.apply (seconds 5.0) parse_raw_proof_steps) NONE trees SMTLIB_Proof.empty_name_binding|> K (raise (SMT_Regression ("Input expected to raise parsing error but did not")))
  handle LETHE_PROOF_PARSE _ => true |
   Fail _ => true


(*expects a string, a SMTLIB.tree and a boolean expressing if the string should be parsed into 
the tree or not.*)
fun check_raw_node trees raw_node expected_value =
let
  val node = Lethe_Proof.parse_raw_proof_steps NONE trees SMTLIB_Proof.empty_name_binding
  val match = (expected_value = ((fn (a,_,_) => a) node =  raw_node))
  (*val _ = @{print}("node",node)*)
in 
 case match of
  true => true |
  false => raise (SMT_Regression ("Lethe_Proof.parse_raw_proof_steps does not give expected output instead resulted in "))
end



(*Regression Tests*)

val missing_concl = SMTLIB.parse ["(step t0  :rule equiv_pos2)"]
val _ = expect_parsing_error [missing_concl]
val missing_id = SMTLIB.parse ["(step (+ 0 1) :rule equiv_pos2)"]
val _ = expect_parsing_error [missing_id]
val invalid_rule = SMTLIB.parse ["(step t0 (+ 0 1) :rule)"]
val _ = expect_parsing_error [invalid_rule]
val missing_rule_name = SMTLIB.parse ["(step t0 (+ 0 1) :rule)"]
val _ = expect_parsing_error [missing_rule_name]
val missing_rule = SMTLIB.parse ["(step t0 (+ 0 1))"]
val _ = expect_parsing_error [missing_rule]
val malformed_args = SMTLIB.parse ["(step t17 (cl) :rule hole :args 0)"]
val _ = expect_parsing_error [malformed_args]


(*steps*)

val testTree = SMTLIB.parse ["(step t99 (cl) :rule resolution)"]
val resTree = 
  Raw_Lethe_Node {concl = Sym "false", context_assignments = [], id = "t99", prems = [], rule = "resolution", step_args = [], subproof = []}
val _ = check_raw_node [testTree] [resTree] true


(*Testing step arguments*)


(* No step argument given for argument optional rule *)
val testTree = SMTLIB.parse ["(step t17 (cl (+ @p_517 0)) :rule hole)"]
val resTree = Raw_Lethe_Node
      {concl = S [Sym "or", S [Sym "+", Sym "@p_517",Num 0]], context_assignments = [], id = "t17", prems = [], rule = "hole", step_args = [], subproof = []}
val _ = check_raw_node [testTree] [resTree] true

(* Step argument given but not added *)
val testTree = SMTLIB.parse ["(step t17 (cl) :rule hole :args (0))"]
val resTree = Raw_Lethe_Node
      {concl = Sym "false", context_assignments = [], id = "t17", prems = [], rule = "hole", step_args = [], subproof = []}
val _ = check_raw_node [testTree] [resTree] false

(* Step argument given and properly added *)
val testTree = SMTLIB.parse ["(step t17 (cl) :rule hole :args (0))"]
val resTree = Raw_Lethe_Node
      {concl = Sym "false", context_assignments = [], id = "t17", prems = [], rule = "hole", step_args = [Num 0], subproof = []}
val _ = check_raw_node [testTree] [resTree] true

(* Rule does not allow step argument and none given *)
val testTree = SMTLIB.parse ["(step t17 (cl (not (not (not a))) a) :rule not_not)"]
val resTree = Raw_Lethe_Node
      {concl =  S [Sym "or", S [Sym "not", S [Sym "not", S [Sym "not", Sym "a"]]], Sym "a"], context_assignments = [], id = "t17", prems = [], rule = "not_not", step_args = [], subproof = []}
val _ = check_raw_node [testTree] [resTree] true

(* Unexpected step argument given TODO*)
val testTree = SMTLIB.parse ["(step t17 (cl (not (not (not a))) a) :rule not_not :args (0))"]
val _ = check_raw_node [testTree] [resTree] false
val resTree = Raw_Lethe_Node
      {concl =  S [Sym "or", S [Sym "not", S [Sym "not", S [Sym "not", Sym "a"]]], Sym "a"], context_assignments = [], id = "t17", prems = [], rule = "not_not", step_args = [Num 0], subproof = []}
val x = check_raw_node [testTree] [resTree] true



val testNode = Lethe_Proof.parse_raw_proof_steps NONE [testTree] SMTLIB_Proof.empty_name_binding


\<close>

end