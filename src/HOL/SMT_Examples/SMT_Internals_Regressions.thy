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
  str |> raw_explode |> SMTLIB.parse |> K (raise (SMT_Regression ("Input expected to raise parsing error but did not: " ^ str)))
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

val _ = expect_parsing_error "v0" 


(*Int*)

val _ = check_tree "1" (SMTLIB.Num 1) true
val _ = check_tree "45" (SMTLIB.Num 54) false
val _ = check_tree "00078768" (SMTLIB.Num 78768) true
val _ = check_tree "00078768" (SMTLIB.Num 078768) true
val _ = check_tree "000" (SMTLIB.Num 0) true
val _ = check_tree "-23" (SMTLIB.Num (~23)) true
val _ = check_tree "-23" (SMTLIB.S[SMTLIB.Sym "-", SMTLIB.Num (~23)]) false

val _ = expect_parsing_error "000" 


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
val _ = expect_parsing_error ".38"
val _ = expect_parsing_error "-." 
val _ = expect_parsing_error "47/-28"


(*Key*)

val _ = check_tree ":hi" (SMTLIB.Key "hi") true
val _ = check_tree ":pattern1" (SMTLIB.Key "hi") false
val _ = expect_parsing_error ": spacebeforepattern"


(*Str*)

val _ = check_tree "\"sdf\"" (SMTLIB.Str "sdf") true
val _ = check_tree "\"\"" (SMTLIB.Str "") true
val _ = check_tree "\" \"" (SMTLIB.Str "") false

val _ = expect_parsing_error "\"notclosed"
val _ = expect_parsing_error "notclosedopen\""


(*BVNum*)

val _ = check_tree "#b00100000101" (SMTLIB.BVNum (261,11)) true



(*S*)
val _ = check_tree "()" (SMTLIB.S []) true
val _ = check_tree "( )" (SMTLIB.S []) true
val _ = check_tree "(op)" (SMTLIB.S [SMTLIB.Sym "op"]) true
val _ = check_tree "(op arg1 arg2)" (SMTLIB.S [SMTLIB.Sym "op",SMTLIB.Sym "arg1",SMTLIB.Sym "arg2"]) true

\<close>

end