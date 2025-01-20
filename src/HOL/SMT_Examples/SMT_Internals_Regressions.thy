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


(* Test alethe_proof.ML *)
(* Purely syntactical testing! *)


ML\<open>
exception SMT_Regression of string
open SMTLIB
open Alethe_Proof

(*expects 
a SMTLIB.tree list, and a raw_alethe_node list, and a boolean indicating
if the SMTLIB.tree list should be parsed into a the raw_alethe_node or not.
The current_anchor_id is set to NONE and the name bindings to the empty name bindings
SMTLIB_Proof.empty_name_binding*)
fun expect_parsing_error trees =
   (Timeout.apply (seconds 5.0) parse_raw_proof_steps) NONE trees SMTLIB_Proof.empty_name_binding|> K (raise (SMT_Regression ("Input expected to raise parsing error but did not")))
  handle ALETHE_PROOF_PARSE _ => true |
   Fail _ => true


(*expects a string, a SMTLIB.tree and a boolean expressing if the string should be parsed into 
the tree or not.*)
fun check_raw_node trees raw_node expected_value =
let
  val node = Alethe_Proof.parse_raw_proof_steps NONE trees SMTLIB_Proof.empty_name_binding
  val match = (expected_value = ((fn (a,_,_) => a) node =  raw_node))
  (*val _ = @{print}("node",node)*)
in 
 case match of
  true => true |
  false => raise (SMT_Regression ("Alethe_Proof.parse_raw_proof_steps does not give expected output instead resulted in "))
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
  Raw_Alethe_Node {concl = Sym "false", context_assignments = [], id = "t99", prems = [], rule = "resolution", step_args = [], subproof = []}
val _ = check_raw_node [testTree] [resTree] true

(*Testing step arguments*)


(* No step argument given for argument optional rule *)
val testTree = SMTLIB.parse ["(step t17 (cl (+ @p_517 0)) :rule hole)"]
val resTree = Raw_Alethe_Node
      {concl = S [Sym "or", S [Sym "+", Sym "@p_517",Num 0]], context_assignments = [], id = "t17", prems = [], rule = "hole", step_args = [], subproof = []}
val _ = check_raw_node [testTree] [resTree] true

(* Step argument given but not added *)
val testTree = SMTLIB.parse ["(step t17 (cl) :rule hole :args (0))"]
val resTree = Raw_Alethe_Node
      {concl = Sym "false", context_assignments = [], id = "t17", prems = [], rule = "hole", step_args = [], subproof = []}
val _ = check_raw_node [testTree] [resTree] false

(* Step argument given and properly added *)
val testTree = SMTLIB.parse ["(step t17 (cl) :rule hole :args (0))"]
val resTree = Raw_Alethe_Node
      {concl = Sym "false", context_assignments = [], id = "t17", prems = [], rule = "hole", step_args = [Num 0], subproof = []}
val _ = check_raw_node [testTree] [resTree] true

(* Rule does not allow step argument and none given *)
val testTree = SMTLIB.parse ["(step t17 (cl (not (not (not a))) a) :rule not_not)"]
val resTree = Raw_Alethe_Node
      {concl =  S [Sym "or", S [Sym "not", S [Sym "not", S [Sym "not", Sym "a"]]], Sym "a"], context_assignments = [], id = "t17", prems = [], rule = "not_not", step_args = [], subproof = []}
val _ = check_raw_node [testTree] [resTree] true

(* Unexpected step argument given TODO*)
val testTree = SMTLIB.parse ["(step t17 (cl (not (not (not a))) a) :rule not_not :args (0))"]
val _ = check_raw_node [testTree] [resTree] false
val resTree = Raw_Alethe_Node
      {concl =  S [Sym "or", S [Sym "not", S [Sym "not", S [Sym "not", Sym "a"]]], Sym "a"], context_assignments = [], id = "t17", prems = [], rule = "not_not", step_args = [Num 0], subproof = []}
val x = check_raw_node [testTree] [resTree] true

(* Step argument is string *)
val testTree = SMTLIB.parse ["(step t17 (cl) :rule rare_rewrite :args (\"evaluate\"))"]
val resTree = Raw_Alethe_Node
      {concl = Sym "false", context_assignments = [], id = "t17", prems = [], rule = "rare_rewrite", step_args = [Str "evaluate"], subproof = []}
val _ = check_raw_node [testTree] [resTree] true



val testNode = Alethe_Proof.parse_raw_proof_steps NONE [testTree] SMTLIB_Proof.empty_name_binding


\<close>


(* Test alethe_replay_methods.ML *)
(* Important: The context can be different than if a step appears inside a proof! E.g., because
of subproofs. Any failure should be double checked carefully. Nonetheless, these regressions are useful
when changes are made to the reconstruction functions. 
Currently only supports indexes as args ^^ This is because the reconstruction of these rules had
some errors.
*)

ML\<open>
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

fun call_parse_token cs = parse_token (Unfinished ([],0)) cs |> (fn Finished(x,xs) => (x |> implode ,xs))

val scanWhiteSpace = Scan.many (curry (op =) " ")

fun tactic_args_parser ctxt cs =
   ((Scan.this_string "Declarations" |-- $$" " |-- scanWhiteSpace |-- $$"[" |-- scanWhiteSpace
     |-- Scan.repeat (call_parse_token --| scanWhiteSpace --| $$"," --| scanWhiteSpace)
     -- call_parse_token
     --| scanWhiteSpace --| $$"]"
   ) cs 
  |> fst
  |> (fn (xs,x) => x::xs) 
  |> map (Syntax.parse_term ctxt))




fun get_tac n ctxt prems args = 
let
  val rule = CVC5_Replay_Methods.cvc5_rule_of n |> @{print}
  val rule_name = rule |> Alethe_Replay_Methods.string_of_alethe_rule
  val _ = @{print}("Found tactic", rule_name)
  val _ = @{print}("args", args  )

  (*FIXME: For some reason this function gets called twice... This definitely should not be necessary*)
  val dummys = Const ("Pure.prop", @{typ "prop \<Rightarrow> prop"}) $ (Const ("Pure.term", @{typ "prop \<Rightarrow> prop"}) $ Const ("Pure.dummy_pattern", @{typ "prop"}))

  val prems=prems
  val step_args=[]
  val context_args=[]
  val args= (if rule_name = "and_pos" andalso Option.isSome args
            then SOME (Index (Option.valOf args |> Syntax.read_term ctxt |> HOLogic.dest_number |> snd))
            else if rule_name = "shuffle" andalso Option.isSome args
            then SOME (CommOp (Option.valOf args |> Syntax.read_term ctxt))
            else NONE)|> @{print}
  fun rule_tac ctxt t = CVC5_Replay_Methods.choose (Context.the_generic_context ()) rule ctxt prems step_args context_args t args
  fun term_to_thm t = rule_tac ctxt t

in
  (fn t => 
  if (t |> Thm.concl_of) = dummys
  then Seq.empty
  else
    let
      val thm2 = t |> Thm.concl_of |> (fn Const (_, _) $ x => x | x => x) |> term_to_thm 
    in
      resolve0_tac [thm2] 1 t
    end)
end

val parse_tactic_args : tactic_args parser = (fn ts => let val _ = @{print}("ts",ts) in (Index 0,ts) end)
fun test x = Parse.term (x|> @{print})
val _ =
 Theory.setup
 (Method.setup \<^binding>\<open>ctxt_tactic\<close>
 (Scan.lift (Parse.string
             -- ( (Scan.optional (Scan.option Parse.string) NONE))) >>
   (fn (rule_name,args) => fn ctxt => fn prems => CONTEXT_TACTIC (get_tac rule_name ctxt prems args)))
 "testing tactics <name> ([<step_args>*]) ([<args>*])")
\<close>


(* Rule 1: assume *)

lemma normalized_input_1:
  assumes "a"
  shows "a"
  using assms
  by (ctxt_tactic "__normalized_input")

lemma normalized_input_2:
  assumes "a \<and> (b \<or> c)"
  shows "a \<and> (b \<or> c)"
  using assms
  by (ctxt_tactic "__normalized_input")

lemma normalized_input_3:
  assumes "a \<and> a"
  shows "a \<and> a"
  using assms
  by (ctxt_tactic "__normalized_input")

lemma normalized_input_4:
  assumes "(\<forall>a. a = (3::int))"
  shows "(\<forall>a. a = (3::int))"
  using assms
  by (ctxt_tactic "__normalized_input")

lemma local_input_1:
  assumes "(\<forall>a. a = (3::int))"
  shows "(\<forall>a. a = (3::int))"
  using assms
  by (ctxt_tactic "__local_input")

lemma local_input_2:
  assumes "a \<and> (b \<or> c)"
  shows "a \<and> (b \<or> c)"
  using assms
  by (ctxt_tactic "__local_input")

lemma local_input_3:
  assumes "a \<and> a"
  shows "a \<and> a"
  using assms
  by (ctxt_tactic "__local_input")

lemma local_input_4:
  assumes "(\<forall>a. a = (3::int))"
  shows "(\<forall>a. a = (3::int))"
  using assms
  by (ctxt_tactic "__local_input")

(* Rule 2: hole *)

(* No checking necessary*)

(* Rule 3: true*)

lemma true_1: "\<top>"
  by (ctxt_tactic "true")

(* Rule 4: false*)

lemma false_2: "\<not>\<bottom>"
  by (ctxt_tactic "false_rule")

(* Rule 5: not_not*)

lemma not_not_1: "\<not>\<not>\<not>a \<or> a"
  by (ctxt_tactic "not_not")

lemma not_not_2: "\<not>\<not>\<not>\<not>a \<or> \<not>a"
  by (ctxt_tactic "not_not")

lemma not_not_3: "\<not>\<not>\<not>(\<not>a \<or> b) \<or> (\<not>a \<or> b)"
  by (ctxt_tactic "not_not")

(* Rule 5 & 6: resolution and th_resolution*)

lemma resolution_1:
  assumes "a" "\<not>a"
  shows "False"
  using assms
  by (ctxt_tactic "unit_res")

lemma resolution_2:
  assumes "a \<or> b" "\<not>a"
  shows "b"
  using assms
  by (ctxt_tactic "unit_res")

lemma resolution_3:
  assumes "a \<or> b" "\<not>a \<or> c"
  shows "b \<or> c"
  using assms
  by (ctxt_tactic "unit_res")

(* Rule 8: tautology *)

lemma tautology_1:
  assumes "a \<or> b \<or> \<not>a \<or> c"
  shows "True"
  using assms
  by (ctxt_tactic "tautology")


(* Rule 9: contraction *)

lemma contraction_1:
  assumes "a \<or> b"
  shows "a \<or> b"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_2:
  assumes "a \<or> a"
  shows "a"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_3:
  assumes "a \<or> b \<or> a \<or> c"
  shows "a \<or> b \<or> c"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_4:
  assumes "a \<or> b \<or> a \<or> b"
  shows "a \<or> b"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_5:
  assumes "a \<or> (b \<longrightarrow> c) \<or> (b \<longrightarrow> c) \<or> b"
  shows "a \<or> (b \<longrightarrow> c) \<or> b"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_6:
  assumes "a \<or> (b \<or> c) \<or> (b \<or> c) \<or> b"
  shows "a \<or> (b \<or> c) \<or> b"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_7:
  assumes "(b \<or> c) \<or> a \<or> (b \<or> c)"
  shows "a \<or> (b \<or> c)"
  using assms
  by (ctxt_tactic "contraction")

lemma contraction_8:
  assumes "((\<not> y3 \<or> \<not> y689) \<or> \<not> \<not> y689) \<or> (\<not> y3 \<or> \<not> y689) \<or> \<not> \<not> y689"
  shows "(\<not> y3 \<or> \<not> y689) \<or> \<not> \<not> y689"
  using assms
  by (ctxt_tactic "contraction")

(* Rule 11: la_generic *)

lemma la_generic_1:
"1 / 5 * y + 3 / 10 \<noteq> 1 / 5 * y + 3 / 10 \<or> 1 / 3 * y \<noteq> - 1 / 5 + 1 / 5 * y \<or> - 3 / 2 \<le> y"
  by (ctxt_tactic "la_generic")



(* Rule 13: la_disequality *)

lemma la_disequality_1: "(a::int) = b \<or> \<not> (a::int) \<le> b \<or> \<not> b \<le> (a::int)"
  by (ctxt_tactic "la_disequality")

lemma la_disequality_2: "(1::int) = (5-4) \<or> \<not> (1::int) \<le> (5-4) \<or> \<not> (5-4) \<le> (1::int)"
  by (ctxt_tactic "la_disequality")

lemma la_disequality_3: "(2::int) = (7-2) \<or> \<not> (2::int) \<le> (7-2) \<or> \<not> (7-2) \<le> (2::int)"
  by (ctxt_tactic "la_disequality")

lemma la_disequality_4: "(2::int) = (7-6) \<or> \<not> (2::int) \<le> (7-6) \<or> \<not> (7-6) \<le> (2::int)"
  by (ctxt_tactic "la_disequality")


(* Rule 14: la_tautology *)

lemma la_totality_1: "(a::int) \<le> b \<or> b \<le> a"
  by (ctxt_tactic "la_totality")

lemma la_totality_2: "((2::int) - 6) \<le> (3 + 4) \<or> (3 + 4)  \<le> ((2::int) - 6)"
  by (ctxt_tactic "la_totality")


(* Rule 15: la_tautology *)

lemma la_tautology_form1_1: "\<not>((1::int) = 2)"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form1_2: "((2::int) < 5)"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form1_3: "((14::int) \<ge> 6)"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form1_4: "((14::int) \<ge> (6-3+1))"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form1_5: "\<not>((-14::int) \<ge> -(6-3+1))"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form2_1: "((a::int) \<le> 11) \<or> \<not>(a \<le> 11)"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form2_2: "(a::int) \<le> 11 \<or> \<not>(a \<le> (66 - 55))"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form2_3: "\<not>(((5::int) + 4) \<le> 11) \<or> \<not>(((5::int) + 4) \<ge> 11)"
  by (ctxt_tactic "la_tautology")

lemma la_tautology_form2_4: "\<not>(((5::int) + 4) \<le> 11) \<or> \<not>(((5::int) + 4) \<ge> 25)"
  by (ctxt_tactic "la_tautology")


(* Rule 16: la_mult_pos*)

lemma la_mult_pos_1: "(0::int) < 3 \<and> (A::int) < 0 \<longrightarrow> 3 * A < 3 * 0 "
  by (ctxt_tactic "la_mult_pos")

lemma la_mult_pos_2: "(0::int) < 3 \<and> (-3::int) < 0 \<longrightarrow> (3::int) * (-3) < 3 * 0"
  by (ctxt_tactic "la_mult_pos")

lemma la_mult_pos_3: "(0::int) < 5 \<and> \<not>((-3::int) = -77) \<longrightarrow> \<not>((5::int) * (-3) = 5 * -77)"
  by (ctxt_tactic "la_mult_pos")


(* Rule 23: trans *)                              

lemma trans_1:
  assumes "a = a"
  shows  "a = a"
  using assms
  by (ctxt_tactic "trans")

lemma trans_2:
  assumes "a = a" "a = b"
  shows  "a = b"
  using assms
  by (ctxt_tactic "trans")

lemma trans_3:
  assumes "(a = f a)" "(f a = b)"
  shows  "a = b"
  using assms
  by (ctxt_tactic "trans")

lemma trans_4:
  assumes "(a = f a)" "(f a = b)" "(f a = a)"
  shows  "a = a"
  using assms
  by (ctxt_tactic "trans")


(* Rule 25: eq_reflexive *)

lemma eq_reflexive_1: "a = a"
  by (ctxt_tactic "eq_reflexive")

lemma eq_reflexive_2: "3 = (3::int)"
  by (ctxt_tactic "eq_reflexive")

lemma eq_reflexive_3: "(a = b) = (a = b)"
  by (ctxt_tactic "eq_reflexive")


(* Rule 26: eq_transitive *)

lemma eq_transitive_1: "\<not> (a = a) \<or> (a = a)"
  by (ctxt_tactic "eq_transitive")

lemma eq_transitive_2: "\<not> (a = a) \<or> \<not>(a = b) \<or> (a = b)"
  by (ctxt_tactic "eq_transitive")

lemma eq_transitive_3: "\<not> (a = f a) \<or> \<not>(f a = b) \<or> (a = b)"
  by (ctxt_tactic "eq_transitive")

lemma eq_transitive_4: "\<not> (a = f a) \<or> \<not>(f a = b) \<or> \<not>(f a = a) \<or> (a = a)"
  by (ctxt_tactic "eq_transitive")


(* Rule 27: eq_congruent *)

lemma eq_congruent_1: "\<not> (a = a) \<or> (a = a)"
  by (ctxt_tactic "eq_congruent")

lemma eq_congruent_2: "\<not> (a = a) \<or> \<not>(a = b) \<or> (f a a = f a b)"
  by (ctxt_tactic "eq_congruent")

lemma eq_congruent_3: "\<not> (3 = 2 + (1::int)) \<or> \<not>(c = g b) \<or> ((3 + c) = ((2 + (1::int)) + g b))"
  by (ctxt_tactic "eq_congruent")


(* Rule 28: eq_congruent_pred *)

lemma eq_congruent_pred_1: "\<not> (a = a) \<or> (a = a)"
  by (ctxt_tactic "eq_congruent_pred")

lemma eq_congruent_pred_2: "\<not> (a = a) \<or> \<not>(a = b) \<or> (P a a = P a b)"
  by (ctxt_tactic "eq_congruent_pred")





(* Rule 30: and *)

lemma and_1:
  assumes "a \<and> b \<and> c"
  shows  "a"
  using assms
  by (ctxt_tactic "and" "0::int")

lemma and_2:
  assumes "a \<and> b \<and> c"
  shows  "c"
  using assms
  by (ctxt_tactic "and" "1::int")

lemma and_3:
  assumes "(a \<and> d) \<and> b \<and> c"
  shows  "(a \<and> d)"
  using assms
  by (ctxt_tactic "and" "0::int")

lemma and_4:
  assumes "a \<and> b \<and> (c \<and> d)"
  shows  "c \<and> d"
  using assms
  by (ctxt_tactic "and" "2::int")


(* Rule 31: not_or *)
(*or_neg 0
 1. (a \<or> b \<or> c) \<or> \<not> a 
or neg 1
 1. a \<Longrightarrow> a \<or> b \<or> c *)

lemma not_or_1:
  assumes "\<not>(a \<or> b \<or> c)"
  shows  "\<not>a"
  using assms
  by (ctxt_tactic "not_or" "0::int")

lemma not_or_2:
  assumes "\<not>(a)"
  shows  "\<not>a"
  using assms
  by (ctxt_tactic "not_or" "1::int")

lemma not_or_3:
  assumes "\<not>((a \<or> d) \<or> b \<or> c)"
  shows  "\<not>(a \<or> d)"
  using assms
  by (ctxt_tactic "not_or" "0::int")

lemma not_or_4:
  assumes "\<not>(a \<or> b \<or> (c \<or> d))"
  shows  "\<not>(c \<or> d)"
  using assms
  by (ctxt_tactic "not_or" "2::int")

lemma not_or_5:
  assumes "\<not>(a \<or> b \<or> \<not>(c \<or> d))"
  shows  "\<not>(\<not>(c \<or> d))"
  using assms
  by (ctxt_tactic "not_or" "2::int")

lemma not_or_6:
  assumes " \<not> (\<not> (\<not> 1 \<le> isabelle_internal_TransferToDisk \<and> 1 \<le> isabelle_internal_TaskReady \<and> 1 \<le> isabelle_internal_LoadingMem \<or>
             1 \<le> isabelle_internal_TaskReady \<or> 1 \<le> isabelle_internal_LoadingMem))"
  shows "\<not> \<not> (\<not> 1 \<le> isabelle_internal_TransferToDisk \<and> 1 \<le> isabelle_internal_TaskReady \<and> 1 \<le> isabelle_internal_LoadingMem)"
  using assms
  by (ctxt_tactic "not_or" "0::int")

(* Rule 32: or *)

lemma or_1:
  assumes "(a \<or> b \<or> c)"
  shows  "(a \<or> b \<or> c)"
  using assms
  by (ctxt_tactic "or")

lemma or_2:
  assumes "(a)"
  shows  "a"
  using assms
  by (ctxt_tactic "or")

lemma or_3:
  assumes "((a \<or> d) \<or> b \<or> c)"
  shows  "(a \<or> d) \<or> b \<or> c"
  using assms
  by (ctxt_tactic "or" "0::int")


(* Rule 33: weakening *)
(*TODO: Add rule*)

lemma weakening_1: 
  assumes "a"
  shows  "a \<or> b"
  using assms
  by (ctxt_tactic "weakening")

lemma weakening_2:
  assumes "a \<or> b \<or> c"
  shows  "a \<or> b \<or> c \<or> d \<or> e"
  using assms
  by (ctxt_tactic "weakening")

lemma weakening_3:
  assumes "a \<or> b \<or> c"
  shows  "a \<or> b \<or> c \<or> c \<or> a"
  using assms
  by (ctxt_tactic "weakening")

lemma weakening_4:
  assumes "(a \<or> b) \<or> b \<or> c"
  shows  "(a \<or> b) \<or> c \<or> (c \<or> a) \<or> e"
  using assms
  by (ctxt_tactic "weakening")


(* Rule 34: reordering *)

lemma reordering_1: 
  assumes "b \<or> a"
  shows "a \<or> b"
  using assms
  by (ctxt_tactic "reordering")

lemma reordering_2:
  assumes "a \<or> b \<or> c"
  shows "c \<or> b \<or> a"
  using assms
  by (ctxt_tactic "reordering")

lemma reordering_3:
  assumes "a \<or> b \<or> a"
  shows "a \<or> a \<or> b"
  using assms
  by (ctxt_tactic "reordering")

lemma reordering_4:
  assumes "(a \<or> b) \<or> a \<or> b"
  shows "a \<or> b \<or> (a \<or> b)"
  using assms
  by (ctxt_tactic "reordering")

(* Rule 34: shuffle *)

lemma shuffle_or_1: 
  shows "(b \<or> a) = (a \<or> b)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_2:
  shows "(a \<or> b) = (a \<or> b)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_3: 
  shows "(a \<or> b \<or> c) = (c \<or> a \<or> b)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_4: 
  shows "(a \<or> b \<or> c) = (a \<or> b \<or> c)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_5: 
  shows "(a \<or> b \<or> c \<or> d) = (c \<or> d \<or> b \<or> a)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_6: 
  shows "(a \<or> (b \<or> c) \<or> d) = ((b \<or> c) \<or> d \<or> a)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_7: 
  shows "(a \<or> b \<or> (c \<or> d)) = (a \<or> (c \<or> d) \<or> b)"
  by (ctxt_tactic "shuffle" "HOL.disj")

lemma shuffle_or_8: 
  shows "(a \<or> b \<or> (c \<and> (d \<or> e))) = (a \<or> (c \<and> (d \<or> e)) \<or> b)"
  by (ctxt_tactic "shuffle" "HOL.disj")


lemma shuffle_and_1: 
  shows "(b \<and> a) = (a \<and> b)"
  by (ctxt_tactic "shuffle" "HOL.conj")

lemma shuffle_and_2: 
  shows "(a \<and> a) = (a \<and> a)"
  by (ctxt_tactic "shuffle" "HOL.conj")

lemma shuffle_and_3: 
  shows "(a \<and> b \<and> c) = (b \<and> a \<and> c)"
  by (ctxt_tactic "shuffle" "HOL.conj")

lemma shuffle_and_4: 
  shows "((a \<longrightarrow> b ) \<and> c) = (c \<and> (a \<longrightarrow> b))"
  by (ctxt_tactic "shuffle" "HOL.conj")

lemma shuffle_and_5: 
  shows "(d \<and> (a \<or> b ) \<and> c) = (c \<and> d \<and> (a \<or> b))"
  by (ctxt_tactic "shuffle" "HOL.conj")


ML \<open>

val x
 = Alethe_Replay_Methods.shuffle
 (Context.the_local_context ()) [] [@{term "1::int"}]
 @{term  " (op e4 e4 \<noteq> e4 \<and> op e3 e4 \<noteq> e3 \<and> op e4 e3 \<noteq> e3 \<and> op e2 e4 \<noteq> e2 \<and> op e4 e2 \<noteq> e2 \<and> op e0 e4 \<noteq> e0 \<and> op e1 e4 \<noteq> e1 \<and> op e4 e0 \<noteq> e0 \<and> op e4 e1 \<noteq> e1) =
    (op e0 e4 \<noteq> e0 \<and> op e1 e4 \<noteq> e1 \<and> op e2 e4 \<noteq> e2 \<and> op e3 e4 \<noteq> e3 \<and> op e4 e4 \<noteq> e4 \<and> op e4 e0 \<noteq> e0 \<and> op e4 e1 \<noteq> e1 \<and> op e4 e2 \<noteq> e2 \<and> op e4 e3 \<noteq> e3) "}
 (SOME (CommOp @{term "conj"}))
\<close>

ML \<open>

val y
 = Alethe_Replay_Methods.shuffle
 (Context.the_local_context ()) [] [@{term "1::int"}]
 @{term  " (A \<or> B \<or> (C \<or> D))  = ((C \<or> D) \<or> B \<or> A)"}
 (*@{term  " (A \<or> B \<or> C)  = (C \<or> B \<or> A)"}*)

 (SOME (CommOp @{term "disj"}))


\<close>




(* 

hi0
 1. (a \<and> b \<and> c) = (b \<and> a \<and> c) 
hi
 1. (a \<and> b \<and> c) = ((a \<and> c) \<and> b) 
hi
 1. (a \<and> b \<and> c) = (b \<and> a \<and> c) 
hi
*)



(* Rule 35: not_and *)

lemma not_and_1: 
  assumes "\<not>(a \<and> b \<and> c)"
  shows "\<not>a \<or> \<not>b \<or> \<not>c"
  using assms
  by (ctxt_tactic "not_and")

lemma not_and_2:
  assumes "\<not>a"
  shows "\<not>a"
  using assms
  by (ctxt_tactic "not_and")

lemma not_and_3:
  assumes "\<not>((a \<and> d) \<and> b \<and> c)"
  shows "\<not>(a \<and> d) \<or> \<not>b \<or> \<not>c"
  using assms
  by (ctxt_tactic "not_and")

lemma not_and_4:
  assumes "\<not>(a \<and> b \<and> c \<and> (a \<and> d))"
  shows "\<not>a \<or> \<not>b \<or> \<not>c \<or> \<not>(a \<and> d)"
  using assms
  by (ctxt_tactic "not_and")

lemma not_and_5:
  assumes "\<not>(a \<and> a \<and> a)"
  shows "\<not>a \<or> \<not>a \<or> \<not>a"
  using assms
  by (ctxt_tactic "not_and")


(* Rule 36: xor1 *)

lemma xor1_1: 
  assumes "\<not>(a = b)"
  shows  "a \<or> b"
  using assms
  by (ctxt_tactic "xor1")

lemma xor1_2:
  assumes "\<not>((a \<or> b) = b)"
  shows  "(a \<or> b) \<or> b"
  using assms
  by (ctxt_tactic "xor1")

lemma xor1_3:
  assumes "\<not>((\<not>(a = b)) = b)"
  shows  "(\<not>(a = b)) \<or> b"
  using assms
  by (ctxt_tactic "xor1")

lemma xor1_4:
  assumes "\<not>((a = b) = (\<not>(b = c)))"
  shows  "(a = b) \<or> (\<not>(b = c))"
  using assms
  by (ctxt_tactic "xor1")


(* Rule 37: xor2 *)

lemma xor2_1: 
  assumes "\<not>(a = b)"
  shows  "\<not>a \<or> \<not>b"
  using assms
  by (ctxt_tactic "xor2")

lemma xor2_2:
  assumes "\<not>((a \<or> b) = b)"
  shows  "\<not>(a \<or> b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "xor2")

lemma xor2_3:
  assumes "\<not>((a = b) = b)"
  shows  "\<not>(a = b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "xor2")

lemma xor2_4:
  assumes "\<not>((\<not>(a = b)) = (\<not>(b = c)))"
  shows  "\<not>(\<not>(a = b)) \<or> \<not>(\<not>(b = c))"
  using assms
  by (ctxt_tactic "xor2")


(* Rule 38: not_xor1 *)

lemma not_xor1_1: 
  assumes "\<not>(\<not>(a = b))"
  shows  "a \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_xor1")

lemma not_xor1_2:
  assumes "\<not>(\<not>((a \<or> b) = b))"
  shows  "(a \<or> b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_xor1")

lemma not_xor1_3:
  assumes "\<not>(\<not>((a = b) = b))"
  shows  "(a = b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_xor1")

lemma not_xor1_4:
  assumes "\<not>(\<not>((\<not>(a = b)) = (\<not>(b = c))))"
  shows  "(\<not>(a = b)) \<or> (\<not>(\<not>(b = c)))"
  using assms
  by (ctxt_tactic "not_xor1")


(* Rule 39: not_xor2 *)

lemma not_xor2_1: 
  assumes "\<not>(\<not>(a = b))"
  shows  "\<not>a \<or> b"
  using assms
  by (ctxt_tactic "not_xor2")

lemma not_xor2_2:
  assumes "\<not>(\<not>((a \<or> b) = b))"
  shows  "\<not>(a \<or> b) \<or> b"
  using assms
  by (ctxt_tactic "not_xor2")

lemma not_xor2_3:
  assumes "\<not>(\<not>((a = b) = b))"
  shows  "\<not>(a = b) \<or> b"
  using assms
  by (ctxt_tactic "not_xor2")

lemma not_xor2_4:
  assumes "\<not>(\<not>((\<not>(a = b)) = (\<not>(b = c))))"
  shows  "(\<not>(\<not>(a = b))) \<or> (\<not>(b = c))"
  using assms
  by (ctxt_tactic "not_xor2")


(* Rule 40: implies *)

lemma implies_1: 
  assumes "(a \<longrightarrow> b)"
  shows  "\<not>a \<or> b"
  using assms
  by (ctxt_tactic "implies")

lemma implies_2:
  assumes "((a\<or>b) \<longrightarrow> b)"
  shows  "\<not>(a\<or>b) \<or> b"
  using assms
  by (ctxt_tactic "implies")

lemma implies_3:
  assumes "((a\<longrightarrow>b) \<longrightarrow> b)"
  shows  "\<not>(a\<longrightarrow>b) \<or> b"
  using assms
  by (ctxt_tactic "implies")

lemma implies_4:
  assumes "((a\<longrightarrow>b) \<longrightarrow> (b \<longrightarrow> c))"
  shows  "\<not>(a\<longrightarrow>b) \<or> (b \<longrightarrow> c)"
  using assms
  by (ctxt_tactic "implies")

lemma implies_5:
  assumes "((\<not>(a\<longrightarrow>b)) \<longrightarrow> (b \<longrightarrow> c))"
  shows  "\<not>(\<not>(a\<longrightarrow>b)) \<or> (b \<longrightarrow> c)"
  using assms
  by (ctxt_tactic "implies")


(* Rule 42: not_implies1 *)

lemma not_implies2_1: 
  assumes "\<not>(a \<longrightarrow> b)"
  shows  "\<not>b"
  using assms
  by (ctxt_tactic "not_implies2")

lemma not_implies2_2:
  assumes "\<not>((a\<or>b) \<longrightarrow> b)"
  shows  "\<not>b"
  using assms
  by (ctxt_tactic "not_implies2")

lemma not_implies2_3:
  assumes "\<not>(a \<longrightarrow> (a\<longrightarrow>b))"
  shows  "\<not>(a\<longrightarrow>b)"
  using assms
  by (ctxt_tactic "not_implies2")

lemma not_implies2_4:
  assumes "\<not>((a \<longrightarrow> b) \<longrightarrow> (b \<longrightarrow> c))"
  shows  "\<not>(b \<longrightarrow> c)"
  using assms
  by (ctxt_tactic "not_implies2")

lemma not_implies2_5:
  assumes "\<not>((a \<longrightarrow> b) \<longrightarrow> (\<not>(b \<longrightarrow> c)))"
  shows  "\<not>(\<not>(b \<longrightarrow> c))"
  using assms
  by (ctxt_tactic "not_implies2")


(* Rule 41: not_implies1 *)

lemma not_implies1_1: 
  assumes "\<not>(a \<longrightarrow> b)"
  shows  "a"
  using assms
  by (ctxt_tactic "not_implies1")

lemma not_implies1_2:
  assumes "\<not>((a\<or>b) \<longrightarrow> b)"
  shows  "(a\<or>b)"
  using assms
  by (ctxt_tactic "not_implies1")

lemma not_implies1_3:
  assumes "\<not>((a\<longrightarrow>b) \<longrightarrow> b)"
  shows  "(a\<longrightarrow>b)"
  using assms
  by (ctxt_tactic "not_implies1")

lemma not_implies1_4:
  assumes "\<not>((a\<longrightarrow>b) \<longrightarrow> (b \<longrightarrow> c))"
  shows  "(a\<longrightarrow>b)"
  using assms
  by (ctxt_tactic "not_implies1")

lemma not_implies1_5:
  assumes "\<not>((\<not>(a\<longrightarrow>b)) \<longrightarrow> (b \<longrightarrow> c))"
  shows  "(\<not>(a\<longrightarrow>b))"
  using assms
  by (ctxt_tactic "not_implies1")


(* Rule 43: equiv1 *)

lemma equiv1_1: 
  assumes "(a = b)"
  shows  "\<not>a \<or> b"
  using assms
  by (ctxt_tactic "equiv1")

lemma equiv1_2:
  assumes "((a\<or>b) = b)"
  shows  "\<not>(a\<or>b) \<or> b"
  using assms
  by (ctxt_tactic "equiv1")

lemma equiv1_3:
  assumes "((a=b) = b)"
  shows  "\<not>(a=b) \<or> b"
  using assms
  by (ctxt_tactic "equiv1")

lemma equiv1_4:
  assumes "((a=b) = (b = c))"
  shows  "\<not>(a=b) \<or> (b = c)"
  using assms
  by (ctxt_tactic "equiv1")

lemma equiv1_5:
  assumes "((\<not>(a=b)) = (b = c))"
  shows  "\<not>(\<not>(a=b)) \<or> (b = c)"
  using assms
  by (ctxt_tactic "equiv1")


(* Rule 44: equiv2 *)

lemma equiv2_1: 
  assumes "(a = b)"
  shows  "a \<or> \<not>b"
  using assms
  by (ctxt_tactic "equiv2")

lemma equiv2_2:
  assumes "((a\<or>b) = b)"
  shows  "(a\<or>b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "equiv2")

lemma equiv2_3:
  assumes "((a=b) = b)"
  shows  "(a=b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "equiv2")

lemma equiv2_4:
  assumes "((a=b) = (b = c))"
  shows  "(a=b) \<or> \<not>(b = c)"
  using assms
  by (ctxt_tactic "equiv2")

lemma equiv2_5:
  assumes "((a=b) = (\<not>(b = c)))"
  shows  "(a=b) \<or> \<not>(\<not>(b = c))"
  using assms
  by (ctxt_tactic "equiv2")


(* Rule 45: not_equiv1 *)

lemma not_equiv1_1: 
  assumes "\<not>(a = b)"
  shows  "a \<or> b"
  using assms
  by (ctxt_tactic "not_equiv1")

lemma not_equiv1_2:
  assumes "\<not>((a\<or>b) = b)"
  shows  "(a\<or>b) \<or> b"
  using assms
  by (ctxt_tactic "not_equiv1")

lemma not_equiv1_3:
  assumes "\<not>((a=b) = b)"
  shows  "(a=b) \<or> b"
  using assms
  by (ctxt_tactic "not_equiv1")

lemma not_equiv1_4:
  assumes "\<not>((a=b) = (b = c))"
  shows  "(a=b) \<or> (b = c)"
  using assms
  by (ctxt_tactic "not_equiv1")

lemma not_equiv1_5:
  assumes "\<not>((a=b) = (\<not>(b = c)))"
  shows  "(a=b) \<or> \<not>(b = c)"
  using assms
  by (ctxt_tactic "not_equiv1")


(* Rule 46: not_equiv2 *)

lemma not_equiv2_1: 
  assumes "\<not>(a = b)"
  shows  "\<not>a \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_equiv2")

lemma not_equiv2_2:
  assumes "\<not>((a\<or>b) = b)"
  shows  "\<not>(a\<or>b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_equiv2")

lemma not_equiv2_3:
  assumes "\<not>((a=b) = b)"
  shows  "\<not>(a=b) \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_equiv2")

lemma not_equiv2_4:
  assumes "\<not>((a=b) = (b = c))"
  shows  "\<not>(a=b) \<or> \<not>(b = c)"
  using assms
  by (ctxt_tactic "not_equiv2")

lemma not_equiv2_5:
  assumes "\<not>((a=b) = (\<not>(b = c)))"
  shows  "\<not>(a=b) \<or> \<not>(\<not>(b = c))"
  using assms
  by (ctxt_tactic "not_equiv2")


(* Rule 47: and_pos *)
(*b's are legacy versions where no index was given*)

lemma and_pos_1a: "\<not>(a \<and> b \<and> c) \<or> b"
  by (ctxt_tactic "and_pos" "1::int")

lemma and_pos_1b: "\<not>(a \<and> b \<and> c) \<or> b"
  by (ctxt_tactic "and_pos")

lemma and_pos_2a: "\<not>(a \<and> b \<and> c) \<or> c"
  by (ctxt_tactic "and_pos" "2")

lemma and_pos_2b: "\<not>(a \<and> b \<and> c) \<or> c"
  by (ctxt_tactic "and_pos")

lemma and_pos_3a: "\<not>(a \<and> (b \<and> c) \<and> d) \<or> (b \<and> c)"
  by (ctxt_tactic "and_pos" "1")

lemma and_pos_3b: "\<not>(a \<and> (b \<and> c) \<and> d) \<or> (b \<and> c)"
  by (ctxt_tactic "and_pos")

lemma and_pos_4: "\<not>(a \<and> (b \<and> c) \<and> d) \<or> d"
  by (ctxt_tactic "and_pos" "2")

lemma and_pos_5: "\<not>(a \<and> (b \<or> \<not>c \<and> d)) \<or> (b \<or> \<not>c \<and> d)"
  by (ctxt_tactic "and_pos")

lemma and_pos_6a: "\<not>(a \<and> (b \<and> c)) \<or> (b \<and> c)"
  by (ctxt_tactic "and_pos" "1")

(*
lemma and_pos_6b: "\<not>(a \<and> (b \<and> c)) \<or> (b \<and> c)" (*This should have worked but didn't*)
  by (ctxt_tactic "and_pos")
*)

(* Rule 48: and_neg *)

lemma and_neg_1: "(a \<and> b \<and> c) \<or> \<not>a \<or> \<not>b \<or> \<not>c"
  by (ctxt_tactic "and_neg")

lemma and_neg_2: "(a \<and> (b \<and> c)) \<or> \<not>a \<or> \<not>(b \<and> c)"
  by (ctxt_tactic "and_neg")

lemma and_neg_3: "((a \<and> b) \<and> d) \<or> \<not>(a \<and> b) \<or> \<not>d"
  by (ctxt_tactic "and_neg")

lemma and_neg_4: "(a \<and> d) \<or> \<not>(a \<and> d)"
  by (ctxt_tactic "and_neg")

lemma and_neg_5: "((a = c) \<and> (b \<longrightarrow> \<not>c \<or> d)) \<or> \<not>(a = c) \<or> \<not>(b \<longrightarrow> \<not>c \<or> d)"
  by (ctxt_tactic "and_neg")


(* Rule 49: or_pos *)

lemma or_pos_1: "\<not>(a \<or> b \<or> c) \<or> a \<or> b \<or> c"
  by (ctxt_tactic "or_pos")

lemma or_pos_2: "\<not>(a \<or> (b \<or> c)) \<or> a \<or> b \<or> c"
  by (ctxt_tactic "or_pos")

lemma or_pos_3: "\<not>((a \<or> b) \<or> c) \<or> (a \<or> b) \<or> c"
  by (ctxt_tactic "or_pos")

lemma or_pos_4: "\<not>(\<not>(e \<or> f) \<or> (a \<or> b \<and> c) \<or> d) \<or> \<not>(e \<or> f) \<or> (a \<or> b \<and> c) \<or> d"
  by (ctxt_tactic "or_pos")

lemma or_pos_5: "\<not>(a) \<or> a"
  by (ctxt_tactic "or_pos")

(* Rule 50: or_neg *)

lemma or_neg_1: "(a \<or> b \<or> c) \<or> \<not>a"
  by (ctxt_tactic "or_neg")

lemma or_neg_2: "(a \<or> b \<or> c) \<or> \<not>b"
  by (ctxt_tactic "or_neg")

lemma or_neg_3: "(a \<or> b \<or> c) \<or> \<not>c"
  by (ctxt_tactic "or_neg")

lemma or_neg_4: "((a \<or> b) \<or> c) \<or> \<not>(a \<or> b)"
  by (ctxt_tactic "or_neg")

lemma or_neg_5: "(a \<or> (b \<or> c) \<or> d) \<or> \<not>(b \<or> c)"
  by (ctxt_tactic "or_neg")

lemma or_neg_6: "(a \<or> b \<or> (c \<or> d)) \<or> \<not>(c \<or> d)"
  by (ctxt_tactic "or_neg")

lemma or_neg_7: "((a \<and> b) \<or> b \<or> (\<not>c \<longrightarrow> d)) \<or> \<not>(\<not>c \<longrightarrow> d)"
  by (ctxt_tactic "or_neg")

lemma or_neg_8: "((a \<and> b) \<or> b \<or> \<not>(c \<longrightarrow> d)) \<or> \<not>(\<not>(c \<longrightarrow> d))"
  by (ctxt_tactic "or_neg")

lemma or_neg_9: "(\<not>a \<or> b \<or> c) \<or> \<not>(\<not>a)"
  by (ctxt_tactic "or_neg")

lemma or_neg_10: "(\<not>a \<or> b) \<or> \<not>(\<not>a)"
  by (ctxt_tactic "or_neg")

lemma or_neg_11: "(\<not>a \<or> b) \<or> \<not>b"
  by (ctxt_tactic "or_neg")

lemma or_neg_12: "(a) \<or> \<not>a"
  by (ctxt_tactic "or_neg")

(* Rule 51: xor_pos1 *)

lemma xor_pos1_1: "\<not>(a \<noteq> b) \<or> a \<or> b"
  by (ctxt_tactic "xor_pos1")

lemma xor_pos1_2: "\<not>((a\<or>c) \<noteq> b) \<or> (a\<or>c) \<or> b"
  by (ctxt_tactic "xor_pos1")

(* Rule 52: xor_pos2 *)

lemma xor_pos2_1: "\<not>(a \<noteq> b) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "xor_pos2")

lemma xor_pos2_2: "\<not>((a\<or>c) \<noteq> b) \<or> \<not>(a\<or>c) \<or> \<not>b"
  by (ctxt_tactic "xor_pos2")

lemma xor_pos2_3: "\<not>((a\<and>c) \<noteq> b) \<or> \<not>(a\<and>c) \<or> \<not>b"
  by (ctxt_tactic "xor_pos2")

(* Rule 53: xor_neg1 *)

lemma xor_neg1_1: "(a \<noteq> b) \<or> a \<or> \<not>b"
  by (ctxt_tactic "xor_neg1")

lemma xor_neg1_2: "((a\<or>c) \<noteq> b) \<or> (a\<or>c) \<or> \<not>b"
  by (ctxt_tactic "xor_neg1")

lemma xor_neg1_3: "(b \<noteq> (a\<and>c)) \<or> b \<or> \<not>(a\<and>c)"
  by (ctxt_tactic "xor_neg1")

(* Rule 54: xor_neg2 *)

lemma xor_neg2_1: "(a \<noteq> b) \<or> \<not>a \<or> b"
  by (ctxt_tactic "xor_neg2")

lemma xor_neg2_2: "((a\<or>c) \<noteq> b) \<or> \<not>(a\<or>c) \<or> b"
  by (ctxt_tactic "xor_neg2")

lemma xor_neg2_3: "(b \<noteq> (a\<and>c)) \<or> \<not>b \<or> (a\<and>c)"
  by (ctxt_tactic "xor_neg2")

(* Rule 55: implies_pos *)

lemma implies_pos_1: "\<not>(a \<longrightarrow> b) \<or> \<not>a \<or> b"
  by (ctxt_tactic "implies_pos")

lemma implies_pos_2:  "\<not>((a \<and> b) \<longrightarrow> c) \<or> \<not>(a \<and> b) \<or> c"
  by (ctxt_tactic "implies_pos")

lemma implies_pos_3: "\<not>((a \<longrightarrow> b) \<longrightarrow> c) \<or> \<not>(a \<longrightarrow> b) \<or> c"
  by (ctxt_tactic "implies_pos")

lemma implies_pos_4: "\<not>((a \<longrightarrow> b) \<longrightarrow> (c \<longrightarrow> d)) \<or> \<not>(a \<longrightarrow> b) \<or> (c \<longrightarrow> d)"
  by (ctxt_tactic "implies_pos")

(* Rule 56: implies_neg1 *)

lemma implies_neg_1: "(a \<longrightarrow> b) \<or> a"
  by (ctxt_tactic "implies_neg1")

lemma implies_neg_2:  "((a \<and> b) \<longrightarrow> c) \<or> (a \<and> b)"
  by (ctxt_tactic "implies_neg1")

lemma implies_neg_3: "((a \<longrightarrow> b) \<longrightarrow> c) \<or> (a \<longrightarrow> b)"
  by (ctxt_tactic "implies_neg1")

lemma implies_neg_4: "((a \<longrightarrow> b) \<longrightarrow> (c \<longrightarrow> d)) \<or> (a \<longrightarrow> b)"
  by (ctxt_tactic "implies_neg1")

(* Rule 57: implies_neg2 *)

lemma implies_neg2_1: "(a \<longrightarrow> b) \<or> \<not>b"
  by (ctxt_tactic "implies_neg2")

lemma implies_neg2_2:  "((a \<and> b) \<longrightarrow> c) \<or> \<not>c"
  by (ctxt_tactic "implies_neg2")

lemma implies_neg2_3: "((a \<longrightarrow> b) \<longrightarrow> c) \<or> \<not>c"
  by (ctxt_tactic "implies_neg2")

lemma implies_neg2_4: "((a \<longrightarrow> b) \<longrightarrow> (c \<longrightarrow> d)) \<or> \<not>(c \<longrightarrow> d)"
  by (ctxt_tactic "implies_neg2")

(* Rule 58: equiv_pos1 *)

lemma equiv_pos1_1: "\<not>(a = b) \<or> a \<or> \<not>b"
  by (ctxt_tactic "equiv_pos1")

lemma equiv_pos1_2: "\<not>(a = (b = c)) \<or> a \<or> \<not>(b = c)"
  by (ctxt_tactic "equiv_pos1")

lemma equiv_pos1_3: "\<not>((a = d) = (b = c)) \<or> (a = d) \<or> \<not>(b = c)"
  by (ctxt_tactic "equiv_pos1")

(* Rule 59: equiv_pos2 *)

lemma equiv_pos2_1: "\<not>(a = b) \<or> \<not>a \<or> b"
  by (ctxt_tactic "equiv_pos2")

lemma equiv_pos2_2: "\<not>(a = (b = c)) \<or> \<not>a \<or> (b = c)"
  by (ctxt_tactic "equiv_pos2")

lemma equiv_pos2_3: "\<not>((a = d) = (b = c)) \<or> \<not>(a = d) \<or> (b = c)"
  by (ctxt_tactic "equiv_pos2")

(* Rule 60: equiv_neg1 *)

lemma equiv_neg1_1: "(a = b) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "equiv_neg1")

lemma equiv_neg1_2: "(a = (b = c)) \<or> \<not>a \<or> \<not>(b = c)"
  by (ctxt_tactic "equiv_neg1")

lemma equiv_neg1_3: "((a = d) = (b = c)) \<or> \<not>(a = d) \<or> \<not>(b = c)"
  by (ctxt_tactic "equiv_neg1")

lemma equiv_neg1_4: "((\<not>a) = b) \<or> \<not>(\<not>a) \<or> \<not>b"
  by (ctxt_tactic "equiv_neg1")

(* Rule 61: equiv_neg2 *)

lemma equiv_neg2_1: "(a = b) \<or> a \<or> b"
  by (ctxt_tactic "equiv_neg2")

lemma equiv_neg2_2: "(a = (b = c)) \<or> a \<or> (b = c)"
  by (ctxt_tactic "equiv_neg2")

lemma equiv_neg2_3: "((a = d) = (b = c)) \<or> (a = d) \<or> (b = c)"
  by (ctxt_tactic "equiv_neg2")

lemma equiv_neg2_4: "((\<not>a) = b) \<or> \<not>a \<or> b"
  by (ctxt_tactic "equiv_neg2")

(* Rule 62: ite1 *)

lemma ite1_1: 
  assumes "(If a b c)"
  shows "a \<or> c"
  using assms
  by (ctxt_tactic "ite1")

lemma ite1_2: 
  assumes "(If (If e d f) b c)"
  shows "(If e d f) \<or> c"
  using assms
  by (ctxt_tactic "ite1")

lemma ite1_3: 
  assumes "(If a b (If e d f))"
  shows "a \<or> (If e d f)"
  using assms
  by (ctxt_tactic "ite1")

(* Rule 63: ite2 *)

lemma ite2_1: 
  assumes "(If a b c)"
  shows "\<not>a \<or> b"
  using assms
  by (ctxt_tactic "ite2")

lemma ite2_2: 
  assumes "(If (If e d f) b c)"
  shows "\<not>(If e d f) \<or> b"
  using assms
  by (ctxt_tactic "ite2")

lemma ite2_3: 
  assumes "(If a b (If e d f))"
  shows "\<not>a \<or> b"
  using assms
  by (ctxt_tactic "ite2")

(* Rule 64: ite_pos1 *)

lemma ite_pos1_1: "\<not>(If a b c) \<or> a \<or> c"
  by (ctxt_tactic "ite_pos1")

lemma ite_pos1_2: "\<not>(If a b (a \<or> c)) \<or> a \<or> (a \<or> c)"
  by (ctxt_tactic "ite_pos1")

lemma ite_pos1_3: "\<not>(If a b (d \<or> c)) \<or> a \<or> (d \<or> c)"
  by (ctxt_tactic "ite_pos1")

lemma ite_pos1_4: "\<not>(If a b (If a b c)) \<or> a \<or> (If a b c)"
  by (ctxt_tactic "ite_pos1")

(* Rule 65: ite_pos2 *)

lemma ite_pos2_1: "\<not>(If a b c) \<or> \<not>a \<or> b"
  by (ctxt_tactic "ite_pos2")

lemma ite_pos2_2: "\<not>(If a (a \<or> c) b) \<or> \<not>a \<or> (a \<or> c)"
  by (ctxt_tactic "ite_pos2")

lemma ite_pos2_3: "\<not>(If a b (d \<or> c)) \<or> \<not>a \<or> b"
  by (ctxt_tactic "ite_pos2")

lemma ite_pos2_4: "\<not>(If a (If a b c) (If d b c)) \<or> \<not>a \<or> (If a b c)"
  by (ctxt_tactic "ite_pos2")

(* Rule 66: ite_neg1 *)

lemma ite_neg1_1: "(If a b c) \<or> a \<or> \<not>c"
  by (ctxt_tactic "ite_neg1")

lemma ite_neg1_2: "(If a b (a \<or> c)) \<or> a \<or> \<not>(a \<or> c)"
  by (ctxt_tactic "ite_neg1")

lemma ite_neg1_3: "(If a b (d \<or> c)) \<or> a \<or> \<not>(d \<or> c)"
  by (ctxt_tactic "ite_neg1")

lemma ite_neg1_4: "(If a (If a b c) (If d b c)) \<or> a \<or> \<not>(If d b c)"
  by (ctxt_tactic "ite_neg1")

(* Rule 67: ite_neg2 *)

lemma ite_neg2_1: "(If a b c) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "ite_neg2")

lemma ite_neg2_2: "(If a b (a \<or> c)) \<or> \<not>a \<or> \<not>b"
  by (ctxt_tactic "ite_neg2")

lemma ite_neg2_3: "(If a (d \<or> c)  b) \<or> \<not>a \<or> \<not>(d \<or> c)"
  by (ctxt_tactic "ite_neg2")

lemma ite_neg2_4: "(If a (If a b c) (If d b c)) \<or> \<not>a \<or> \<not>(If a b c)"
  by (ctxt_tactic "ite_neg2")

(* Rule 68: not_ite1 *)

lemma not_ite1_1: 
  assumes "\<not>(If a b c)"
  shows "a \<or> \<not>c"
  using assms
  by (ctxt_tactic "not_ite1")

lemma not_ite1_2: 
  assumes "\<not>(If (If e d f) b c)"
  shows "(If e d f) \<or> \<not>c"
  using assms
  by (ctxt_tactic "not_ite1")

lemma not_ite1_3: 
  assumes "\<not>(If a b (If e d f))"
  shows "a \<or> \<not>(If e d f)"
  using assms
  by (ctxt_tactic "not_ite1")

(* Rule 69: not_ite2 *)

lemma not_ite2_1: 
  assumes "\<not>(If a b c)"
  shows "\<not>a \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_ite2")

lemma not_ite2_2: 
  assumes "\<not>(If (If e d f) b c)"
  shows "\<not>(If e d f) \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_ite2")

lemma not_ite2_3: 
  assumes "\<not>(If a b (If e d f))"
  shows "\<not>a \<or> \<not>b"
  using assms
  by (ctxt_tactic "not_ite2")

(* Rule 70: connective_def *)

(*TODO: Add xor*)
lemma connective_def_1: "\<not>(a = b) = ((\<not>a \<and> b) \<or> (a \<and> \<not>b))"
  by (ctxt_tactic "connective_def")

lemma connective_def_2: "\<not>((a = c) = b) = ((\<not>(a = c) \<and> b) \<or> ((a = c) \<and> \<not>b))"
  by (ctxt_tactic "connective_def")

lemma connective_def_3: "(a = b) = ((a \<longrightarrow> b) \<and> (b \<longrightarrow> a))"
  by (ctxt_tactic "connective_def")

lemma connective_def_4: "(If a b c) = ((a \<longrightarrow> b) \<and> (\<not>a \<longrightarrow> c))"
  by (ctxt_tactic "connective_def")

lemma connective_def_5: "(\<forall>x. y) = (\<not>(\<exists>x. \<not>y))"
  by (ctxt_tactic "connective_def")

lemma connective_def_6: "(\<forall>x. x \<and> a) = (\<not>(\<exists>x. \<not>(x \<and> a)))"
  by (ctxt_tactic "connective_def")

lemma connective_def_7: "(\<forall>x y. x \<and> y) = (\<not>(\<exists>x y. \<not>(x \<and> y)))"
  by (ctxt_tactic "connective_def")

(* Rule 71: and_simplify *)

lemma and_simplify_1: "(True \<and> True) = True"
  by (ctxt_tactic "and_simplify")

lemma and_simplify_2: "(True \<and> a) = a"
  by (ctxt_tactic "and_simplify")

lemma and_simplify_3: "(True \<and> a \<and> False) = False"
  by (ctxt_tactic "and_simplify")

lemma and_simplify_4: "(True \<and> \<not>\<not>a \<and> b \<and> \<not>\<not>\<not>a) = False"
  by (ctxt_tactic "and_simplify")

(* Rule 72: or_simplify *)

lemma or_simplify_1: "(True \<or> True) = True"
  by (ctxt_tactic "or_simplify")

lemma or_simplify_2: "(True \<or> a) = True"
  by (ctxt_tactic "or_simplify")

lemma or_simplify_3: "(True \<or> a \<or> False) = True"
  by (ctxt_tactic "or_simplify")

lemma or_simplify_4: "(False \<or> \<not>\<not>a \<or> b \<or> \<not>\<not>\<not>a) = True"
  by (ctxt_tactic "or_simplify")

(* Rule 73: not_simplify *)

lemma not_simplify_1: "(\<not>False) = True"
  supply [[simp_trace]]
  by (ctxt_tactic "not_simplify")

lemma not_simplify_2: "(\<not>True) = False"
  by (ctxt_tactic "not_simplify")

lemma not_simplify_3: "(\<not>\<not>a) = a"
  by (ctxt_tactic "not_simplify")

lemma not_simplify_4: "(\<not>\<not>\<not>a) = (\<not>a)"
  by (ctxt_tactic "not_simplify")

lemma not_simplify_5: "(\<not>\<not>\<not>True) = False"
  by (ctxt_tactic "not_simplify")

lemma not_simplify_6: "(\<not>\<not>\<not>False) = True"
  by (ctxt_tactic "not_simplify")

(* Rule 74: implies_simplify *)

lemma implies_simplify_1: "((\<not>a) \<longrightarrow> \<not>b) = (b \<longrightarrow> a)"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_2: "False \<longrightarrow> a = True"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_3: "(a \<longrightarrow> True) = True"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_4: "True \<longrightarrow> (a = a)"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_5: "(a \<longrightarrow> False) = (\<not>a)"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_6: "(a \<longrightarrow> a) = True"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_7: "(\<not>a \<longrightarrow> a) = a"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_8: "(a \<longrightarrow> \<not>a) = (\<not>a)"
  by (ctxt_tactic "implies_simplify")

lemma implies_simplify_9: "((False \<longrightarrow> a) \<longrightarrow> (\<not>a)) = (\<not>a)"
  by (ctxt_tactic "implies_simplify")

(* Rule 75: equiv_simplify *)

lemma equiv_simplify_1: "(\<not>b = (\<not>b)) = True"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_2: "(b = (\<not>b)) = False"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_3: "(\<not>b = b) = False"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_4: "(True = b) = b"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_5: "(b = True) = b"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_6: "(False = b) = (\<not>b)"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_7: "(False = b) = (\<not>b)"
  by (ctxt_tactic "equiv_simplify")

lemma equiv_simplify_8: "((\<not>a) = (\<not>b)) = (a = b)"
  by (ctxt_tactic "equiv_simplify")


(* Rule 76: bool_simplify *)

lemma bool_simplify_1:
  shows "(\<not>(a \<longrightarrow> b)) = (a \<and> \<not>b)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_2: 
  shows "\<not>(a \<or> b) = (\<not>a \<and> \<not>b)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_3: 
  shows "\<not>(a \<and> b) = (\<not>a \<or> \<not>b)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_4:
  shows "(a \<longrightarrow> (b \<longrightarrow> c)) = ((a \<and> b) \<longrightarrow> c)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_5: 
  shows "((a \<longrightarrow> b) \<longrightarrow> b) = (a \<or> b)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_6:
  shows "(a \<and> (a \<longrightarrow> b)) = (a \<and> b)"
  by (ctxt_tactic "bool_simplify")

lemma bool_simplify_7:
  shows "((a \<longrightarrow> b) \<and> a) = (a \<and> b)"
  by (ctxt_tactic "bool_simplify")

(* Rule 77: ac_simp *)
lemma ac_simp_1: "(b \<and> b) = b"
  by (ctxt_tactic "ac_simp")

lemma ac_simp_2: "(b \<and> a \<and> b) = (a \<and> b)"
  by (ctxt_tactic "ac_simp")

lemma ac_simp_3: "(b \<and> a \<and> b) = (a \<and> b)"
  by (ctxt_tactic "ac_simp")

lemma ac_simp_4: "(b \<and> ((a \<and> c) \<and> (d \<and> a))) = (a \<and> b \<and> c \<and> d)"
  by (ctxt_tactic "ac_simp")


(* Rule 78: ite_simplify *)
           
lemma ite_simplify_1:
  shows "(If True a b) = a"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_2:
  shows "(If False a b) = b"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_3:
  shows "(If c b b) = b"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_4:
  shows "(If (\<not>c) a b) = (If c b a)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_5:
  shows "(If c (If c a b) d) = (If c a d)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_6:
  shows "(If c a (If c b d)) = (If c a d)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_7:
  shows "(If c True False) = c"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_8:
  shows "(If c False True) = (\<not>c)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_9:
  shows "(If c True d) = (c \<or> d)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_10:
  shows "(If c a False) = (c \<and> a)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_11:
  shows "(If c False a) = (\<not>c \<and> a)"
  by (ctxt_tactic "ite_simplify")

lemma ite_simplify_12:
  shows "(If c a True) = (\<not>c \<or> a)"
  by (ctxt_tactic "ite_simplify")


(* Rule 79: qnt_simplify *)

lemma qnt_simplify_1:
  shows "(\<forall>x1. True) = True"
  by (ctxt_tactic "qnt_simplify")

lemma qnt_simplify_2:
  shows "(\<forall>x1 x2. True) = True"
  by (ctxt_tactic "qnt_simplify")

lemma qnt_simplify_3:
  shows "(\<forall>x1. False) = False"
  by (ctxt_tactic "qnt_simplify")

lemma qnt_simplify_4:
  shows "(\<forall>x1 x2. False) = False"
  by (ctxt_tactic "qnt_simplify")


(* Rule 81: qnt_join *)

lemma qnt_join_1:
  shows "(\<forall>x1. a) = (\<forall>x1. a)"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_2:
  shows "(\<forall>x1 . (\<forall>x2. a \<and> x1)) = (\<forall>x1 x2. a \<and> x1)"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_3: (*TODO: Mathias*)
  shows "(\<forall>x1 (x2::'a). (\<forall>x3 x4. (a \<and> x3 \<or> x4 \<and> x1))) = (\<forall>x1 (x2::'a) x3 x4. (a \<and> x3 \<or> x4 \<and> x1))"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_4:
  shows "(\<forall>x1 x2. (\<forall>x3 . (\<forall>x4. a))) = (\<forall>x1 x2 x3 x4. a)"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_5:
  shows "(\<exists>x1. a) = (\<exists>x1. a)"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_6:
  shows "(\<exists>x1 . (\<exists>x2. a \<and> x1)) = (\<exists>x1 x2. a \<and> x1)"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_7: (*TODO: Mathias*)
  shows "(\<exists>x1 (x2::'a). (\<exists>x3 x4. (a \<and> x3 \<or> x4 \<and> x1))) = (\<exists>x1 (x2::'a) x3 x4. (a \<and> x3 \<or> x4 \<and> x1))"
  by (ctxt_tactic "qnt_join")

lemma qnt_join_8:
  shows "(\<exists>x1 x2. (\<exists>x3 . (\<exists>x4. a))) = (\<forall>x1 x2 x3 x4. a)"
  by (ctxt_tactic "qnt_join")


(* Rule 82: qnt_rm_ununsed *)

lemma qnt_rm_unused_1:
  shows "(\<forall>x1. a) = a"
  by (ctxt_tactic "qnt_rm_unused")

lemma qnt_rm_unused_2:
  shows "(\<forall>x1 x2. x2) = (\<forall>x2. x2)"
  by (ctxt_tactic "qnt_rm_unused")

lemma qnt_rm_unused_3:
  shows "(\<forall>x1 x2 x3. x1 \<and> x3) = (\<forall>x1 x3. x1 \<and> x3)"
  by (ctxt_tactic "qnt_rm_unused")

lemma qnt_rm_unused_4:
  shows "(\<exists>x1. a) = a"
  by (ctxt_tactic "qnt_rm_unused")

lemma qnt_rm_unused_5:
  shows "(\<exists>x1 x2. x2) = (\<exists>x2. x2)"
  by (ctxt_tactic "qnt_rm_unused")

lemma qnt_rm_unused_6:
  shows "(\<exists>x1 x2 x3. x1 \<and> x3) = (\<exists>x1 x3. x1 \<and> x3)"
  by (ctxt_tactic "qnt_rm_unused")


(* Rule 83: eq_simplify *)

lemma eq_simplify_1:
  shows "(a = a) = True"
  by (ctxt_tactic "eq_simplify")

lemma eq_simplify_2:
  shows "((3::int) = 3) = True"
  by (ctxt_tactic "eq_simplify")

lemma eq_simplify_3:
  shows "((3::int) = 4) = False"
  by (ctxt_tactic "eq_simplify")

lemma eq_simplify_4:
  shows "\<not>((3::int) = 3) = False"
  by (ctxt_tactic "eq_simplify")


(* Rule 84: div_simplify *)

lemma div_simplify_1:
  shows "((a::int) div a) = 1"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_2:
  shows "((3::int) = 3) = True"
  by (ctxt_tactic "div_simplify")

lemma div_simplify_3:
  shows "((3::int) = 4) = False"
  by (ctxt_tactic "div_simplify")





(* Rule 92: distinct_elim *)

lemma distinct_elim_1: "(x \<noteq> y) = (x \<noteq> y)"
  by (ctxt_tactic "distinct_elim")

lemma distinct_elim_2: "(((x::bool) \<noteq> y) \<and> ((x::bool) \<noteq> z) \<and> ((y::bool) \<noteq> z)) = False"
  by (ctxt_tactic "distinct_elim")

lemma distinct_elim_3: "(((x::int) \<noteq> y) \<and> ((x::int) \<noteq> z) \<and> ((y::int) \<noteq> z)) = (((x::int) \<noteq> y) \<and> ((x::int) \<noteq> z) \<and> ((y::int) \<noteq> z))"
  by (ctxt_tactic "distinct_elim")

lemma distinct_elim_4: "(((x::bool) \<noteq> y) \<and> ((x::bool) \<noteq> z) \<and> ((x::bool) \<noteq> a) \<and> ((y::bool) \<noteq> z) \<and> ((y::bool) \<noteq> a) \<and> ((z::bool) \<noteq> a)) = False"
  by (ctxt_tactic "distinct_elim")

lemma distinct_elim_5:
  "(((x::bool) \<noteq> y) \<and> ((x::bool) \<noteq> z) \<and> ((x::bool) \<noteq> a) \<and> ((x::bool) \<noteq> b)
 \<and> ((y::bool) \<noteq> z) \<and> ((y::bool) \<noteq> a) \<and> ((y::bool) \<noteq> b)
 \<and> ((z::bool) \<noteq> a) \<and> ((z::bool) \<noteq> b)
 \<and> ((a::bool) \<noteq> b)
 ) = False"
  by (ctxt_tactic "distinct_elim")

lemma distinct_elim_6:
  "(((x::bool) \<noteq> y) \<and> ((x::bool) \<noteq> z) \<and> ((x::bool) \<noteq> a) \<and> ((x::bool) \<noteq> b) \<and> ((x::bool) \<noteq> c)
 \<and> ((y::bool) \<noteq> z) \<and> ((y::bool) \<noteq> a) \<and> ((y::bool) \<noteq> b) \<and> ((y::bool) \<noteq> c)
 \<and> ((z::bool) \<noteq> a) \<and> ((z::bool) \<noteq> b) \<and> ((z::bool) \<noteq> c)
 \<and> ((a::bool) \<noteq> b) \<and> ((a::bool) \<noteq> c)
 \<and> ((b::bool) \<noteq> c)
 ) = False"
  by (ctxt_tactic "distinct_elim")



lemma "(x::bool)=y"
  apply (rule alethe_distinct_elim_2)
  back (* soll man nicht benutzen, auf allen moeglichkeiten arbeiten *)









end