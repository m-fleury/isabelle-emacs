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
fun get_tac n ctxt _ args = 
let
  val rule = CVC5_Replay_Methods.cvc5_rule_of n
  val rule_name = rule |> Alethe_Replay_Methods.string_of_alethe_rule
  val _ = @{print}("Found tactic (if it is rare-rewrite there might be a typo in the input string)", rule_name)

  (*FIXME: For some reason this function gets called twice... This definitely should not be necessary*)
  val dummys = Const ("Pure.prop", @{typ "prop \<Rightarrow> prop"}) $ (Const ("Pure.term", @{typ "prop \<Rightarrow> prop"}) $ Const ("Pure.dummy_pattern", @{typ "prop"}))

  val prems=[]
  val step_args=[]
  val context_args=[]
  val args= (if rule_name = "and_pos" andalso Option.isSome args
            then SOME (Index (Option.valOf args |> Syntax.read_term ctxt |> HOLogic.dest_number |> snd))
            else NONE)
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

val _ =
 Theory.setup
 (Method.setup \<^binding>\<open>ctxt_tactic\<close>
 (Scan.lift (Parse.string 
             -- (Scan.optional (Scan.option Parse.term) NONE)) >>
   (fn (rule_name,args) => fn ctxt => fn prems => CONTEXT_TACTIC (get_tac rule_name ctxt prems args)))
 "testing tactics <name> ([<args>*])  ")
\<close>

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


(* equiv pos 1*)


lemma "\<not>(a=b) \<or> a \<or> \<not>b"
  by (ctxt_tactic "equiv_pos1")


end