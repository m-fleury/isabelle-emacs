theory SMT_Internals_Regressions_Word
  imports HOL.SMT_CVC_Word
begin
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
  (*arguments are only supported for some rules and are a little brittle*)
  (*maybe I should have parsed tokens, at the time I wrote this I only wanted to test one specific rule*)
  val args= (if member (op =) ["and_pos", "or_neg", "Not_Or", "and"] rule_name andalso Option.isSome args
            then SOME (Index (Option.valOf args |> Syntax.read_term ctxt |> HOLogic.dest_number |> snd))
            else if rule_name = "shuffle" andalso Option.isSome args
            then SOME (CommOp (Option.valOf args |> Syntax.read_term ctxt))
            else if rule_name = "la_generic" andalso Option.isSome args
            (*There has to be an int parser from a string out there...*)
            then 

let
val keyword_list = Keyword.empty_keywords |> Keyword.add_major_keywords [")","("]
 |> Keyword.add_major_keywords ["[","]"] |> Keyword.add_major_keywords [","]

(*TODO: there should be an optional in this for the last comma and can be made far nicer, had to get this working quick*)
val x = (Option.valOf args |> Token.explode keyword_list Position.none
        |> Parse.command_name "["  
        |-- 
 Scan.repeat (Parse.command_name "(" |-- Parse.int --| Parse.command_name "," -- Parse.int --| Parse.command_name ")"
 --| ( Parse.command_name ","))
--  (Parse.command_name "(" |-- Parse.int --| Parse.command_name "," -- Parse.int --| Parse.command_name ")")
 --| ( Parse.command_name "]")
) |> fst |> (fn (ys,z) => ys @ [z])

in 
SOME (Farkas_Coefficients x)
end
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

declare[[show_types,show_sorts]]

lemma poly_simp_rel:
  assumes "(65535::16 word) * ((if (16::int) \<le> (3::int) then 0 else smtlib_bvlshr 1 (word_of_int (3::int))) - 0) =
         1 * (0 - (if (16::int) \<le> (3::int) then 0 else smtlib_bvlshr 1 (word_of_int (3::int))))"
  shows "((if (16::int) \<le> (3::int) then (0::16 word) else smtlib_bvlshr 1 (word_of_int (3::int))) = 0) =
   ((0::16 word) = (if (16::int) \<le> (3::int) then 0 else smtlib_bvlshr 1 (word_of_int (3::int))))"
  using assms
  by (ctxt_tactic "poly_simp_rel")


lemma bv_repeat_elim:
  shows "(smt_repeat (3::nat) (smtlib_extract (15::int) (15::int) (1705::16 word)::1 word)::3 word) =
    word_cat (smtlib_extract (15::int) (15::int) (1705::16 word)::1 word)
     (word_cat (smtlib_extract (15::int) (15::int) (1705::16 word)::1 word)
       (smtlib_extract (15::int) (15::int) (1705::16 word)::1 word) :: 2 word)"
  by (ctxt_tactic "bv_repeat_elim")

thm word_repeat_word_cat
         
end
