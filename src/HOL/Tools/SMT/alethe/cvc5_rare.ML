(*  Title:      HOL/Tools/SMT/cvc5_rare.ML
    Author:     Mathias Fleury, Uni Freiburg
    Author:     Hanna Lachnitt, Stanford University

Declaration of the rare rules used for the reconstruction
*)

signature CVC5_RARE =
sig
  val rare_lookup: Context.generic -> string -> thm list option
  val rare_rule: Context.generic -> string -> thm list
  val rare_add: string * string -> Context.generic -> Context.generic
  val rare_rm: string -> Context.generic -> Context.generic
end;


structure CVC5_Rare: CVC5_RARE =
struct

type rare = {rules: (string * string) list}
fun mk_rare rules  = {rules = rules}

val empty_rare = mk_rare []

fun merge_rare ({rules=rules1}:rare, {rules=rules2}:rare) : rare =
  mk_rare (AList.merge (op =) (op =) (rules1, rules2))

structure Data = Generic_Data
(
  type T = rare
  val empty = empty_rare
  val merge = merge_rare
)

fun rare_lookup ctxt name =
  let
    val {rules} = Data.get ctxt
  in
    AList.lookup (op=) rules name
    |> (fn SOME a => SOME (Named_Theorems.get (Context.proof_of ctxt) a)
         | NONE => NONE)
  end

fun rare_rule ctxt = rare_lookup ctxt #> the


fun rare_add name_thy context =
  let
    val {rules} = Data.get context
  in
    Data.map
      (K (mk_rare (AList.update (op =) name_thy rules)))
      context
  end

fun rare_rm name context =
  let
    val {rules} = Data.get context
  in
    Data.map
      (K (mk_rare (AList.delete (op =) name rules)))
      context
  end


fun rare_check_and_add (short, long) context =
  let
    val _ = Named_Theorems.get (Context.proof_of context) long
  in
    rare_add (short, long) context
  end

val _ = Outer_Syntax.command \<^command_keyword>\<open>cvc5_rare\<close>
         "Declare a string of a named_theorems as a rare rules"
    (Parse.string >> (fn long => fn lthy =>
  let
    val short = Long_Name.base_name long
  in
    Toplevel.theory (Context.theory_map (rare_check_and_add ((short, long)))) lthy
  end))

end;
