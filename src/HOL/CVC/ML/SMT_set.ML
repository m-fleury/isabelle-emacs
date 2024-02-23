(*  Title:      HOL/Tools/SMT/SMT_string.ML
    Author:     Hanna Lachnitt, Stanford

SMT setup for sets. Note: There is no SMT-LIB Set theory, this formalization follows this theory
reference on the cvc5 website
(https://cvc5.github.io/docs/cvc5-1.0.0/theories/sets-and-relations.html). The theory of sets is
not proof producing in cvc5 yet so fine-grained reconstruction is not possible yet. However, this
theory can be used to get an unsat core from cvc5.

TODO: Hard to test before real problem in the Alethe printer is fixed
TODO: We probably don't want to enable this if smt_cvc_lethe is set since the reconstruction
does not work?
*)

signature SMT_Set = 
sig 
   val set_type_parser : SMTLIB.tree * typ list -> typ option
   val set_term_parser :  SMTLIB.tree * term list -> term option
   val setup_builtins : Context.generic -> Context.generic
end


structure SMT_Set: SMT_Set =
struct

(*Parsing into Isabelle from SMT-LIB*)

fun mk_unary n U t =
  let val T = fastype_of t
  in Const (n, T --> U) $ t end

fun mk_binary n U t1 t2 =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
  in Const (n, [T1, T2] ---> U) $ t1 $ t2 end

fun mk_rassoc f t ts =
  let val us = rev (t :: ts)
  in fold f (tl us) (hd us) end

fun set_type_parser (SMTLIB.Sym "Set", [ts]) = SOME (Type(\<^type_name>\<open>Set.set\<close>,[ts]))
  | set_type_parser _ = NONE

fun set_term_parser (SMTLIB.Sym "set.card", [t1]) =
   SOME (mk_unary \<^const_name>\<open>of_nat\<close> \<^typ>\<open>int\<close> (mk_unary \<^const_name>\<open>card\<close> \<^typ>\<open>nat\<close> t1)) 
  | set_term_parser (SMTLIB.Sym "set.member", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>Set.member\<close> \<^typ>\<open>bool\<close> t1 t2)
  | set_term_parser (SMTLIB.Sym "set.singleton", [t1]) =
    let
     val T1 = fastype_of t1
     val U = Type(\<^type_name>\<open>Set.set\<close>,[T1])
    in
     SOME (mk_binary \<^const_name>\<open>insert\<close> U t1 (Const (\<^const_name>\<open>bot\<close>,U)))
    end
  | set_term_parser (SMTLIB.Sym "set.insert", (t1::ts)) =
   (if ts = [] 
    then NONE
    else
     let
      val T = (fastype_of t1)
      val U = (Type(\<^type_name>\<open>Set.set\<close>,[T]))
     in
      SOME (mk_rassoc (fn x => fn y => Const(\<^const_name>\<open>insert\<close>,[T, U] ---> U) $ x $ y) t1 ts)
     end)
  | set_term_parser (SMTLIB.Sym "set.member", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>Set.member\<close> \<^typ>\<open>bool\<close> t1 t2)
  | set_term_parser (SMTLIB.Sym "set.subset", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>less_eq\<close> \<^typ>\<open>bool\<close> t1 t2)
  | set_term_parser (SMTLIB.Sym "set.union", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>sup\<close> (fastype_of t1) t1 t2)
  | set_term_parser (SMTLIB.Sym "set.inter", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>inf\<close> (fastype_of t1) t1 t2)
  | set_term_parser (SMTLIB.Sym "set.minus", [t1,t2]) =
   SOME (mk_binary \<^const_name>\<open>minus\<close> (fastype_of t1) t1 t2)
  | set_term_parser (SMTLIB.Sym "set.complement", [t1]) =
   SOME (mk_unary \<^const_name>\<open>uminus\<close> (fastype_of t1) t1)
  | set_term_parser (SMTLIB.Sym "set.card", [t1]) =
   SOME (mk_unary \<^const_name>\<open>card\<close> \<^typ>\<open>nat\<close> t1)
(* These don't work yet. Their semantics is more intricate.
   They are also written as (as set.empty (Set Int))
  | set_term_parser (SMTLIB.Sym "set.empty", []) =
   SOME (Const (\<^const_name>\<open>bot\<close>,Type(\<^type_name>\<open>Set.set\<close>,[dummyT])))
  | set_term_parser (SMTLIB.Sym "set.universe", []) =
   SOME (Const (\<^const_name>\<open>Pow\<close>,Type(\<^type_name>\<open>Set.set\<close>,[dummyT]))
       $(Const (\<^const_name>\<open>top\<close>,Type(\<^type_name>\<open>Set.set\<close>,[dummyT]))))
*)
  | set_term_parser _ = NONE

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser set_type_parser #>
  SMTLIB_Proof.add_term_parser set_term_parser))

(*Translating from Isabelle into SMT-LIB*)

(*Utils*)

(*Should we really add t? Check with different types*)
fun add_set_const f t  =
let
  (*val x = SMT_Builtin.dest_builtin_typ cx @{typ "int set"}
  val _ = @{print}("x",x)*)
in
 SMT_Builtin.add_builtin_fun' SMTLIB_Interface.setsmtlibC (t,f t)
end

fun add_set_fun f t =
 SMT_Builtin.add_builtin_fun SMTLIB_Interface.setsmtlibC (Term.dest_Const t,K (f t))

fun empty2 (Const ("Orderings.bot_class.bot", Type("Set.set",[t]))) =
let
 val _ = @{print}("t",t)

 (*How to look up t in table and get string?!*)
in
  (*SOME ("(as set.empty )", 1, ts, fn x => (@{print}("x",x);@{term True}))*)
   ("(set.singleton 1)")
end

fun empty4 (Const ("SMT_CVC.bot_type", T)) =
let
 val _ = @{print}("empty4 T",T)
 val x = Term.dest_Type T
 val _ = @{print}("empty4 x",x)

(*Const ("SMT_CVC.bot_type", "'a itself")*)
in
  (*SOME ("(as set.empty )", 1, ts, fn x => (@{print}("x",x);@{term True}))*)
   ("(as set.empty (Set Int))")
end

fun empty3 t T ts =
let
 val _ = @{print}("t",t)
 val _ = @{print}("T",T)
 val _ = @{print}("ts",ts)
val _ = @{print}("test",Type("Set.set",[\<^typ>\<open>bool\<close>]))

in
SOME ("(as set.empty )", 1, [(Const ("itself", T))], fn x => (@{print}("x",x);t))
end

fun empty t T ts =
let
 val _ = @{print}("t",t)
 val _ = @{print}("T",T)
 val _ = @{print}("ts",ts)
val _ = @{print}("test",Type("Set.set",[\<^typ>\<open>bool\<close>]))

in
SOME ("(as set.empty )", 1, ts, fn x => (@{print}("x",x);t))
end

fun set_typ (Type("Set.set",t))  = SOME ("Set",t) |
    set_typ _ = NONE

(*TODO: Find out what this does*)
fun set_term _  _ = ( SOME "botl")

val setup_builtins =
   (SMT_Builtin.add_builtin_typ SMTLIB_Interface.setsmtlibC)
    (Type("Set.set",[\<^typ>\<open>'a\<close>]),set_typ, set_term) #>

  (* (SMT_Builtin.add_builtin_typ SMTLIB_Interface.setsmtlibC)
    (Type("Set.set",[\<^typ>\<open>'a\<close>]),set_typ, (fn a => fn b => SOME "bottle")) #>*)

  fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.setsmtlibC)
 [
   (\<^Const>\<open>card \<^typ>\<open>int\<close>\<close>, "set.card"),
   (\<^Const>\<open>insert \<^typ>\<open>int\<close>\<close>, "set.insert"),
   (\<^term>\<open>sup :: int set \<Rightarrow> _ \<Rightarrow> _ \<close>, "set.union"),
   (\<^term>\<open>inf :: int set \<Rightarrow> _ \<Rightarrow> _ \<close>, "set.inter"),
   (\<^term>\<open>minus :: int set \<Rightarrow> _ \<Rightarrow> _ \<close>, "set.minus"),
   (\<^term>\<open>less_eq :: int set \<Rightarrow> _ \<Rightarrow> _ \<close>, "set.subset"),
   (\<^term>\<open>minus :: int set \<Rightarrow> _ \<close>, "set.complement")




  ] 
#>
 (add_set_const empty2 (\<^Const>\<open>bot \<^Type>\<open>set \<^typ>\<open>int\<close>\<close>\<close>))
(*#>
 (add_set_fun empty3 (\<^Const>\<open>bot \<^Type>\<open>set \<^typ>\<open>bool\<close>\<close>\<close>)) #>
 (add_set_const empty4 (\<^Const>\<open>bot_type \<^typ>\<open>'a\<close>\<close>))*)
(*
Why do not all work?

fold (SMT_Builtin.add_builtin_fun' SMTLIB_Interface.setsmtlibC) [
    (\<^Const>\<open>bot \<^Type>\<open>bool\<close>\<close>, "(as set.empty (Set Bool))"),
    (\<^Const>\<open>bot \<^Type>\<open>set \<^typ>\<open>bool\<close>\<close>\<close>, "(as set.empty (Set Bool))"),
    (\<^Const>\<open>bot \<^typ>\<open>bool\<close>\<close>, "(as set.empty (Set Bool))"),
    (\<^Const>\<open>bot \<^typ>\<open>bool set\<close>\<close>, "(as set.empty (Set Bool))"),
    (\<^Const>\<open>bot \<^typ>\<open>_\<close>\<close>, "(as set.empty (Set Bool))")
  ]*)





(*Sets should just be enabled if the option native_set is true and
there are actually sets or set operators in the term. For now this
just supports none of these since I don't have the context to do the first.*)
fun smtlib_logic "cvc5" _ ctxt = 
    if Config.get ctxt SMT_Config.native_set
    then SOME "QF_UFLIAFS"
    else NONE |
  smtlib_logic _ _ _ = NONE

(*context ist hier von wo die ML datei importiert wird! Es ist ein statischer Kontext*)
val _ = Theory.setup (Context.theory_map (
   SMTLIB_Interface.add_logic (40, smtlib_logic) #>
  setup_builtins))

end;
