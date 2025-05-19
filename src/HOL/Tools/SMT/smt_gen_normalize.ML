(*  Title:      HOL/Tools/int_lifting.ML
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University Freiburg

   
*)

signature INT_LIFTING =
sig
  type context2 = thm Termtab.table * Proof.context

  val lift_nats': string option ->  ('a * term) list ->
    Proof.context ->  thm list * Proof.context
end

structure Int_Lifting: INT_LIFTING =
struct

fun replace_lambda basename Us Ts n' t (cx as (defs, ctxt)) =
let

    fun app f = Term.list_comb (f, map Bound [])

    val T = Term.fastype_of1 (Us @ Ts, t)
  in
    (case Termtab.lookup defs t of
      SOME (f,_) => (app f, cx)
    | NONE =>
        let
          val (n, ctxt') = yield_singleton Variable.variant_fixes basename ctxt

   val (d,ctxt'') = Local_Defs.define [((Binding.name (n^"new"),Mixfix.mixfix (n^"new")),(Binding.empty_atts,@{term "int (x::nat)"}))] ctxt'
   val _ = @{print}("d",d)
   val _ = @{print}("d'",Thm.assume (Thm.cterm_of ctxt' @{term "u \<equiv> int (x::nat)"}) )

   val f = d |> hd |> fst
   val new = d |> hd |> snd |> snd


   val ctxt'' = fold Thm.declare_hyps (Thm.chyps_of new) ctxt''

   in (app f, (Termtab.update (t, (f,new)) defs, ctxt'')) end)
  end


type context2 = thm Termtab.table * Proof.context

fun init ctxt = (Termtab.empty, ctxt)


fun lift_lambdas basename =
  let
    val basename' = the_default Name.uu basename

    fun traverse Ts (t as (Const ("Nat.semiring_1_class.of_nat", _)) $ (Free (n,@{typ "nat"}))) =
         pair t #-> replace_lambda basename' [@{typ "nat"}] [@{typ "int"}] n
      | traverse Ts (t $ u) = traverse Ts t ##>> traverse Ts u #>> (op $)
      | traverse _ t = pair t
  in traverse [] end


fun finish (defs, ctxt) = (Termtab.fold (cons o snd o snd) defs [], ctxt)

fun lift_nats' basename ts ctxt =
  init ctxt
  |> fold_map (fn (x, t) => apfst (pair x) o lift_lambdas  basename t) ts
  |-> (fn ts' => finish )


end
