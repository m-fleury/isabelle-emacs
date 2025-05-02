(*  Title:      HOL/Tools/SMT/smt_global_normalize.ML
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University Freiburg

   
*)

signature SMT_GLOBAL_NORMALIZE =
sig
  type context2 = thm Termtab.table * Proof.context

  val lift_nats': string option ->  ('a * term) list ->
    Proof.context ->  thm list * Proof.context

  val global_normalize: Proof.context -> ((int * SMT_Util.role) * thm) list -> ((int * SMT_Util.role) * thm) list * Proof.context

end

structure SMT_Global_Normalize: SMT_GLOBAL_NORMALIZE =
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

fun global_normalize ctxt ithms =
let
    val (ctxt_nats,  il_defs_thm) =
     lift_nats' NONE (map (fn (a,b) => (a,Thm.prop_of b)) ithms) ctxt
      |-> (fn il_defs_thm => fn ctxt' =>
      let
        val il_defs_thm = map Thm.symmetric il_defs_thm
        val ctxt_nats = fold (fn t => fn cn => Thm.declare_hyps t cn) (List.concat (map Thm.chyps_of il_defs_thm)) ctxt'
      in
        (ctxt_nats, il_defs_thm)
      end)

    val norm_thms_unfolded = map (fn a => a ||> (Local_Defs.unfold0 ctxt_nats il_defs_thm)) ithms
in
   (norm_thms_unfolded, ctxt_nats)
end


end
