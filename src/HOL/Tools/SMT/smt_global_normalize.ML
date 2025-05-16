(*  Title:      HOL/Tools/SMT/smt_global_normalize.ML
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University Freiburg

   
*)

signature SMT_GLOBAL_NORMALIZE =
sig

  val global_normalize: Proof.context -> ((int * SMT_Util.role) * thm) list -> ((int * SMT_Util.role) * thm) list * Proof.context

end

structure SMT_Global_Normalize: SMT_GLOBAL_NORMALIZE =
struct

open SMT_Config

fun debug_msg ctxt = alethe_debug_msg ctxt "smt_global_normalize"


fun init ctxt = (Termtab.empty, ctxt)
fun finish (defs, ctxt) = (Termtab.fold (cons o snd o snd) defs [], ctxt)

fun replace_lambda basename Us Ts n t (cx as (defs, ctxt)) =
  let
    fun app f = Term.list_comb (f, map Bound [])
  in
    (case Termtab.lookup defs t of
      SOME (f,_) => (app f, cx)
    | NONE =>
        let
          val (n',ctxt') = yield_singleton Variable.variant_fixes basename ctxt
          val n' = n' ^ n 
          val t = (Free (n,@{typ "nat"}))
          val (d,ctxt'') = Local_Defs.define [((Binding.name n',Mixfix.mixfix n'),(Binding.empty_atts,t))] ctxt'

          val f = d |> hd |> fst
          val new = d |> hd |> snd |> snd


          val ctxt'' = fold Thm.declare_hyps (Thm.chyps_of new) ctxt''
          val _ = @{print}("(d,new)",(d,new))

          in (app f, (Termtab.update (t, (f,new)) defs, ctxt'')) end)
  end



fun lift_lambdas basename =
  let
    val basename' = the_default Name.uu basename

    fun traverse _ (t as (Const ("Nat.semiring_1_class.of_nat", _)) $ (Free (n,@{typ "nat"}))) =
         pair t #-> replace_lambda basename' [@{typ "nat"}] [@{typ "int"}] n
      | traverse Ts (t $ u) = traverse Ts (t |> @{print}) ##>> traverse Ts u #>> (op $)
      | traverse _ t = pair t
  in traverse [] end



fun lift_nats' basename ithms ctxt =
  if Config.get ctxt (SMT_Config.nat_as_int) then
    init ctxt
    |> fold_map (fn (x, t) => apfst (pair x) o lift_lambdas basename t) (map (fn (a,b) => (a,Thm.prop_of b)) ithms)
    |-> (fn ts' => finish )
    |>> map Thm.symmetric 
  else ([], ctxt) 

fun global_normalize ctxt ithms =
let
    val (ctxt_nats,  il_defs_thm) =
     lift_nats' (SOME "n_") ithms ctxt
      |-> (fn il_defs_thm => fn ctxt' =>
      let
        val ctxt_nats = fold (fn t => fn cn => Thm.declare_hyps t cn) (List.concat (map Thm.chyps_of il_defs_thm)) ctxt'
      in
        (ctxt_nats, il_defs_thm)
      end) |> @{print}
   val _ = debug_msg ctxt low (fn () => \<^print> ("After global natural number normalization: ", il_defs_thm))

    val norm_thms_unfolded = map (fn a => a ||> (Local_Defs.unfold0 ctxt_nats il_defs_thm)) ithms
in
   (norm_thms_unfolded, ctxt_nats)
end


end
