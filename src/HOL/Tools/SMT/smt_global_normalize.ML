(*  Title:      HOL/Tools/SMT/smt_global_normalize.ML
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University Freiburg

   
*)

signature SMT_GLOBAL_NORMALIZE =
sig

  val global_normalize: Proof.context -> ((int * SMT_Util.role) * thm) list -> ((int * SMT_Util.role) * thm) list * Proof.context
  val pre_global_normalize: Proof.context -> thm list -> thm list * Proof.context

end

structure SMT_Global_Normalize: SMT_GLOBAL_NORMALIZE =
struct

open SMT_Config

fun debug_msg ctxt = alethe_debug_msg ctxt "smt_global_normalize"


fun init ctxt = (Termtab.empty, ctxt)
fun finish (defs, ctxt) = (Termtab.fold (cons o snd o snd) defs [], ctxt)

fun replace_lambda basename Ts n t (cx as (defs, ctxt)) =
  let
    fun app f = Term.list_comb (f, map Bound [])
    fun map_types f f' t =
    let
      fun typ (Type (a, Ts)) = Type ((f' a), map typ Ts)
        | typ T = f T
    in typ t end;

    val new_typ = map_types (fn x => x) (fn "Nat.nat" => "Int.int" | x => x) Ts
    val _ = @{print}("new_typ",new_typ)
  in
    (case Termtab.lookup defs t of
      SOME (f,_) => (app f, cx)
    | NONE =>
        let
          val (n',ctxt') = yield_singleton Variable.variant_fixes basename ctxt
          val n' = n' ^ n 
          val t = Const ("Nat.semiring_1_class.of_nat", @{typ "nat \<Rightarrow> int"}) $ (Free (n,@{typ "nat"}))
          val (d,ctxt'') = Local_Defs.define [((Binding.name n',Mixfix.mixfix n'),(Binding.empty_atts,t))] ctxt'

          val f = d |> hd |> fst
          val new = d |> hd |> snd |> snd |>  Thm.symmetric


          val ctxt'' = fold Thm.declare_hyps (Thm.chyps_of new) ctxt''
          val _ = @{print}("(d,new)",(d,new))

          in (app f, (Termtab.update (t, (f,new)) defs, ctxt'')) end)
  end


fun replace_lambda2 basename Ts n ts t  (cx as (defs, ctxt)) =
  let
    fun app f = Term.list_comb (f, map Bound [])
    fun map_types f f' t =
    let
      fun typ (Type (a, Ts)) = Type ((f' a), map typ Ts)
        | typ T = f T
    in typ t end;

    val new_typ = map_types (fn x => x) (fn "Nat.nat" => "Int.int" | x => x) Ts
    val _ = @{print}("new_typ",new_typ)
    val _ = @{print}("t",t)
    val _ = @{print}("Ts",Ts)
    val prem_typ = Term.binder_types Ts 
    val _ = @{print}("prem_typ",prem_typ)
    val prem_typ2 = prem_typ ---> @{typ int}
    val _ = @{print}("prem_typ2",prem_typ2)

  in
    (case Termtab.lookup defs t of
      SOME (f,_) => (app f, cx)
    | NONE =>
        let
          val (n',ctxt') = yield_singleton Variable.variant_fixes basename ctxt
          val n' = n' ^ n 
          fun qqq [x] = x |
              qqq (x::xs) = x $ qqq xs
          fun mk_t' []  ys i = Const ("Nat.semiring_1_class.of_nat", @{typ "(nat \<Rightarrow> int)"}) $ (Term.list_comb ((Free (n,Ts)), ys)) |
              mk_t' (x::xs) ys i = Abs ("uT_" ^ Int.toString i, x, mk_t' xs ( Bound i :: ys) (i + 1))
          val t' = mk_t' prem_typ [] 0
          val _ = @{print}("arr",t')
          val _ = @{print} ("h",(fastype_of t'))


          (*val t' =  Const ("Fun.comp",@{typ "(nat \<Rightarrow> int)"} --> Ts --> @{typ "int \<Rightarrow> int \<Rightarrow> int"}  ) $ Const ("Nat.semiring_1_class.of_nat", @{typ "(nat \<Rightarrow> int)"}) $ (Free (n,Ts))
          val _ = @{print}("t'",t')
*)

          val (d,ctxt'') = Local_Defs.define [((Binding.name n',Mixfix.mixfix n'),(Binding.empty_atts,t'))] ctxt'
          val _ = @{print}("(d)",(d))



          val f = d |> hd |> fst
          val new = d |> hd |> snd |> snd
(*\<lambda>x. \<lambda>y. int (f x y)*)

          val ctxt'' = fold Thm.declare_hyps (Thm.chyps_of new) ctxt''
          val _ = @{print}("(d,new)",(d,new))
          val tthm = Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt f),SOME (Thm.cterm_of ctxt (Free (n,Ts))),SOME (Thm.cterm_of ctxt (Term.list_comb ((Free (n,Ts)),ts)))] @{thm alethe_nat_embedding}
          val _ = @{print}("tthm",(tthm))
          val tthm2 = Thm.implies_elim tthm new
          val _ = @{print}("tthm2",(tthm2))

          in (app f, (Termtab.update (t, (f,tthm2)) defs, ctxt'')) end)
  end


fun lift_lambdas basename =
  let
    val basename' = the_default Name.uu basename

    fun traverse _ (t as (Const ("Nat.semiring_1_class.of_nat", _)) $ (Free (n,@{typ "nat"}))) =
         pair t #-> replace_lambda basename' @{typ "int"} n
      (*| traverse _ (t as (Const ("Nat.semiring_1_class.of_nat", _)) $ b) =
        (case strip_comb b of
          ((Free (n,T) ),ts) =>  pair t #-> replace_lambda2 basename' T n ts |
          _ => pair t )*)
      | traverse Ts (t $ u) = traverse Ts t ##>> traverse Ts u #>> (op $)
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





(*
Adds lemmas that change functions f to f':
- if any of the arguments xi of f has type nat
  (f x1 ... xi ... xn) = (f' x1 ... (int xi) ... xn)  
- if the return type is nat
  (f x1 ... xn) = nat (f' x1 ... xn)

Therefore, in the first case:
f' = \<lambda>x1' ... xn'. (f x1' ... (nat xi') ... xn')
then, apply x1'' to xn'' to both sides where xi'' is xi if it is not nat and (int xi) otherwise
(f' x1 ... xn) = (f x1 ... (nat (int xi)) ... xn)
then unfold (nat (int xi)) = xi
(f' x1 ... xn) = (f x1 ... xi ... xn)

And in the second
f' = \<lambda>x1 ... xn. (int (f x1 ... xn))
Then, apply xi to both sides
(f' x1 ... xn) = (int (f x1 ... xn)
Apply nat to both sides
nat (f' x1 ... xn) = nat (int (f x1 ... xn)
then unfold (nat (int xi)) = xi
(f' x1 ... xn) = nat (int (f x1 ... xn)

*)

(*
Instead
Adds lemmas that change functions f to f':
- if any of the arguments xi of f has type nat
  \<lambda>x1 ... xn. f x1 ... xi ... xn = \<lambda>x1...xn. f' x1 ... (int xi) ... xn)  
- if the return type is nat
 \<lambda>x1 ... xn.  (f x1 ... xn) = \<lambda>x1 ... xn. nat (f' x1 ... xn)

Therefore, in the first case:
f' = \<lambda>x1' ... xn'. (f x1' ... (nat xi') ... xn')
then rewrite (nat xi) = int xi
(f' x1 ... xn) = (f x1 ... xi ... xn)

And in the second
f' = \<lambda>x1 ... xn. (int (f x1 ... xn))
Then, apply xi to both sides
(f' x1 ... xn) = (int (f x1 ... xn)
Apply nat to both sides
nat (f' x1 ... xn) = nat (int (f x1 ... xn)
then unfold (nat (int xi)) = xi
(f' x1 ... xn) = nat (int (f x1 ... xn)

*)
fun pre_global_normalize ctxt ithms =
let
    val (ctxt_nats,  il_defs_thm) =
     lift_nats' (SOME "n_") (map (fn it => ((0,SMT_Util.Axiom),it)) ithms) ctxt
      |-> (fn il_defs_thm => fn ctxt' =>
      let
        val ctxt_nats = fold (fn t => fn cn => Thm.declare_hyps t cn) (List.concat (map Thm.chyps_of il_defs_thm)) ctxt'
      in
        (ctxt_nats, il_defs_thm)
      end)
      |> @{print}

   val _ = debug_msg ctxt low (fn () => \<^print> ("After global natural number normalization: ", il_defs_thm))

    val norm_thms_unfolded = map (fn a => a ||> (Local_Defs.unfold0 ctxt_nats il_defs_thm)) (map (fn it => ((0,SMT_Util.Axiom),it)) ithms)
in
   (norm_thms_unfolded |> map snd, ctxt_nats)
end



end
