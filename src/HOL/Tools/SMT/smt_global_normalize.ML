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
(*
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
*)


  (*TODO: Find existing function to do this*)
  fun intify_type (Type (str,Ts)) =
        let 
          val str2 = (if str = "Nat.nat" then "Int.int" else str)
        in
          (Type (str2,map intify_type Ts))
        end |
      intify_type (T as (TFree (str,S))) = (@{print}("TODO str",str);T) |
      intify_type (T as (TVar (idN,S))) =  (@{print}("TODO str2",str);T)

  fun mkGeTerm t =  Const ("Orderings.ord_class.greater_eq", @{typ "int \<Rightarrow> int \<Rightarrow> bool"})  $ t $ @{term "0::int"} |> @{print}
  fun apply_subst subst t = t (*TODO*)

  fun mk_new_variable ctxt subst x t =
  let
    val x' = "lift_" ^ x
    val new_t = (Free (x',@{typ int}))

    val x_cond = HOLogic.mk_exists (x',@{typ int},
                 Const("HOL.conj",@{typ "bool => bool \<Rightarrow> bool"})
                   $ (Const("HOL.eq",@{typ "nat => nat \<Rightarrow> bool"})
                   $ t $ (@{term "nat"} $ new_t))
                   $ mkGeTerm new_t)              
    val _ = @{print}("x_cond",x_cond)

    val ex = Goal.prove ctxt [] [] (\<^make_judgment> x_cond)
      (fn {context = ctxt', ...} => HEADGOAL (Skip_Proof.cheat_tac ctxt'))
    val _ = @{print}("ex",ex)


     val (([(_, x)], [B]), ctxt1) = ctxt
       |> Obtain.result (fn _ => eresolve_tac ctxt @{thms exE} 1) [ex];
     val _ = @{print}("B",B)
     val _ = @{print}("x",x)

     val (B_alpha,B_beta) =
          ([@{thm conjunct1}|> (HEADGOAL(resolve_tac ctxt1 [B]))|> Seq.hd] ,
                [@{thm conjunct2} |> (HEADGOAL(resolve_tac ctxt1 [B]))|> Seq.hd] )
     val _ = @{print}("(B_alpha,B_beta)",(B_alpha,B_beta))
     val subst = Termtab.update (t,x |> Thm.term_of) subst

   in (ctxt1,subst,B_alpha,B_beta,new_t) end

fun mk_lambda (subst:term Termtab.table)  t ts n T' new_args f ctxt2 = 
let
       (*Make new term*)
                val Tt = fastype_of t
                val Tts = map fastype_of ts

                val retNat = (Tt = @{typ nat})
                val arg_Nat = (List.find (fn t =>  t = @{typ nat}) Tts)
                val newf = Free(n,T')
                val newt = (newf,new_args) |> list_comb

            (*First, search is operator f has already been encountered.
              In that case get f'.

              Otherwise, first make f':
                1. f does not return nat but has an argument of type nat:
                   Prove: \<exists>f'.  f = \<lambda>x1...xn. f' x1 ... (int xi) ... xn
                2. f does return nat but has not argument of type nat
                   Prove: \<exists>f'.  f = \<lambda>x1...xn. nat (f' x1 ... xn) \<and> \<forall>x1. f' x \<ge> 0
                3. If both is the case
                   Prove: \<exists>f'.  f = \<lambda>x1...xn. nat (f' x1 ... (int xi) ... xn) \<and> \<forall>x1. f' x \<ge> 0

              Then, add condition for current term using the proven statements when making f'

              *)
            fun mk_lambda [] k US = let
                val res = list_comb (newf, rev US )
                in if retNat then @{term "nat::int => nat"} $ res else res end|
              mk_lambda (T::Ts) k US =
              let
                 val xi = "a" ^ Int.toString(k)
              in
                (if T = @{typ "nat"}
                then absfree (xi,T) (mk_lambda Ts (k+1) ((@{term "int::nat => int"} $ Free(xi,T)::US)))
                else absfree (xi,T) (mk_lambda Ts k ((Free(xi,T)::US))))
              end
              fun mk_greater_term [] k US = HOLogic.mk_eq(list_comb (newf, rev US ),@{term "0::int"}) |
              mk_greater_term (T::Ts) k US =
              let
                 val xi = "a" ^ Int.toString(k)
              in
                HOLogic.mk_all  (xi,T,(mk_greater_term Ts k ((Free(xi,T)::US))))
              end

            val lambda_term =  mk_lambda (map fastype_of ts) 0 []
            val eq_term = HOLogic.mk_eq(f,lambda_term)
            val conj_term = if retNat then HOLogic.mk_conj(eq_term,mk_greater_term (map fastype_of new_args) 0 []) else eq_term
            val ex_term = HOLogic.mk_exists (n,T',conj_term)
             val _ = @{print}("f",f)

             val _ = @{print}("ex_term",ex_term)

         
            val ex = Goal.prove ctxt2 [] [] (\<^make_judgment> ex_term)
              (fn {context = ctxt', ...} => HEADGOAL (Skip_Proof.cheat_tac ctxt'))
         val _ = @{print}("ex",ex)

         val (([(_, x)], [B]), ctxt1) = ctxt2
            |> Obtain.result (fn _ => eresolve_tac ctxt2 @{thms exE} 1) [ex];
         val B' = Variable.gen_all ctxt2 B;

         val _ = @{print}("B",B)
         val _ = @{print}("x",x)
         val _ = @{print}("B'",B')

           val (B_alpha,B_beta) =
           if retNat
           then ([@{thm conjunct1}|> (HEADGOAL(resolve_tac ctxt1 [B]))|> Seq.hd] ,
                [@{thm conjunct2} |> (HEADGOAL(resolve_tac ctxt1 [B]))|> Seq.hd] )
            else ([B],[])
         val _ = @{print}("(B_alpha,B_beta)",(B_alpha,B_beta))
in 
(ctxt1,subst, B_alpha,B_beta,newt)
end



fun
    transform ctxt (subst:term Termtab.table) alpha beta (t as Const _) = (ctxt,subst,alpha,beta,t)
  | transform ctxt (subst:term Termtab.table) alpha beta (t as Var (x,@{typ nat})) =
    (case Termtab.get_first (fn (a,b) => if a = t then SOME b else NONE) subst of
      NONE =>
      let
         val _ = @{print}("TODO: current term is var t: ",t)
         (*TODO*)
      in (ctxt,subst,alpha,beta,(Var (x,@{typ int}))) end
    | (SOME b) => (ctxt,subst,alpha,beta,b) 
   )
  | transform ctxt (subst:term Termtab.table) alpha beta (t as Free (x,@{typ nat})) =
    (case Termtab.get_first (fn (a,b) => if a = t then SOME b else NONE) subst of
      NONE =>
      let
        val _ = @{print}("current term is free variable t",t)
        val (ctxt1,subst,B_alpha,B_beta,new_t) = mk_new_variable ctxt subst x t
      in (ctxt1,subst,alpha @ B_alpha,beta @ B_beta,new_t) end
    | (SOME b) => (ctxt,subst,[],[],b) 
   )
  | transform ctxt (subst:term Termtab.table) alpha beta (t as Var (_,_)) = (ctxt,subst,alpha,beta,t) 
  | transform ctxt (subst:term Termtab.table) alpha beta t = 
    let 
       val (f,ts) = strip_comb t
       val T = fastype_of f
       val n = (if is_Const f then fst (dest_Const f) else "lift_" ^ fst (dest_Free f))
       val _ = @{print}("current term t=(f,ts)",(f,ts))
    in
       (*numeral constants*)
       (*int constants just added as an optimization*)
       if n = "Num.numeral_class.numeral" 
       then 
          (ctxt,subst,alpha,beta,if T = @{typ "nat"} then list_comb (Const (n, @{typ "num \<Rightarrow> int"}), ts) else t)
       else
       let
         (*Transform arguments*)
         fun transform_args ctxt2 cum_subst cum_alpha cum_beta new_t [] = (ctxt2,cum_subst,cum_alpha,cum_beta,new_t) | 
           transform_args ctxt2 cum_subst cum_alpha cum_beta new_t (u::us) =
           let  
              val (ctxt3,sigma_o,alpha_o,beta_o,u_o) = transform ctxt2 cum_subst [] [] (apply_subst cum_subst u)
           in
               transform_args ctxt3 sigma_o (cum_alpha @ alpha_o) (cum_beta @ beta_o) (u_o :: new_t) us
           end
         val (ctxt2,subst,args_alpha,args_beta,new_args) = transform_args ctxt subst [] [] [] (rev ts)
         val alpha = args_alpha @ alpha
         val beta = args_beta @ beta
         
         (*Calculate new type*)
         val T' = intify_type T
         val _ = @{print}("(old type,new type): (T,T')",(T,T'))

      in
        (*Neither return type nor argument type is natural number*)
        if T = T'
        then (ctxt,subst,alpha,beta,list_comb (f,new_args))
        (*Native operator. Should not be translated. TODO: Add nat functions*)
        else if (List.exists (fn x => n = x) ["Nat.semiring_1_class.of_nat","HOL.eq"])
        then (ctxt2,subst,alpha @ args_alpha,beta @ args_beta,list_comb (f,new_args))
        else
          (*Check if operator has already been translated*)
          (case Termtab.get_first (fn (a,b) => if a = f then SOME b else NONE) subst of
             NONE => 
              let
                 val (ctxt1,subst,B_alpha,B_beta,newt) = mk_lambda subst t ts n T' new_args f ctxt

        
              in (ctxt1,subst,alpha @ B_alpha,beta @ B_beta,newt) end
            | (SOME b) => (ctxt,subst,[],[],list_comb(b,new_args))
)
end 

            
           
(*
       (*val ts = map (transform ctxt) ts*)
       val (arg_type,ret_type) = strip_type (fastype_of f)
       val _ = @{print}("arg_type",arg_type)
       fun new_args [] [] = [] |
           new_args (x::xs) (a::ass) = (if a = @{typ "nat"} then strip_nat x else x)::new_args xs ass
       val _ = @{print}("aaa",new_args ts arg_type)
       val new_arg_type = map nat_to_int arg_type
       val _ = @{print}("new_arg_type",new_arg_type)
       val newT = new_arg_type  ---> ret_type
       val _ = @{print}("newT",newT)

       (*Make f'*)
       val res = 
       if  List.exists (fn t => t = @{typ "nat"}) arg_type
       then
        let
          val _ = @{print}("in here",f)

          val n = (if is_Const f then fst (dest_Const f) else fst (dest_Free f)) ^ "_lift"
          val newf =  Free(n,newT)
          val newt = (newf,new_args ts arg_type) |> list_comb
          (*val tn = Const("Pure.eq",@{typ "int => int \<Rightarrow> prop"}) $ @{term "3::int"} $ Free(n,@{typ "int"})*)  (* (@{term "int::nat \<Rightarrow> int"} $ f)*)
          val tn = Const("Pure.eq",@{typ "int => int \<Rightarrow> prop"}) $ t $ newt
          val temp = Proof.init ctxt 
          val temp2 = Obtain.obtain (Binding.name n) [(Binding.name n, SOME @{typ int}, NoSyn)] [] [] [((Binding.name "x_def",[]),[(tn,[])])] true temp |> Proof.goal
          val _ = @{print}("RESULT",temp2)

       in  [#goal temp2] end
       else []

       val t2 = @{term "((g::nat \<Rightarrow> int \<Rightarrow> int) (x::nat) (2::int)) = 3 \<Longrightarrow> g x 2 = 3"} 
       val solveThm = t2 |> Thm.cterm_of @{context} |> Goal.init
       val _ = @{print}("theorem to solve",solveThm)

       fun as_prop (t as Const (\<^const_name>\<open>Trueprop\<close>, _) $ _) = t
       | as_prop t = HOLogic.mk_Trueprop t
       val newThm = Goal.prove @{context} [] [] t2 (fn _ => ( (print_tac @{context} "hi") THEN Local_Defs.unfold_tac @{context} res THEN Skip_Proof.cheat_tac @{context} 1)) 
       val _ = @{print}("newThm",newThm)
*)

end



fun global_normalize ctxt ithms =
let

  val (ctxt',subst,alpha,beta,res) = transform ctxt Termtab.empty [] [] (Thm.prop_of (hd (map snd ithms)))
  val _ = @{print}("res",res)
  val _ = @{print}("alpha",alpha)
  val _ = @{print}("beta",beta)

  val ithms2 = map (Local_Defs.unfold0 ctxt' alpha) (map snd ithms) @ beta
  val _ = @{print}("ithms2",ithms2)


 (*  val res3 = Thm.implies_elim @{thm conjunct1} (hd res1) |> @{print}*)

in
 (ithms,ctxt)
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
