(*  Title:      HOL/Tools/SMT/smt_global_normalize.ML
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University Freiburg

   
*)

signature SMT_GLOBAL_NORMALIZE =
sig
  val global_normalize: Proof.context -> ((int * SMT_Util.role) * thm) list -> ((int * SMT_Util.role) * thm) list * ((int * SMT_Util.role) * thm) list * Proof.context
  exception SMT_GLOBAL_NORMALIZE of string
end

structure SMT_Global_Normalize: SMT_GLOBAL_NORMALIZE =
struct

exception SMT_GLOBAL_NORMALIZE of string

open SMT_Config
fun debug_msg ctxt = alethe_debug_msg ctxt "smt_global_normalize"

fun find_in_table f = (fn (a,(b,_)) => if a = f then SOME b else NONE)

(*TODO: Find existing function to do this*)
fun intify_type_name name = (if name = "Nat.nat" then "Int.int" else name)
fun intify_type (Type (str,Ts)) = (Type (intify_type_name str,map intify_type Ts)) |
    intify_type (T as (TFree (_,_))) = T |
    intify_type (T as (TVar (idN,_))) =  (@{print}("TODO when does this case occur?",idN);T)
fun intify_var (Free (str,T)) = Free (str,intify_type T)

fun all_pure_const T = Const ("Pure.all", (T --> @{typ "prop"}) --> @{typ "prop"});
val nat_cast = @{term "nat::int => nat"}
val int_cast = @{term "int::nat => int"} 

fun mkGeTerm t = (@{term "Orderings.ord_class.greater_eq::int \<Rightarrow> int \<Rightarrow> bool"} $ t $ @{term "0::int"} )

fun split_by_thm ctxt thm B =
  case (thm |> HEADGOAL (resolve_tac ctxt [B])|> try Seq.hd) of
    NONE => raise (SMT_GLOBAL_NORMALIZE "definition of lifted variable has unexpected form")
    | (SOME x) => [x]
fun split ctxt B = (split_by_thm ctxt @{thm conjunct1} B, split_by_thm ctxt @{thm conjunct2} B)

fun obtain_new_variable ctxt new_var_cond lambda_term =
let
  val _ = debug_msg ctxt low (fn () => \<^print> ("Condition for new variable ",new_var_cond))

  val exI_inst = Drule.infer_instantiate' ctxt [NONE,SOME(Thm.cterm_of ctxt lambda_term)] @{thm exI}

  val ex = Goal.prove ctxt [] [] (\<^make_judgment> new_var_cond)
    (fn {context = ctxt', ...} => 
      (print_tac ctxt' "needs to be shown to obtain new variable") THEN
      (HEADGOAL (resolve_tac ctxt' [@{thm alethe_nat_embedding}])
      ORELSE 
        (HEADGOAL (resolve_tac ctxt' [exI_inst])
        THEN (print_tac ctxt' "sdf")
        THEN (unfold_tac ctxt' [@{thm nat_int}])
        THEN (unfold_tac ctxt' [@{thm of_nat_0_le_iff},@{thm simp_thms(6)},@{thm simp_thms(22)},@{thm simp_thms(35)}])
        )
      )
      THEN (* HEADGOAL (Skip_Proof.cheat_tac ctxt') THEN *) (print_tac ctxt' "should be solved by now"))
   val _ = @{print}("ex",ex |> Thm.prop_of)
   val _ = debug_msg ctxt low (fn () => \<^print> ("ex",ex))
   val _ = @{print}("test",new_var_cond |> HOLogic.mk_Trueprop|> Thm.cterm_of ctxt |> Thm.assume )

   fun tactic_to_obtain ctxt = (print_tac ctxt "hi0") THEN  HEADGOAL (eresolve_tac ctxt @{thms exE})
 THEN (print_tac ctxt "hi") (*THEN HEADGOAL (Skip_Proof.cheat_tac ctxt)*)
   val (res, ctxt1) =
       Obtain.result (tactic_to_obtain) [ex] ctxt

   val (x, B) = res |> apfst (snd o the_single) |> apsnd the_single
     handle List.Empty => raise (SMT_GLOBAL_NORMALIZE "Could not obtain all lifted variables") 
     handle Match => raise (SMT_GLOBAL_NORMALIZE "Could not obtain all lifted variables")

   val _ = debug_msg ctxt1 low (fn () => \<^print> ("Obtained new variable ",x," defined by ",B))
in (ctxt1,x,B) end

(*
  For each variable x::nat we want to add (x'::int) and the following theorem:
    \<exists> x'. x = nat x' \<and> x' \<ge> 0

  From that we show that:
    (x::nat) = nat (x'::int)
    (x'::int) \<ge> 0
*)
fun mk_new_variable ctxt subst x t =
let
  (*TODO: Check if name is already used first! Not sure if it matters because Isabelle renames, try out*)
  val x' = "lift_" ^ x
  val new_t = (Free (x',@{typ int}))

   val x_cond = HOLogic.mk_exists (x',@{typ int},
               @{term "HOL.conj :: bool => bool \<Rightarrow> bool"}
             $ (@{term "HOL.eq :: nat => nat \<Rightarrow> bool"} $ t $ (@{term "nat"} $ new_t))
             $ (@{term "Orderings.ord_class.less_eq::int \<Rightarrow> int \<Rightarrow> bool"} $ @{term "0::int"} $ new_t))
        (*("Condition for new variable ",
 Const ("HOL.Ex", "(int \<Rightarrow> bool) \<Rightarrow> bool") $
   Abs ("lift_x", "int",
     Const ("HOL.conj", "bool \<Rightarrow> bool \<Rightarrow> bool") $
       (Const ("HOL.eq", "nat \<Rightarrow> nat \<Rightarrow> bool") $ Free ("x", "nat") $ (Const ("Int.nat", "int \<Rightarrow> nat") $ Bound 0)) $
       (Abs ("x", "int", Abs ("y", "int", Const ("Orderings.ord_class.less_eq", "...") $ Bound 0 $ Bound 1)) $ Bound 0 $
         Const ("Groups.zero_class.zero",
                "int")))*)
  val _ = debug_msg ctxt low (fn () => \<^print> ("x_cond ",x_cond))

   
  val (ctxt1,c_x,B) = obtain_new_variable ctxt x_cond new_t
 
  val x = Thm.term_of c_x  
    
  val subst = Termtab.update (t,(x,B)) subst
  val (B_alpha,B_beta) = split ctxt1 B

in (ctxt1,subst,B_alpha,B_beta,x,B) end


(*
  For each function (f::T) that either returns a natural number or has an argument of type nat
  we want to add (f'::intify T) and one of the following theorems:

  1. if the return type of f is a natural number
      \<exists> f'. \<forall>t1...tn. f t1 ... tn = nat (f t1' ... tn') \<and> (f t1' ... tn') \<ge> 0
     where ti' = (nat ti) if ti has type nat and ti otherwise.

  2. if one of the arguments of f is a natural number but the return type of f is not nat
      \<exists> f'. \<forall>t1...tn. f t1 ... tn = f t1' ... tn'

  When we encounter a concrete term (f u1 ... un) we then instantiate the corresponding theorem with
  the current arguments. An argument ti' is the already translated version of ti.
  This might mean that a conversion to nat has been added to it as expected.
*)
local
  (*
    Naming convention
    f                        original function
    T1 \<Rightarrow> ... \<Rightarrow> Tn \<Rightarrow> T      type of f
    retNat                   true iff T is nat, i.e., f returns a natural number

    f'                       new function
    T1' \<Rightarrow> ... \<Rightarrow> Tn' \<Rightarrow> T'   type of f',
                             Ti' = int, if Ti is a nat
                             Ti' = Ti, otherwise
                             T' = int, if retNat,
                             T' = T, otherwise

    x1, ..., xn              fresh variables of types T1,...,Tn 
    f_xs                      f x1 ... xn            
    x1', ..., xn'            xi' = int xi, if xi is a nat
                             xi' = xi, otherwise
    f'_xs'                   f' x1' ... xn'            
    T1' \<Rightarrow> ... \<Rightarrow> Tn' \<Rightarrow> T'   type of f
    g                        g x1' .. xn' = (nat(f' x1' .. xn')), if retNat
                             g x1' .. xn' = (f' x1' .. xn'), otherwise      
                            
    If a function is used by both f and f', the name h is used. If it is used for both xs and xs' then zs is used
  *)

  (* f, [x1, ..., xn] \<mapsto> f x1 ... xn*)
  fun mk_f_xs f xs = list_comb (f, xs)

  (* f', [x1, ..., xn] \<mapsto> f' x1' ... xn'*)
  fun mk_f'_xs' f' xs =
  let
    val xs' = map (fn xi => (if fastype_of xi = @{typ "nat"} then int_cast $ xi else xi)) xs
  in list_comb (f', xs') end

  (* f' x1' ... xn' \<mapsto> g x1' ... xn' *)
  fun mk_g_xs' retNat f'_xs' = (if retNat then nat_cast $ f'_xs' else f'_xs')

  (* f, f', [x1, ..., xn] to one of the following
       f x1 ... xn = (nat (f' x1' ... xn')) \<and> (f' x1' ... xn') \<ge> 0, if retNat
       f x1 ... xn = (f' x1' ... xn')                              , otherwise
     I.e.
       f_xs = g \<and> f'_xs' \<ge> 0       , if retNat
       f_xs = g                     , otherwise
   *)
  fun mk_f_def_ground retNat f f' xs = 
  let
    val f_xs = mk_f_xs f xs
    val f'_xs' = mk_f'_xs' f' xs 
    val g = mk_g_xs' retNat f'_xs'
    val eq_term = HOLogic.mk_eq (f_xs,g)
  in (if retNat then HOLogic.mk_conj (eq_term,mkGeTerm f'_xs') else eq_term) end
 



  (*Other*)
  (* f, [x1, ..., xn] \<mapsto> f y1 ... yn, where yi = nat (xi::int), if xi is a nat
                                            yi = xi, otherwise *)
  fun mk_nat_f f xs =
  let
    val xs' = map (fn xi => (if fastype_of xi = @{typ "nat"} then nat_cast $ intify_var xi else xi)) xs
    val f_t = mk_f_xs f xs'
  in f_t end

  (* f, [x1, ..., xn] \<mapsto> (int (f y1 ... yn)), if retNat
     f, [x1, ..., xn] \<mapsto> (f y1 ... yn), otherwise
    where yi = nat (xi::int), if xi is a nat
          yi = xi, otherwise *)
  fun mk_nat_f_nat retNat f xs =
  let
    val f_t = mk_nat_f f xs
  in (if retNat then int_cast $ f_t else f_t) end


  fun mk_prop_all xi'_name T' H = all_pure_const T' $ absfree (xi'_name,T') H
  fun mk_hol_all xi'_name T' H = HOLogic.mk_all(xi'_name,T',H)
  fun mk_lambda xi'_name T' H = absfree (xi'_name,(fn @{typ "nat"} => @{typ "int"} | x => x) T') H

  (*Combinator function*)
  (*For a list of types [T1,...,Tn] the function generates n new variables xi=Free(lb_i,Ti). It recursively
    runs through the list until it is empty in which case it returns a ground term. Then, the variables are
    bound.
    Two functions are required as arguments
    1. ground, transforms [x1,..,xn] to a term
    2. all_fun, instructions how a current variable xi is bound, e.g. (fn xi rec \<Rightarrow> \<forall> xi . rec )
    *)
  fun mk_forall ground _ [] _ US = ground (rev US) |
  mk_forall ground all_fun (T::Ts) k US =
  let
    (*TODO: Check if name is already used first!*)
    val xi'_name = "lb" ^ Int.toString(k)
    val xi' = Free(xi'_name,T)
  in
    all_fun xi'_name T (mk_forall ground all_fun Ts (k+1) (xi'::US))
  end

  

in
fun mk_new_fun (subst:(term * thm) Termtab.table) t ts n T' new_args f ctxt = 
let
  val Tt = fastype_of t
  val Tts = (map fastype_of ts)

  val retNat = (Tt = @{typ nat})
  val newf = Free(n,T')
  val newt = (newf,new_args) |> list_comb
  val _ = debug_msg ctxt middle (fn () => \<^print> ("encountered function ",f, " for the first time. Replace by ",newf))

  (*
    \<forall>x1 ... xn. f x1 ... xn = nat(f' x1' ... xn') \<and> f' x1' ... xn' \<ge> 0  or
    \<forall>x1 ... xn. f x1 ... xn = f' x1' ... xn'
  *)
  val forall_term = mk_forall (mk_f_def_ground retNat f newf) mk_hol_all Tts 0 [] 
  val _ = debug_msg ctxt middle (fn () => \<^print> ("forall_term ",forall_term))

  (*
    \<lambda>x1 ... xn. f y1 ... yn
  *)
  val lambda_term = mk_forall (mk_nat_f_nat retNat f) mk_lambda Tts 0 [] 
  val _ = debug_msg ctxt middle (fn () => \<^print> ("lambda_term ",lambda_term))

  (*
    \<exists>f'. \<forall>x1...xn. f x1' ... xn' = (nat (f' x1' ... xn')) \<and> (f' x1' ... xn') \<ge> 0
    \<exists>f'. \<forall>x1...xn. f x1' ... xn' = (f' x1' ... xn')
  *)
  val f_cond = HOLogic.mk_exists (n,T',forall_term)
  val (ctxt1,x,B) = obtain_new_variable ctxt f_cond lambda_term
  
  (* Now show:
       f ?x1' ... ?xn' = (nat (f' ?x1' ... ?xn')) \<and> (f' ?x1' ... ?xn') \<ge> 0
       f ?x1' ... ?xn' = (f' ?x1' ... ?xn')
     where ?xi' = nat ?xi if ?xi is a nat otherwise ?xi *)
  val goal = mk_forall (HOLogic.mk_Trueprop o (mk_f_def_ground retNat f (Thm.term_of x))) mk_prop_all Tts 0 [] 
  val goal_thm = Goal.prove ctxt1 [] [] goal (fn {context: Proof.context, ...}  => 
      print_tac context "hiya" 
      THEN (unfold_tac context [@{thm atomize_all}])
      THEN  print_tac context "hiya2a"
      THEN HEADGOAL (   Method.insert_tac context [B])  THEN  print_tac context "hiya2b"
      THEN HEADGOAL (assume_tac context)  THEN  print_tac context "hiya2" )
   val _ = debug_msg ctxt1 high (fn () => \<^print> ("Showed goal from obtain thm:  ",goal_thm))
 
   val subst = Termtab.update (f,(x |> Thm.term_of,goal_thm)) subst
in 
  (ctxt1,subst,newt,goal_thm,B)
end
end

(*two substs? One to search if concrete term appears again and one for the def itself?*)
fun inst_function_thm ctxt ts ret_nat goal_thm = 
let
  val B' = Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) ts) goal_thm
  val _ = debug_msg ctxt middle (fn () => \<^print> ("Instantiated already existing theorem for current term ",B'))
  (*Only need to split if return type is nat*)
  val (B_alpha,B_beta) = if ret_nat then split ctxt B' else ([B'],[])
in
  (B_alpha,B_beta)
end

fun
  transform ctxt (subst:(term*thm) Termtab.table) alpha beta gamma (t as Const _) = (ctxt,subst,alpha,beta,gamma,t)
| transform ctxt subst alpha beta gamma (t as Var (x,@{typ nat})) =
    (case Termtab.lookup subst t of
      NONE =>
      let
         val _ = @{print}("TODO: current term is var t: ",t)
         (*TODO:Not clear yet what case this in*)
      in (ctxt,subst,alpha,beta,gamma,(Var (x,@{typ int}))) end
    | (SOME (b,_)) => (ctxt,subst,alpha,beta,gamma,b) 
   )
| transform ctxt subst alpha beta gamma (t as Free (x,@{typ nat})) =
    (case Termtab.lookup subst t of
      NONE =>
      let
        val _ = debug_msg ctxt high (fn () => \<^print> ("current term is free variable t that has not been encountered yet ",t))
        val (ctxt1,subst,B_alpha,B_beta,new_t,B) = mk_new_variable ctxt subst x t
      in (ctxt1,subst,alpha @ B_alpha,beta @ B_beta,gamma @ [B],new_t) end
    | (SOME (b,_)) => (ctxt,subst,alpha,beta,gamma,b) 
   )
| transform ctxt subst alpha beta gamma (t as Var (_,_)) = (ctxt,subst,alpha,beta,gamma,t) 
| transform ctxt subst alpha beta gamma t = 
    let 
       val (f,ts) = strip_comb t
       val T = fastype_of f
       val n = (if is_Const f then fst (dest_Const f) else fst (dest_Free f))
       val n' =  "lift_" ^ n
       val _ = debug_msg ctxt middle (fn () => \<^print> ("encountered function ",t))

    in
      (*translate numeral constants directly, skip traversal of arguments*)
      (*int constants just added as an optimization*)
      if n = "Num.numeral_class.numeral" 
      then 
        (ctxt,subst,alpha,beta,gamma,if T = @{typ "nat"} then list_comb (Const (n, @{typ "num \<Rightarrow> int"}), ts) else t)
      else
      let
        (*transform arguments*)
        fun transform_args ctxt2 cum_subst cum_alpha cum_beta cum_gamma new_t [] = (ctxt2,cum_subst,cum_alpha,cum_beta,cum_gamma,new_t) | 
          transform_args ctxt2 cum_subst cum_alpha cum_beta cum_gamma new_t (u::us) =
          let  
            val (ctxt3,sigma_o,alpha_o,beta_o,gamma_o,u_o) = transform ctxt2 cum_subst cum_alpha cum_beta cum_gamma u
          in
            transform_args ctxt3 sigma_o alpha_o beta_o gamma_o (u_o :: new_t) us
          end
        val (ctxt2,subst,alpha,beta,gamma,new_args) = transform_args ctxt subst alpha beta gamma [] (rev ts)


         (*Calculate new type*)
         val T' = intify_type T
      in
        (*Neither return type nor argument type is natural number*)
        if T = T'
        then (ctxt2,subst,alpha,beta,gamma,list_comb (f,new_args))
        (*Native operator. Should not be translated. TODO: Add nat functions*)
        else if (List.exists (fn x => n = x) ["Int.nat", "HOL.implies", "Nat.semiring_1_class.of_nat","HOL.eq"])
        then (ctxt2,subst,alpha,beta,gamma,list_comb (f,new_args))
        else
          let
            val Tt = fastype_of t
            val retNat = (Tt = @{typ nat})
            fun notNum x = x |> strip_comb |> fst |> (fn t => t <> @{term "Num.numeral_class.numeral"})
            fun add_cast [] [] = []|
            add_cast (x::xs) (T::Ts) = (if T = @{typ nat} andalso fastype_of x = @{typ "int"} andalso notNum x then nat_cast $ x else x) :: add_cast xs Ts
            val new_args2 = add_cast new_args (map fastype_of ts)

          in
          (*Check if operator has already been translated*)
          (case Termtab.lookup subst f of
             NONE => 
              let
                 val (ctxt4,subst,f',goal,B) = mk_new_fun subst t ts n' T' new_args f ctxt2
                 val (B_alpha,B_beta) = inst_function_thm ctxt4 new_args2 retNat goal
                 val newt = list_comb (f',new_args)
              in (ctxt4,subst,alpha @ B_alpha,beta @ B_beta,gamma @[B],newt) end
            | (SOME (b,c)) =>
              let
                 val (B_alpha,B_beta) = inst_function_thm ctxt2 new_args2 retNat c
                 val newt = list_comb (b,new_args)
              in (ctxt2,subst,alpha @ B_alpha,beta @ B_beta,gamma,newt) end
          ) end
end 


end



fun global_normalize ctxt ithms =
let
  fun iterate_thms [x] (ctxt',subst,alpha,beta,gamma) = (transform ctxt' subst alpha beta gamma (Thm.prop_of (snd x))) |
      iterate_thms (x::xs) (ctxt',subst,alpha,beta,gamma) =
      let
        val (ctxt',subst,alpha,beta,gamma,_) = (transform ctxt' subst alpha beta gamma (Thm.prop_of (snd x)))
      in iterate_thms xs (ctxt',subst,alpha,beta,gamma) end

  val (ctxt',_,alpha,beta,gamma,_) = iterate_thms ithms (ctxt,Termtab.empty,[],[],[])
  val beta' = map (fn b => HEADGOAL (resolve_tac ctxt' [b]) @{thm "nat_0_le"}) beta  |> map ( Seq.hd) |> @{print}
  val beta'' = map (fn b => ((1,SMT_Util.Axiom),b)) beta'
  val gamma'' = map (fn b => ((1,SMT_Util.Axiom),b)) gamma

  val _ = debug_msg ctxt middle (fn () => \<^print> ("obtained conversions ",alpha,beta''))
  val ithms2 = map (fn (a,b) => (a,Local_Defs.unfold0 ctxt' (alpha @ beta'@ [@{thm alethe_nat_embedding2}]) b)) ithms
  val _ = debug_msg ctxt middle (fn () => \<^print> ("ithms before conversion ",ithms))
  val _ = debug_msg ctxt middle (fn () => \<^print> ("ithms after conversion ",ithms2))

in
 (ithms2,gamma'',ctxt')
end




end
