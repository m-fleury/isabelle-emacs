(*  Title:      HOL/Tools/SMT/smt_global_normalize.ML
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University Freiburg

   
*)

signature SMT_GLOBAL_NORMALIZE =
sig
  val global_normalize: Proof.context -> ((int * SMT_Util.role) * thm) list -> ((int * SMT_Util.role) * thm) list * Proof.context
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

fun mkGeTerm t = @{term "Orderings.ord_class.greater_eq::int \<Rightarrow> int \<Rightarrow> bool"}  $ t $ @{term "0::int"}
fun split_by_thm ctxt thm B =
  case (thm |> HEADGOAL (resolve_tac ctxt [B])|> try Seq.hd) of
    NONE => raise (SMT_GLOBAL_NORMALIZE "definition of lifted variable has unexpected form")
    | (SOME x) => [x]
fun split ctxt B = (split_by_thm ctxt @{thm conjunct1} B, split_by_thm ctxt @{thm conjunct2} B)

fun obtain_new_variable ctxt x_cond lambda_term =
let
   val _ = debug_msg ctxt low (fn () => \<^print> ("x_cond ",x_cond))

  val exI_inst = 
 Drule.infer_instantiate' ctxt [NONE,SOME(Thm.cterm_of ctxt lambda_term)] @{thm exI}
   val _ = debug_msg ctxt low (fn () => \<^print> ("exI_inst ",exI_inst))

  val ex = Goal.prove ctxt [] [] (\<^make_judgment> x_cond)
    (fn {context = ctxt', ...} => 
      (print_tac ctxt "needs to be shown to obtain new variable") THEN
      (HEADGOAL (resolve_tac ctxt' [@{thm alethe_nat_embedding}])
      ORELSE 
        (HEADGOAL (resolve_tac ctxt' [exI_inst])
        THEN (unfold_tac ctxt' [@{thm nat_int}])
        THEN (unfold_tac ctxt' [@{thm of_nat_0_le_iff},@{thm simp_thms(6)},@{thm simp_thms(22)},@{thm simp_thms(35)}])
        )
      )
      THEN (print_tac ctxt "should be solved by now"))

   val tactic_to_obtain = HEADGOAL (eresolve_tac ctxt @{thms exE})
   val (res, ctxt1) =
       Obtain.result (fn _ => tactic_to_obtain) [ex] ctxt
   val ([(_, x)], [B]) = res
     handle Match => raise (SMT_GLOBAL_NORMALIZE "Could not obtain all lifted variables")

   val _ = debug_msg ctxt low (fn () => \<^print> ("Obtained new variable ",x," defined by ",B))
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
  (*TODO: Check if name is already used first!*)
  val x' = "lift_" ^ x
  val new_t = (Free (x',@{typ int}))
  val x_cond = HOLogic.mk_exists (x',@{typ int},
               @{term "HOL.conj :: bool => bool \<Rightarrow> bool"}
             $ (@{term "HOL.eq :: nat => nat \<Rightarrow> bool"} $ t $ (@{term "nat"} $ new_t))
             $ mkGeTerm new_t)
           
  val (ctxt1,x,B) = obtain_new_variable ctxt x_cond new_t
  val subst = Termtab.update (t,(x |> Thm.term_of,B)) subst
  val (B_alpha,B_beta) = split ctxt1 B

in (ctxt1,subst,B_alpha,B_beta,x|> Thm.term_of) end


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

fun mk_new_fun (subst:(term * thm) Termtab.table) t ts n T' new_args f ctxt = 
let
  val Tt = fastype_of t
  val Tts = (map fastype_of ts)

  val retNat = (Tt = @{typ nat})
  val newf = Free(n,T')
  val newt = (newf,new_args) |> list_comb
  val _ = debug_msg ctxt middle (fn () => \<^print> ("encountered function ",f, " for the first time. Replace by ",newf))

  (* x1 ... xn to f x1 ... xn*)
  fun mk_f US = list_comb (f, US)

  (* x1 ... xn to f x1' ... xn',
     where xi' = nat xi if xi is a nat otherwise xi *)
  fun mk_nat_f US =
  let
    val VS = map (fn xi => (if fastype_of xi = @{typ "nat"} then nat_cast $ intify_var xi else xi)) US
    val f_t = list_comb (f, VS)
  in (if retNat then int_cast $ f_t else f_t) end


  (* x1 ... xn to f' x1' ... xn' or to (nat (f' x1' ... xn')) if f returns a nat,
     where xi' = nat xi if xi is a nat otherwise xi *)
  fun mk_nat_f' x US =
  let
    val VS = map (fn xi => (if fastype_of xi = @{typ "nat"} then int_cast $ xi else xi)) US
    val f' = list_comb (x, VS)
  in (f',(if retNat then nat_cast $ f' else f')) end

  (* x1 ... xn to one of the following
       f x1 ... xn = (nat (f' x1' ... xn')) \<and> (f' x1' ... xn') \<ge> 0
       f x1 ... xn = (f' x1' ... xn')
     where xi' = nat xi if xi is a nat otherwise xi *)
  fun mk_ground x US = 
  let
    val (f',f'_nat) = mk_nat_f' x US
    (* x1 ... xn to f x1 ... xn = f' x1' ... xn' or f x1 ... xn = nat (f' x1' ... xn')*)
    val eq_term = HOLogic.mk_eq (mk_f US,f'_nat)
  in (if retNat then HOLogic.mk_conj (eq_term,mkGeTerm f') else eq_term) end

 
  fun mk_prop_all xi'_name T' H = all_pure_const T' $ absfree (xi'_name,T') H
  fun mk_hol_all xi'_name T' H = HOLogic.mk_all(xi'_name,T',H)
  fun mk_lambda xi'_name T' H = absfree (xi'_name,(fn @{typ "nat"} => @{typ "int"} | x => x) T') H


  (*For a list of types [T1,...,Tn] and function trf1 return \<forall>x1 ... xn. (trf1 x1 ... xn) where xi has type int
    if Ti is nat or keeps it original type otherwise
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
 
  val forall_term = mk_forall (mk_ground newf) mk_hol_all Tts 0 [] 
  val _ = debug_msg ctxt middle (fn () => \<^print> ("forall_term ",forall_term))
  val lambda_term = mk_forall mk_nat_f mk_lambda Tts 0 [] 
  val _ = debug_msg ctxt middle (fn () => \<^print> ("lambda_term ",lambda_term))

  (* x1 ... xn to one of the following
       \<exists>f'. \<forall>x1...xn. f x1' ... xn' = (nat (f' x1' ... xn')) \<and> (f' x1' ... xn') \<ge> 0
       \<exists>f'. \<forall>x1...xn. f x1' ... xn' = (f' x1' ... xn')
     where xi' = nat xi if xi is a nat otherwise xi *)
  val f_cond = HOLogic.mk_exists (n,T',forall_term)
  val (ctxt1,x,B) = obtain_new_variable ctxt f_cond lambda_term
  
  (* Now show:
       f ?x1' ... ?xn' = (nat (f' ?x1' ... ?xn')) \<and> (f' ?x1' ... ?xn') \<ge> 0
       f ?x1' ... ?xn' = (f' ?x1' ... ?xn')
     where ?xi' = nat ?xi if ?xi is a nat otherwise ?xi *)
  val goal = mk_forall (HOLogic.mk_Trueprop o (mk_ground (Thm.term_of x))) mk_prop_all Tts 0 [] 
  val goal_thm = Goal.prove ctxt1 [] [] goal (fn {context: Proof.context, ...}  => 
      print_tac context "hiya" 
      THEN (unfold_tac context [@{thm atomize_all}])
      THEN  print_tac context "hiya2a"
      THEN HEADGOAL (   Method.insert_tac context [B])  THEN  print_tac context "hiya2b"
      THEN HEADGOAL (assume_tac context)  THEN  print_tac context "hiya2" )
   val _ = debug_msg ctxt high (fn () => \<^print> ("Showed goal from obtain thm:  ",goal_thm))
 
   val subst = Termtab.update (f,(x |> Thm.term_of,goal_thm)) subst
in 
  (ctxt1,subst,newt,goal_thm)
end

(*two substs? One to search if concrete term appears again and one for the def itself?*)
fun inst_function_thm ctxt ts ret_nat goal_thm = 
let
   val _ = debug_msg ctxt low (fn () => \<^print> ("goal_thm ",goal_thm))
   val _ = debug_msg ctxt low (fn () => \<^print> ("ts ",ts))

  val B' = Drule.infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) ts) goal_thm
  val _ = debug_msg ctxt middle (fn () => \<^print> ("Instantiated already existing theorem for current term ",B'))
  (*Only need to split if return type is nat*)
  val (B_alpha,B_beta) = if ret_nat then split ctxt B' else ([B'],[])
in
  (B_alpha,B_beta)
end

fun apply_subst _ t = t

fun
  transform ctxt (subst:(term*thm) Termtab.table) alpha beta (t as Const _) = (ctxt,subst,alpha,beta,t)
| transform ctxt subst alpha beta (t as Var (x,@{typ nat})) =
    (case Termtab.lookup subst t of
      NONE =>
      let
         val _ = @{print}("TODO: current term is var t: ",t)
         (*TODO:Not clear yet what case this in*)
      in (ctxt,subst,alpha,beta,(Var (x,@{typ int}))) end
    | (SOME (b,_)) => (ctxt,subst,alpha,beta,b) 
   )
| transform ctxt subst alpha beta (t as Free (x,@{typ nat})) =
    (case Termtab.lookup subst t of
      NONE =>
      let
        val _ = debug_msg ctxt high (fn () => \<^print> ("current term is free variable t that has not been encountered yet ",t))
        val (ctxt1,subst,B_alpha,B_beta,new_t) = mk_new_variable ctxt subst x t
      in (ctxt1,subst,alpha @ B_alpha,beta @ B_beta,new_t) end
    | (SOME (b,_)) => (ctxt,subst,alpha,beta,b) 
   )
| transform ctxt subst alpha beta (t as Var (_,_)) = (ctxt,subst,alpha,beta,t) 
| transform ctxt subst alpha beta t = 
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
        (ctxt,subst,alpha,beta,if T = @{typ "nat"} then list_comb (Const (n, @{typ "num \<Rightarrow> int"}), ts) else t)
      else
      let
        (*transform arguments*)
        fun transform_args ctxt2 cum_subst cum_alpha cum_beta new_t [] = (ctxt2,cum_subst,cum_alpha,cum_beta,new_t) | 
          transform_args ctxt2 cum_subst cum_alpha cum_beta new_t (u::us) =
          let  
            val (ctxt3,sigma_o,alpha_o,beta_o,u_o) = transform ctxt2 cum_subst cum_alpha cum_beta (apply_subst cum_subst u)
          in
            transform_args ctxt3 sigma_o alpha_o beta_o (u_o :: new_t) us
          end
        val (ctxt2,subst,alpha,beta,new_args) = transform_args ctxt subst alpha beta [] (rev ts)


         (*Calculate new type*)
         val T' = intify_type T
      in
        (*Neither return type nor argument type is natural number*)
        if T = T'
        then (ctxt,subst,alpha,beta,list_comb (f,new_args))
        (*Native operator. Should not be translated. TODO: Add nat functions*)
        else if (List.exists (fn x => n = x) ["Int.nat", "HOL.implies", "Nat.semiring_1_class.of_nat","HOL.eq"])
        then (ctxt2,subst,alpha,beta,list_comb (f,new_args))
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
                 val (ctxt1,subst,f',goal) = mk_new_fun subst t ts n' T' new_args f ctxt2
                 val (B_alpha,B_beta) = inst_function_thm ctxt1 new_args2 retNat goal
                 val newt = list_comb (f',new_args)
              in (ctxt1,subst,alpha @ B_alpha,beta @ B_beta,newt) end
            | (SOME (b,c)) =>
              let
                 val (B_alpha,B_beta) = inst_function_thm ctxt2 new_args2 retNat c
                 val newt = list_comb (b,new_args)
              in (ctxt2,subst,alpha @ B_alpha,beta @ B_beta,newt) end
          ) end
end 


end



fun global_normalize ctxt ithms =
let
  fun iterate_thms [x] (ctxt',subst,alpha,beta) = (transform ctxt' subst alpha beta (Thm.prop_of (snd x))) |
      iterate_thms (x::xs) (ctxt',subst,alpha,beta) =
      let
        val (ctxt',subst,alpha,beta,_) = (transform ctxt' subst alpha beta (Thm.prop_of (snd x)))
      in iterate_thms xs (ctxt',subst,alpha,beta) end

  val (ctxt',_,alpha,beta,_) = iterate_thms ithms (ctxt,Termtab.empty,[],[])
  val beta' = map (fn b => HEADGOAL (resolve_tac ctxt' [b]) @{thm "nat_0_le"}) beta  |> map ( Seq.hd) |> @{print}
  val beta'' = map (fn b => ((1,SMT_Util.Axiom),b)) beta'

  val _ = debug_msg ctxt middle (fn () => \<^print> ("obtained conversions ",alpha,beta''))
  val ithms2 = map (fn (a,b) => (a,Local_Defs.unfold0 ctxt' (alpha @ beta'@ [@{thm alethe_nat_embedding2}]) b)) ithms
  val _ = debug_msg ctxt middle (fn () => \<^print> ("ithms before conversion ",ithms))
  val _ = debug_msg ctxt middle (fn () => \<^print> ("ithms after conversion ",ithms2))

in
 (ithms2,ctxt)
end




end
