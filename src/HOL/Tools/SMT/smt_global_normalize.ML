(*  Title:      HOL/Tools/SMT/smt_global_normalize.ML
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University Freiburg

   
   NOTE: This would probably be better with conversions but I don't know well enough how they work.
   TODO: Make recursions pretty so that the functions can be folded.
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
fun debug_msg_tac ctxt = alethe_debug_msg_tac ctxt "smt_global_normalize"

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

fun mkLeTerm t = (@{term "Orderings.ord_class.less_eq::int \<Rightarrow> int \<Rightarrow> bool"} $ @{term "0::int"} $ t )
fun mkGeTerm t = (@{term "Orderings.ord_class.greater_eq::int \<Rightarrow> int \<Rightarrow> bool"} $ t $ @{term "0::int"} )

fun split_by_thm ctxt thm B =
  case (thm |> HEADGOAL (resolve_tac ctxt [B])|> try Seq.hd ) of
    NONE => (@{print}("here");raise (SMT_GLOBAL_NORMALIZE "definition of lifted variable has unexpected form"))
    | (SOME x) => [x]
fun split ctxt B = (split_by_thm ctxt @{thm conjunct1} B, split_by_thm ctxt @{thm conjunct2} B)

(*Deal with quantifiers*)
fun
  preproc_abs bounds i (Abs(var_name,@{typ "nat"},t1)) _ f = 
    let
      val res = preproc (bounds @ [i]) (i+1) t1
      val t1' = f (mkLeTerm (Bound 0),res)
    in (Abs(var_name,@{typ "int"},t1')) end |
  preproc_abs bounds i (Abs(var_name,U1,t1)) T _ = 
    let
      val res = preproc bounds (i+1) t1
    in (Abs(var_name,U1,res)) end |
  preproc_abs _ _ t _ _ = t
and
  preproc bounds i (Const("HOL.All",T) $ t) =
     (Const("HOL.All",intify_type T)) $ preproc_abs bounds i t T HOLogic.mk_imp |
  preproc bounds i (Const("HOL.Ex",T) $ t) =
      (Const("HOL.Ex",intify_type T)) $ preproc_abs bounds i t T HOLogic.mk_conj |
  preproc bounds i (t as (@{term "int"} $ Bound k))
     = (if List.exists (fn x => (i-x-1) = k) bounds then Bound k else t) |
  preproc bounds i (t as Bound k)
     = (if List.exists (fn x => (i-x-1) = k) bounds then @{term "nat"} $ t else t) |
  preproc bounds i (Abs(var_name,T,t1)) = (Abs(var_name,T,preproc bounds i t1)) |
  preproc bounds i (t1 $ t2) = preproc bounds i t1 $ preproc bounds i t2 |
  preproc _ _ t = t


(*Mostly copied from Obtain.result except for call to Variable.focus_cterm (we want to name the new
variable ourselves *)
fun result2 tac n facts ctxt =
  let
    val ((thesis_var, thesis), thesis_ctxt) = Obtain.obtain_thesis ctxt;
    val st = Goal.init (Thm.cterm_of ctxt thesis);
    val rule =
      (case SINGLE (Method.insert_tac thesis_ctxt facts 1 THEN tac thesis_ctxt) st of
        NONE => raise THM ("Obtain.result: tactic failed", 0, facts)
      | SOME th =>
          Obtain.check_result thesis_ctxt thesis (Raw_Simplifier.norm_hhf thesis_ctxt (Goal.conclude th)));

    val closed_rule = Thm.forall_intr (Thm.cterm_of ctxt (Free thesis_var)) rule;
    val ((_, [rule']), ctxt') = Variable.import false [closed_rule] ctxt;
    val obtain_rule =
      Thm.forall_elim (Thm.cterm_of ctxt (Logic.varify_global (Free thesis_var))) rule';
    val ((params, stmt), fix_ctxt) = Variable.focus_cterm (SOME [(Binding.name n)]) (Thm.cprem_of obtain_rule 1) ctxt';
    val (prems, ctxt'') =
      Assumption.add_assms (Obtain.obtain_export fix_ctxt obtain_rule (map #2 params))
        (Drule.strip_imp_prems stmt) fix_ctxt;
  in ((params, prems), ctxt'') end;

(*
Currently, this first shows
 \<exists>lift_foo. \<forall>lb0. foo lb0 = nat (lift_foo (int lb0)) \<and> 0 \<le> lift_foo (int lb0) 
and then shows
  \<And>lift_foo. \<forall>lb0. foo lb0 = nat (lift_foo (int lb0)) \<and> 0 \<le> lift_foo (int lb0)

TODO: This should be done in one step instead

*)

fun obtain_new_variable ctxt new_var_name new_var_cond lambda_term =
let
  val _ = debug_msg ctxt high (fn () => \<^print> ("Condition for new variable ",new_var_cond))

  val exI_inst = Drule.infer_instantiate' ctxt [NONE,SOME(Thm.cterm_of ctxt lambda_term)] @{thm exI}

  val ex = Goal.prove ctxt [] [] (\<^make_judgment> new_var_cond)
    (fn {context = ctxt', ...} => 
          (debug_msg_tac ctxt' high "needs to be shown to obtain new variable") THEN
      (HEADGOAL (resolve_tac ctxt' [@{thm alethe_nat_embedding}])
      ORELSE 
        (HEADGOAL (resolve_tac ctxt' [exI_inst])
        THEN (unfold_tac ctxt' [@{thm nat_int}])
        THEN (unfold_tac ctxt' [@{thm of_nat_0_le_iff},@{thm simp_thms(6)},@{thm simp_thms(22)},@{thm simp_thms(35)}])
        )
      )
      THEN(debug_msg_tac ctxt' high "should be solved by now"))
   val _ = debug_msg ctxt high (fn () => \<^print> ("ex",ex))

   fun tactic_to_obtain ctxt = (debug_msg_tac ctxt high "extract new variable") THEN  HEADGOAL (eresolve_tac ctxt @{thms exE})
 THEN (debug_msg_tac ctxt high "should be solved by now") (*THEN HEADGOAL (Skip_Proof.cheat_tac ctxt)*)
   val (res, ctxt1) =
       result2 (tactic_to_obtain) new_var_name [ex] ctxt


   val (x, B) = res |> apfst (snd o the_single) |> apsnd the_single
     handle List.Empty => raise (SMT_GLOBAL_NORMALIZE "Could not obtain all lifted variables") 
     handle Match => raise (SMT_GLOBAL_NORMALIZE "Could not obtain all lifted variables")

   val _ = debug_msg ctxt1 high (fn () => \<^print> ("Obtained new variable ",x," defined by ",B))
in (ctxt1,x,B) end

(*
  For each variable x::nat we want to add (x'::int) and the following theorem:
    \<exists> x'. x = nat x' \<and> x' \<ge> 0
*)
fun mk_new_variable ctxt subst x t =
let
  (*TODO: Check if name is already used first! Not sure if it matters because Isabelle renames, try out*)
  val x' = "lift_" ^ x
  val new_t = (Free (x',@{typ int}))
  val new_t_ge_0 = mkLeTerm new_t
  val x_cond = HOLogic.mk_exists (x',@{typ int},
               @{term "HOL.conj :: bool => bool \<Rightarrow> bool"}
             $ (@{term "HOL.eq :: nat => nat \<Rightarrow> bool"} $ t $ (@{term "nat"} $ new_t))
             $ new_t_ge_0)
  val _ = debug_msg ctxt low (fn () => \<^print> ("Condition for new variable ",x_cond))

  val (ctxt1,c_x,B) = obtain_new_variable ctxt x' x_cond new_t
  val x = Thm.term_of c_x  
  val subst = Termtab.update (t,(x,B)) subst
  val new_t_ge_0_2 = mkLeTerm x

in (ctxt1,subst,new_t_ge_0_2,x,B) end


fun inst_function_thm ctxt ts ret_nat goal_thm = 
let
   val _ = debug_msg ctxt low (fn () => \<^print> ("goal_thm ",goal_thm))
   val _ = debug_msg ctxt low (fn () => \<^print> ("ts ",ts))
  val ts' = (map (try (Thm.cterm_of ctxt)) ts)
  val B' = Drule.infer_instantiate' ctxt ts' goal_thm
  val _ = debug_msg ctxt middle (fn () => \<^print> ("Instantiated already existing theorem for current term ",B'))
  (*Only need to split if return type is nat*)
  (*val (B_alpha,B_beta) = if ret_nat then split ctxt B' else ([B'],[])*)
in
  B'
end

fun arg_with_casts (t,a) = (if is_Bound t orelse is_Bound a then a else
  (if fastype_of t = @{typ nat} andalso fastype_of a = @{typ int} then @{term "nat"} $ a else a))

fun args_with_casts ts args = map arg_with_casts (ListPair.zipEq (ts,args))
  handle ListPair.UnequalLengths => raise SMT_GLOBAL_NORMALIZE("corrupted function arguments")

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
    val xs' = map (fn xi => (if is_Bound xi then xi else (if fastype_of xi = @{typ "nat"} then int_cast $ xi else xi))) xs
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

    val xs' = map (fn xi => (if is_Bound xi then xi else (if fastype_of xi = @{typ "nat"} then nat_cast $ intify_var xi else xi))) xs
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
fun mk_new_fun (subst:(term * thm) Termtab.table) t ts n T' Tts new_args f ctxt = 
let
  val Tt = fastype_of t

  val retNat = (Tt = @{typ nat})
  val newf = Free(n,T')
  val newt = (newf,new_args) |> list_comb
  val _ = debug_msg ctxt middle (fn () => \<^print> ("encountered function ",f, " for the first time. Replace by ",newf))

  (*
    \<forall>x1 ... xn. f x1 ... xn = nat(f' x1' ... xn') \<and> f' x1' ... xn' \<ge> 0  or
    \<forall>x1 ... xn. f x1 ... xn = f' x1' ... xn'
  *)
  val forall_term = mk_forall (mk_f_def_ground retNat f newf) mk_hol_all Tts 0 [] 
  (*val _ = debug_msg ctxt middle (fn () => \<^print> ("forall_term ",forall_term))*)

  (*
    \<lambda>x1 ... xn. f y1 ... yn
  *)
  val lambda_term = mk_forall (mk_nat_f_nat retNat f) mk_lambda Tts 0 [] 
  (*val _ = debug_msg ctxt middle (fn () => \<^print> ("lambda_term ",lambda_term))*)

  (*
    \<exists>f'. \<forall>x1...xn. f x1' ... xn' = (nat (f' x1' ... xn')) \<and> (f' x1' ... xn') \<ge> 0
    \<exists>f'. \<forall>x1...xn. f x1' ... xn' = (f' x1' ... xn')
  *)
  val f_cond = HOLogic.mk_exists (n,T',forall_term)

  val (ctxt1,x,B) = obtain_new_variable ctxt n f_cond lambda_term
  
  (* Now show:
       f ?x1' ... ?xn' = (nat (f' ?x1' ... ?xn')) \<and> (f' ?x1' ... ?xn') \<ge> 0
       f ?x1' ... ?xn' = (f' ?x1' ... ?xn')
     where ?xi' = nat ?xi if ?xi is a nat otherwise ?xi *)
  val goal = mk_forall (HOLogic.mk_Trueprop o (mk_f_def_ground retNat f (Thm.term_of x))) mk_prop_all Tts 0 [] 
  val goal_thm = Goal.prove ctxt1 [] [] goal (fn {context: Proof.context, ...}  => 
      (debug_msg_tac context high "Obtain new function variable")
      THEN (unfold_tac context [@{thm atomize_all}])
      THEN HEADGOAL (Method.insert_tac context [B])
      THEN HEADGOAL (assume_tac context)
      THEN (debug_msg_tac context high "Should be solved"))
   val _ = debug_msg ctxt1 high (fn () => \<^print> ("Showed goal from obtain thm:",goal_thm))
 
      val args_with_casts = args_with_casts ts new_args
              val _ = debug_msg ctxt middle (fn () => \<^print> ("args_with_casts",args_with_casts))

   val B_alpha = inst_function_thm ctxt args_with_casts retNat goal_thm 
    val _ = debug_msg ctxt middle (fn () => \<^print> ("(B_alpha, B_beta)",B_alpha))

   val subst = Termtab.update (f,(x |> Thm.term_of,goal_thm)) subst
in 
  (ctxt1,subst,x |> Thm.term_of,B,B_alpha)
end


fun mk_new_fun2 (subst:(term * thm) Termtab.table) t ts n T' new_args Tts f ctxt = 
let
  val Tt = fastype_of t

  val retNat = (Tt = @{typ nat})
  val newf = Free(n,T')
  val _ = debug_msg ctxt middle (fn () => \<^print> ("encountered function ",f, " for the first time. Replace by ",newf))

  (*
    \<forall>x1 ... xn. f x1 ... xn = nat(f' x1' ... xn') \<and> f' x1' ... xn' \<ge> 0  or
    \<forall>x1 ... xn. f x1 ... xn = f' x1' ... xn'
  *)
  val forall_term = mk_forall (mk_f_def_ground retNat f newf) mk_hol_all Tts 0 [] 
  (*val _ = debug_msg ctxt middle (fn () => \<^print> ("forall_term ",forall_term))*)

  (*
    \<lambda>x1 ... xn. f y1 ... yn
  *)
  val lambda_term = mk_forall (mk_nat_f_nat retNat f) mk_lambda Tts 0 [] 
  (*val _ = debug_msg ctxt middle (fn () => \<^print> ("lambda_term ",lambda_term))*)

  (*
    \<exists>f'. \<forall>x1...xn. f x1' ... xn' = (nat (f' x1' ... xn')) \<and> (f' x1' ... xn') \<ge> 0
    \<exists>f'. \<forall>x1...xn. f x1' ... xn' = (f' x1' ... xn')
  *)
  val f_cond = HOLogic.mk_exists (n,T',forall_term)

  val (ctxt1,x,B) = obtain_new_variable ctxt n f_cond lambda_term
  
  (* Now show:
       f ?x1' ... ?xn' = (nat (f' ?x1' ... ?xn')) \<and> (f' ?x1' ... ?xn') \<ge> 0
       f ?x1' ... ?xn' = (f' ?x1' ... ?xn')
     where ?xi' = nat ?xi if ?xi is a nat otherwise ?xi *)
  val goal = (mk_forall (HOLogic.mk_Trueprop o (mk_f_def_ground retNat f (Thm.term_of x))) mk_prop_all Tts 0 [])
  val goal_thm = Goal.prove ctxt1 [] [] goal (fn {context: Proof.context, ...}  => 
      print_tac context "Obtain new function variable" 
      THEN (unfold_tac context [@{thm atomize_all}])
      THEN HEADGOAL (Method.insert_tac context [B])
      THEN HEADGOAL (assume_tac context)  THEN  print_tac context "Should be solved" )
   val _ = debug_msg ctxt1 high (fn () => \<^print> ("Showed goal from obtain thm:",goal_thm))
 
      val args_with_casts = args_with_casts ts new_args
              val _ = debug_msg ctxt middle (fn () => \<^print> ("args_with_casts",args_with_casts))

   val B_alpha = inst_function_thm ctxt args_with_casts retNat goal_thm 
    val _ = debug_msg ctxt middle (fn () => \<^print> ("(B_alpha)",B_alpha))
    val B_alpha' = B_alpha (*unfold *)
    val _ = debug_msg ctxt middle (fn () => \<^print> ("(B_alpha')",B_alpha'))

   val subst = Termtab.update (f,(x |> Thm.term_of,goal_thm)) subst
in 
  (ctxt1,subst,x  |> Thm.term_of,B,B_alpha)
end


fun mk_new_fun3 (subst:(term * thm) Termtab.table) t ts n T' new_args Tts f ctxt = 
let
  val Tt = fastype_of t

  val retNat = (Tt = @{typ nat})
  val newf = Free(n,T')
  val _ = debug_msg ctxt middle (fn () => \<^print> ("encountered function ",f, " for the first time. Replace by ",newf))
  val _ = @{print}("Tts",Tts)
  (*
    \<forall>x1 ... xn. f x1 ... xn = nat(f' x1' ... xn') \<and> f' x1' ... xn' \<ge> 0  or
    \<forall>x1 ... xn. f x1 ... xn = f' x1' ... xn'
  *)
  val forall_term = mk_forall (mk_f_def_ground retNat f newf) mk_hol_all Tts 0 [] 
  (*val _ = debug_msg ctxt middle (fn () => \<^print> ("forall_term ",forall_term))*)

  (*
    \<lambda>x1 ... xn. f y1 ... yn
  *)
  val lambda_term = mk_forall (mk_nat_f_nat retNat f) mk_lambda Tts 0 [] 
  (*val _ = debug_msg ctxt middle (fn () => \<^print> ("lambda_term ",lambda_term))*)

  (*
    \<exists>f'. \<forall>x1...xn. f x1' ... xn' = (nat (f' x1' ... xn')) \<and> (f' x1' ... xn') \<ge> 0
    \<exists>f'. \<forall>x1...xn. f x1' ... xn' = (f' x1' ... xn')
  *)
  val f_cond = HOLogic.mk_exists (n,T',forall_term)

  val (ctxt1,x,B) = obtain_new_variable ctxt n f_cond lambda_term
  
  (* Now show:
       f ?x1' ... ?xn' = (nat (f' ?x1' ... ?xn')) \<and> (f' ?x1' ... ?xn') \<ge> 0
       f ?x1' ... ?xn' = (f' ?x1' ... ?xn')
     where ?xi' = nat ?xi if ?xi is a nat otherwise ?xi *)
  val goal = (mk_forall (HOLogic.mk_Trueprop o (mk_f_def_ground retNat f (Thm.term_of x))) mk_prop_all Tts 0 [])
  val goal_thm = Goal.prove ctxt1 [] [] goal (fn {context: Proof.context, ...}  => 
      print_tac context "Obtain new function variable" 
      THEN (unfold_tac context [@{thm atomize_all}])
      THEN HEADGOAL (Method.insert_tac context [B])
      THEN HEADGOAL (assume_tac context)  THEN  print_tac context "Should be solved" )
   val _ = debug_msg ctxt1 high (fn () => \<^print> ("Showed goal from obtain thm:",goal_thm))
 
      val args_with_casts = args_with_casts ts new_args
              val _ = debug_msg ctxt middle (fn () => \<^print> ("args_with_casts",args_with_casts))

   val B_alpha = inst_function_thm ctxt args_with_casts retNat goal_thm 
    val _ = debug_msg ctxt middle (fn () => \<^print> ("(B_alpha)",B_alpha))
val y = (Thm.cterm_of ctxt (Term.list_comb (Thm.term_of x,args_with_casts)))
    val _ = debug_msg ctxt middle (fn () => \<^print> ("y",y))

   val B_alpha' = Drule.infer_instantiate' ctxt [SOME y] @{thm nat_0_le}

    val _ = debug_msg ctxt middle (fn () => \<^print> ("(B_alpha')",B_alpha'))

   val subst = Termtab.update (f,(x |> Thm.term_of,goal_thm)) subst
in 
  (ctxt1,subst,x  |> Thm.term_of,B_alpha',B_alpha)
end

end



fun mk_conj [x] = x |
    mk_conj (x::xs) = HOLogic.mk_conj (x,(mk_conj xs))
fun delete_casts (@{term nat} $ x) = x |
    delete_casts x = x
fun notNum x = x |> strip_comb |> fst |> (fn t => t <> @{term "Num.numeral_class.numeral"})
fun add_cast [] [] [] = []|
    add_cast (x::xs) (y::ys) (T::Ts) = 
    let
      (*val _ = @{print}("x",x)
      val _ = @{print}("y",y)
      val _ = @{print}("T",T)*)

    in
      (if Term.is_Bound y orelse Term.is_Bound x then x
       else
       if T = @{typ int} andalso fastype_of x = @{typ "nat"} andalso notNum x 
       then int_cast $ x 
       else x)
      :: add_cast xs ys Ts
    end
(*
subst: mapping from function f to f' and f' s definition
odefs: collect obtain theoreme (koennten auch aus subst ausgelesen werden)
gamma: collect local assumptions
*)
fun
  transform ctxt (subst:(term*thm) Termtab.table) odefs odefs2 gamma (t as Free (x,@{typ nat})) =
    (case Termtab.lookup subst t of
      NONE =>
      let
        val _ = debug_msg ctxt high (fn () => \<^print> ("current term is free variable t that has not been encountered yet ",t))
        val (ctxt1,subst,cond,new_t,B) = mk_new_variable ctxt subst x t
      in (ctxt1,subst,odefs @ [B], odefs2, gamma @ [cond],new_t) end
    | (SOME (b,_)) => (ctxt,subst,odefs,odefs2,gamma,b) 
   )
| transform ctxt subst odefs odefs2 (gamma:term list) (t as Abs (a,b,c)) = 
  let
    val (ctxt',subst',odefs',odefs2',gamma',c') = transform ctxt subst odefs odefs2 gamma c
    val c'' = (if gamma' = [] then c' else  HOLogic.mk_imp (mk_conj gamma', c'))
  in (ctxt',subst',odefs',odefs2',[],Abs(a,b,c'')) end
| transform ctxt subst odefs odefs2 gamma (t as Bound _) = (ctxt,subst,odefs,odefs2,gamma,t) 
| transform ctxt subst odefs odefs2 gamma (t as Var _) = (ctxt,subst,odefs,odefs2,gamma,t) 
| transform ctxt subst odefs odefs2 gamma (t as _ ) = 
    let 
       val _ = debug_msg ctxt middle (fn () => \<^print> ("current term",t))

       val (f,ts) = strip_comb t
       val T = fastype_of f
       val (n,Ts) = (if is_Const f then (dest_Const f) else (dest_Free f))
         handle (TERM x) => (@{print}("x",x);raise (SMT_GLOBAL_NORMALIZE "Term name cannot be obtained"))
       val n' =  "lift_" ^ (Long_Name.base_name n)
       val (Tts,_) = Ts |> Term.strip_type
       val _ = debug_msg ctxt middle (fn () => \<^print> ("builtin fun",SMT_Builtin.is_builtin_fun ctxt (n,Ts) ts))
       val _ = debug_msg ctxt middle (fn () => \<^print> ("builtin fun ext",SMT_Builtin.is_builtin_fun_ext ctxt (n,Ts) ts))



       (*val _ = debug_msg ctxt middle (fn () => \<^print> ("encountered function ",t))*)
    in
      (*translate numeral constants directly, skip traversal of arguments*)
      (*int constants just added as an optimization*)
      if n = "Num.numeral_class.numeral" 
      then 
        ((ctxt,subst,odefs,odefs2,gamma,if T = @{typ "nat"} then list_comb (Const (n, @{typ "num \<Rightarrow> int"}), ts) else t))
      else
      let
        (*transform arguments*)
        fun transform_args ctxt2 cum_subst cum_odefs cum_odefs2 cum_gamma new_t [] = (ctxt2,cum_subst,cum_odefs,cum_odefs2,cum_gamma,new_t) | 
          transform_args ctxt2 cum_subst cum_odefs cum_odefs2 cum_gamma new_t (u::us) =
          let  
            val (ctxt3,sigma_o,odefs_o,odefs2_o,gamma_o,u_o) = transform ctxt2 cum_subst cum_odefs cum_odefs2 cum_gamma u
          in
            transform_args ctxt3 sigma_o odefs_o odefs2_o gamma_o (u_o :: new_t) us
          end
        val (ctxt2,subst,odefs,odefs2,gamma,new_args) = transform_args ctxt subst odefs odefs2 gamma [] (rev ts)
        val _ = debug_msg ctxt middle (fn () => \<^print> ("transformed arguments of f ",f))
    
        (*Calculate new type*)
        val T' = intify_type T
      in
        (*Conversion operator skip*)
        if (List.exists (fn x => n = x)
           ["Int.nat", "Nat.semiring_1_class.of_nat"])
        then ((ctxt2,subst,odefs,odefs2,gamma,hd new_args))
        (*Native operator. Should not be translated.*)
        else if SMT_Builtin.is_builtin_fun ctxt (n,Ts) ts
          orelse SMT_Builtin.is_builtin_fun_ext ctxt (n,Ts) ts
        then 
          let
            (*Casts that surrounded the children of a built-in operator might have gotten deleted.
              To reconstruct them we could theoretically take the original type of f and compare it 
              with the types of the children but some of them might be Bound's and we cannot get a type
              We could add a flag as a return type showing if the type of the term was changed.
              We could check if the original arg was a nat and if it is a bound we assume it is not!
              We know that because of preprocessing Bounds cannot be nats!
              *)
            (*val _ = @{print}("strip_type Ts",strip_type Ts)
            val _ = @{print}("Ts",new_args)
            val _ = @{print}("T",T)*)
        val _ = debug_msg ctxt middle (fn () => \<^print> ("Here",f))

            val (U,U2) = (strip_type Ts)
            val res2 = list_comb (Const(n,intify_type T), add_cast new_args ts U)
            val res = (if (U2 = @{typ "nat"}) then int_cast $ res2 else res2)
          in (ctxt2,subst,odefs,odefs2,gamma,res) end
        (*Neither return type nor argument type is natural number*)
        else if T = T'
        then ((ctxt2,subst,odefs,odefs2,gamma,list_comb (f,new_args)))
        (*New operator needs to be added*)
        else
          let
        val _ = debug_msg ctxt middle (fn () => \<^print> ("Here",f))

            val Tt = fastype_of t
            val retNat = (Tt = @{typ nat})
        val _ = debug_msg ctxt middle (fn () => \<^print> ("Here",f))

          in
          (*Check if operator has already been translated*)
          (case Termtab.lookup subst f of
            NONE => 
            let
      val _ = debug_msg ctxt middle (fn () => \<^print> ("new_args",new_args))
              val _ = debug_msg ctxt middle (fn () => \<^print> ("ts",ts))
        
              val (ctxt4,subst,f',B,B_beta) = mk_new_fun subst t ts n' T' Tts new_args f ctxt2
              val new_args' = map delete_casts new_args
        
              val _ = debug_msg ctxt middle (fn () => \<^print> ("function symbol has not been translated, add new symbol "))
              val _ = debug_msg ctxt middle (fn () => \<^print> ("(new function symbol,transformed arguments)",(f',new_args')))
              val newt = list_comb (f',new_args')

              (*Make \<ge> 0 condition for concrete term and add to gamma*)
              val cond = (if retNat then [mkLeTerm newt] else [])
              val _ = debug_msg ctxt middle (fn () => \<^print> ("collect local condition",cond))
             
              in (
                  (ctxt4,subst,odefs @ [B],B_beta::odefs2  ,gamma @ cond,newt)) end
           | (SOME (b,c)) =>
              let
                val args_with_casts = args_with_casts ts new_args
                val _ = debug_msg ctxt middle (fn () => \<^print> ("args_with_casts",args_with_casts))

                val new_args' = map delete_casts new_args
                val _ = debug_msg ctxt middle (fn () => \<^print> ("function symbol has already been translated! "))
                val _ = debug_msg ctxt middle (fn () => \<^print> ("(new function symbol,transformed arguments)",(b,new_args')))
                val newt = list_comb (b,new_args')

                (*Make \<ge> 0 condition for concrete term and add to gamma*)
                val cond = (if retNat then [mkLeTerm newt] else [])
                val _ = debug_msg ctxt middle (fn () => \<^print> ("collect local condition",cond))
                val (B_alpha) = inst_function_thm ctxt args_with_casts retNat c
                val _ = debug_msg ctxt middle (fn () => \<^print> ("(B_alpha, B_beta)",(B_alpha)))

              in ((ctxt2,subst,odefs,B_alpha::odefs2,gamma @ cond,newt)) end
          ) end
end 
end
| transform ctxt subst odefs odefs2 gamma t = (ctxt,subst,odefs,odefs2,gamma,t) 


fun mk_cond ctxt B = 
let
  val (B1,B2) = split ctxt B
  val B1_2 = map (fn b => b RS @{thm eq_reflection}) B1
  val _ = debug_msg ctxt high (fn () => \<^print> ("B",B))
  val _ = debug_msg ctxt high (fn () => \<^print> ("(B1,B2)",(B1,B2)))
  val _ = debug_msg ctxt high (fn () => \<^print> ("B1_2",B1_2))
in (B2,B1_2) end

fun custom_no_conv ctxt subst = (fn r => (subst,ctxt,[], Conv.all_conv r))


fun transform2 ctxt (subst:(term*thm) Termtab.table) ct =
let
  val t = Thm.term_of ct
in
 (case t of (Free (x,@{typ nat})) =>
   (case Termtab.lookup subst t of
      NONE =>
      let
        val _ = debug_msg ctxt high (fn () => \<^print> ("current term is free variable t of type nat" 
          ^ " that has not been encountered yet: ",t))
        val (ctxt1,subst1,cond,new_t,B) = mk_new_variable ctxt subst x t
        val (B2,B1_2) = mk_cond ctxt B

      in ((fn r => (subst1,ctxt1,B2,(Conv.top_rewrs_conv B1_2 ctxt1) r))) end
      | (SOME (t',B)) => 
      let
        val _ = debug_msg ctxt high (fn () => \<^print> ("current term is free variable t of type nat" 
          ^ " that has already been encountered: ",t'))
        val (_,B1_2) = mk_cond ctxt B
      in ((fn r => (subst,ctxt,[],(Conv.top_rewrs_conv B1_2 ctxt) r))) end
     ) |
 (_ $ _) =>
   let
     val (f,ts) = strip_comb t
     val T = fastype_of f
     val (n,Ts) = (if is_Const f then (dest_Const f) else (dest_Free f))
       handle (TERM x) => (@{print}("x",x);raise (SMT_GLOBAL_NORMALIZE "Term name cannot be obtained"))
     val n' =  "lift_" ^ (Long_Name.base_name n)
     val (Tts,_) = Ts |> Term.strip_type
     val T' = intify_type T
   in
     transform2_function subst ctxt f n n' Ts  ts Tts T T' t
   end |
 _ => (fn r => (subst,ctxt,[],Conv.all_conv r))
) ct
end

and 
transform2_function subst ctxt f n n' Ts ts Tts T T' t = (*Function only here to avoid indents*)
  if n = "Num.numeral_class.numeral" then
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("current term is a numeral, so we skip it",f))
  in custom_no_conv ctxt subst end
  else if SMT_Builtin.is_builtin_fun ctxt (n,Ts) ts
    orelse SMT_Builtin.is_builtin_fun_ext ctxt (n,Ts) ts
    orelse n = "Nat.semiring_1_class.of_nat"
    orelse n = "Int.nat" then
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("current term is a builtin, so we skip it",f))
  in custom_no_conv ctxt subst end
  else if T = T' then
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("the type of the current term has no nats in it, so we skip it",f))
  in custom_no_conv ctxt subst end     
  else
    (case Termtab.lookup subst t of
      NONE =>
      let
        val _ = debug_msg ctxt middle (fn () => \<^print> ("current term is a function f that has not been encountered yet ",t))
        val (ctxt4,subst,f',C,B) = mk_new_fun3 subst t ts n' T' ts Tts f ctxt
        val _ = debug_msg ctxt middle (fn () => \<^print> ("B",B))
        val Tt = fastype_of t
        val retNat = (Tt = @{typ nat}) |> @{print}
        val (B1,B2) = if retNat then split ctxt B  else ([],[B]) |> @{print}
        val B2 = 
map (Conv.fconv_rule 
  ((Conv.top_rewrs_conv [@{thm atomize_eq[symmetric]}] ctxt))) B2
        
        val _ = debug_msg ctxt middle (fn () => \<^print> ("(B1,B2)",(B1,B2)))
        val _ = debug_msg ctxt middle (fn () => \<^print> ("C",C))
        val D = Thm.implies_elim C (hd B2)
        val _ = debug_msg ctxt middle (fn () => \<^print> ("D",D))
 val B1' =  map (fn b =>  b RS @{thm eq_reflection}) B1

      in (fn r => (subst,ctxt4,[D],(
((Conv.top_rewrs_conv (B1') ctxt4))) r)) end
      | (SOME (t',B)) => 
      let
        val _ = debug_msg ctxt high (fn () => \<^print> ("current term is a function f" 
          ^ " that has already been encountered: ",t'))
        val B =  (fn b =>  b RS @{thm eq_reflection}) B
        val _ = debug_msg ctxt high (fn () => \<^print> ("B",B))
      in (fn r => (subst,ctxt,[],(Conv.top_rewrs_conv [B] ctxt) r)) end
     )





type subst_tab = (term * thm) Termtab.table 
type ret_conv = subst_tab * Proof.context * thm list * thm
type conv_with_tab_and_context = subst_tab -> Proof.context -> cterm -> ret_conv
 

fun atomize_eq_imp ctxt =
Conv.fconv_rule 
  ((Conv.top_rewrs_conv [@{thm atomize_eq}] ctxt) then_conv (Conv.top_rewrs_conv [@{thm atomize_imp}] ctxt))

fun abs_conv2 (ccv : conv_with_tab_and_context) (tab : subst_tab) ctxt ct =
  (case Thm.term_of ct of
    Abs (a, _, _) =>
      let
        val ((v, ct'), ctxt') = Variable.dest_abs_cterm ct ctxt;
        val (tab',ctxt'',cond,eq) = ccv tab ctxt' ct';
        val _ = @{print}("cond in abs",cond)
        val eq'' =
          let
            val eq' = fold Thm.implies_intr (map (Thm.cprop_of) cond) eq
            val _ = @{print}("eq'",eq')
            val eq'' = atomize_eq_imp ctxt'' eq'
            val _ = @{print}("eq''",eq'')      
          in 
            if length cond = 0 then eq else eq''
          end

      
        val test = @{thm H_nat_embedding} OF cond
        val _ = @{print}("testint",test)

      in (tab',ctxt'',[],if Thm.is_reflexive eq then Conv.all_conv ct else Thm.abstract_rule a v eq'') end
  | _ => raise CTERM ("abs_conv", [ct]));

(* (cterm -> 'a list * thm) -> (cterm -> 'a list * thm) -> cterm ->  Proof.context -> 'a list * thm *)
fun combination_conv2  (ccv1':conv_with_tab_and_context) (ccv2':conv_with_tab_and_context) tab ctxt ct =
  let
    val (ct1, ct2) = Thm.dest_comb ct
    val (tab1,ctxt1,cond1,cv1) = (ccv1' tab ctxt ct1)
    val (tab2,ctxt2,cond2,cv2) = (ccv2' tab1 ctxt1 ct2)

  in (tab2,ctxt2,cond1 @ cond2,Thm.combination cv1 cv2) end;

(* (cterm -> 'a list * thm) -> Proof.context -> cterm -> 'a list * thm*)
fun comb_conv2 ccv' tab ctxt = combination_conv2 ccv' ccv' tab ctxt;


fun else_conv2 ccv1' ccv2' tab ctxt ct =
  (ccv1' tab ctxt ct
    handle THM _ => ccv2' tab ctxt ct
      | CTERM _ => ccv2' tab ctxt ct
      | TERM _ => ccv2' tab ctxt ct
      | TYPE _ => ccv2' tab ctxt ct);

fun all_conv2 tab ctxt ct = (tab,ctxt,[],Thm.reflexive ct);

(*fun sub_conv conv ctxt =
  comb_conv (conv ctxt) else_conv
  abs_conv (conv o snd) ctxt else_conv
  all_conv;*)
fun sub_conv2 (ccv':conv_with_tab_and_context) tab ctxt ct =
let
  val ccv2 = comb_conv2 ccv'
  val elseccv = (fn tab => fn ctxt => fn ct => (else_conv2 (fn tab => fn ctxt => (abs_conv2 ccv' tab ctxt)) all_conv2 tab ctxt ct))

in
  else_conv2 ccv2 elseccv tab ctxt ct
end

fun then_conv2 (ccv1':conv_with_tab_and_context) ccv2' tab ctxt ct =
  let
    val (tab1,ctxt1,cond1,eq1) = ccv1' tab ctxt ct;
    val (tab2,ctxt2,cond2,eq2) = ccv2' tab1 ctxt1 (Thm.rhs_of eq1);
  in
    if Thm.is_reflexive eq1 then (tab2,ctxt2,cond1 @ cond2,eq2)
    else if Thm.is_reflexive eq2 then (tab2,ctxt2,cond1 @ cond2,eq1)
    else (tab2,ctxt2,cond1 @ cond2,Thm.transitive eq1 eq2)
  end;



(*fun bottom_conv conv ctxt ct =
  (sub_conv (bottom_conv conv) ctxt then_conv conv ctxt) ct;
*)
(*cf. BOTTOM_CONV in HOL*)
fun bottom_conv2 (ccv':conv_with_tab_and_context) tab ctxt ct =
let
  val bottom_conv2_res = bottom_conv2 ccv'
  val (sub_conv2_res : conv_with_tab_and_context) = sub_conv2 bottom_conv2_res
in
  then_conv2 sub_conv2_res ccv' tab ctxt ct
end

fun unfold_test ctxt cthm =
 let

   val (_,ctxt1,cond,thms) =
  (bottom_conv2  (fn tab2=> fn ctxt2 => transform2 ctxt2 tab2) (Termtab.empty) ctxt) (Thm.cprop_of cthm)

   val _ = @{print}("original thms",cthm)
   val _ = @{print}("thms",thms)
   val _ = @{print}("cond",cond)

(* 

   A \<equiv> B  A
  ---------
      B

*)
  


   val thms'' =
   let
     val thms2 = 
Thm.equal_elim thms cthm
     val _ = @{print}("thms2",thms2) 
     (*val thms3 = fold Thm.implies_intr (map (Thm.cprop_of) cond) thms2
       |> (Conv.fconv_rule  (Conv.top_rewrs_conv [@{thm atomize_imp}] ctxt))
     val _ = @{print}("thms3",thms3)*)
     val cond2 = map  (Conv.fconv_rule (Conv.top_rewrs_conv [@{thm atomize_eq[symmetric]}] ctxt)) cond
                    
     val _ = @{print}("cond2",cond2)
     val thms4 = thms2
       |> (Conv.fconv_rule (Conv.top_rewrs_conv cond2 ctxt))
     val _ = @{print}("thms4",thms4)
     (*val thms5 = ( thms4) RS @{lemma "x \<ge> 0 \<Longrightarrow> P (int (nat x)) = P x"
  by simp}
     val _ = @{print}("thms5",thms5)*)

   in (if length cond = 0 then thms2 else thms4
) end


 in (ctxt1,thms'') end

  fun unfold_extension_conv ctxt ct thms =
    let
      val t = Thm.term_of ct
      val t1 = Term.head_of t
    in
      (case t1 of
        Const(n,T) =>
           (fn x => (Conv.top_rewrs_conv thms ctxt x))
       | _ => Conv.all_conv) ct
    end





fun simplify_tac ctxt thms =
  ctxt
  |> empty_simpset
  |> put_simpset HOL_basic_ss
  |> (fn ctxt => ctxt addsimps @{thms simp_thms} addsimps thms)
  |> Simplifier.add_cong @{thm all_cong} 
  |> Simplifier.add_cong (hd thms)
  |> Clasimp.auto_tac

fun auto_tac ctxt cong_thm thms =
  ctxt
  |> empty_simpset
  |> put_simpset HOL_basic_ss
  |> (fn ctxt => ctxt addsimps @{thms simp_thms} addsimps thms)
  |> Simplifier.add_cong @{thm all_cong} 
  |> Simplifier.add_cong cong_thm
  |> Clasimp.auto_tac


fun without_trueprop (Const ("HOL.Trueprop", _) $ t) = t | 
    without_trueprop t = t


fun global_normalize ctxt ithms =
let

  val _ = debug_msg ctxt middle (fn () => \<^print> ("ithms before conversion ",ithms))
  val ithms_without_role = map snd ithms

  val goal_preproc = map (fn (a,b) => (a,preproc [] 0 (Thm.prop_of b))) ithms
  val _ = debug_msg ctxt high (fn () => \<^print> ("preprocessed term to show ",goal_preproc))

  val ithms_preproc = map_index (fn (i,(a,it)) => (a, Goal.prove ctxt [] [] it (fn {context: Proof.context, ...}  => 
    debug_msg_tac context high "starting preprocessing" 
    THEN HEADGOAL (Method.insert_tac ctxt [nth ithms_without_role i])
    THEN debug_msg_tac context high "starting preprocessing" 
    THEN (
        HEADGOAL (assume_tac ctxt)
      ORELSE
        (unfold_tac context @{thms int_nat_embedding_preproc_all int_nat_embedding_preproc_ex}
        THEN TRY (Clasimp.auto_tac ctxt))
    )
    THEN debug_msg_tac context high "end preprocessing"
    ))) goal_preproc
  val _ = debug_msg ctxt middle (fn () => \<^print> ("ithms after quantifier preprocessing ",ithms_preproc))


 (* fun iterate_thms [] _ = raise (SMT_GLOBAL_NORMALIZE "no facts found") | 
    iterate_thms (x::xs) (ctxt',subst,odefs,odefs2,terms) =
      let
        val _ = debug_msg ctxt middle (fn () => \<^print> ("x ",x))

        val (ctxt',subst,odefs,odefs2',gamma,new_t) = transform ctxt' subst odefs [] [] (Thm.prop_of (snd x))       
        val new_t' = (if gamma = [] then new_t else HOLogic.mk_Trueprop( HOLogic.mk_conj (mk_conj gamma, without_trueprop new_t)))
        val _ = debug_msg ctxt middle (fn () => \<^print> ("new_t' ",new_t'))
       in if length xs = 0 then  (ctxt',subst,odefs,odefs2 @ [odefs2'],gamma,terms @ [(fst x,new_t')])
       else iterate_thms xs (ctxt',subst,odefs,odefs2 @ [odefs2'],terms @ [(fst x,new_t')]) end

  val (ctxt',_,odefs,odefs2,gamma,new_ithms_as_terms) =  iterate_thms ithms_preproc (ctxt,Termtab.empty,[],[],[])
  val _ = debug_msg ctxt middle (fn () => \<^print> ("New terms ",new_ithms_as_terms))

  val _ = debug_msg ctxt middle (fn () => \<^print> ("New terms ",new_ithms_as_terms |> map (Thm.cterm_of ctxt' o snd)))
  val _ = debug_msg ctxt middle (fn () => \<^print> ("o_defs ",odefs))
  val _ = debug_msg ctxt middle (fn () => \<^print> ("o_defs2 ",odefs2))
  val _ = debug_msg ctxt middle (fn () => \<^print> ("gamma ",gamma))

  (*val (B_alpha,B_beta) = split ctxt' (hd odefs) |> @{print}*)

  val ithms3 = map_index (fn (i,(a,it)) => (a, Goal.prove ctxt' [] [] it (fn {context: Proof.context, ...}  => 
  debug_msg_tac context high "processing"
  THEN TRY (HEADGOAL (Method.insert_tac context [(snd (nth ithms_preproc i))]))
  THEN (debug_msg_tac context high "processing 0")

  THEN TRY (HEADGOAL (Method.insert_tac context (nth odefs2 i)))
  THEN (debug_msg_tac context high "processing 0")
  (*THEN TRY (HEADGOAL (dresolve_tac context [(Drule.infer_instantiate' context [NONE,SOME (@{cterm "0::nat"})] @{thm spec})|> @{print}]))*)
  THEN  (unfold_tac context (nth odefs2 i))
  THEN (debug_msg_tac context high "processing 1")
  THEN TRY ( (unfold_tac context @{thms all_conj_distrib}))
  THEN (debug_msg_tac context high "processing 2")
  THEN TRY (HEADGOAL (eresolve_tac context @{thms conjE}))
  THEN (debug_msg_tac context high "processing 3")
  THEN TRY (HEADGOAL (resolve_tac context @{thms conjI}))
  THEN (debug_msg_tac context high "processing 4")
  THEN TRY (HEADGOAL (Method.insert_tac context odefs))
  THEN TRY (HEADGOAL (Skip_Proof.cheat_tac context)) (*(Metis_Tactic.metis_tac [] ATP_Problem_Generate.combsN context @{thms of_nat_0}))*)
  THEN (debug_msg_tac context high "processing 5")
  THEN TRY (HEADGOAL (assume_tac context))
  THEN (debug_msg_tac context high "processing 6")
  THEN TRY (HEADGOAL (Method.insert_tac context [(snd (nth ithms_preproc i))] ))
  THEN (debug_msg_tac context high "processing 7")
  THEN  TRY (unfold_tac context (odefs))
  THEN (debug_msg_tac context high "processing 8")
 THEN 
  TRY(    HEADGOAL (Method.insert_tac context odefs )
  THEN (debug_msg_tac context high "processing 9")
 (*THEN  (unfold_tac context (@{thms atomize_imp}))
 THEN print_tac context "processing3a"*)
  THEN (debug_msg_tac context high "processing 10")

 THEN TRY (simplify_tac context (@{thms all_conj_distrib imp_conv_disj H1 de_Morgan_conj not_all H_nat_embedding alethe_nat_embedding2}))
  THEN (debug_msg_tac context high "processing 11")
 THEN TRY (auto_tac context (@{thm H_nat_embedding}) @{thms H_nat_embedding triv_forall_equality nat_le_0 int_nat_eq})
  THEN (debug_msg_tac context high "processing 12")
 THEN TRY (HEADGOAL (Skip_Proof.cheat_tac context))
         THEN (debug_msg_tac context high "processing end")
 )))) new_ithms_as_terms
handle (ERROR _) => raise (SMT_GLOBAL_NORMALIZE "Could not proof lifted form") 
*)

fun unfold_test_it (ctxt,[]) = (ctxt,[]) |
unfold_test_it (ctxt,((a,x)::xs)) =
 let 
  val (ctxt1,x') = unfold_test ctxt x
  val (ctxt2,xs')= unfold_test_it (ctxt1,xs)
 in (ctxt2,(a,x')::xs') end

val (ctxt',ithms3) = unfold_test_it (ctxt,ithms_preproc)

in
 (ithms3,[],ctxt')
end





end
