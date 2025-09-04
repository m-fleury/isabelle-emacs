(*  Title:      HOL/Tools/SMT/smt_global_normalize.ML
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University Freiburg

   
   TODO: Make recursions pretty so that the functions can be folded.
*)

signature SMT_GLOBAL_NORMALIZE =
sig
  val global_normalize: Proof.context -> ((int * SMT_Util.role) * thm) list -> Proof.context * ((int * SMT_Util.role) * thm) list * (term * cterm) list
  exception SMT_GLOBAL_NORMALIZE of string
end

structure SMT_Global_Normalize: SMT_GLOBAL_NORMALIZE =
struct

exception SMT_GLOBAL_NORMALIZE of string

open SMT_Config
fun debug_msg ctxt = alethe_debug_msg ctxt "smt_global_normalize"
fun debug_msg_tac ctxt = alethe_debug_msg_tac ctxt "smt_global_normalize"


type subst_tab = (cterm * thm) Termtab.table 
type ret_conv = subst_tab * Proof.context * thm list * thm
type conv_with_tab_and_context = subst_tab -> Proof.context -> cterm -> ret_conv
 
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

fun split B = ([@{thm conjunct2} OF [B]], @{thm conjunct1} OF [B])
  handle (THM _) => ([],B)

fun mk_cond ctxt B = 
let
  val (ge_cond,lift_def) = split B
  val lift_def = (fn b => b RS @{thm eq_reflection}) lift_def
  val _ = debug_msg ctxt middle (fn () => \<^print> ("lift_def",lift_def))
  val _ = debug_msg ctxt middle (fn () => \<^print> ("ge_cond",ge_cond))
in (ge_cond,lift_def) end

fun atomize_eq_thm ctxt = (Conv.top_rewrs_conv [@{thm atomize_eq[symmetric]}] ctxt) |> Conv.fconv_rule
          

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

   fun tactic_to_obtain ctxt = (debug_msg_tac ctxt high "extract new variable")
 THEN  HEADGOAL (eresolve_tac ctxt @{thms exE})
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
  val subst = Termtab.update (t,(c_x,B)) subst
  val new_t_ge_0_2 = HOLogic.mk_Trueprop (mkLeTerm x)

  val cond =  Drule.infer_instantiate' ctxt [SOME c_x] @{thm nat_0_le}
  val _ = debug_msg ctxt low (fn () => \<^print> ("cond ",cond))
in (ctxt1,subst,cond,B) end

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

fun mk_new_fun (subst:(cterm * thm) Termtab.table) t ts n T' new_args Tts f ctxt = 
let
  val Tt = fastype_of t

  val retNat = (Tt = @{typ nat})
  val newf = Free(n,T')
  val _ = debug_msg ctxt middle (fn () => \<^print> ("encountered function ",f, " for the first time. Replace by ",newf))
  val _ = @{print}("Tts",Tts)
  val _ = @{print}("new_args",new_args)
  val _ = @{print}("ts",ts)

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
  val n' = "lift_" ^ n

  val (ctxt1,x,B) = obtain_new_variable ctxt n' f_cond lambda_term
  
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
 
   
   val subst = Termtab.update (f,(x,goal_thm)) subst
   val _ = debug_msg ctxt1 middle (fn () => \<^print> ("Added f to table",f))

in 
  (ctxt1,subst,x,goal_thm)
end

end



fun inst_function_thm ctxt ts goal_thm = 
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

fun mk_new_fun2 ts Tts f ctxt x goal_thm = 
let


   val B_alpha = inst_function_thm ctxt ts goal_thm
   val (B1,B2) = mk_cond ctxt B_alpha
   val B2 = B2 |> atomize_eq_thm ctxt (*TODO: This should already be stored atomized*)
    val _ = debug_msg ctxt middle (fn () => \<^print> ("(B_alpha)",B_alpha))
    val _ = debug_msg ctxt middle (fn () => \<^print> ("(B1,B2)",(B1,B2)))

    val _ = debug_msg ctxt middle (fn () => \<^print> ("x",x))
    val _ = debug_msg ctxt middle (fn () => \<^print> ("new_args",ts))

    val _ = debug_msg ctxt middle (fn () => \<^print> ("args_with_casts",args_with_casts))
    val _ = debug_msg ctxt middle (fn () => \<^print> ("ts",ts))

fun arg_with_casts2 a = (if is_Bound a then a else
  (if fastype_of a = @{typ nat} then @{term "int"} $ a else a))
  val args_with_casts2' = map arg_with_casts2 ts

    val _ = debug_msg ctxt middle (fn () => \<^print> ("args_with_casts2",args_with_casts2'))

val y = (Thm.cterm_of ctxt (Term.list_comb (Thm.term_of x, args_with_casts2')))
    val _ = debug_msg ctxt middle (fn () => \<^print> ("y",y))

   val B_alpha' = if length B1 = 0 then [] else
 [Drule.infer_instantiate' ctxt [SOME y] @{thm nat_0_le}]

    val _ = debug_msg ctxt middle (fn () => \<^print> ("(B_alpha')",B_alpha'))

   val B_alpha'' = if length B1 = 0 then []
  else [atomize_eq_thm ctxt (Thm.implies_elim (hd B_alpha') (hd B1))]

    val _ = debug_msg ctxt middle (fn () => \<^print> ("(B_alpha'')",B_alpha''))




in   (B1,B2,B_alpha'') end
(*("B_alpha'",
 "0 \<le> (fa__::int \<Rightarrow> int) (int (nat (3::int))) \<Longrightarrow>
  int (nat (fa__ (int (nat (3::int))))) =
  fa__
   (int (nat (3::int)))") (line 579 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Tools/SMT/smt_global_normalize.ML") 
("B_alpha",
 "(f::nat \<Rightarrow> int) (nat (3::int)) = (fa__::int \<Rightarrow> int) (int (nat (3::int)))*)



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


fun custom_no_conv ctxt subst = (fn r => (subst,ctxt,[], [],Conv.all_conv r))

(*For a function f x1 ... xn and conversion cv returns f (cv0 x1) ... (cvn xn) where cv0 = cv and
cvi is cvi-1 plus the termtable and context from transforming argument xi.
*)
fun arg_conv2 (ccv1':conv_with_tab_and_context) tab cond ctxt [] = (tab,ctxt,cond,[]) |
 arg_conv2  (ccv1':conv_with_tab_and_context) tab cond ctxt (ct1:: cts) =
  let
    val (tab1,ctxt1,cond1,thm1) = (ccv1' tab ctxt ct1)
    val _ = @{print}("Applied conversion to argument ct1",ct1)
    val (tab2,ctxt2,cond2,thms)  = arg_conv2 ccv1' tab1 (cond @ cond1) ctxt1 cts
  in (tab2,ctxt2,cond2,thm1::thms) end;


(*For a function f x1 ... xn and conversion cv returns f (cv0 x1) ... (cvn xn) where cv0 = cv and
cvi is cvi-1 plus the termtable and context from transforming argument xi.
*)
fun fun_conv2 ccv' tab ctxt ct = 
let
    val (ct1,cts) = Drule.strip_comb ct |> @{print}
    val (tab2,ctxt2,cond2,thms) = arg_conv2 ccv' tab [] ctxt cts
    val ct1_thm = ct1 |> Conv.all_conv
    val x = fold (Thm.combination ) thms ct1_thm
in (tab2,ctxt2,cond2,x) end

fun arg_conv2' (ccv:conv)  [] = [] |
 arg_conv2'  (ccv:conv) (ct1:: cts) =
  let
    val thm1 = ccv ct1
    val thms  = arg_conv2' ccv cts
  in (thm1::thms) end;

fun fun_conv2' ccv' ct = 
let
    val (ct1,cts) = Drule.strip_comb ct |> @{print}
    val thms = arg_conv2' ccv' cts
    val ct1_thm = ct1 |> Conv.all_conv
   fun mk_thm y [] = y|
      mk_thm y (x::xs) = mk_thm (Thm.combination y x) xs
    val x =  (mk_thm ct1_thm ( thms))|> @{print}
in x end

fun then_conv2 cv1  cv2 ct =
  let
    val eq1 = cv1 ct;
    val eq2 = cv2 (Thm.rhs_of eq1);
  in
    if Thm.is_reflexive eq1 then eq2
    else if Thm.is_reflexive eq2 then eq1
    else Thm.transitive eq1 eq2
  end;

(*
B1: x \<equiv> nat (lift_x)
B2: 0 \<le> lift_x
D: int (nat (lift_x__::int)) = lift_x
*)
fun transform2 ctxt (subst:(cterm*thm) Termtab.table) ct =
let
  val t = Thm.term_of ct
in
 (case t of
 (Abs (a, _, _)) => ((fn r => (subst,ctxt,[],[],(Conv.all_conv) r))) 
| (Free (x,@{typ nat})) =>
  let
   val (subst1,ctxt1,cond,B) = 
   (case Termtab.lookup subst t of
    NONE =>
     let
       val _ = debug_msg ctxt high (fn () => \<^print> ("current term is free variable t of type nat" 
         ^ " that has not been encountered yet: ",t))
       val (ctxt1,subst1,cond,B) = mk_new_variable ctxt subst x t
       val _ = debug_msg ctxt middle (fn () => \<^print> ("cond compare",cond))

    in (subst1,ctxt1,cond,B) end
  | (SOME (t',B)) => 
      let
        val _ = debug_msg ctxt high (fn () => \<^print> ("current term is free variable t of type nat" 
          ^ " that has already been encountered: ",t'))
        val cond =  Drule.infer_instantiate' ctxt [SOME t'] @{thm nat_0_le} (*TODO*)
       val _ = debug_msg ctxt middle (fn () => \<^print> ("cond compare",cond))

    in (subst,ctxt,cond,B) end
     ) 
   val ([ge_cond],lift_def) = mk_cond ctxt B
       val nat_int_lemma = Thm.implies_elim cond ge_cond
       val _ = debug_msg ctxt middle (fn () => \<^print> ("lift_def",lift_def))
       val _ = debug_msg ctxt middle (fn () => \<^print> ("ge_cond",ge_cond))
       val _ = debug_msg ctxt middle (fn () => \<^print> ("nat_int_lemma",nat_int_lemma))
        val nat_int_lemma = (atomize_eq_thm ctxt1) nat_int_lemma

   in ((fn r => (subst1,ctxt1,[ge_cond],[nat_int_lemma],(Conv.top_rewrs_conv [lift_def] ctxt) r))) end
|
 _ =>
   let
     val (f,ts) = strip_comb t
     val _ = @{print}("f",f)
     val _ = @{print}("ts",ts)
     val T = fastype_of f
     val (n,Ts) = (if is_Const f then (dest_Const f) else (dest_Free f))
       handle (TERM x) => (@{print}("x",x);raise (SMT_GLOBAL_NORMALIZE "Term name cannot be obtained"))
     val n' =  "lift_" ^ (Long_Name.base_name n)
     val (Tts,_) = Ts |> Term.strip_type
     val T' = intify_type T
   in
     transform2_function subst ctxt f n n' Ts  ts Tts T T' t
   end |
 _ => (fn r => (subst,ctxt,[],[],Conv.all_conv r))
) ct
end

and 
transform2_function subst ctxt f n n' Ts ts Tts T T' t = (*Function only here to avoid indents*)
  if n = "Num.numeral_class.numeral" then
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("current term is a numeral, so we skip it",f))
  in custom_no_conv ctxt subst end
  else if n = "Int.nat"
  then
    (case ts of
      [Const ("Groups.zero_class.zero",_)] => (fn r => (subst,ctxt,[],[@{thm SMT.H1(1)}],Conv.all_conv r))
    | [Const ("Groups.zero_class.one",_)] => (fn r => (subst,ctxt,[],[@{thm SMT.H1(2)}],Conv.all_conv r))
    | [Const ("Num.numeral_class.numeral", _) $ t1]
      => (fn r => (subst,ctxt,[],[Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t1)] @{thm alethe_nat_embedding2}],Conv.all_conv r))
    | _ => custom_no_conv ctxt subst)
  else if  n = "Nat.semiring_1_class.of_nat"
    orelse n = "Int.nat" then
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("current term is a conversion, so we skip it",t))
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
  let
    val (ctxt1,subst,x,goal_thm) = 
    (case Termtab.lookup subst f of
      NONE =>
      let
        val _ = debug_msg ctxt middle (fn () => \<^print> ("current term is a function f that has not been encountered yet ",t))
        val (ctxt1,subst,x,goal_thm) = mk_new_fun subst t ts n T' ts Tts f ctxt
      in (ctxt1,subst,x,goal_thm) end |
      SOME (ct',B) => (ctxt, subst,ct', B)
    )
    val _ = debug_msg ctxt1 middle (fn () => \<^print> ("goal_thm",goal_thm))

    val (ge_cond,lift_def,nat_int_lemma) = mk_new_fun2 ts Tts f ctxt1 x goal_thm
    val _ = debug_msg ctxt1 middle (fn () => \<^print> ("lift_def",lift_def))
    val _ = debug_msg ctxt1 middle (fn () => \<^print> ("ge_cond",ge_cond))

        val _ = debug_msg ctxt1 middle (fn () => \<^print> ("x",x))


        val _ = debug_msg ctxt1 middle (fn () => \<^print> ("nat_int_lemma",nat_int_lemma))
        val nat_int_lemma = map (atomize_eq_thm ctxt1) nat_int_lemma
      in (fn r => (subst,ctxt1,ge_cond,nat_int_lemma,
(then_conv2

  (fn x1 => (Conv.top_rewrs_conv [lift_def] ctxt1) (x1 |> @{print})
|> @{print})
  (*Simplify numerals, needs drule*)
  (Conv.try_conv (fn x2 =>  let
     val x = (fun_conv2' (Conv.top_sweep_rewrs_conv [@{thm alethe_nat_embedding2}] ctxt1 ) ) x2 |> @{print}
   in x end |> @{print}))
)


 (r |> @{print}) |> @{print}))  end
 



fun atomize_eq_imp ctxt =
Conv.fconv_rule 
  ((Conv.top_rewrs_conv [@{thm atomize_eq}] ctxt) then_conv (Conv.top_rewrs_conv [@{thm atomize_imp}] ctxt))

fun then_conv2 (ccv1':conv_with_tab_and_context) ccv2' tab ctxt ct =
  let
    val (tab1,ctxt1,cond1,eq1) = ccv1' tab ctxt ct;
    val _ = @{print}("eq1",eq1)

    val (tab2,ctxt2,cond2,eq2) = ccv2' tab1 ctxt1 (Thm.rhs_of eq1);
    val _ = @{print}("eq2",eq2)

  in
    if Thm.is_reflexive eq1 then (tab2,ctxt2,cond1 @ cond2,eq2)
    else if Thm.is_reflexive eq2 then (tab2,ctxt2,cond1 @ cond2,eq1)
    else (tab2,ctxt2,cond1 @ cond2,Thm.transitive eq1 eq2)
  end;



fun else_conv2 ccv1' ccv2' tab ctxt ct =
  (ccv1' tab ctxt ct
    handle THM _ => ccv2' tab ctxt ct
      | CTERM _ => ccv2' tab ctxt ct
      | TERM _ => ccv2' tab ctxt ct
      | TYPE _ => ccv2' tab ctxt ct);

fun add_conds ctxt int_nat_conds ge_conds thm cthm =

      if length ge_conds = 0 then thm else
      let
        fun mk_and [x] = x |
           mk_and (x::xs) = (@{thm HOL.conjI} OF [x]) OF ([mk_and xs])
        val ge_conds = mk_and ge_conds
        val _ = @{print}("ge_cond",ge_conds)
        val (_,[thm_unfolded_nat_int'_lhs]) = Drule.strip_comb (Thm.lhs_of thm)
        val (_,[thm_unfolded_nat_int'_rhs]) = Drule.strip_comb (Thm.rhs_of thm)

        val temp2 = Drule.infer_instantiate' ctxt [NONE,SOME thm_unfolded_nat_int'_lhs,SOME thm_unfolded_nat_int'_rhs]
          @{lemma "A \<Longrightarrow> ( (Trueprop B) \<equiv> Trueprop C) \<Longrightarrow> ((Trueprop B) \<equiv> Trueprop(A \<and> C))" by simp}
     val _ = @{print}("temp2",temp2)

        val temp3 = temp2 OF [ge_conds]
     val _ = @{print}("temp3",temp3 |> Thm.concl_of)
     val _ = @{print}("thm_unfolded_nat_int'",thm|> Thm.concl_of)

        val temp4 = Thm.implies_elim temp3 thm

     val _ = @{print}("temp4",temp4)

       
      in temp4 end

fun arg_conv ccv ct =
let
  val (ct1,cts) = Drule.strip_comb ct 
  val ct1_thm = Conv.all_conv ct1  
  fun mk_thm y [] = y|
      mk_thm y (x::xs) = mk_thm (Thm.combination y x) xs
  val thm_children = if length cts <> 0 then (mk_thm ct1_thm ( (map ccv cts))) else ct1_thm
in thm_children end


(*

bottom_list gets a term list cts and fills up tab, cond, ctxt and a theorem list.
It first gets a theorem using bottom for the first argument. Then, it traverses the
rest of the arguments 
*)
fun bottom_list ccv' tab ocond cond ctxt [] ths = (tab,ctxt,ocond,cond,ths) | 
  bottom_list ccv' tab ocond cond ctxt (ct::cts) ths =
  let
    val _ = @{print}("In bottom list",cond)

    val (tab2,ctxt2,ocond2,cond2,tthm) = bottom ccv' tab [] cond ctxt ct
    val _ = @{print}("In bottom list2",cond2)

  in  bottom_list ccv' tab2 (ocond @ ocond2) cond2 ctxt2 cts (tthm::ths)  end

and 

bottom ccv' tab ocond cond ctxt ct = 
let
 val (ct1,cts) = Drule.strip_comb ct   
 val _ = debug_msg ctxt high (fn () => \<^print> ("(ct1,cts)",(ct1,cts)))
in
  (case Thm.term_of ct of 
   Const (quant_name, T) $ (Abs (bv_name, T2, _)) => 
   let
    val is_all = (quant_name = "HOL.All")
    val is_ex = (quant_name = "HOL.Ex")
    val _ = if is_all orelse is_ex then () else raise (SMT_GLOBAL_NORMALIZE "Unsupported Quantifier")
    val quant = 
     if is_all then @{cterm "HOL.All::(int => bool) \<Rightarrow> bool"}
     else @{cterm "HOL.Ex::(int => bool) \<Rightarrow> bool"}
    val bound_is_nat = (T2 = @{typ nat})
    val ct_thm = Conv.all_conv ct


    val ((bound_var, body), _) = Variable.dest_abs_cterm (hd cts) ctxt;
    val _ = debug_msg ctxt high (fn () => \<^print> ("body",body))
    val _ = debug_msg ctxt high (fn () => \<^print> ("bound_var",bound_var))

    val qnt_transform_thm =
      if is_all then @{thm int_nat_embedding_preproc_all}
      else @{thm int_nat_embedding_preproc_ex}
    (*
     In nat case: "\<forall>x::nat. P (int x) \<equiv> \<forall>x\<ge>0. P (int (nat x))"
     Otherwise: "\<forall>x. P x \<equiv> \<forall>x. P x"
    *)
    val qnt_transform =
     if bound_is_nat then (Drule.infer_instantiate' ctxt [SOME (hd cts)] qnt_transform_thm)
     else Conv.all_conv ct
    val _ = debug_msg ctxt high (fn () => \<^print> ("Applied lemma transforming quantifier",qnt_transform))
    val qnt_transform_rhs = Thm.rhs_of qnt_transform
    val (_,[qnt_transform_lambda]) = (if bound_is_nat then Drule.strip_comb qnt_transform_rhs else (ct1,cts))
    val _ = debug_msg ctxt high (fn () => \<^print> ("qnt_transform_lambda",qnt_transform_lambda))

    (*
     In nat case: "(x::int)\<ge>0 \<longrightarrow> P (int (nat x))"
     Otherwise: "P x"
    *)
    val ((transformed_bound_var_ct, qnt_transform_body), _) = Variable.dest_abs_cterm qnt_transform_lambda ctxt;
    val _ = debug_msg ctxt high (fn () => \<^print> ("(transformed_bound_var, qnt_transform_body)",(transformed_bound_var_ct, qnt_transform_body)))

    (*
     In nat case: Add (x::int)\<ge>0  to hypothesis, transform "P (int (nat x))" to "P x"
     Otherwise: "P x"
    *)
    val (ct'_atom3,qnt_original_unfold_nat_int_bound_var,nat_0_le,ge_cond_bound_var,bound_var_ge_cond) =
    (if bound_is_nat then
    let
     val (_,[bound_var_ge_cond,consequent]) = Drule.strip_comb qnt_transform_body   
     val _ = debug_msg ctxt high (fn () => \<^print> ("bound_var_ge_cond,consequent",bound_var_ge_cond,consequent))

     val nat_0_le = Drule.infer_instantiate' ctxt [SOME transformed_bound_var_ct] @{thm nat_0_le} |> atomize_eq_thm ctxt
     val nat_0_le' = Thm.implies_elim nat_0_le (Thm.assume (Thm.apply @{cterm Trueprop} bound_var_ge_cond))
     val _ = @{print}("nat_0_le'",nat_0_le')                                                       
     val (bv_ge_cond_thms,ctxt2) = Assumption.add_assumes [Thm.apply @{cterm Trueprop} bound_var_ge_cond] ctxt
     val _ = debug_msg ctxt high (fn () => \<^print> ("bv_ge_cond_thms",bv_ge_cond_thms))

    val thm_with_defs = [nat_0_le']
      |>  (Proof_Context.export ctxt2 ctxt)

     val _ = debug_msg ctxt high (fn () => \<^print> ("thm_with_defs",thm_with_defs))

     val body_unfold_nat_int_bound_var = (Conv.top_rewrs_conv [nat_0_le'] ctxt) qnt_transform_body
     (*" 0 \<le> (x::int) \<Longrightarrow> 0 \<le> x \<and> P (int (nat x) \<equiv> 0 \<le> x \<and> P x"*)
     val body_unfold_nat_int_bound_var' = Thm.implies_intr (Thm.apply @{cterm Trueprop} bound_var_ge_cond) body_unfold_nat_int_bound_var
     val _ = debug_msg ctxt high (fn () => \<^print> ("body_unfold_nat_int_bound_var'",body_unfold_nat_int_bound_var'))

     val [newb1,newb2] = Thm.cconcl_of body_unfold_nat_int_bound_var' |> Drule.strip_comb |> snd
     val newb1 = newb1 |> Drule.strip_comb |> snd |> tl |> the_single (*" P (int (nat x) *)
     val newb2 = newb2 |> Drule.strip_comb |> snd |> tl |> the_single (*" P x *)
     val x = subst
     val lemma =
       if is_all then @{lemma "(a \<Longrightarrow> (a \<longrightarrow> B \<equiv> a \<longrightarrow> C)) \<Longrightarrow> (a \<longrightarrow> B \<equiv> a \<longrightarrow>C)" by simp}
       else @{lemma "(a \<Longrightarrow> (a \<and> B \<equiv> a \<and> C)) \<Longrightarrow> (a \<and> B \<equiv> a \<and> C)" by linarith}
     val lemma_inst = Drule.infer_instantiate' ctxt [SOME bound_var_ge_cond,SOME newb1,SOME newb2] lemma |> atomize_eq_thm ctxt
     val body_unfold_nat_int_bound_var'' = Thm.implies_elim lemma_inst body_unfold_nat_int_bound_var' (* FIXME: This should be done on the fly eventually and not in this additional traversal*)
     val _ = debug_msg ctxt high (fn () => \<^print> ("body_unfold_nat_int_bound_var''",body_unfold_nat_int_bound_var''))

     val lambda_unfold_nat_int_bound_var = Thm.abstract_rule bv_name transformed_bound_var_ct body_unfold_nat_int_bound_var''
     val _ = @{print}("lambda_unfold_nat_int_bound_var",lambda_unfold_nat_int_bound_var)
     val qnt_unfold_nat_int_bound_var = Thm.combination (Conv.all_conv quant) lambda_unfold_nat_int_bound_var
     val _ = @{print}("qnt_unfold_nat_int_bound_var",qnt_unfold_nat_int_bound_var)

     val qnt_original_unfold_nat_int_bound_var = Thm.transitive qnt_transform qnt_unfold_nat_int_bound_var
     val _ = debug_msg ctxt high (fn () => \<^print> ("qnt_original_unfold_nat_int_bound_var",qnt_original_unfold_nat_int_bound_var))
     val (_,[_,u1]) = Drule.strip_comb (Thm.lhs_of body_unfold_nat_int_bound_var'')
     val (_,[_,u2]) = Drule.strip_comb (Thm.rhs_of body_unfold_nat_int_bound_var'')
     val _ = debug_msg ctxt high (fn () => \<^print> ("u1,u2",u1,u2))
     val u3 = Thm.apply @{cterm "Pure.eq::prop \<Rightarrow> _"} ( Thm.apply @{cterm Trueprop} u1)
     val _ = debug_msg ctxt high (fn () => \<^print> ("u3",u3))
     val u3' = Thm.apply u3 ( Thm.apply @{cterm Trueprop} u2)
     val _ = debug_msg ctxt high (fn () => \<^print> ("u3'",u3'))

    in (u2,qnt_original_unfold_nat_int_bound_var,nat_0_le',bound_var_ge_cond,bound_var_ge_cond) end
    else (qnt_transform_body,ct_thm,ct_thm,ct,ct))
    val _ = debug_msg ctxt high (fn () => \<^print> ("ct'_atom3",ct'_atom3))

    (*Recursive Call*)
    (* 
      In nat case: Transform body "P (x::int)" and obtain theorem "P x \<equiv> P' x"
      Otherwise: Transform body "P x" and obtain thm: "P x \<equiv> P' x" *)
    val (tab1,ctxt1,ge_conds,int_nat_conds,[thm]) = bottom_list ccv' tab [] [] ctxt [ct'_atom3] []
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("Body of quantified term was transformed to:",thm))

    val ge_conds = distinct (fn (a,b) => Thm.prop_of a = Thm.prop_of b) ge_conds (*TODO: Why are they added so often?*)
    val ge_conds = map (Conv.fconv_rule (Conv.repeat_changed_conv (Conv.top_sweep_rewrs_conv int_nat_conds ctxt))) ge_conds
    val int_nat_conds = map (Conv.fconv_rule (Conv.top_rewrs_conv [@{thm atomize_eq[symmetric]}] ctxt)) int_nat_conds
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("int_nat_conds of body",int_nat_conds))
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("ge_cond of body",ge_conds))
    (* Unfold any nat(int t) in the body FIXME: This should be done on the fly eventually and not in this additional traversal*)
    val thm_unfolded_nat_int = Conv.fconv_rule (Conv.top_rewrs_conv int_nat_conds ctxt) thm
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("Rewriten thm",thm_unfolded_nat_int))
  
    (*Add any conditions due to lifted variables "P x \<equiv> cond \<and> P' x" *)
    val thm_with_cond = 
      if length ge_conds = 0 then thm_unfolded_nat_int else
      let
        fun mk_and [x] = x |
           mk_and (x::xs) = (@{thm HOL.conjI} OF [x]) OF ([mk_and xs])
        val ge_conds = mk_and ge_conds
        val quant2 = 
          if is_all then @{lemma "A \<Longrightarrow> ( B \<equiv>  C) \<Longrightarrow> ( B \<equiv> (A \<and> C))" by simp}
          else @{lemma "A \<Longrightarrow> ( B \<equiv>  C) \<Longrightarrow> ( B \<equiv> (A \<longrightarrow> C))" by simp}
        val temp2 = Drule.infer_instantiate' ctxt
          [NONE,SOME (Thm.lhs_of thm_unfolded_nat_int),SOME (Thm.rhs_of thm_unfolded_nat_int)]
          quant2

        val temp3 = temp2 OF [ge_conds]
        val temp4 = Thm.implies_elim temp3 thm_unfolded_nat_int
      in temp4 end
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("added conditions to theorem",thm_with_cond))

    (*This here should eventually be done during transformation.
      By transforming the lemma, nat(int(bound_var)) terms were re-introduced and need to be simplified to bound_var
*)
    val thm_unfolded_nat_int = thm_with_cond

    val thm_unfolded_nat_int =
    if bound_is_nat then
    let
     val _ = debug_msg ctxt high (fn () => \<^print> ("nat_0_le",nat_0_le))
     val _ = debug_msg ctxt high (fn () => \<^print> ("thm_unfolded_nat_int",thm_unfolded_nat_int))

     val _ = debug_msg ctxt high (fn () => \<^print> ("ge_cond_bound_var",ge_cond_bound_var))
     val (bv_ge_cond_thms,ctxt2) = Assumption.add_assumes [Thm.apply @{cterm Trueprop} bound_var_ge_cond] ctxt |> @{print}


     val thm_unfolded_nat_int' = Conv.top_rewrs_conv [nat_0_le] ctxt2 (Thm.rhs_of thm_unfolded_nat_int) (*TODO: This doesn't work*)
     val thm_unfolded_nat_int = Thm.transitive thm_unfolded_nat_int thm_unfolded_nat_int'
     val _ = debug_msg ctxt high (fn () => \<^print> ("tthm",thm_unfolded_nat_int))

     val thm_unfolded_nat_int = Thm.implies_intr (Thm.apply @{cterm Trueprop} ge_cond_bound_var) thm_unfolded_nat_int
     val _ = debug_msg ctxt high (fn () => \<^print> ("ct'_atom2",thm_unfolded_nat_int))
     val [newb1,newb2] = Thm.cconcl_of thm_unfolded_nat_int |> Drule.strip_comb |> snd
     val _ = debug_msg ctxt high (fn () => \<^print> ("newb",(newb1,newb2)))

     val lemma = 
      if is_all then @{lemma "(a \<Longrightarrow> (B \<equiv> C)) \<Longrightarrow> (a \<longrightarrow> B \<equiv> a \<longrightarrow>C)" by simp}
      else @{lemma "(a \<Longrightarrow> (B \<equiv> C)) \<Longrightarrow> (a \<and> B \<equiv> a \<and> C)" by linarith}
     val lemma_inst =  Drule.infer_instantiate' ctxt [SOME ge_cond_bound_var,SOME newb1, SOME newb2] lemma |> atomize_eq_thm ctxt
     val _ = debug_msg ctxt high (fn () => \<^print> ("lemma_inst",lemma_inst))

     val thm_unfolded_nat_int = Thm.implies_elim lemma_inst thm_unfolded_nat_int
     val _ = debug_msg ctxt high (fn () => \<^print> ("Re-introduce implication",thm_unfolded_nat_int))
    in thm_unfolded_nat_int end else thm_unfolded_nat_int

    (* "\<lambda>x::int. P x \<equiv> \<lambda>x. P' x" *)
    val thm23 = Thm.abstract_rule bv_name transformed_bound_var_ct thm_unfolded_nat_int
    val _ = @{print}("Re-add \<lambda>",thm23)
    (* "\<forall>x::int. P x \<equiv> \<forall>x. P' x" *)
    val thm23' = Thm.combination (Conv.all_conv quant) thm23
    val _ = @{print}("Re-add quantifier",thm23')
    val _ = @{print}("Re-add quantifier",qnt_original_unfold_nat_int_bound_var)

    (* "\<forall>x::nat. P (int x) \<equiv> \<forall>x::int. P' x" *)
    val thm23' = Thm.transitive qnt_original_unfold_nat_int_bound_var thm23'
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("Body of quantified term was transformed to:",thm23'))


 in (tab1,ctxt1,[],[],thm23') end |
_ => 
  if length cts = 0
  then ccv' tab ctxt ct1
  else
   let
    (*Transform children*)
    val (tab1,ctxt1,args_ge_cond,args_nat_int_lemma,thms_children) = bottom_list ccv' tab [] [] ctxt cts []
    val ct1_thm = Conv.all_conv ct1
    fun mk_thm y [] = y|
      mk_thm y (x::xs) = mk_thm (Thm.combination y x) xs
    val thm_children = if length cts <> 0 then (mk_thm ct1_thm (rev thms_children)) else ct1_thm
    val _ = debug_msg ctxt high (fn () => \<^print> ("Transformed all children and combined ",thms_children))

    (*Transform current*)
    val (tab2,ctxt2,curr_ge_cond,curr_nat_int_lemma,thm_curr) = ccv' tab1 ctxt1 (Thm.rhs_of thm_children)
    val _ = debug_msg ctxt high (fn () => \<^print> ("Transformed current: ",thm_curr))

    val thm = Thm.transitive thm_children thm_curr
    val _ = debug_msg ctxt high (fn () => \<^print> ("Combine current and children: ",thm))

    in (tab2,ctxt2,ocond @ args_ge_cond @ curr_ge_cond,cond @ curr_nat_int_lemma @ args_nat_int_lemma,thm) end)
 end 


fun all_conv2 tab ctxt ct = (tab,ctxt,[],Thm.reflexive ct);

type test2 = ((int * SMT_Util.role) * thm) list
type test = Proof.context * thm list * (Termtab.key * cterm) list

fun unfold_test cthm ((ctxt,thms,mapping) :test)  =
 let
   val _ = debug_msg ctxt low (fn () => \<^print> ("current original thm",(Thm.cprop_of cthm)))
   val (tab,ctxt1,ge_conds,int_nat_conds,thm) =
    (bottom (fn tab2 => fn ctxt2 => transform2 ctxt2 tab2) (Termtab.empty) [] [] ctxt) (Thm.cprop_of cthm)
   (*FIXME: This should be done on the fly*)
   val thm = Conv.fconv_rule (Conv.top_rewrs_conv int_nat_conds ctxt) thm

   val ge_conds = distinct (fn (a,b) => Thm.prop_of a = Thm.prop_of b) ge_conds
   val ge_conds = map (Conv.fconv_rule (Conv.repeat_changed_conv (Conv.top_sweep_rewrs_conv int_nat_conds ctxt))) ge_conds
   val _ = debug_msg ctxt low (fn () => \<^print> ("current transformed thm",thm))
   val _ = debug_msg ctxt low (fn () => \<^print> ("int of nat conditions",int_nat_conds))
   val _ = debug_msg ctxt low (fn () => \<^print> ("obtained greater equal conditions",ge_conds))

   val thms'' = add_conds ctxt1 int_nat_conds ge_conds thm cthm 
   val thms''' = Conv.fconv_rule (Conv.rewr_conv thms'') cthm

   (*This is used for counterexample generation only*)
   val keys = Termtab.keys tab
   val curr_mapping = ListPair.zip (keys, keys |> map (fst o the o Termtab.lookup tab))
in ((ctxt1,thms'''::thms,curr_mapping @ mapping):test) end

fun global_normalize ctxt ithms =
let
  val _ = debug_msg ctxt middle (fn () => \<^print> ("ithms before conversion ",ithms))
  val (i,thms) = split_list ithms

  val (ctxt',thms',mapping) = fold unfold_test thms (ctxt,[],[])
  val ithms' = ListPair.zip (i,thms')
in
 (ctxt',ithms',mapping)
end





end
