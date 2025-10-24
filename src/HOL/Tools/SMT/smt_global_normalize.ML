(*  Title:      HOL/Tools/SMT/smt_global_normalize.ML
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University Freiburg

   
   TODO: Make recursions pretty so that the functions can be folded.

We assume that the int has been pushed in as far as possible

E.g.,
  "(x::nat) = (x::nat)" 
gets transformed into:
  "int (x::nat) \<noteq> int x"

E.g.,
  "(f::nat \<Rightarrow> int) (3::nat) = (5::int)"
gets transformed into:
  "(f::nat \<Rightarrow> int) (nat (3::int)) = (5::int)"

E.g.,
  "(foo::nat \<Rightarrow> nat) 0 = 1" 
gets transfomed into:
  int (foo (nat 0)) \<noteq> 1


\<forall>x ::nat. (f::nat \<Rightarrow> int) x = f (3::nat)

After preprocessing Nr. 1: 
  \<forall>x ::nat. (f (nat (3::int))) = ((f::nat \<Rightarrow> int) x)

Then,

  \<forall>x ::nat. (f (nat (3::int))) = ((f::nat \<Rightarrow> int) x)

Preprocessing Nr. 2: 
  \<forall>x ::int. x \<ge> 0 \<and> (f (nat (3::int))) = ((f::nat \<Rightarrow> int) (nat x))




3::int \<Rightarrow> 3::int
(nat (3::int)) \<Rightarrow> (nat (3::int))

f (nat (3::int)) \<Rightarrow> 
Obtain f' where \<forall>lb0. (f'::int \<Rightarrow> int) lb0 = f (nat lb0) 

x \<Longrightarrow> is a bound var \<Longrightarrow> we need to know its type




  \<forall>x ::nat. ((f::nat => nat) a) = ((f::nat \<Rightarrow> nat) x)

Table Bound vars

   Bound 0    nat      x'::int      x' = int x, x = nat x', x' \<ge> 0        

Table lifted mappings
   f'         f         \<forall>lb0. (f'::int \<Rightarrow> int) lb0 = int (f (nat lb0)), \<forall>lb0. (f lb0) = (nat (f' (int lb0))) , \<forall>lb0. f' lb0 \<ge> 0
   a'         a         a' = int (a), a = nat a', a' \<ge> 0

Go top down, left to right:
return (bounds table, mapping table, conversion)
- Meet quantifier \<Rightarrow> Add entry to Bounds Table
- Go into LHS of equality
- Go into f => Add entry to Mappings Table \<Longrightarrow>  return conversions in the table associated to them
- Go into a \<Rightarrow>  Add entry to Mappings Table \<Longrightarrow> return conversions in the table associated to them
- Return to f a
  Instantiate theorems
  Apply conversion returned from f to conversion returned for a (TODO: Look this up)
  ==> return resulting conversion (f a) = (nat (f' (int (nat a')))) 
  (f a) = (nat (f' (int a))) (using second lemma f' in table) 
        = (nat (f' a'))  (using first lemma for a')
- Go into RHS of equality ((f::nat \<Rightarrow> nat) x)
- Hit f \<Rightarrow> already in table
- Hit x \<Rightarrow> find in bounds table \<Rightarrow> return conversion x = x
- 






((f::nat => nat) a) =



  \<forall>x ::int. (a' \<ge> 0) \<Longrightarrow> (f' a' \<ge> 0) \<and> (f' x \<ge> 0) \<Longrightarrow>  (f' a') = ((f'::int \<Rightarrow> int) x)









Recurse term bottom up, maintaining a list of conditions cond.
The current term should always have the form nat t, where t only contains
integers and no natural numbers after transformation.

1. For a numerical constants c, if c's type is nat return (nat (c::int)).
   This should have already happened though (as explained above)...
   Otherwise, don't change.

2. For variables x, if x's type is nat, obtain new variable lift_x = int x.
   Return (nat lift_x). Add lift_x \<ge> 0 to cond. 
   Otherwise, don't change.

3a. If current term has form (nat t) return it unchanged.

3b. For any occurence of int, if the child is a (nat t):
    int (nat t) simplify to t

4. For any other function f:
   - If argument t_i has type nat, we know that it has to be of form (nat t_i').
     Have f t_1 ... t_i ... t_n = f t_1 ... (nat t_i') ... t_n
     Obtain new function lift_f:
       \<forall>u1...un. lift_f u1 ... ui ... un = f u1 ... (nat ui) ... un
     Return lift_f t_1 ... t_i' ... t_n'
   - If return type is of type nat
     Obtain new function lift_f:
       \<forall>u1...un. lift_f u1 ... ui ... un = (int (f u1 ... ui ... un))
     Return (nat (lift_f t_1' ... t_i' ... t_n')). Add (lift_f t_1' ... t_i' ... t_n') \<ge> 0 to cond.
   - If both:
     Obtain new function lift_f:
       \<forall>u1...un. lift_f u1 ... ui ... un = (int (f u1 ... (nat ui) ... un))
   -  Otherwise, don't change
5. For quantifier:
   Add all conditions
  



For each function f

Obtain new function variable
 1. \<And>lb0::nat. prime_nat lb0 = lift_prime_nat (int lb0)
variables:
    lift_prime_nat :: int \<Rightarrow> bool 





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

val intT = @{typ int}
val natT = @{typ nat}
val isNat = (curry (op =)) @{typ nat}

fun all_pure_const T = Const ("Pure.all", (T --> @{typ "prop"}) --> @{typ "prop"});
val nat_cast = @{term "nat::int => nat"}
val int_cast = @{term "int::nat => int"} 
val conj = @{term conj}

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
fun custom_all_conv ctxt subst = (fn r => (subst,ctxt,[],Conv.all_conv r))
         

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
  val _ = debug_msg ctxt middle (fn () => \<^print> ("n ",n))

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
  For each variable x::nat we want to obtain (x'::int) and the following theorem:
    \<exists> x'::int. x = nat x' \<and> x' \<ge> 0
  Input is the name of a variable of type nat
*)
fun mk_new_variable ctxt x_name =
let

  (*TODO: Check if name is already used first! Not sure if it matters because Isabelle renames, try out*)
  val x'_name =  "lift_" ^ (Long_Name.base_name x_name)
  val t = (Free (x_name,natT))
  val t' = (Free (x'_name,intT))
  val _ = debug_msg ctxt middle (fn () => \<^print> ("(variable, lifted variable)",(t,t')))

  (*Show that lifted variable exists*)
  val x'_def = HOLogic.mk_exists (x'_name,intT,
               conj
             $ (@{term "HOL.eq :: nat => nat \<Rightarrow> bool"} $ t $ (nat_cast $ t'))
             $ mkLeTerm t') (*\<exists> x'::int. x = nat x' \<and> x' \<ge> 0*)
  val _ = debug_msg ctxt middle (fn () => \<^print> ("New variable is defined by", x'_def))
  val exI_inst = Drule.infer_instantiate' ctxt [NONE,SOME(Thm.cterm_of ctxt t')] @{thm exI}
  val x'_ex = Goal.prove ctxt [] [] (\<^make_judgment> x'_def)
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
   val _ = debug_msg ctxt high (fn () => \<^print> ("x' exists: ",x'_ex))

   fun tactic_to_obtain ctxt = (debug_msg_tac ctxt high "extract new variable")
     THEN  HEADGOAL (eresolve_tac ctxt @{thms exE})
     THEN (debug_msg_tac ctxt high "should be solved by now")
   val (x'_thm, ctxt1) = result2 (tactic_to_obtain) x'_name [x'_ex] ctxt
   val _ = debug_msg ctxt1 high (fn () => \<^print> ("obtained a new lifted variable",x'_thm))

   val (x', x'_thm_def) = x'_thm |> apfst (snd o the_single) |> apsnd the_single
     handle List.Empty => raise (SMT_GLOBAL_NORMALIZE "Could not obtain all lifted variables") 
     handle Match => raise (SMT_GLOBAL_NORMALIZE "Could not obtain all lifted variables")

   val _ = debug_msg ctxt1 high (fn () => \<^print> ("Obtained new variable ",x'," defined by ",x'_thm_def))

  val ([x'_ge_0],x'_def) = split x'_thm_def
  val x'_def = atomize_eq_thm ctxt1 x'_def
  val _ = debug_msg ctxt middle (fn () => \<^print> ("(x'_def,x'_ge_0) ",(x'_def,x'_ge_0)))
in (ctxt1,x',(x'_def,[x'_ge_0])) end



fun transform_variable ctxt subst (x as Free (x_name,@{typ nat})) =
(case Termtab.lookup subst x of
  NONE =>
  let
    val _ = debug_msg ctxt low (fn () => \<^print> ("current term is free variable t of type nat" 
      ^ " that has not been encountered yet: ",x))
    val (ctxt1,c_x',(x'_def,x'_ge_0)) = mk_new_variable ctxt x_name
    val subst1 = Termtab.update (x,(c_x',(x'_def,x'_ge_0))) subst
  in ((fn r => (subst1,ctxt1,x'_ge_0,(Conv.top_rewrs_conv [x'_def] ctxt) r))) end
 |(SOME (c_x',(x'_def,x'_ge_0))) => 
  let
    val _ = debug_msg ctxt middle (fn () => \<^print> ("current term is free variable t of type nat" 
      ^ " that has already been encountered: ",x))
  in ((fn r => (subst,ctxt,x'_ge_0,(Conv.top_rewrs_conv [x'_def] ctxt) r))) end
)
| transform_variable ctxt subst _ = (fn r => (subst,ctxt,[],Conv.all_conv r))


local

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
    val xi' = Free(xi'_name,intify_type T)
  in
    all_fun xi'_name T (mk_forall ground all_fun Ts (k+1) (xi'::US))
  end

 (* f, [x1, ..., xn] \<mapsto> f x1' ... xn'
   where
    xi' = (nat xi), if f_T[i] has type nat
    xi' = xi, otherwise
  *)
  local
    fun mk_f_xs'_h f _ [] = []
     |  mk_f_xs'_h f (f_Ti::f_Ts) (xi::xs) =
       (if isNat f_Ti then nat_cast $ xi else xi) :: mk_f_xs'_h f f_Ts xs
  in
    fun mk_f_xs' f f_Ts xs  = let val ys = mk_f_xs'_h f f_Ts xs in list_comb (f, ys) end
  end


  (* f, f', [x1, ..., xn] to one of the following
       f x1' ... xn' = (nat (f' x1 ... xn)) \<and> (f' x1 ... xn) \<ge> 0, if retNat
       f x1' ... xn' = (f' x1 ... xn)                              , otherwise
     where
       xi' = (nat xi), if f_T[i] has type nat
       xi' = xi, otherwise
   *)
  fun mk_f_def_ground f f' xs = 
  let
    val (xs_T,f_T) = fastype_of f |> strip_type

    val retNat = isNat f_T
    val f'_T = fastype_of f' |> strip_type |> fst

    val f_xs' = mk_f_xs' f xs_T xs (*f t_1 ... (nat t_i) ... t_n*)
    val _ = @{print}("f x1' ... xn'",f_xs')

    val f'_xs = list_comb (f',xs) (*f' t_1 ... t_n*)
    val _ = @{print}("f' x1 ... xn",f'_xs)

    val nat_f'_xs = (if retNat then nat_cast $ f'_xs else f'_xs)
    val eq_term = HOLogic.mk_eq (f_xs',nat_f'_xs)
  in
 (if retNat
  then HOLogic.mk_conj (Const ("Orderings.ord_class.less_eq", @{typ "int \<Rightarrow> int \<Rightarrow> bool"}) $ @{term "0::int"} $ f'_xs,eq_term)
  else eq_term) end
 
  fun mk_hol_all xi'_name T' H = HOLogic.mk_all(xi'_name,intify_type T',H)

  fun mk_prop_all xi'_name T' H = all_pure_const T' $ absfree (xi'_name,T') H


in
fun mk_new_fun ctxt f f_name ts_T = (*TODO: Just copied from variable for now*)
let
  (*TODO: Check if name is already used first! Not sure if it matters because Isabelle renames, try out*)
  val f'_name =  "lift_" ^ (Long_Name.base_name f_name)
  val f_T = fastype_of f
  val retNat = isNat (f_T |> strip_type |> snd)

  val f'_T = intify_type f_T
  val t' = if is_Free f then (Free (f'_name,f'_T)) else (Const (f'_name,f'_T))
  val _ = debug_msg ctxt middle (fn () => \<^print> ("(variable, lifted variable)",(f,t')))


  (*
    \<forall>x1 ... xn. f x1 ... xn = nat(f' x1' ... xn') \<and> f' x1' ... xn' \<ge> 0  or
    \<forall>x1 ... xn. f x1 ... xn = f' x1' ... xn'
  *)
  val forall_term = mk_forall (mk_f_def_ground f t') mk_hol_all ts_T 0 [] 
  val _ = debug_msg ctxt middle (fn () => \<^print> ("forall_term",forall_term))

  (*Show that lifted function exists*)
  val x'_def = HOLogic.mk_exists (f'_name,f'_T,forall_term)
  val _ = debug_msg ctxt middle (fn () => \<^print> ("New function is defined by", x'_def))
  val exI_inst = Drule.infer_instantiate' ctxt [NONE,SOME(Thm.cterm_of ctxt t')] @{thm exI}
  val x'_ex = Goal.prove ctxt [] [] (\<^make_judgment> x'_def)
    (fn {context = ctxt', ...} => 
          (debug_msg_tac ctxt' high "needs to be shown to obtain new variable") THEN
      (HEADGOAL (Skip_Proof.cheat_tac ctxt)
      
      )
      THEN(debug_msg_tac ctxt' high "should be solved by now"))
   val _ = debug_msg ctxt high (fn () => \<^print> ("x' exists: ",x'_ex))

   fun tactic_to_obtain ctxt = (debug_msg_tac ctxt high "extract new variable")
     THEN  HEADGOAL (eresolve_tac ctxt @{thms exE})
     THEN (debug_msg_tac ctxt high "should be solved by now") (*THEN HEADGOAL (Skip_Proof.cheat_tac ctxt)*)
   val (x'_thm, ctxt1) = result2 (tactic_to_obtain) f'_name [x'_ex] ctxt
   val _ = debug_msg ctxt1 high (fn () => \<^print> ("obtained a new lifted variable",x'_thm))

   val (x', x'_thm_def) = x'_thm |> apfst (snd o the_single) |> apsnd the_single
     handle List.Empty => raise (SMT_GLOBAL_NORMALIZE "Could not obtain all lifted variables") 
     handle Match => raise (SMT_GLOBAL_NORMALIZE "Could not obtain all lifted variables")

   val _ = debug_msg ctxt1 high (fn () => \<^print> ("Obtained new variable ",x'," defined by ",x'_thm_def))

  (* Now show:
       f ?x1'' ... ?xn'' = (nat (f' ?x1' ... ?xn')) \<and> (f' ?x1' ... ?xn') \<ge> 0
       f ?x1'' ... ?xn'' = (f' ?x1' ... ?xn')
     where ?xi'' = nat ?xi' if ?xi is a nat otherwise ?xi *)
  val goal = (mk_forall (HOLogic.mk_Trueprop o (mk_f_def_ground f (Thm.term_of x'))) mk_prop_all (map intify_type ts_T) 0 [])|> @{print}
  val goal_thm = Goal.prove ctxt1 [] [] goal (fn {context: Proof.context, ...}  => 
      print_tac context "Obtain new function variable" 
      THEN HEADGOAL (Skip_Proof.cheat_tac ctxt))
     
   val _ = debug_msg ctxt1 high (fn () => \<^print> ("Showed goal from obtain thm:",goal_thm))
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("retNat",retNat))
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("f_T",f_T))


  val (x'_ge_0,x'_def) = if retNat then (fn (a,b) => ([a],hd b)) (swap (split goal_thm)) else ([],goal_thm)
  val x'_def = atomize_eq_thm ctxt1 x'_def
  val _ = debug_msg ctxt middle (fn () => \<^print> ("(x'_def,x'_ge_0) ",(x'_def,x'_ge_0)))
in (ctxt1,x',(x'_def,x'_ge_0)) end
end


fun transform_function ctxt subst t f f_name ts f_T f'_T = 
  if f_name = "Nat.semiring_1_class.of_nat" then
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("current term is a cast from nat to int. If its child is a cast from nat to int we know that we can delete the casts",t))
    val _ = debug_msg ctxt high (fn () => \<^print> ("ts",ts))
    (*Const ("Nat.semiring_1_class.of_nat", "nat \<Rightarrow> int") $
   (Const ("Int.nat", "int \<Rightarrow> nat") $
     Free ("lift_x__",
           "int")))*)

    val _ = debug_msg ctxt high (fn () => \<^print> ("hd ts",hd ts))
    
  in 
   case hd ts of
     Const ("Int.nat", @{typ "int \<Rightarrow> nat"})$ Const ("Groups.zero_class.zero",@{typ "int"})
       => (fn r => (subst,ctxt,[],Conv.top_sweep_rewrs_conv [@{thm SMT.H1'(1)}] ctxt r))
     | Const ("Int.nat", @{typ "int \<Rightarrow> nat"})$ Const ("Groups.one_class.one",@{typ "int"})
       => (fn r => (subst,ctxt,[],Conv.top_sweep_rewrs_conv [@{thm SMT.H1'(2)}] ctxt r))
     | Const ("Int.nat", @{typ "int \<Rightarrow> nat"})$ (Const ("Num.numeral_class.numeral", @{typ "num \<Rightarrow> int"}) $ u1)
       => (fn r => (subst,ctxt,[],Conv.top_sweep_rewrs_conv [Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt u1)] @{thm alethe_nat_embedding2}|> @{print}] ctxt r))
     | Const ("Int.nat", @{typ "int \<Rightarrow> nat"})$ t1 =>
     let
      val _ = debug_msg ctxt high (fn () => \<^print> (" (t1 |> strip_comb |> fst)", (t1 |> strip_comb |> fst)))
      fun search_for_value [] = NONE |
         search_for_value ((_,(a,(b,c)))::xs) = if (Thm.term_of a = (t1 |> strip_comb |> fst |> @{print})) then SOME c else search_for_value xs
      val t_thms = search_for_value (Termtab.dest subst)
      val _ = debug_msg ctxt high (fn () => \<^print> ("(Termtab.dest subst) ",(Termtab.dest subst) ))
     in
      case t_thms of
        NONE => (*We can only add an if-then-else lemma*)
        (fn r => (subst,ctxt,[],Conv.top_sweep_rewrs_conv [Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t1)] @{thm int_nat_eq}|> atomize_eq_thm ctxt |> @{print}] ctxt r)) 
    | SOME t_thms => 
        let
          val _ = debug_msg ctxt high (fn () => \<^print> ("t1",t1))

          val _ = debug_msg ctxt high (fn () => \<^print> ("t_thms",t_thms))
          val u2 = case t1 of (_ $ u1) => (SOME (Thm.cterm_of ctxt u1)) | _ =>  NONE
          val _ = debug_msg ctxt high (fn () => \<^print> ("u2",u2))

          val ass = case u2 of NONE => hd t_thms | (SOME u2') =>  Drule.infer_instantiate' ctxt [u2] (hd t_thms) |> atomize_eq_thm ctxt
          val _ = debug_msg ctxt high (fn () => \<^print> ("ass",ass))



          val thm_int_nat = Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t1)] @{thm H_nat_embedding'} |> atomize_eq_thm ctxt
          val _ = debug_msg ctxt high (fn () => \<^print> ("thm_int_nat",thm_int_nat))

          val thm3 = Thm.implies_elim thm_int_nat ass
          val _ = debug_msg ctxt high (fn () => \<^print> ("thm3",thm3 ))

       in
       (fn r => (subst,ctxt,[],Conv.top_sweep_rewrs_conv [thm3] ctxt r))
       end
     end
     | _ => custom_all_conv ctxt subst end
  else if f_name = "Int.nat" then
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("current term is a cast from int to nat if its child is a cast from nat to int, resolve it",t))
    val nat_int_thm' = Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t)] (atomize_eq_thm ctxt @{thm nat_int}) |> @{print}
  in  (fn r => (subst,ctxt,[],Conv.top_sweep_rewrs_conv [nat_int_thm'] ctxt r)) end

  else if f_T = f'_T then
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("current term is a function that does not take or return nats, skip it",t))
  in custom_all_conv ctxt subst end
  else
  let
    val (ts_T,_) = f_T |> Term.strip_type

    val  (ctxt1,subst,c_f',(f'_def,t'_ge_0)) = 
    (case Termtab.lookup subst f of
      NONE =>
      let
        val _ = debug_msg ctxt low (fn () => \<^print> ("current term is a function f that has not been encountered yet ",t))
        val (ctxt1,c_f',(f'_def,t'_ge_0)) = mk_new_fun ctxt f f_name ts_T

        val subst = Termtab.update (f,(c_f',(f'_def,t'_ge_0))) subst
      in (ctxt1,subst,c_f',(f'_def,t'_ge_0)) end |
      SOME (c_f',(f'_def,t'_ge_0)) => 
      let
        val _ = debug_msg ctxt low (fn () => \<^print> ("current term is a function f that has been encountered before ",t))
      in (ctxt, subst,c_f',(f'_def,t'_ge_0)) end
    )

    val _ = debug_msg ctxt1 middle (fn () => \<^print> ("ts ",ts))
    val ts_trans = map (fn @{term "nat"} $ t => t | t => t) ts
    val _ = debug_msg ctxt1 middle (fn () => \<^print> ("ts_trans ",ts_trans))
    val ct_ts_trans = map (SOME o Thm.cterm_of ctxt1) ts_trans

    val f'_def_concrete = (*instantiate_fun*) Drule.infer_instantiate' ctxt1 ct_ts_trans f'_def
    val t'_ge_0_concrete = map (Drule.infer_instantiate' ctxt1 ct_ts_trans) t'_ge_0
    val _ = debug_msg ctxt1 middle (fn () => \<^print> ("Instantiated f'_def ",f'_def_concrete))
    val _ = debug_msg ctxt1 middle (fn () => \<^print> ("Instantiated t'_ge_0_concrete ",t'_ge_0_concrete))

      in ((fn r => (subst,ctxt,t'_ge_0_concrete,(Conv.top_rewrs_conv [f'_def_concrete] ctxt) r))) end



fun transform_non_quant_term ctxt (subst:(cterm*(thm*thm list)) Termtab.table) ct =
let
  val t = Thm.term_of ct
in
 (case t of
 (Abs (a, _, _)) => custom_all_conv ctxt subst
| (Free (_,@{typ nat})) => transform_variable ctxt subst t
| (Free (_,_)) => custom_all_conv ctxt subst
|  _ =>
   let
     val (f,ts) = strip_comb t
     val T = fastype_of f
     val (f_name,f_T) = (if is_Const f then dest_Const f else dest_Free f)
       handle (TERM x) => (@{print}("x",x);raise (SMT_GLOBAL_NORMALIZE "Term name cannot be obtained"))
     val f'_name =  "lift_" ^ (Long_Name.base_name f_name)
     val f'_T = intify_type T
   in
      transform_function ctxt subst t f f_name ts f_T f'_T 
   end |
 _ => custom_all_conv ctxt subst
) ct
end


















(*-----------------------------------------------------------*)
































(*

Show:
  \<And>lift_foo::int \<Rightarrow> int. 
    \<forall>lb0::int.
      foo (nat lb0) = nat (lift_foo lb0) \<and> 0 \<le> lift_foo lb0

TODO
*)

fun obtain_new_variable ctxt new_var_name new_var_cond lambda_term =
let
  val _ = debug_msg ctxt high (fn () => \<^print> ("Condition for new variable ",new_var_cond))
  val _ = debug_msg ctxt high (fn () => \<^print> ("lambda_term ",lambda_term))
  val _ = debug_msg ctxt high (fn () => \<^print> ("new_var_name ",new_var_name))

  val exI_inst = Drule.infer_instantiate' ctxt [NONE,SOME(Thm.cterm_of ctxt lambda_term)] @{thm exI} |> @{print}

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
   val _ = debug_msg ctxt1 high (fn () => \<^print> ("res",res))


   val (x, B) = res |> apfst (snd o the_single) |> apsnd the_single
     handle List.Empty => raise (SMT_GLOBAL_NORMALIZE "Could not obtain all lifted variables") 
     handle Match => raise (SMT_GLOBAL_NORMALIZE "Could not obtain all lifted variables")

   val _ = debug_msg ctxt1 high (fn () => \<^print> ("Obtained new variable ",x," defined by ",B))
in (ctxt1,x,B) end



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
  fun mk_f'_xs' f' _ _ [] = [] |
  mk_f'_xs' f' (T_f1::T_fs) (T_f1'::T_f's) (xi::xs) =
let
val _ = @{print}("xi",xi)
in
   (if (fastype_of xi <> T_f1') then xi else nat_cast $ xi) :: mk_f'_xs' f' T_fs T_f's xs
end
  fun mk_f'_xs'2 f' T_f T_f' xs = let val ys = mk_f'_xs' f' T_f T_f' xs in list_comb (f', ys) end

  (* f' x1' ... xn' \<mapsto> g x1' ... xn' *)
  fun mk_g_xs' retNat f'_xs' = (if retNat then nat_cast $ f'_xs' else f'_xs')

  (* f, f', [x1, ..., xn] to one of the following
       f x1 ... xn = (nat (f' x1' ... xn')) \<and> (f' x1' ... xn') \<ge> 0, if retNat
       f x1 ... xn = (f' x1' ... xn')                              , otherwise
     I.e.
       f_xs = g \<and> f'_xs' \<ge> 0       , if retNat
       f_xs = g                     , otherwise
   *)open Term
  fun mk_f_def_ground retNat f f' xs = 
  let
  val _ = @{print}("xs",xs)

    val T_f = fastype_of f |> strip_type |> fst
    val T_f' = fastype_of f' |> strip_type |> fst

    val f_xs = mk_f'_xs'2 f T_f T_f' xs (*f t_1 ... (nat t_i) ... t_n*)
  val _ = @{print}("f_xs",f_xs)

    val f'_xs' = mk_f_xs (f') xs
  val _ = @{print}("f'_xs'",f'_xs')

    val g = mk_g_xs' retNat f'_xs'
    val eq_term = HOLogic.mk_eq (f_xs,g)
  in (if retNat then HOLogic.mk_conj (eq_term, Const ("Orderings.ord_class.less_eq", @{typ "int \<Rightarrow> int \<Rightarrow> bool"}) $ @{term "0::int"} $ f'_xs') else eq_term) end
 



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
  fun mk_nat_f_nat retNat f T_f T_f' xs =
  let
    val f_xs = mk_f'_xs'2 f T_f T_f' xs (*f t_1 ... (nat t_i) ... t_n*)

    val f_t = mk_nat_f f xs
  in (if retNat then int_cast $ f_xs else f_xs) end


  fun mk_prop_all xi'_name T' H = all_pure_const T' $ absfree (xi'_name,T') H
  fun mk_hol_all xi'_name T' H = HOLogic.mk_all(xi'_name,intify_type T',H)
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
    val xi' = Free(xi'_name,intify_type T)
  in
    all_fun xi'_name T (mk_forall ground all_fun Ts (k+1) (xi'::US))
  end

  

in

fun mk_new_fun (subst:(cterm * thm) Termtab.table) t ts n T' new_args Tts f ctxt = 
let
  val Tt = fastype_of t

  val retNat = (Tt = @{typ nat})
  val newf = Free(n,intify_type T')
  val _ = debug_msg ctxt low (fn () => \<^print> ("encountered function ",f, " for the first time. Replace by ",newf))
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
  val lambda_term = mk_forall (mk_nat_f_nat retNat f (strip_type T'|>fst) (strip_type T' |> fst) ) mk_lambda Tts 0 [] 
  (*val _ = debug_msg ctxt middle (fn () => \<^print> ("lambda_term ",lambda_term))*)

  (*
    \<exists>f'. \<forall>x1...xn. f x1' ... xn' = (nat (f' x1' ... xn')) \<and> (f' x1' ... xn') \<ge> 0
    \<exists>f'. \<forall>x1...xn. f x1' ... xn' = (f' x1' ... xn')
  *)
  val f_cond = HOLogic.mk_exists (n,T',forall_term)
  val n' =  (Long_Name.base_name n)
  val _ = debug_msg ctxt middle (fn () => \<^print> ("n' ",n'))

  val (ctxt1,x,B) = obtain_new_variable ctxt n' f_cond lambda_term
  
  (* Now show:
       f ?x1'' ... ?xn'' = (nat (f' ?x1' ... ?xn')) \<and> (f' ?x1' ... ?xn') \<ge> 0
       f ?x1'' ... ?xn'' = (f' ?x1' ... ?xn')
     where ?xi'' = nat ?xi' if ?xi is a nat otherwise ?xi *)
  val goal = (mk_forall (HOLogic.mk_Trueprop o (mk_f_def_ground retNat f (Thm.term_of x))) mk_prop_all (map intify_type Tts) 0 [])|> @{print}
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
  val ts' = (map (try (Thm.cterm_of ctxt)) (map (fn Const ("Int.nat", @{typ "int \<Rightarrow> nat"}) $ t => t) ts))
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


in   (B1,B2) end
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


(*
and 
transform2_function subst ctxt f n n' Ts ts Tts T T' t = (*Function only here to avoid indents*)
  if n = "Num.numeral_class.numeral" then
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("current term is a numeral, so we skip it",f))
  in custom_no_conv ctxt subst end
  else if n = "Int.nat" then
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("current term is a cast from int to nat if its child is a cast from nat to int, resolve it",t))
    val nat_int_thm' = Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t)] (atomize_eq_thm ctxt @{thm nat_int}) |> @{print}
  in  (fn r => (subst,ctxt,[],Conv.top_sweep_rewrs_conv [nat_int_thm'] ctxt r)) end
  else if n = "Nat.semiring_1_class.of_nat" then
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("current term is a cast from nat to int. If its child is a cast from nat to int we know that we can delete the casts",t))
    val _ = debug_msg ctxt high (fn () => \<^print> ("ts",ts))
    (*Const ("Nat.semiring_1_class.of_nat", "nat \<Rightarrow> int") $
   (Const ("Int.nat", "int \<Rightarrow> nat") $
     Free ("lift_x__",
           "int")))*)

    val _ = debug_msg ctxt high (fn () => \<^print> ("hd ts",hd ts))
    val t = case (hd ts) of Const ("Int.nat", @{typ "int \<Rightarrow> nat"})$ t => t | t => t
    val _ = debug_msg ctxt high (fn () => \<^print> ("t",t))

    val thm_int_nat = Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t)] @{thm H_nat_embedding'} |> atomize_eq_thm ctxt
    val _ = debug_msg ctxt high (fn () => \<^print> ("thm_int_nat",thm_int_nat|> Thm.cprop_of |> Thm.term_of))
    val ass = Thm.assume (Thm.apply @{cterm Trueprop} (Thm.cterm_of ctxt ( Const ("Orderings.ord_class.less_eq", @{typ "int \<Rightarrow> int \<Rightarrow> bool"}) $ @{term "0::int"} $ t)))
    val _ = debug_msg ctxt high (fn () => \<^print> ("ass",ass |> Thm.cprop_of |> Thm.term_of))
    val thm3 = Thm.implies_elim thm_int_nat ass
    val _ = debug_msg ctxt high (fn () => \<^print> ("thm3",thm3 ))

  in (fn r => (subst,ctxt,[], [],Conv.top_sweep_rewrs_conv [thm3] ctxt r))  end
  else if T = T' then
  let
    val _ = debug_msg ctxt high (fn () => \<^print> ("current term is a function that does not take or return nats, skip it",t))
  in custom_no_conv ctxt subst end
  else
  let
    val (ctxt1,subst,x,goal_thm) = 
    (case Termtab.lookup subst f of
      NONE =>
      let
        val _ = debug_msg ctxt low (fn () => \<^print> ("current term is a function f that has not been encountered yet ",(t,T')))
        val (ctxt1,subst,x,goal_thm) = mk_new_fun subst t ts ("lift_" ^ n) T' ts Tts f ctxt
      in (ctxt1,subst,x,goal_thm) end |
      SOME (ct',B) => (ctxt, subst,ct', B)
    )
    val _ = debug_msg ctxt1 middle (fn () => \<^print> ("goal_thm",goal_thm)) (* "foo2 (?lb0.0::nat) = (lift_foo2__::int \<Rightarrow> int) (int ?lb0.0)"*)

    val (ge_cond,lift_def) = mk_new_fun2 ts Tts f ctxt1 x goal_thm
    val _ = debug_msg ctxt1 middle (fn () => \<^print> ("lift_def",lift_def))
    val _ = debug_msg ctxt1 middle (fn () => \<^print> ("ge_cond",ge_cond))

        val _ = debug_msg ctxt1 middle (fn () => \<^print> ("x",x))


        (*val _ = debug_msg ctxt1 middle (fn () => \<^print> ("nat_int_lemma",nat_int_lemma))
        val nat_int_lemma = map (atomize_eq_thm ctxt1) nat_int_lemma*)
      in (fn r => (subst,ctxt1,ge_cond,[],
(then_conv2

  (fn x1 => (Conv.top_rewrs_conv [lift_def] ctxt1) (x1 |> @{print})
|> @{print})
  (*Simplify numerals, needs drule*)
  (Conv.try_conv (fn x2 =>  let
     val x = (fun_conv2' (Conv.top_sweep_rewrs_conv [@{thm alethe_nat_embedding2}] ctxt1 ) ) x2 |> @{print}
   in x end |> @{print}))
)


 (r |> @{print}) |> @{print}))  end
 
*)


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
fun bottom_list ccv' tab ge_conds ctxt [] ths = (tab,ctxt,ge_conds,ths) | 
  bottom_list ccv' tab ge_conds ctxt (ct::cts) ths =
  let
    val (tab2,ctxt2,ge_conds2,tthm) = bottom ccv' tab ge_conds ctxt ct
  in bottom_list ccv' tab2 (ge_conds @ ge_conds2) ctxt2 cts (tthm::ths)  end
and 

bottom (ccv':
      (cterm * (thm * thm list)) Termtab.table ->
        Proof.context -> cterm -> (cterm * (thm * thm list)) Termtab.table * Proof.context * thm list * thm) tab cond ctxt ct = 
let
  val (ct1,cts) = Drule.strip_comb ct   
  val _ = debug_msg ctxt high (fn () => \<^print> ("(current term,current children)",(ct1,cts)))
in
 (case Thm.term_of ct of 
   Const (quant_name, T) $ (Abs (bv_name, T2, _)) => 
   let
    val _ = debug_msg ctxt high (fn () => \<^print> ("current is quantifier: ",quant_name))

    val is_all = (quant_name = "HOL.All")
    val is_ex = (quant_name = "HOL.Ex")
    val _ = if is_all orelse is_ex then () else raise (SMT_GLOBAL_NORMALIZE "Unsupported Quantifier")
    val quant = Thm.cterm_of ctxt (Const(quant_name,intify_type T))
    val bound_is_nat = (T2 = @{typ nat})
    val ct_thm = Conv.all_conv ct |> @{print}

    val ((bound_var, body), ctxt) = Variable.dest_abs_cterm (hd cts) ctxt;
    val _ = debug_msg ctxt high (fn () => \<^print> ("body",body))
    val _ = debug_msg ctxt high (fn () => \<^print> ("bound_var",bound_var))

    (* "(\<forall>(x::nat) . P x) \<equiv> (\<forall>(x::int). x \<ge> 0 \<longrightarrow> P (nat x))"*)
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
    val ((transformed_bound_var_ct, qnt_transform_body), ctxt) = Variable.dest_abs_cterm qnt_transform_lambda ctxt;
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
    val (tab1,ctxt1,ge_conds,[thm]) = bottom_list ccv' tab [] ctxt [ct'_atom3] []
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("Body of quantified term was transformed to:",thm))

    val ge_conds = distinct (fn (a,b) => Thm.prop_of a = Thm.prop_of b) ge_conds (*TODO: Why are they added so often?*)
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("ge_cond of body",ge_conds))
    (* Unfold any nat(int t) in the body FIXME: This should be done on the fly eventually and not in this additional traversal*)
    val try0 = fold (fn x => fn thm => Thm.implies_intr x thm) (map Thm.cprop_of ge_conds) thm
(*TODO: stopped here*)
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("try",try0))



    (*Add any conditions due to lifted variables "P x \<equiv> cond \<and> P' x" *)
    val thm_with_cond =
      if length ge_conds = 0 then thm else
      let
        fun mk_and [x] = x |
           mk_and (x::xs) = (@{thm HOL.conjI} OF [x]) OF ([mk_and xs])
        val ge_conds = mk_and ge_conds

        val quant2 = 
          if is_all then @{lemma "A \<Longrightarrow> ( B \<equiv>  C) \<Longrightarrow> ( B \<equiv> (A \<and> C))" by simp}
          else @{lemma "A \<Longrightarrow> ( B \<equiv>  C) \<Longrightarrow> ( B \<equiv> (A \<longrightarrow> C))" by simp}
        val temp2 = Drule.infer_instantiate' ctxt
          [NONE,SOME (Thm.lhs_of thm),SOME (Thm.rhs_of thm)]
          quant2
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("temp2",temp2))

        val temp3 = temp2 OF [ge_conds]
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("temp3",temp3))
        val temp4 = Thm.implies_elim temp3 thm
    val _ = debug_msg ctxt1 high (fn () => \<^print> ("temp4",temp4))

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
    val _ = debug_msg ctxt high (fn () => \<^print> ("Transformed current: ",thm23'))


 in (tab1,ctxt1,[],thm23') end

 (*|
(Abs (bv_name, T, t2)) => (*TODO: lambda case*)
  let
    val _ = @{print}("bv_name", bv_name)
    val _ = @{print}("t2", t2)
    val ((bound_var, body), ctxt) = Variable.dest_abs_cterm ct1 ctxt;
    val _ = @{print}("body", body)

    val (tab1,ctxt1,ge_conds,[thm]) = bottom_list ccv' tab [] ctxt [body] []
    val _ = @{print}("thm", thm)
    val thm23 = Thm.abstract_rule bv_name bound_var thm
    val _ = @{print}("thm23", thm23)
    (*TODO: Add/pass conditions *)
 in (tab1,ctxt1,[],thm23) end*) |
_ => 
  if length cts = 0
  then
    let
      (*Transform current*)
      val (tab2,ctxt2,curr_ge_cond,thm_curr) = ccv' tab ctxt ct1
      val _ = debug_msg ctxt low (fn () => \<^print> ("Transformed current term (old,new): ",(Thm.lhs_of thm_curr,Thm.rhs_of thm_curr)))
    in (tab2,ctxt2,curr_ge_cond,thm_curr) end
  else
    let
      (*Transform children*)
      val (tab1,ctxt1,args_ge_cond,thms_children) = bottom_list ccv' tab  [] ctxt cts []
      val ct1_thm = Conv.all_conv ct1
      fun mk_thm y [] = y|
         mk_thm y (x::xs) = mk_thm (Thm.combination y x) xs
      val thm_children = mk_thm ct1_thm (rev thms_children)


      (*Transform current*)
      val (tab2,ctxt2,curr_ge_cond,thm_curr) = ccv' tab1 ctxt1 (Thm.rhs_of thm_children)
      val thm = Thm.transitive thm_children thm_curr
      val _ = debug_msg ctxt low (fn () => \<^print> ("Transformed current term with children (old,new): ",(Thm.lhs_of thm,Thm.rhs_of thm)))

   in (tab2,ctxt2,args_ge_cond @ curr_ge_cond,thm) end

 
)
 end


fun all_conv2 tab ctxt ct = (tab,ctxt,[],Thm.reflexive ct);

type test2 = ((int * SMT_Util.role) * thm) list
type test = Proof.context * thm list * (Termtab.key * cterm) list

fun unfold_test cthm ((ctxt,thms,mapping) :test)  =
 let
   val _ = debug_msg ctxt low (fn () => \<^print> ("---------------------------------------------------"))

   val _ = debug_msg ctxt low (fn () => \<^print> ("current original thm",(Thm.cprop_of cthm)))
   val (tab,ctxt1,ge_conds,thm) =
    (bottom (fn tab2 => fn ctxt2 => transform_non_quant_term ctxt2 tab2) (Termtab.empty) [] ctxt) (Thm.cprop_of cthm)
   (*FIXME: This should be done on the fly*)
   val _ = debug_msg ctxt low (fn () => \<^print> ("current transformed thm",thm))


   val ge_conds = distinct (fn (a,b) => Thm.prop_of a = Thm.prop_of b) ge_conds
   val _ = debug_msg ctxt low (fn () => \<^print> ("current transformed thm with unfolded int_nat_conds",thm))
   val _ = debug_msg ctxt low (fn () => \<^print> ("obtained greater equal conditions",ge_conds))

   val thms'' = add_conds ctxt1 [] ge_conds thm cthm 
   val _ = debug_msg ctxt low (fn () => \<^print> ("added greater equal conditions",thms''))
   val _ = debug_msg ctxt low (fn () => \<^print> ("cthm",cthm))

   val thms''' = Conv.fconv_rule (Conv.rewr_conv thms'') cthm

   (*This is used for counterexample generation only*)
   val keys = Termtab.keys tab
   val curr_mapping = ListPair.zip (keys, keys |> map (fst o the o Termtab.lookup tab))
in ((ctxt1,thms'''::thms,curr_mapping @ mapping):test) end

fun global_normalize ctxt ithms =
let
  val _ = debug_msg ctxt low (fn () => \<^print> ("---------------------------------------------------"))
  val _ = debug_msg ctxt low (fn () => \<^print> ("---------------------------------------------------"))
  val _ = debug_msg ctxt low (fn () => \<^print> ("---------------------------------------------------"))

  val _ = debug_msg ctxt middle (fn () => \<^print> ("ithms before conversion ",ithms))
  val (i,thms) = split_list ithms

  val (ctxt',thms',mapping) = fold unfold_test thms (ctxt,[],[])
  val ithms' = ListPair.zip (i,rev thms')
in
 (ctxt',ithms',mapping)
end





end
