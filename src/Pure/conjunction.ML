(*  Title:      Pure/conjunction.ML
    Author:     Makarius

Meta-level conjunction.
*)

signature CONJUNCTION =
sig
  val conjunction: cterm
  val mk_conjunction: cterm * cterm -> cterm
  val mk_conjunction_balanced: cterm list -> cterm
  val dest_conjunction: cterm -> cterm * cterm
  val dest_conjunctions: cterm -> cterm list
  val cong: thm -> thm -> thm
  val convs: (cterm -> thm) -> cterm -> thm
  val conjunctionD1: thm
  val conjunctionD2: thm
  val conjunctionI: thm
  val intr: thm -> thm -> thm
  val intr_balanced: thm list -> thm
  val elim: thm -> thm * thm
  val elim_conjunctions: thm -> thm list
  val elim_balanced: int -> thm -> thm list
  val curry_balanced: int -> thm -> thm
  val uncurry_balanced: int -> thm -> thm
end;

structure Conjunction: CONJUNCTION =
struct

(** abstract syntax **)

fun certify t = Thm.global_cterm_of (Context.the_global_context ()) t;
val read_prop = certify o Simple_Syntax.read_prop;

val true_prop = certify Logic.true_prop;
val conjunction = certify Logic.conjunction;

fun mk_conjunction (A, B) = Thm.apply (Thm.apply conjunction A) B;

fun mk_conjunction_balanced [] = true_prop
  | mk_conjunction_balanced ts = Balanced_Tree.make mk_conjunction ts;

fun dest_conjunction ct =
  (case Thm.term_of ct of
    (Const ("Pure.conjunction", _) $ _ $ _) => Thm.dest_binop ct
  | _ => raise TERM ("dest_conjunction", [Thm.term_of ct]));

fun dest_conjunctions ct =
  (case try dest_conjunction ct of
    NONE => [ct]
  | SOME (A, B) => dest_conjunctions A @ dest_conjunctions B);



(** derived rules **)

(* conversion *)

val cong = Thm.combination o Thm.combination (Thm.reflexive conjunction);

fun convs cv ct =
  (case try dest_conjunction ct of
    NONE => cv ct
  | SOME (A, B) => cong (convs cv A) (convs cv B));


(* intro/elim *)

local

val A = read_prop "A" and vA = (("A", 0), propT);
val B = read_prop "B" and vB = (("B", 0), propT);
val C = read_prop "C";
val ABC = read_prop "A \<Longrightarrow> B \<Longrightarrow> C";
val A_B = read_prop "A &&& B";

val conjunction_def =
  Thm.unvarify_axiom (Context.the_global_context ()) "Pure.conjunction_def";

fun conjunctionD which =
  Drule.implies_intr_list [A, B] (Thm.assume (which (A, B))) COMP
  Thm.forall_elim_vars 0 (Thm.equal_elim conjunction_def (Thm.assume A_B));

in

val conjunctionD1 =
  Drule.store_standard_thm (Binding.make ("conjunctionD1", \<^here>)) (conjunctionD #1);

val conjunctionD2 =
  Drule.store_standard_thm (Binding.make ("conjunctionD2", \<^here>)) (conjunctionD #2);

val conjunctionI =
  Drule.store_standard_thm (Binding.make ("conjunctionI", \<^here>))
    (Drule.implies_intr_list [A, B]
      (Thm.equal_elim
        (Thm.symmetric conjunction_def)
        (Thm.forall_intr C (Thm.implies_intr ABC
          (Drule.implies_elim_list (Thm.assume ABC) [Thm.assume A, Thm.assume B])))));


fun intr tha thb =
  Thm.implies_elim
    (Thm.implies_elim
      (Thm.instantiate (TVars.empty, Vars.make2 (vA, Thm.cprop_of tha) (vB, Thm.cprop_of thb))
        conjunctionI)
    tha)
  thb;

fun elim th =
  let
    val (A, B) = dest_conjunction (Thm.cprop_of th)
      handle TERM (msg, _) => raise THM (msg, 0, [th]);
    val inst = Thm.instantiate (TVars.empty, Vars.make2 (vA, A) (vB, B));
  in
   (Thm.implies_elim (inst conjunctionD1) th,
    Thm.implies_elim (inst conjunctionD2) th)
  end;

end;

fun elim_conjunctions th =
  (case try elim th of
    NONE => [th]
  | SOME (th1, th2) => elim_conjunctions th1 @ elim_conjunctions th2);


(* balanced conjuncts *)

fun intr_balanced [] = asm_rl
  | intr_balanced ths = Balanced_Tree.make (uncurry intr) ths;

fun elim_balanced 0 _ = []
  | elim_balanced n th = Balanced_Tree.dest elim n th;


(* currying *)

local

val bootstrap_thy = Context.the_global_context ();

fun conjs n =
  let
    val As =
      map (fn A => Thm.global_cterm_of bootstrap_thy (Free (A, propT)))
        (Name.invent Name.context "A" n);
  in (As, mk_conjunction_balanced As) end;

val B = read_prop "B";

fun comp_rule th rule =
  Thm.adjust_maxidx_thm ~1 (th COMP
    (rule |> Thm.forall_intr_frees |> Thm.forall_elim_vars (Thm.maxidx_of th + 1)));

in

(*
  A1 &&& ... &&& An \<Longrightarrow> B
  -----------------------
  A1 \<Longrightarrow> ... \<Longrightarrow> An \<Longrightarrow> B
*)
fun curry_balanced n th =
  if n < 2 then th
  else
    let
      val (As, C) = conjs n;
      val D = Drule.mk_implies (C, B);
    in
      comp_rule th
        (Thm.implies_elim (Thm.assume D) (intr_balanced (map Thm.assume As))
          |> Drule.implies_intr_list (D :: As))
    end;

(*
  A1 \<Longrightarrow> ... \<Longrightarrow> An \<Longrightarrow> B
  -----------------------
  A1 &&& ... &&& An \<Longrightarrow> B
*)
fun uncurry_balanced n th =
  if n < 2 then th
  else
    let
      val (As, C) = conjs n;
      val D = Drule.list_implies (As, B);
    in
      comp_rule th
        (Drule.implies_elim_list (Thm.assume D) (elim_balanced n (Thm.assume C))
          |> Drule.implies_intr_list [D, C])
    end;

end;

end;
