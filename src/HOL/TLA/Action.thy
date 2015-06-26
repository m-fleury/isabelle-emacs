(*  Title:      HOL/TLA/Action.thy
    Author:     Stephan Merz
    Copyright:  1998 University of Munich
*)

section {* The action level of TLA as an Isabelle theory *}

theory Action
imports Stfun
begin


(** abstract syntax **)

type_synonym 'a trfun = "(state * state) \<Rightarrow> 'a"
type_synonym action   = "bool trfun"

instance prod :: (world, world) world ..

consts
  (** abstract syntax **)
  before        :: "'a stfun \<Rightarrow> 'a trfun"
  after         :: "'a stfun \<Rightarrow> 'a trfun"
  unch          :: "'a stfun \<Rightarrow> action"

  SqAct         :: "[action, 'a stfun] \<Rightarrow> action"
  AnAct         :: "[action, 'a stfun] \<Rightarrow> action"
  enabled       :: "action \<Rightarrow> stpred"

(** concrete syntax **)

syntax
  (* Syntax for writing action expressions in arbitrary contexts *)
  "_ACT"        :: "lift \<Rightarrow> 'a"                      ("(ACT _)")

  "_before"     :: "lift \<Rightarrow> lift"                    ("($_)"  [100] 99)
  "_after"      :: "lift \<Rightarrow> lift"                    ("(_$)"  [100] 99)
  "_unchanged"  :: "lift \<Rightarrow> lift"                    ("(unchanged _)" [100] 99)

  (*** Priming: same as "after" ***)
  "_prime"      :: "lift \<Rightarrow> lift"                    ("(_`)" [100] 99)

  "_SqAct"      :: "[lift, lift] \<Rightarrow> lift"            ("([_]'_(_))" [0,1000] 99)
  "_AnAct"      :: "[lift, lift] \<Rightarrow> lift"            ("(<_>'_(_))" [0,1000] 99)
  "_Enabled"    :: "lift \<Rightarrow> lift"                    ("(Enabled _)" [100] 100)

translations
  "ACT A"            =>   "(A::state*state \<Rightarrow> _)"
  "_before"          ==   "CONST before"
  "_after"           ==   "CONST after"
  "_prime"           =>   "_after"
  "_unchanged"       ==   "CONST unch"
  "_SqAct"           ==   "CONST SqAct"
  "_AnAct"           ==   "CONST AnAct"
  "_Enabled"         ==   "CONST enabled"
  "w \<Turnstile> [A]_v"       <=   "_SqAct A v w"
  "w \<Turnstile> <A>_v"       <=   "_AnAct A v w"
  "s \<Turnstile> Enabled A"   <=   "_Enabled A s"
  "w \<Turnstile> unchanged f" <=   "_unchanged f w"

axiomatization where
  unl_before:    "(ACT $v) (s,t) \<equiv> v s" and
  unl_after:     "(ACT v$) (s,t) \<equiv> v t" and

  unchanged_def: "(s,t) \<Turnstile> unchanged v \<equiv> (v t = v s)"

defs
  square_def:    "ACT [A]_v \<equiv> ACT (A \<or> unchanged v)"
  angle_def:     "ACT <A>_v \<equiv> ACT (A \<and> \<not> unchanged v)"

  enabled_def:   "s \<Turnstile> Enabled A  \<equiv>  \<exists>u. (s,u) \<Turnstile> A"


(* The following assertion specializes "intI" for any world type
   which is a pair, not just for "state * state".
*)

lemma actionI [intro!]:
  assumes "\<And>s t. (s,t) \<Turnstile> A"
  shows "\<turnstile> A"
  apply (rule assms intI prod.induct)+
  done

lemma actionD [dest]: "\<turnstile> A \<Longrightarrow> (s,t) \<Turnstile> A"
  apply (erule intD)
  done

lemma pr_rews [int_rewrite]:
  "\<turnstile> (#c)` = #c"
  "\<And>f. \<turnstile> f<x>` = f<x` >"
  "\<And>f. \<turnstile> f<x,y>` = f<x`,y` >"
  "\<And>f. \<turnstile> f<x,y,z>` = f<x`,y`,z` >"
  "\<turnstile> (\<forall>x. P x)` = (\<forall>x. (P x)`)"
  "\<turnstile> (\<exists>x. P x)` = (\<exists>x. (P x)`)"
  by (rule actionI, unfold unl_after intensional_rews, rule refl)+


lemmas act_rews [simp] = unl_before unl_after unchanged_def pr_rews

lemmas action_rews = act_rews intensional_rews


(* ================ Functions to "unlift" action theorems into HOL rules ================ *)

ML {*
(* The following functions are specialized versions of the corresponding
   functions defined in Intensional.ML in that they introduce a
   "world" parameter of the form (s,t) and apply additional rewrites.
*)

fun action_unlift ctxt th =
  (rewrite_rule ctxt @{thms action_rews} (th RS @{thm actionD}))
    handle THM _ => int_unlift ctxt th;

(* Turn  \<turnstile> A = B  into meta-level rewrite rule  A == B *)
val action_rewrite = int_rewrite

fun action_use ctxt th =
    case Thm.concl_of th of
      Const _ $ (Const (@{const_name Valid}, _) $ _) =>
              (flatten (action_unlift ctxt th) handle THM _ => th)
    | _ => th;
*}

attribute_setup action_unlift =
  {* Scan.succeed (Thm.rule_attribute (action_unlift o Context.proof_of)) *}
attribute_setup action_rewrite =
  {* Scan.succeed (Thm.rule_attribute (action_rewrite o Context.proof_of)) *}
attribute_setup action_use =
  {* Scan.succeed (Thm.rule_attribute (action_use o Context.proof_of)) *}


(* =========================== square / angle brackets =========================== *)

lemma idle_squareI: "(s,t) \<Turnstile> unchanged v \<Longrightarrow> (s,t) \<Turnstile> [A]_v"
  by (simp add: square_def)

lemma busy_squareI: "(s,t) \<Turnstile> A \<Longrightarrow> (s,t) \<Turnstile> [A]_v"
  by (simp add: square_def)

lemma squareE [elim]:
  "\<lbrakk> (s,t) \<Turnstile> [A]_v; A (s,t) \<Longrightarrow> B (s,t); v t = v s \<Longrightarrow> B (s,t) \<rbrakk> \<Longrightarrow> B (s,t)"
  apply (unfold square_def action_rews)
  apply (erule disjE)
  apply simp_all
  done

lemma squareCI [intro]: "\<lbrakk> v t \<noteq> v s \<Longrightarrow> A (s,t) \<rbrakk> \<Longrightarrow> (s,t) \<Turnstile> [A]_v"
  apply (unfold square_def action_rews)
  apply (rule disjCI)
  apply (erule (1) meta_mp)
  done

lemma angleI [intro]: "\<And>s t. \<lbrakk> A (s,t); v t \<noteq> v s \<rbrakk> \<Longrightarrow> (s,t) \<Turnstile> <A>_v"
  by (simp add: angle_def)

lemma angleE [elim]: "\<lbrakk> (s,t) \<Turnstile> <A>_v; \<lbrakk> A (s,t); v t \<noteq> v s \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  apply (unfold angle_def action_rews)
  apply (erule conjE)
  apply simp
  done

lemma square_simulation:
   "\<And>f. \<lbrakk> \<turnstile> unchanged f \<and> \<not>B \<longrightarrow> unchanged g;
            \<turnstile> A \<and> \<not>unchanged g \<longrightarrow> B
         \<rbrakk> \<Longrightarrow> \<turnstile> [A]_f \<longrightarrow> [B]_g"
  apply clarsimp
  apply (erule squareE)
  apply (auto simp add: square_def)
  done

lemma not_square: "\<turnstile> (\<not> [A]_v) = <\<not>A>_v"
  by (auto simp: square_def angle_def)

lemma not_angle: "\<turnstile> (\<not> <A>_v) = [\<not>A]_v"
  by (auto simp: square_def angle_def)


(* ============================== Facts about ENABLED ============================== *)

lemma enabledI: "\<turnstile> A \<longrightarrow> $Enabled A"
  by (auto simp add: enabled_def)

lemma enabledE: "\<lbrakk> s \<Turnstile> Enabled A; \<And>u. A (s,u) \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  apply (unfold enabled_def)
  apply (erule exE)
  apply simp
  done

lemma notEnabledD: "\<turnstile> \<not>$Enabled G \<longrightarrow> \<not> G"
  by (auto simp add: enabled_def)

(* Monotonicity *)
lemma enabled_mono:
  assumes min: "s \<Turnstile> Enabled F"
    and maj: "\<turnstile> F \<longrightarrow> G"
  shows "s \<Turnstile> Enabled G"
  apply (rule min [THEN enabledE])
  apply (rule enabledI [action_use])
  apply (erule maj [action_use])
  done

(* stronger variant *)
lemma enabled_mono2:
  assumes min: "s \<Turnstile> Enabled F"
    and maj: "\<And>t. F (s,t) \<Longrightarrow> G (s,t)"
  shows "s \<Turnstile> Enabled G"
  apply (rule min [THEN enabledE])
  apply (rule enabledI [action_use])
  apply (erule maj)
  done

lemma enabled_disj1: "\<turnstile> Enabled F \<longrightarrow> Enabled (F \<or> G)"
  by (auto elim!: enabled_mono)

lemma enabled_disj2: "\<turnstile> Enabled G \<longrightarrow> Enabled (F \<or> G)"
  by (auto elim!: enabled_mono)

lemma enabled_conj1: "\<turnstile> Enabled (F \<and> G) \<longrightarrow> Enabled F"
  by (auto elim!: enabled_mono)

lemma enabled_conj2: "\<turnstile> Enabled (F \<and> G) \<longrightarrow> Enabled G"
  by (auto elim!: enabled_mono)

lemma enabled_conjE:
    "\<lbrakk> s \<Turnstile> Enabled (F \<and> G); \<lbrakk> s \<Turnstile> Enabled F; s \<Turnstile> Enabled G \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  apply (frule enabled_conj1 [action_use])
  apply (drule enabled_conj2 [action_use])
  apply simp
  done

lemma enabled_disjD: "\<turnstile> Enabled (F \<or> G) \<longrightarrow> Enabled F \<or> Enabled G"
  by (auto simp add: enabled_def)

lemma enabled_disj: "\<turnstile> Enabled (F \<or> G) = (Enabled F \<or> Enabled G)"
  apply clarsimp
  apply (rule iffI)
   apply (erule enabled_disjD [action_use])
  apply (erule disjE enabled_disj1 [action_use] enabled_disj2 [action_use])+
  done

lemma enabled_ex: "\<turnstile> Enabled (\<exists>x. F x) = (\<exists>x. Enabled (F x))"
  by (force simp add: enabled_def)


(* A rule that combines enabledI and baseE, but generates fewer instantiations *)
lemma base_enabled:
    "\<lbrakk> basevars vs; \<exists>c. \<forall>u. vs u = c \<longrightarrow> A(s,u) \<rbrakk> \<Longrightarrow> s \<Turnstile> Enabled A"
  apply (erule exE)
  apply (erule baseE)
  apply (rule enabledI [action_use])
  apply (erule allE)
  apply (erule mp)
  apply assumption
  done

(* ======================= action_simp_tac ============================== *)

ML {*
(* A dumb simplification-based tactic with just a little first-order logic:
   should plug in only "very safe" rules that can be applied blindly.
   Note that it applies whatever simplifications are currently active.
*)
fun action_simp_tac ctxt intros elims =
    asm_full_simp_tac
         (ctxt setloop (fn _ => (resolve_tac ctxt ((map (action_use ctxt) intros)
                                    @ [refl,impI,conjI,@{thm actionI},@{thm intI},allI]))
                      ORELSE' (eresolve_tac ctxt ((map (action_use ctxt) elims)
                                             @ [conjE,disjE,exE]))));
*}

(* ---------------- enabled_tac: tactic to prove (Enabled A) -------------------- *)

ML {*
(* "Enabled A" can be proven as follows:
   - Assume that we know which state variables are "base variables"
     this should be expressed by a theorem of the form "basevars (x,y,z,...)".
   - Resolve this theorem with baseE to introduce a constant for the value of the
     variables in the successor state, and resolve the goal with the result.
   - Resolve with enabledI and do some rewriting.
   - Solve for the unknowns using standard HOL reasoning.
   The following tactic combines these steps except the final one.
*)

fun enabled_tac ctxt base_vars =
  clarsimp_tac (ctxt addSIs [base_vars RS @{thm base_enabled}]);
*}

method_setup enabled = {*
  Attrib.thm >> (fn th => fn ctxt => SIMPLE_METHOD' (enabled_tac ctxt th))
*}

(* Example *)

lemma
  assumes "basevars (x,y,z)"
  shows "\<turnstile> x \<longrightarrow> Enabled ($x \<and> (y$ = #False))"
  apply (enabled assms)
  apply auto
  done

end
