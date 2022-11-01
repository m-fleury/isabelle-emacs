(*  Title:      ZF/UNITY/WFair.thy
    Author:     Sidi Ehmety, Computer Laboratory
    Copyright   1998  University of Cambridge
*)

section\<open>Progress under Weak Fairness\<close>

theory WFair
imports UNITY ZFC
begin

text\<open>This theory defines the operators transient, ensures and leadsTo,
assuming weak fairness. From Misra, "A Logic for Concurrent Programming",
1994.\<close>

definition
  (* This definition specifies weak fairness.  The rest of the theory
    is generic to all forms of fairness.*)
  transient :: "i\<Rightarrow>i"  where
  "transient(A) \<equiv>{F \<in> program. (\<exists>act\<in>Acts(F). A<=domain(act) \<and>
                               act``A \<subseteq> state-A) \<and> st_set(A)}"

definition
  ensures :: "[i,i] \<Rightarrow> i"       (infixl \<open>ensures\<close> 60)  where
  "A ensures B \<equiv> ((A-B) co (A \<union> B)) \<inter> transient(A-B)"

consts

  (*LEADS-TO constant for the inductive definition*)
  leads :: "[i, i]\<Rightarrow>i"

inductive
  domains
     "leads(D, F)" \<subseteq> "Pow(D)*Pow(D)"
  intros
    Basis:  "\<lbrakk>F \<in> A ensures B;  A \<in> Pow(D); B \<in> Pow(D)\<rbrakk> \<Longrightarrow> \<langle>A,B\<rangle>:leads(D, F)"
    Trans:  "\<lbrakk>\<langle>A,B\<rangle> \<in> leads(D, F); \<langle>B,C\<rangle> \<in> leads(D, F)\<rbrakk> \<Longrightarrow>  \<langle>A,C\<rangle>:leads(D, F)"
    Union:   "\<lbrakk>S \<in> Pow({A \<in> S. \<langle>A, B\<rangle>:leads(D, F)}); B \<in> Pow(D); S \<in> Pow(Pow(D))\<rbrakk> \<Longrightarrow>
              <\<Union>(S),B>:leads(D, F)"

  monos        Pow_mono
  type_intros  Union_Pow_iff [THEN iffD2] UnionI PowI

definition
  (* The Visible version of the LEADS-TO relation*)
  leadsTo :: "[i, i] \<Rightarrow> i"       (infixl \<open>\<longmapsto>\<close> 60)  where
  "A \<longmapsto> B \<equiv> {F \<in> program. \<langle>A,B\<rangle>:leads(state, F)}"

definition
  (* wlt(F, B) is the largest set that leads to B*)
  wlt :: "[i, i] \<Rightarrow> i"  where
    "wlt(F, B) \<equiv> \<Union>({A \<in> Pow(state). F \<in> A \<longmapsto> B})"

(** Ad-hoc set-theory rules **)

lemma Int_Union_Union: "\<Union>(B) \<inter> A = (\<Union>b \<in> B. b \<inter> A)"
by auto

lemma Int_Union_Union2: "A \<inter> \<Union>(B) = (\<Union>b \<in> B. A \<inter> b)"
by auto

(*** transient ***)

lemma transient_type: "transient(A)<=program"
by (unfold transient_def, auto)

lemma transientD2:
"F \<in> transient(A) \<Longrightarrow> F \<in> program \<and> st_set(A)"
apply (unfold transient_def, auto)
done

lemma stable_transient_empty: "\<lbrakk>F \<in> stable(A); F \<in> transient(A)\<rbrakk> \<Longrightarrow> A = 0"
by (simp add: stable_def constrains_def transient_def, fast)

lemma transient_strengthen: "\<lbrakk>F \<in> transient(A); B<=A\<rbrakk> \<Longrightarrow> F \<in> transient(B)"
apply (simp add: transient_def st_set_def, clarify)
apply (blast intro!: rev_bexI)
done

lemma transientI:
"\<lbrakk>act \<in> Acts(F); A \<subseteq> domain(act); act``A \<subseteq> state-A;
    F \<in> program; st_set(A)\<rbrakk> \<Longrightarrow> F \<in> transient(A)"
by (simp add: transient_def, blast)

lemma transientE:
     "\<lbrakk>F \<in> transient(A);
         \<And>act. \<lbrakk>act \<in> Acts(F);  A \<subseteq> domain(act); act``A \<subseteq> state-A\<rbrakk>\<Longrightarrow>P\<rbrakk>
      \<Longrightarrow>P"
by (simp add: transient_def, blast)

lemma transient_state: "transient(state) = 0"
apply (simp add: transient_def)
apply (rule equalityI, auto)
apply (cut_tac F = x in Acts_type)
apply (simp add: Diff_cancel)
apply (auto intro: st0_in_state)
done

lemma transient_state2: "state<=B \<Longrightarrow> transient(B) = 0"
apply (simp add: transient_def st_set_def)
apply (rule equalityI, auto)
apply (cut_tac F = x in Acts_type)
apply (subgoal_tac "B=state")
apply (auto intro: st0_in_state)
done

lemma transient_empty: "transient(0) = program"
by (auto simp add: transient_def)

declare transient_empty [simp] transient_state [simp] transient_state2 [simp]

(*** ensures ***)

lemma ensures_type: "A ensures B <=program"
by (simp add: ensures_def constrains_def, auto)

lemma ensuresI:
"\<lbrakk>F:(A-B) co (A \<union> B); F \<in> transient(A-B)\<rbrakk>\<Longrightarrow>F \<in> A ensures B"
  unfolding ensures_def
apply (auto simp add: transient_type [THEN subsetD])
done

(* Added by Sidi, from Misra's notes, Progress chapter, exercise 4 *)
lemma ensuresI2: "\<lbrakk>F \<in> A co A \<union> B; F \<in> transient(A)\<rbrakk> \<Longrightarrow> F \<in> A ensures B"
apply (drule_tac B = "A-B" in constrains_weaken_L)
apply (drule_tac [2] B = "A-B" in transient_strengthen)
apply (auto simp add: ensures_def transient_type [THEN subsetD])
done

lemma ensuresD: "F \<in> A ensures B \<Longrightarrow> F:(A-B) co (A \<union> B) \<and> F \<in> transient (A-B)"
by (unfold ensures_def, auto)

lemma ensures_weaken_R: "\<lbrakk>F \<in> A ensures A'; A'<=B'\<rbrakk> \<Longrightarrow> F \<in> A ensures B'"
  unfolding ensures_def
apply (blast intro: transient_strengthen constrains_weaken)
done

(*The L-version (precondition strengthening) fails, but we have this*)
lemma stable_ensures_Int:
     "\<lbrakk>F \<in> stable(C);  F \<in> A ensures B\<rbrakk> \<Longrightarrow> F:(C \<inter> A) ensures (C \<inter> B)"

  unfolding ensures_def
apply (simp (no_asm) add: Int_Un_distrib [symmetric] Diff_Int_distrib [symmetric])
apply (blast intro: transient_strengthen stable_constrains_Int constrains_weaken)
done

lemma stable_transient_ensures: "\<lbrakk>F \<in> stable(A);  F \<in> transient(C); A<=B \<union> C\<rbrakk> \<Longrightarrow> F \<in> A ensures B"
apply (frule stable_type [THEN subsetD])
apply (simp add: ensures_def stable_def)
apply (blast intro: transient_strengthen constrains_weaken)
done

lemma ensures_eq: "(A ensures B) = (A unless B) \<inter> transient (A-B)"
by (auto simp add: ensures_def unless_def)

lemma subset_imp_ensures: "\<lbrakk>F \<in> program; A<=B\<rbrakk> \<Longrightarrow> F \<in> A ensures B"
by (auto simp add: ensures_def constrains_def transient_def st_set_def)

(*** leadsTo ***)
lemmas leads_left = leads.dom_subset [THEN subsetD, THEN SigmaD1]
lemmas leads_right = leads.dom_subset [THEN subsetD, THEN SigmaD2]

lemma leadsTo_type: "A \<longmapsto> B \<subseteq> program"
by (unfold leadsTo_def, auto)

lemma leadsToD2:
"F \<in> A \<longmapsto> B \<Longrightarrow> F \<in> program \<and> st_set(A) \<and> st_set(B)"
  unfolding leadsTo_def st_set_def
apply (blast dest: leads_left leads_right)
done

lemma leadsTo_Basis:
    "\<lbrakk>F \<in> A ensures B; st_set(A); st_set(B)\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto> B"
  unfolding leadsTo_def st_set_def
apply (cut_tac ensures_type)
apply (auto intro: leads.Basis)
done
declare leadsTo_Basis [intro]

(* Added by Sidi, from Misra's notes, Progress chapter, exercise number 4 *)
(* \<lbrakk>F \<in> program; A<=B;  st_set(A); st_set(B)\<rbrakk> \<Longrightarrow> A \<longmapsto> B *)
lemmas subset_imp_leadsTo = subset_imp_ensures [THEN leadsTo_Basis]

lemma leadsTo_Trans: "\<lbrakk>F \<in> A \<longmapsto> B;  F \<in> B \<longmapsto> C\<rbrakk>\<Longrightarrow>F \<in> A \<longmapsto> C"
  unfolding leadsTo_def
apply (auto intro: leads.Trans)
done

(* Better when used in association with leadsTo_weaken_R *)
lemma transient_imp_leadsTo: "F \<in> transient(A) \<Longrightarrow> F \<in> A \<longmapsto> (state-A)"
  unfolding transient_def
apply (blast intro: ensuresI [THEN leadsTo_Basis] constrains_weaken transientI)
done

(*Useful with cancellation, disjunction*)
lemma leadsTo_Un_duplicate: "F \<in> A \<longmapsto> (A' \<union> A') \<Longrightarrow> F \<in> A \<longmapsto> A'"
by simp

lemma leadsTo_Un_duplicate2:
     "F \<in> A \<longmapsto> (A' \<union> C \<union> C) \<Longrightarrow> F \<in> A \<longmapsto> (A' \<union> C)"
by (simp add: Un_ac)

(*The Union introduction rule as we should have liked to state it*)
lemma leadsTo_Union:
    "\<lbrakk>\<And>A. A \<in> S \<Longrightarrow> F \<in> A \<longmapsto> B; F \<in> program; st_set(B)\<rbrakk>
     \<Longrightarrow> F \<in> \<Union>(S) \<longmapsto> B"
  unfolding leadsTo_def st_set_def
apply (blast intro: leads.Union dest: leads_left)
done

lemma leadsTo_Union_Int:
    "\<lbrakk>\<And>A. A \<in> S \<Longrightarrow>F \<in> (A \<inter> C) \<longmapsto> B; F \<in> program; st_set(B)\<rbrakk>
     \<Longrightarrow> F \<in> (\<Union>(S)Int C)\<longmapsto> B"
  unfolding leadsTo_def st_set_def
apply (simp only: Int_Union_Union)
apply (blast dest: leads_left intro: leads.Union)
done

lemma leadsTo_UN:
    "\<lbrakk>\<And>i. i \<in> I \<Longrightarrow> F \<in> A(i) \<longmapsto> B; F \<in> program; st_set(B)\<rbrakk>
     \<Longrightarrow> F:(\<Union>i \<in> I. A(i)) \<longmapsto> B"
apply (simp add: Int_Union_Union leadsTo_def st_set_def)
apply (blast dest: leads_left intro: leads.Union)
done

(* Binary union introduction rule *)
lemma leadsTo_Un:
     "\<lbrakk>F \<in> A \<longmapsto> C; F \<in> B \<longmapsto> C\<rbrakk> \<Longrightarrow> F \<in> (A \<union> B) \<longmapsto> C"
apply (subst Un_eq_Union)
apply (blast intro: leadsTo_Union dest: leadsToD2)
done

lemma single_leadsTo_I:
    "\<lbrakk>\<And>x. x \<in> A\<Longrightarrow> F:{x} \<longmapsto> B; F \<in> program; st_set(B)\<rbrakk>
     \<Longrightarrow> F \<in> A \<longmapsto> B"
apply (rule_tac b = A in UN_singleton [THEN subst])
apply (rule leadsTo_UN, auto)
done

lemma leadsTo_refl: "\<lbrakk>F \<in> program; st_set(A)\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto> A"
by (blast intro: subset_imp_leadsTo)

lemma leadsTo_refl_iff: "F \<in> A \<longmapsto> A \<longleftrightarrow> F \<in> program \<and> st_set(A)"
by (auto intro: leadsTo_refl dest: leadsToD2)

lemma empty_leadsTo: "F \<in> 0 \<longmapsto> B \<longleftrightarrow> (F \<in> program \<and> st_set(B))"
by (auto intro: subset_imp_leadsTo dest: leadsToD2)
declare empty_leadsTo [iff]

lemma leadsTo_state: "F \<in> A \<longmapsto> state \<longleftrightarrow> (F \<in> program \<and> st_set(A))"
by (auto intro: subset_imp_leadsTo dest: leadsToD2 st_setD)
declare leadsTo_state [iff]

lemma leadsTo_weaken_R: "\<lbrakk>F \<in> A \<longmapsto> A'; A'<=B'; st_set(B')\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto> B'"
by (blast dest: leadsToD2 intro: subset_imp_leadsTo leadsTo_Trans)

lemma leadsTo_weaken_L: "\<lbrakk>F \<in> A \<longmapsto> A'; B<=A\<rbrakk> \<Longrightarrow> F \<in> B \<longmapsto> A'"
apply (frule leadsToD2)
apply (blast intro: leadsTo_Trans subset_imp_leadsTo st_set_subset)
done

lemma leadsTo_weaken: "\<lbrakk>F \<in> A \<longmapsto> A'; B<=A; A'<=B'; st_set(B')\<rbrakk>\<Longrightarrow> F \<in> B \<longmapsto> B'"
apply (frule leadsToD2)
apply (blast intro: leadsTo_weaken_R leadsTo_weaken_L leadsTo_Trans leadsTo_refl)
done

(* This rule has a nicer conclusion *)
lemma transient_imp_leadsTo2: "\<lbrakk>F \<in> transient(A); state-A<=B; st_set(B)\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto> B"
apply (frule transientD2)
apply (rule leadsTo_weaken_R)
apply (auto simp add: transient_imp_leadsTo)
done

(*Distributes over binary unions*)
lemma leadsTo_Un_distrib: "F:(A \<union> B) \<longmapsto> C  \<longleftrightarrow>  (F \<in> A \<longmapsto> C \<and> F \<in> B \<longmapsto> C)"
by (blast intro: leadsTo_Un leadsTo_weaken_L)

lemma leadsTo_UN_distrib:
"(F:(\<Union>i \<in> I. A(i)) \<longmapsto> B)\<longleftrightarrow> ((\<forall>i \<in> I. F \<in> A(i) \<longmapsto> B) \<and> F \<in> program \<and> st_set(B))"
apply (blast dest: leadsToD2 intro: leadsTo_UN leadsTo_weaken_L)
done

lemma leadsTo_Union_distrib: "(F \<in> \<Union>(S) \<longmapsto> B) \<longleftrightarrow>  (\<forall>A \<in> S. F \<in> A \<longmapsto> B) \<and> F \<in> program \<and> st_set(B)"
by (blast dest: leadsToD2 intro: leadsTo_Union leadsTo_weaken_L)

text\<open>Set difference: maybe combine with \<open>leadsTo_weaken_L\<close>??\<close>
lemma leadsTo_Diff:
     "\<lbrakk>F: (A-B) \<longmapsto> C; F \<in> B \<longmapsto> C; st_set(C)\<rbrakk>
      \<Longrightarrow> F \<in> A \<longmapsto> C"
by (blast intro: leadsTo_Un leadsTo_weaken dest: leadsToD2)

lemma leadsTo_UN_UN:
    "\<lbrakk>\<And>i. i \<in> I \<Longrightarrow> F \<in> A(i) \<longmapsto> A'(i); F \<in> program\<rbrakk>
     \<Longrightarrow> F: (\<Union>i \<in> I. A(i)) \<longmapsto> (\<Union>i \<in> I. A'(i))"
apply (rule leadsTo_Union)
apply (auto intro: leadsTo_weaken_R dest: leadsToD2)
done

(*Binary union version*)
lemma leadsTo_Un_Un: "\<lbrakk>F \<in> A \<longmapsto> A'; F \<in> B \<longmapsto> B'\<rbrakk> \<Longrightarrow> F \<in> (A \<union> B) \<longmapsto> (A' \<union> B')"
apply (subgoal_tac "st_set (A) \<and> st_set (A') \<and> st_set (B) \<and> st_set (B') ")
prefer 2 apply (blast dest: leadsToD2)
apply (blast intro: leadsTo_Un leadsTo_weaken_R)
done

(** The cancellation law **)
lemma leadsTo_cancel2: "\<lbrakk>F \<in> A \<longmapsto> (A' \<union> B); F \<in> B \<longmapsto> B'\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto> (A' \<union> B')"
apply (subgoal_tac "st_set (A) \<and> st_set (A') \<and> st_set (B) \<and> st_set (B') \<and>F \<in> program")
prefer 2 apply (blast dest: leadsToD2)
apply (blast intro: leadsTo_Trans leadsTo_Un_Un leadsTo_refl)
done

lemma leadsTo_cancel_Diff2: "\<lbrakk>F \<in> A \<longmapsto> (A' \<union> B); F \<in> (B-A') \<longmapsto> B'\<rbrakk>\<Longrightarrow> F \<in> A \<longmapsto> (A' \<union> B')"
apply (rule leadsTo_cancel2)
prefer 2 apply assumption
apply (blast dest: leadsToD2 intro: leadsTo_weaken_R)
done


lemma leadsTo_cancel1: "\<lbrakk>F \<in> A \<longmapsto> (B \<union> A'); F \<in> B \<longmapsto> B'\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto> (B' \<union> A')"
apply (simp add: Un_commute)
apply (blast intro!: leadsTo_cancel2)
done

lemma leadsTo_cancel_Diff1:
     "\<lbrakk>F \<in> A \<longmapsto> (B \<union> A'); F: (B-A') \<longmapsto> B'\<rbrakk>\<Longrightarrow> F \<in> A \<longmapsto> (B' \<union> A')"
apply (rule leadsTo_cancel1)
prefer 2 apply assumption
apply (blast intro: leadsTo_weaken_R dest: leadsToD2)
done

(*The INDUCTION rule as we should have liked to state it*)
lemma leadsTo_induct:
  assumes major: "F \<in> za \<longmapsto> zb"
      and basis: "\<And>A B. \<lbrakk>F \<in> A ensures B; st_set(A); st_set(B)\<rbrakk> \<Longrightarrow> P(A,B)"
      and trans: "\<And>A B C. \<lbrakk>F \<in> A \<longmapsto> B; P(A, B);
                              F \<in> B \<longmapsto> C; P(B, C)\<rbrakk> \<Longrightarrow> P(A,C)"
      and union: "\<And>B S. \<lbrakk>\<forall>A \<in> S. F \<in> A \<longmapsto> B; \<forall>A \<in> S. P(A,B);
                           st_set(B); \<forall>A \<in> S. st_set(A)\<rbrakk> \<Longrightarrow> P(\<Union>(S), B)"
  shows "P(za, zb)"
apply (cut_tac major)
apply (unfold leadsTo_def, clarify)
apply (erule leads.induct)
  apply (blast intro: basis [unfolded st_set_def])
 apply (blast intro: trans [unfolded leadsTo_def])
apply (force intro: union [unfolded st_set_def leadsTo_def])
done


(* Added by Sidi, an induction rule without ensures *)
lemma leadsTo_induct2:
  assumes major: "F \<in> za \<longmapsto> zb"
      and basis1: "\<And>A B. \<lbrakk>A<=B; st_set(B)\<rbrakk> \<Longrightarrow> P(A, B)"
      and basis2: "\<And>A B. \<lbrakk>F \<in> A co A \<union> B; F \<in> transient(A); st_set(B)\<rbrakk>
                          \<Longrightarrow> P(A, B)"
      and trans: "\<And>A B C. \<lbrakk>F \<in> A \<longmapsto> B; P(A, B);
                              F \<in> B \<longmapsto> C; P(B, C)\<rbrakk> \<Longrightarrow> P(A,C)"
      and union: "\<And>B S. \<lbrakk>\<forall>A \<in> S. F \<in> A \<longmapsto> B; \<forall>A \<in> S. P(A,B);
                           st_set(B); \<forall>A \<in> S. st_set(A)\<rbrakk> \<Longrightarrow> P(\<Union>(S), B)"
  shows "P(za, zb)"
apply (cut_tac major)
apply (erule leadsTo_induct)
apply (auto intro: trans union)
apply (simp add: ensures_def, clarify)
apply (frule constrainsD2)
apply (drule_tac B' = " (A-B) \<union> B" in constrains_weaken_R)
apply blast
apply (frule ensuresI2 [THEN leadsTo_Basis])
apply (drule_tac [4] basis2, simp_all)
apply (frule_tac A1 = A and B = B in Int_lower2 [THEN basis1])
apply (subgoal_tac "A=\<Union>({A - B, A \<inter> B}) ")
prefer 2 apply blast
apply (erule ssubst)
apply (rule union)
apply (auto intro: subset_imp_leadsTo)
done


(** Variant induction rule: on the preconditions for B **)
(*Lemma is the weak version: can't see how to do it in one step*)
lemma leadsTo_induct_pre_aux:
  "\<lbrakk>F \<in> za \<longmapsto> zb;
      P(zb);
      \<And>A B. \<lbrakk>F \<in> A ensures B;  P(B); st_set(A); st_set(B)\<rbrakk> \<Longrightarrow> P(A);
      \<And>S. \<lbrakk>\<forall>A \<in> S. P(A); \<forall>A \<in> S. st_set(A)\<rbrakk> \<Longrightarrow> P(\<Union>(S))
\<rbrakk> \<Longrightarrow> P(za)"
txt\<open>by induction on this formula\<close>
apply (subgoal_tac "P (zb) \<longrightarrow> P (za) ")
txt\<open>now solve first subgoal: this formula is sufficient\<close>
apply (blast intro: leadsTo_refl)
apply (erule leadsTo_induct)
apply (blast+)
done


lemma leadsTo_induct_pre:
  "\<lbrakk>F \<in> za \<longmapsto> zb;
      P(zb);
      \<And>A B. \<lbrakk>F \<in> A ensures B;  F \<in> B \<longmapsto> zb;  P(B); st_set(A)\<rbrakk> \<Longrightarrow> P(A);
      \<And>S. \<forall>A \<in> S. F \<in> A \<longmapsto> zb \<and> P(A) \<and> st_set(A) \<Longrightarrow> P(\<Union>(S))
\<rbrakk> \<Longrightarrow> P(za)"
apply (subgoal_tac " (F \<in> za \<longmapsto> zb) \<and> P (za) ")
apply (erule conjunct2)
apply (frule leadsToD2)
apply (erule leadsTo_induct_pre_aux)
prefer 3 apply (blast dest: leadsToD2 intro: leadsTo_Union)
prefer 2 apply (blast intro: leadsTo_Trans leadsTo_Basis)
apply (blast intro: leadsTo_refl)
done

(** The impossibility law **)
lemma leadsTo_empty:
   "F \<in> A \<longmapsto> 0 \<Longrightarrow> A=0"
apply (erule leadsTo_induct_pre)
apply (auto simp add: ensures_def constrains_def transient_def st_set_def)
apply (drule bspec, assumption)+
apply blast
done
declare leadsTo_empty [simp]

subsection\<open>PSP: Progress-Safety-Progress\<close>

text\<open>Special case of PSP: Misra's "stable conjunction"\<close>

lemma psp_stable:
   "\<lbrakk>F \<in> A \<longmapsto> A'; F \<in> stable(B)\<rbrakk> \<Longrightarrow> F:(A \<inter> B) \<longmapsto> (A' \<inter> B)"
  unfolding stable_def
apply (frule leadsToD2)
apply (erule leadsTo_induct)
prefer 3 apply (blast intro: leadsTo_Union_Int)
prefer 2 apply (blast intro: leadsTo_Trans)
apply (rule leadsTo_Basis)
apply (simp add: ensures_def Diff_Int_distrib2 [symmetric] Int_Un_distrib2 [symmetric])
apply (auto intro: transient_strengthen constrains_Int)
done


lemma psp_stable2: "\<lbrakk>F \<in> A \<longmapsto> A'; F \<in> stable(B)\<rbrakk>\<Longrightarrow>F: (B \<inter> A) \<longmapsto> (B \<inter> A')"
apply (simp (no_asm_simp) add: psp_stable Int_ac)
done

lemma psp_ensures:
"\<lbrakk>F \<in> A ensures A'; F \<in> B co B'\<rbrakk>\<Longrightarrow> F: (A \<inter> B') ensures ((A' \<inter> B) \<union> (B' - B))"
  unfolding ensures_def constrains_def st_set_def
(*speeds up the proof*)
apply clarify
apply (blast intro: transient_strengthen)
done

lemma psp:
"\<lbrakk>F \<in> A \<longmapsto> A'; F \<in> B co B'; st_set(B')\<rbrakk>\<Longrightarrow> F:(A \<inter> B') \<longmapsto> ((A' \<inter> B) \<union> (B' - B))"
apply (subgoal_tac "F \<in> program \<and> st_set (A) \<and> st_set (A') \<and> st_set (B) ")
prefer 2 apply (blast dest!: constrainsD2 leadsToD2)
apply (erule leadsTo_induct)
prefer 3 apply (blast intro: leadsTo_Union_Int)
 txt\<open>Basis case\<close>
 apply (blast intro: psp_ensures leadsTo_Basis)
txt\<open>Transitivity case has a delicate argument involving "cancellation"\<close>
apply (rule leadsTo_Un_duplicate2)
apply (erule leadsTo_cancel_Diff1)
apply (simp add: Int_Diff Diff_triv)
apply (blast intro: leadsTo_weaken_L dest: constrains_imp_subset)
done


lemma psp2: "\<lbrakk>F \<in> A \<longmapsto> A'; F \<in> B co B'; st_set(B')\<rbrakk>
    \<Longrightarrow> F \<in> (B' \<inter> A) \<longmapsto> ((B \<inter> A') \<union> (B' - B))"
by (simp (no_asm_simp) add: psp Int_ac)

lemma psp_unless:
   "\<lbrakk>F \<in> A \<longmapsto> A';  F \<in> B unless B'; st_set(B); st_set(B')\<rbrakk>
    \<Longrightarrow> F \<in> (A \<inter> B) \<longmapsto> ((A' \<inter> B) \<union> B')"
  unfolding unless_def
apply (subgoal_tac "st_set (A) \<and>st_set (A') ")
prefer 2 apply (blast dest: leadsToD2)
apply (drule psp, assumption, blast)
apply (blast intro: leadsTo_weaken)
done


subsection\<open>Proving the induction rules\<close>

(** The most general rule \<in> r is any wf relation; f is any variant function **)
lemma leadsTo_wf_induct_aux: "\<lbrakk>wf(r);
         m \<in> I;
         field(r)<=I;
         F \<in> program; st_set(B);
         \<forall>m \<in> I. F \<in> (A \<inter> f-``{m}) \<longmapsto>
                    ((A \<inter> f-``(converse(r)``{m})) \<union> B)\<rbrakk>
      \<Longrightarrow> F \<in> (A \<inter> f-``{m}) \<longmapsto> B"
apply (erule_tac a = m in wf_induct2, simp_all)
apply (subgoal_tac "F \<in> (A \<inter> (f-`` (converse (r) ``{x}))) \<longmapsto> B")
 apply (blast intro: leadsTo_cancel1 leadsTo_Un_duplicate)
apply (subst vimage_eq_UN)
apply (simp del: UN_simps add: Int_UN_distrib)
apply (auto intro: leadsTo_UN simp del: UN_simps simp add: Int_UN_distrib)
done

(** Meta or object quantifier ? **)
lemma leadsTo_wf_induct: "\<lbrakk>wf(r);
         field(r)<=I;
         A<=f-``I;
         F \<in> program; st_set(A); st_set(B);
         \<forall>m \<in> I. F \<in> (A \<inter> f-``{m}) \<longmapsto>
                    ((A \<inter> f-``(converse(r)``{m})) \<union> B)\<rbrakk>
      \<Longrightarrow> F \<in> A \<longmapsto> B"
apply (rule_tac b = A in subst)
 defer 1
 apply (rule_tac I = I in leadsTo_UN)
 apply (erule_tac I = I in leadsTo_wf_induct_aux, assumption+, best)
done

lemma nat_measure_field: "field(measure(nat, \<lambda>x. x)) = nat"
  unfolding field_def
apply (simp add: measure_def)
apply (rule equalityI, force, clarify)
apply (erule_tac V = "x\<notin>range (y)" for y in thin_rl)
apply (erule nat_induct)
apply (rule_tac [2] b = "succ (succ (xa))" in domainI)
apply (rule_tac b = "succ (0) " in domainI)
apply simp_all
done


lemma Image_inverse_lessThan: "k<A \<Longrightarrow> measure(A, \<lambda>x. x) -`` {k} = k"
apply (rule equalityI)
apply (auto simp add: measure_def)
apply (blast intro: ltD)
apply (rule vimageI)
prefer 2 apply blast
apply (simp add: lt_Ord lt_Ord2 Ord_mem_iff_lt)
apply (blast intro: lt_trans)
done

(*Alternative proof is via the lemma F \<in> (A \<inter> f-`(lessThan m)) \<longmapsto> B*)
lemma lessThan_induct:
 "\<lbrakk>A<=f-``nat;
     F \<in> program; st_set(A); st_set(B);
     \<forall>m \<in> nat. F:(A \<inter> f-``{m}) \<longmapsto> ((A \<inter> f -`` m) \<union> B)\<rbrakk>
      \<Longrightarrow> F \<in> A \<longmapsto> B"
apply (rule_tac A1 = nat and f1 = "\<lambda>x. x" in wf_measure [THEN leadsTo_wf_induct])
apply (simp_all add: nat_measure_field)
apply (simp add: ltI Image_inverse_lessThan vimage_def [symmetric])
done


(*** wlt ****)

(*Misra's property W3*)
lemma wlt_type: "wlt(F,B) <=state"
by (unfold wlt_def, auto)

lemma wlt_st_set: "st_set(wlt(F, B))"
  unfolding st_set_def
apply (rule wlt_type)
done
declare wlt_st_set [iff]

lemma wlt_leadsTo_iff: "F \<in> wlt(F, B) \<longmapsto> B \<longleftrightarrow> (F \<in> program \<and> st_set(B))"
  unfolding wlt_def
apply (blast dest: leadsToD2 intro!: leadsTo_Union)
done

(* \<lbrakk>F \<in> program;  st_set(B)\<rbrakk> \<Longrightarrow> F \<in> wlt(F, B) \<longmapsto> B  *)
lemmas wlt_leadsTo = conjI [THEN wlt_leadsTo_iff [THEN iffD2]]

lemma leadsTo_subset: "F \<in> A \<longmapsto> B \<Longrightarrow> A \<subseteq> wlt(F, B)"
  unfolding wlt_def
apply (frule leadsToD2)
apply (auto simp add: st_set_def)
done

(*Misra's property W2*)
lemma leadsTo_eq_subset_wlt: "F \<in> A \<longmapsto> B \<longleftrightarrow> (A \<subseteq> wlt(F,B) \<and> F \<in> program \<and> st_set(B))"
apply auto
apply (blast dest: leadsToD2 leadsTo_subset intro: leadsTo_weaken_L wlt_leadsTo)+
done

(*Misra's property W4*)
lemma wlt_increasing: "\<lbrakk>F \<in> program; st_set(B)\<rbrakk> \<Longrightarrow> B \<subseteq> wlt(F,B)"
apply (rule leadsTo_subset)
apply (simp (no_asm_simp) add: leadsTo_eq_subset_wlt [THEN iff_sym] subset_imp_leadsTo)
done

(*Used in the Trans case below*)
lemma leadsTo_123_aux:
   "\<lbrakk>B \<subseteq> A2;
       F \<in> (A1 - B) co (A1 \<union> B);
       F \<in> (A2 - C) co (A2 \<union> C)\<rbrakk>
    \<Longrightarrow> F \<in> (A1 \<union> A2 - C) co (A1 \<union> A2 \<union> C)"
apply (unfold constrains_def st_set_def, blast)
done

(*Lemma (1,2,3) of Misra's draft book, Chapter 4, "Progress"*)
(* slightly different from the HOL one \<in> B here is bounded *)
lemma leadsTo_123: "F \<in> A \<longmapsto> A'
      \<Longrightarrow> \<exists>B \<in> Pow(state). A<=B \<and> F \<in> B \<longmapsto> A' \<and> F \<in> (B-A') co (B \<union> A')"
apply (frule leadsToD2)
apply (erule leadsTo_induct)
  txt\<open>Basis\<close>
  apply (blast dest: ensuresD constrainsD2 st_setD)
 txt\<open>Trans\<close>
 apply clarify
 apply (rule_tac x = "Ba \<union> Bb" in bexI)
 apply (blast intro: leadsTo_123_aux leadsTo_Un_Un leadsTo_cancel1 leadsTo_Un_duplicate, blast)
txt\<open>Union\<close>
apply (clarify dest!: ball_conj_distrib [THEN iffD1])
apply (subgoal_tac "\<exists>y. y \<in> Pi (S, \<lambda>A. {Ba \<in> Pow (state) . A<=Ba \<and> F \<in> Ba \<longmapsto> B \<and> F \<in> Ba - B co Ba \<union> B}) ")
defer 1
apply (rule AC_ball_Pi, safe)
apply (rotate_tac 1)
apply (drule_tac x = x in bspec, blast, blast)
apply (rule_tac x = "\<Union>A \<in> S. y`A" in bexI, safe)
apply (rule_tac [3] I1 = S in constrains_UN [THEN constrains_weaken])
apply (rule_tac [2] leadsTo_Union)
prefer 5 apply (blast dest!: apply_type, simp_all)
apply (force dest!: apply_type)+
done


(*Misra's property W5*)
lemma wlt_constrains_wlt: "\<lbrakk>F \<in> program; st_set(B)\<rbrakk> \<Longrightarrow>F \<in> (wlt(F, B) - B) co (wlt(F,B))"
apply (cut_tac F = F in wlt_leadsTo [THEN leadsTo_123], assumption, blast)
apply clarify
apply (subgoal_tac "Ba = wlt (F,B) ")
prefer 2 apply (blast dest: leadsTo_eq_subset_wlt [THEN iffD1], clarify)
apply (simp add: wlt_increasing [THEN subset_Un_iff2 [THEN iffD1]])
done


subsection\<open>Completion: Binary and General Finite versions\<close>

lemma completion_aux: "\<lbrakk>W = wlt(F, (B' \<union> C));
       F \<in> A \<longmapsto> (A' \<union> C);  F \<in> A' co (A' \<union> C);
       F \<in> B \<longmapsto> (B' \<union> C);  F \<in> B' co (B' \<union> C)\<rbrakk>
    \<Longrightarrow> F \<in> (A \<inter> B) \<longmapsto> ((A' \<inter> B') \<union> C)"
apply (subgoal_tac "st_set (C) \<and>st_set (W) \<and>st_set (W-C) \<and>st_set (A') \<and>st_set (A) \<and> st_set (B) \<and> st_set (B') \<and> F \<in> program")
 prefer 2
 apply simp
 apply (blast dest!: leadsToD2)
apply (subgoal_tac "F \<in> (W-C) co (W \<union> B' \<union> C) ")
 prefer 2
 apply (blast intro!: constrains_weaken [OF constrains_Un [OF _ wlt_constrains_wlt]])
apply (subgoal_tac "F \<in> (W-C) co W")
 prefer 2
 apply (simp add: wlt_increasing [THEN subset_Un_iff2 [THEN iffD1]] Un_assoc)
apply (subgoal_tac "F \<in> (A \<inter> W - C) \<longmapsto> (A' \<inter> W \<union> C) ")
 prefer 2 apply (blast intro: wlt_leadsTo psp [THEN leadsTo_weaken])
(** step 13 **)
apply (subgoal_tac "F \<in> (A' \<inter> W \<union> C) \<longmapsto> (A' \<inter> B' \<union> C) ")
apply (drule leadsTo_Diff)
apply (blast intro: subset_imp_leadsTo dest: leadsToD2 constrainsD2)
apply (force simp add: st_set_def)
apply (subgoal_tac "A \<inter> B \<subseteq> A \<inter> W")
prefer 2 apply (blast dest!: leadsTo_subset intro!: subset_refl [THEN Int_mono])
apply (blast intro: leadsTo_Trans subset_imp_leadsTo)
txt\<open>last subgoal\<close>
apply (rule_tac leadsTo_Un_duplicate2)
apply (rule_tac leadsTo_Un_Un)
 prefer 2 apply (blast intro: leadsTo_refl)
apply (rule_tac A'1 = "B' \<union> C" in wlt_leadsTo[THEN psp2, THEN leadsTo_weaken])
apply blast+
done

lemmas completion = refl [THEN completion_aux]

lemma finite_completion_aux:
     "\<lbrakk>I \<in> Fin(X); F \<in> program; st_set(C)\<rbrakk> \<Longrightarrow>
       (\<forall>i \<in> I. F \<in> (A(i)) \<longmapsto> (A'(i) \<union> C)) \<longrightarrow>
                     (\<forall>i \<in> I. F \<in> (A'(i)) co (A'(i) \<union> C)) \<longrightarrow>
                   F \<in> (\<Inter>i \<in> I. A(i)) \<longmapsto> ((\<Inter>i \<in> I. A'(i)) \<union> C)"
apply (erule Fin_induct)
apply (auto simp add: Inter_0)
apply (rule completion)
apply (auto simp del: INT_simps simp add: INT_extend_simps)
apply (blast intro: constrains_INT)
done

lemma finite_completion:
     "\<lbrakk>I \<in> Fin(X);
         \<And>i. i \<in> I \<Longrightarrow> F \<in> A(i) \<longmapsto> (A'(i) \<union> C);
         \<And>i. i \<in> I \<Longrightarrow> F \<in> A'(i) co (A'(i) \<union> C); F \<in> program; st_set(C)\<rbrakk>
      \<Longrightarrow> F \<in> (\<Inter>i \<in> I. A(i)) \<longmapsto> ((\<Inter>i \<in> I. A'(i)) \<union> C)"
by (blast intro: finite_completion_aux [THEN mp, THEN mp])

lemma stable_completion:
     "\<lbrakk>F \<in> A \<longmapsto> A';  F \<in> stable(A');
         F \<in> B \<longmapsto> B';  F \<in> stable(B')\<rbrakk>
    \<Longrightarrow> F \<in> (A \<inter> B) \<longmapsto> (A' \<inter> B')"
  unfolding stable_def
apply (rule_tac C1 = 0 in completion [THEN leadsTo_weaken_R], simp+)
apply (blast dest: leadsToD2)
done


lemma finite_stable_completion:
     "\<lbrakk>I \<in> Fin(X);
         (\<And>i. i \<in> I \<Longrightarrow> F \<in> A(i) \<longmapsto> A'(i));
         (\<And>i. i \<in> I \<Longrightarrow> F \<in> stable(A'(i)));  F \<in> program\<rbrakk>
      \<Longrightarrow> F \<in> (\<Inter>i \<in> I. A(i)) \<longmapsto> (\<Inter>i \<in> I. A'(i))"
  unfolding stable_def
apply (subgoal_tac "st_set (\<Inter>i \<in> I. A' (i))")
prefer 2 apply (blast dest: leadsToD2)
apply (rule_tac C1 = 0 in finite_completion [THEN leadsTo_weaken_R], auto)
done

end
