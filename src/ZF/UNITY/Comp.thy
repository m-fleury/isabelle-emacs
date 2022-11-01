(*  Title:      ZF/UNITY/Comp.thy
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   1998  University of Cambridge

From Chandy and Sanders, "Reasoning About Program Composition",
Technical Report 2000-003, University of Florida, 2000.

Revised by Sidi Ehmety on January  2001 

Added: a strong form of the order relation over component and localize 

Theory ported from HOL.
  
*)

section\<open>Composition\<close>

theory Comp imports Union Increasing begin

definition
  component :: "[i,i]\<Rightarrow>o"  (infixl \<open>component\<close> 65)  where
  "F component H \<equiv> (\<exists>G. F \<squnion> G = H)"

definition
  strict_component :: "[i,i]\<Rightarrow>o" (infixl \<open>strict'_component\<close> 65)  where
  "F strict_component H \<equiv> F component H \<and> F\<noteq>H"

definition
  (* A stronger form of the component relation *)
  component_of :: "[i,i]\<Rightarrow>o"   (infixl \<open>component'_of\<close> 65)  where
  "F component_of H  \<equiv> (\<exists>G. F ok G \<and> F \<squnion> G = H)"
  
definition
  strict_component_of :: "[i,i]\<Rightarrow>o" (infixl \<open>strict'_component'_of\<close> 65)  where
  "F strict_component_of H  \<equiv> F component_of H  \<and> F\<noteq>H"

definition
  (* Preserves a state function f, in particular a variable *)
  preserves :: "(i\<Rightarrow>i)\<Rightarrow>i"  where
  "preserves(f) \<equiv> {F:program. \<forall>z. F: stable({s:state. f(s) = z})}"

definition
  fun_pair :: "[i\<Rightarrow>i, i \<Rightarrow>i] \<Rightarrow>(i\<Rightarrow>i)"  where
  "fun_pair(f, g) \<equiv> \<lambda>x. <f(x), g(x)>"

definition
  localize  :: "[i\<Rightarrow>i, i] \<Rightarrow> i"  where
  "localize(f,F) \<equiv> mk_program(Init(F), Acts(F),
                       AllowedActs(F) \<inter> (\<Union>G\<in>preserves(f). Acts(G)))"

  
(*** component and strict_component relations ***)

lemma componentI: 
     "H component F | H component G \<Longrightarrow> H component (F \<squnion> G)"
apply (unfold component_def, auto)
apply (rule_tac x = "Ga \<squnion> G" in exI)
apply (rule_tac [2] x = "G \<squnion> F" in exI)
apply (auto simp add: Join_ac)
done

lemma component_eq_subset: 
     "G \<in> program \<Longrightarrow> (F component G) \<longleftrightarrow>  
   (Init(G) \<subseteq> Init(F) \<and> Acts(F) \<subseteq> Acts(G) \<and> AllowedActs(G) \<subseteq> AllowedActs(F))"
apply (unfold component_def, auto)
apply (rule exI)
apply (rule program_equalityI, auto)
done

lemma component_SKIP [simp]: "F \<in> program \<Longrightarrow> SKIP component F"
  unfolding component_def
apply (rule_tac x = F in exI)
apply (force intro: Join_SKIP_left)
done

lemma component_refl [simp]: "F \<in> program \<Longrightarrow> F component F"
  unfolding component_def
apply (rule_tac x = F in exI)
apply (force intro: Join_SKIP_right)
done

lemma SKIP_minimal: "F component SKIP \<Longrightarrow> programify(F) = SKIP"
apply (rule program_equalityI)
apply (simp_all add: component_eq_subset, blast)
done

lemma component_Join1: "F component (F \<squnion> G)"
by (unfold component_def, blast)

lemma component_Join2: "G component (F \<squnion> G)"
  unfolding component_def
apply (simp (no_asm) add: Join_commute)
apply blast
done

lemma Join_absorb1: "F component G \<Longrightarrow> F \<squnion> G = G"
by (auto simp add: component_def Join_left_absorb)

lemma Join_absorb2: "G component F \<Longrightarrow> F \<squnion> G = F"
by (auto simp add: Join_ac component_def)

lemma JOIN_component_iff:
     "H \<in> program\<Longrightarrow>(JOIN(I,F) component H) \<longleftrightarrow> (\<forall>i \<in> I. F(i) component H)"
apply (case_tac "I=0", force)
apply (simp (no_asm_simp) add: component_eq_subset)
apply auto
apply blast
apply (rename_tac "y")
apply (drule_tac c = y and A = "AllowedActs (H)" in subsetD)
apply (blast elim!: not_emptyE)+
done

lemma component_JOIN: "i \<in> I \<Longrightarrow> F(i) component (\<Squnion>i \<in> I. (F(i)))"
  unfolding component_def
apply (blast intro: JOIN_absorb)
done

lemma component_trans: "\<lbrakk>F component G; G component H\<rbrakk> \<Longrightarrow> F component H"
  unfolding component_def
apply (blast intro: Join_assoc [symmetric])
done

lemma component_antisym:
     "\<lbrakk>F \<in> program; G \<in> program\<rbrakk> \<Longrightarrow>(F component G \<and> G  component F) \<longrightarrow> F = G"
apply (simp (no_asm_simp) add: component_eq_subset)
apply clarify
apply (rule program_equalityI, auto)
done

lemma Join_component_iff:
     "H \<in> program \<Longrightarrow> 
      ((F \<squnion> G) component H) \<longleftrightarrow> (F component H \<and> G component H)"
apply (simp (no_asm_simp) add: component_eq_subset)
apply blast
done

lemma component_constrains:
     "\<lbrakk>F component G; G \<in> A co B; F \<in> program\<rbrakk> \<Longrightarrow> F \<in> A co B"
apply (frule constrainsD2)
apply (auto simp add: constrains_def component_eq_subset)
done


(*** preserves ***)

lemma preserves_is_safety_prop [simp]: "safety_prop(preserves(f))"
  unfolding preserves_def safety_prop_def
apply (auto dest: ActsD simp add: stable_def constrains_def)
apply (drule_tac c = act in subsetD, auto)
done

lemma preservesI [rule_format]: 
     "\<forall>z. F \<in> stable({s \<in> state. f(s) = z})  \<Longrightarrow> F \<in> preserves(f)"
apply (auto simp add: preserves_def)
apply (blast dest: stableD2)
done

lemma preserves_imp_eq: 
     "\<lbrakk>F \<in> preserves(f);  act \<in> Acts(F);  \<langle>s,t\<rangle> \<in> act\<rbrakk> \<Longrightarrow> f(s) = f(t)"
  unfolding preserves_def stable_def constrains_def
apply (subgoal_tac "s \<in> state \<and> t \<in> state")
 prefer 2 apply (blast dest!: Acts_type [THEN subsetD], force) 
done

lemma Join_preserves [iff]: 
"(F \<squnion> G \<in> preserves(v)) \<longleftrightarrow>   
      (programify(F) \<in> preserves(v) \<and> programify(G) \<in> preserves(v))"
by (auto simp add: preserves_def INT_iff)
 
lemma JOIN_preserves [iff]:
     "(JOIN(I,F): preserves(v)) \<longleftrightarrow> (\<forall>i \<in> I. programify(F(i)):preserves(v))"
by (auto simp add: JOIN_stable preserves_def INT_iff)

lemma SKIP_preserves [iff]: "SKIP \<in> preserves(v)"
by (auto simp add: preserves_def INT_iff)

lemma fun_pair_apply [simp]: "fun_pair(f,g,x) = <f(x), g(x)>"
  unfolding fun_pair_def
apply (simp (no_asm))
done

lemma preserves_fun_pair:
     "preserves(fun_pair(v,w)) = preserves(v) \<inter> preserves(w)"
apply (rule equalityI)
apply (auto simp add: preserves_def stable_def constrains_def, blast+)
done

lemma preserves_fun_pair_iff [iff]:
     "F \<in> preserves(fun_pair(v, w))  \<longleftrightarrow> F \<in> preserves(v) \<inter> preserves(w)"
by (simp add: preserves_fun_pair)

lemma fun_pair_comp_distrib:
     "(fun_pair(f, g) comp h)(x) = fun_pair(f comp h, g comp h, x)"
by (simp add: fun_pair_def metacomp_def)

lemma comp_apply [simp]: "(f comp g)(x) = f(g(x))"
by (simp add: metacomp_def)

lemma preserves_type: "preserves(v)<=program"
by (unfold preserves_def, auto)

lemma preserves_into_program [TC]: "F \<in> preserves(f) \<Longrightarrow> F \<in> program"
by (blast intro: preserves_type [THEN subsetD])

lemma subset_preserves_comp: "preserves(f) \<subseteq> preserves(g comp f)"
apply (auto simp add: preserves_def stable_def constrains_def)
apply (drule_tac x = "f (xb)" in spec)
apply (drule_tac x = act in bspec, auto)
done

lemma imp_preserves_comp: "F \<in> preserves(f) \<Longrightarrow> F \<in> preserves(g comp f)"
by (blast intro: subset_preserves_comp [THEN subsetD])

lemma preserves_subset_stable: "preserves(f) \<subseteq> stable({s \<in> state. P(f(s))})"
apply (auto simp add: preserves_def stable_def constrains_def)
apply (rename_tac s' s)
apply (subgoal_tac "f (s) = f (s') ")
apply (force+)
done

lemma preserves_imp_stable:
     "F \<in> preserves(f) \<Longrightarrow> F \<in> stable({s \<in> state. P(f(s))})"
by (blast intro: preserves_subset_stable [THEN subsetD])

lemma preserves_imp_increasing: 
 "\<lbrakk>F \<in> preserves(f); \<forall>x \<in> state. f(x):A\<rbrakk> \<Longrightarrow> F \<in> Increasing.increasing(A, r, f)"
  unfolding Increasing.increasing_def
apply (auto intro: preserves_into_program)
apply (rule_tac P = "\<lambda>x. \<langle>k, x\<rangle>:r" in preserves_imp_stable, auto)
done

lemma preserves_id_subset_stable: 
 "st_set(A) \<Longrightarrow> preserves(\<lambda>x. x) \<subseteq> stable(A)"
apply (unfold preserves_def stable_def constrains_def, auto)
apply (drule_tac x = xb in spec)
apply (drule_tac x = act in bspec)
apply (auto dest: ActsD)
done

lemma preserves_id_imp_stable:
     "\<lbrakk>F \<in> preserves(\<lambda>x. x); st_set(A)\<rbrakk> \<Longrightarrow> F \<in> stable(A)"
by (blast intro: preserves_id_subset_stable [THEN subsetD])

(** Added by Sidi **)
(** component_of **)

(*  component_of is stronger than component *)
lemma component_of_imp_component: 
"F component_of H \<Longrightarrow> F component H"
apply (unfold component_def component_of_def, blast)
done

(* component_of satisfies many of component's properties *)
lemma component_of_refl [simp]: "F \<in> program \<Longrightarrow> F component_of F"
  unfolding component_of_def
apply (rule_tac x = SKIP in exI, auto)
done

lemma component_of_SKIP [simp]: "F \<in> program \<Longrightarrow>SKIP component_of F"
apply (unfold component_of_def, auto)
apply (rule_tac x = F in exI, auto)
done

lemma component_of_trans: 
     "\<lbrakk>F component_of G; G component_of H\<rbrakk> \<Longrightarrow> F component_of H"
  unfolding component_of_def
apply (blast intro: Join_assoc [symmetric])
done

(** localize **)
lemma localize_Init_eq [simp]: "Init(localize(v,F)) = Init(F)"
by (unfold localize_def, simp)

lemma localize_Acts_eq [simp]: "Acts(localize(v,F)) = Acts(F)"
by (unfold localize_def, simp)

lemma localize_AllowedActs_eq [simp]: 
 "AllowedActs(localize(v,F)) = AllowedActs(F) \<inter> (\<Union>G \<in> preserves(v). Acts(G))"
  unfolding localize_def
apply (rule equalityI)
apply (auto dest: Acts_type [THEN subsetD])
done


(** Theorems used in ClientImpl **)

lemma stable_localTo_stable2: 
 "\<lbrakk>F \<in> stable({s \<in> state. P(f(s), g(s))});  G \<in> preserves(f);  G \<in> preserves(g)\<rbrakk>  
      \<Longrightarrow> F \<squnion> G \<in> stable({s \<in> state. P(f(s), g(s))})"
apply (auto dest: ActsD preserves_into_program simp add: stable_def constrains_def)
apply (case_tac "act \<in> Acts (F) ")
apply auto
apply (drule preserves_imp_eq)
apply (drule_tac [3] preserves_imp_eq, auto)
done

lemma Increasing_preserves_Stable:
     "\<lbrakk>F \<in> stable({s \<in> state. <f(s), g(s)>:r});  G \<in> preserves(f);    
         F \<squnion> G \<in> Increasing(A, r, g);  
         \<forall>x \<in> state. f(x):A \<and> g(x):A\<rbrakk>      
      \<Longrightarrow> F \<squnion> G \<in> Stable({s \<in> state. <f(s), g(s)>:r})"
apply (auto simp add: stable_def Stable_def Increasing_def Constrains_def all_conj_distrib)
apply (simp_all add: constrains_type [THEN subsetD] preserves_type [THEN subsetD])
apply (blast intro: constrains_weaken)
(*The G case remains*)
apply (auto dest: ActsD simp add: preserves_def stable_def constrains_def ball_conj_distrib all_conj_distrib)
(*We have a G-action, so delete assumptions about F-actions*)
apply (erule_tac V = "\<forall>act \<in> Acts (F). P (act)" for P in thin_rl)
apply (erule_tac V = "\<forall>k\<in>A. \<forall>act \<in> Acts (F) . P (k,act)" for P in thin_rl)
apply (subgoal_tac "f (x) = f (xa) ")
apply (auto dest!: bspec)
done


(** Lemma used in AllocImpl **)

lemma Constrains_UN_left: 
     "\<lbrakk>\<forall>x \<in> I. F \<in> A(x) Co B; F \<in> program\<rbrakk> \<Longrightarrow> F:(\<Union>x \<in> I. A(x)) Co B"
by (unfold Constrains_def constrains_def, auto)


lemma stable_Join_Stable: 
 "\<lbrakk>F \<in> stable({s \<in> state. P(f(s), g(s))});  
     \<forall>k \<in> A. F \<squnion> G \<in> Stable({s \<in> state. P(k, g(s))});  
     G \<in> preserves(f); \<forall>s \<in> state. f(s):A\<rbrakk>
  \<Longrightarrow> F \<squnion> G \<in> Stable({s \<in> state. P(f(s), g(s))})"
  unfolding stable_def Stable_def preserves_def
apply (rule_tac A = "(\<Union>k \<in> A. {s \<in> state. f(s)=k} \<inter> {s \<in> state. P (f (s), g (s))})" in Constrains_weaken_L)
prefer 2 apply blast
apply (rule Constrains_UN_left, auto)
apply (rule_tac A = "{s \<in> state. f(s)=k} \<inter> {s \<in> state. P (f (s), g (s))} \<inter> {s \<in> state. P (k, g (s))}" and A' = "({s \<in> state. f(s)=k} \<union> {s \<in> state. P (f (s), g (s))}) \<inter> {s \<in> state. P (k, g (s))}" in Constrains_weaken)
 prefer 2 apply blast 
 prefer 2 apply blast 
apply (rule Constrains_Int)
apply (rule constrains_imp_Constrains)
apply (auto simp add: constrains_type [THEN subsetD])
apply (blast intro: constrains_weaken) 
apply (drule_tac x = k in spec)
apply (blast intro: constrains_weaken) 
done

end
