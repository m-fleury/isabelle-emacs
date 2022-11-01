(*  Title:      ZF/UNITY/FP.thy
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

From Misra, "A Logic for Concurrent Programming", 1994

Theory ported from HOL.
*)

section\<open>Fixed Point of a Program\<close>

theory FP imports UNITY begin

definition   
  FP_Orig :: "i\<Rightarrow>i"  where
    "FP_Orig(F) \<equiv> \<Union>({A \<in> Pow(state). \<forall>B. F \<in> stable(A \<inter> B)})"

definition
  FP :: "i\<Rightarrow>i"  where
    "FP(F) \<equiv> {s\<in>state. F \<in> stable({s})}"


lemma FP_Orig_type: "FP_Orig(F) \<subseteq> state"
by (unfold FP_Orig_def, blast)

lemma st_set_FP_Orig [iff]: "st_set(FP_Orig(F))"
  unfolding st_set_def
apply (rule FP_Orig_type)
done

lemma FP_type: "FP(F) \<subseteq> state"
by (unfold FP_def, blast)

lemma st_set_FP [iff]: "st_set(FP(F))"
  unfolding st_set_def
apply (rule FP_type)
done

lemma stable_FP_Orig_Int: "F \<in> program \<Longrightarrow> F \<in> stable(FP_Orig(F) \<inter> B)"
apply (simp only: FP_Orig_def stable_def Int_Union2)
apply (blast intro: constrains_UN)
done

lemma FP_Orig_weakest2: 
    "\<lbrakk>\<forall>B. F \<in> stable (A \<inter> B); st_set(A)\<rbrakk>  \<Longrightarrow> A \<subseteq> FP_Orig(F)"
by (unfold FP_Orig_def stable_def st_set_def, blast)

lemmas FP_Orig_weakest = allI [THEN FP_Orig_weakest2]

lemma stable_FP_Int: "F \<in> program \<Longrightarrow> F \<in> stable (FP(F) \<inter> B)"
apply (subgoal_tac "FP (F) \<inter> B = (\<Union>x\<in>B. FP (F) \<inter> {x}) ")
 prefer 2 apply blast
apply (simp (no_asm_simp) add: Int_cons_right)
  unfolding FP_def stable_def
apply (rule constrains_UN)
apply (auto simp add: cons_absorb)
done

lemma FP_subset_FP_Orig: "F \<in> program \<Longrightarrow> FP(F) \<subseteq> FP_Orig(F)"
by (rule stable_FP_Int [THEN FP_Orig_weakest], auto)

lemma FP_Orig_subset_FP: "F \<in> program \<Longrightarrow> FP_Orig(F) \<subseteq> FP(F)"
apply (unfold FP_Orig_def FP_def, clarify)
apply (drule_tac x = "{x}" in spec)
apply (simp add: Int_cons_right)
apply (frule stableD2)
apply (auto simp add: cons_absorb st_set_def)
done

lemma FP_equivalence: "F \<in> program \<Longrightarrow> FP(F) = FP_Orig(F)"
by (blast intro!: FP_Orig_subset_FP FP_subset_FP_Orig)

lemma FP_weakest [rule_format]:
     "\<lbrakk>\<forall>B. F \<in> stable(A \<inter> B); F \<in> program; st_set(A)\<rbrakk> \<Longrightarrow> A \<subseteq> FP(F)"
by (simp add: FP_equivalence FP_Orig_weakest)


lemma Diff_FP: 
     "\<lbrakk>F \<in> program;  st_set(A)\<rbrakk> 
      \<Longrightarrow> A-FP(F) = (\<Union>act \<in> Acts(F). A - {s \<in> state. act``{s} \<subseteq> {s}})"
by (unfold FP_def stable_def constrains_def st_set_def, blast)

end
