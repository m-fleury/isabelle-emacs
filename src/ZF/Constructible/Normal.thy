(*  Title:      ZF/Constructible/Normal.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>Closed Unbounded Classes and Normal Functions\<close>

theory Normal imports ZF begin

text\<open>
One source is the book

Frank R. Drake.
\emph{Set Theory: An Introduction to Large Cardinals}.
North-Holland, 1974.
\<close>


subsection \<open>Closed and Unbounded (c.u.) Classes of Ordinals\<close>

definition
  Closed :: "(i\<Rightarrow>o) \<Rightarrow> o" where
    "Closed(P) \<equiv> \<forall>I. I \<noteq> 0 \<longrightarrow> (\<forall>i\<in>I. Ord(i) \<and> P(i)) \<longrightarrow> P(\<Union>(I))"

definition
  Unbounded :: "(i\<Rightarrow>o) \<Rightarrow> o" where
    "Unbounded(P) \<equiv> \<forall>i. Ord(i) \<longrightarrow> (\<exists>j. i<j \<and> P(j))"

definition
  Closed_Unbounded :: "(i\<Rightarrow>o) \<Rightarrow> o" where
    "Closed_Unbounded(P) \<equiv> Closed(P) \<and> Unbounded(P)"


subsubsection\<open>Simple facts about c.u. classes\<close>

lemma ClosedI:
  "\<lbrakk>\<And>I. \<lbrakk>I \<noteq> 0; \<forall>i\<in>I. Ord(i) \<and> P(i)\<rbrakk> \<Longrightarrow> P(\<Union>(I))\<rbrakk> 
      \<Longrightarrow> Closed(P)"
  by (simp add: Closed_def)

lemma ClosedD:
  "\<lbrakk>Closed(P); I \<noteq> 0; \<And>i. i\<in>I \<Longrightarrow> Ord(i); \<And>i. i\<in>I \<Longrightarrow> P(i)\<rbrakk> 
      \<Longrightarrow> P(\<Union>(I))"
  by (simp add: Closed_def)

lemma UnboundedD:
  "\<lbrakk>Unbounded(P);  Ord(i)\<rbrakk> \<Longrightarrow> \<exists>j. i<j \<and> P(j)"
  by (simp add: Unbounded_def)

lemma Closed_Unbounded_imp_Unbounded: "Closed_Unbounded(C) \<Longrightarrow> Unbounded(C)"
  by (simp add: Closed_Unbounded_def) 


text\<open>The universal class, V, is closed and unbounded.
      A bit odd, since C. U. concerns only ordinals, but it's used below!\<close>
theorem Closed_Unbounded_V [simp]: "Closed_Unbounded(\<lambda>x. True)"
  by (unfold Closed_Unbounded_def Closed_def Unbounded_def, blast)

text\<open>The class of ordinals, \<^term>\<open>Ord\<close>, is closed and unbounded.\<close>
theorem Closed_Unbounded_Ord   [simp]: "Closed_Unbounded(Ord)"
  by (unfold Closed_Unbounded_def Closed_def Unbounded_def, blast)

text\<open>The class of limit ordinals, \<^term>\<open>Limit\<close>, is closed and unbounded.\<close>
theorem Closed_Unbounded_Limit [simp]: "Closed_Unbounded(Limit)"
  apply (simp add: Closed_Unbounded_def Closed_def Unbounded_def Limit_Union, 
      clarify)
  apply (rule_tac x="i++nat" in exI)  
  apply (blast intro: oadd_lt_self oadd_LimitI Limit_has_0) 
  done

text\<open>The class of cardinals, \<^term>\<open>Card\<close>, is closed and unbounded.\<close>
theorem Closed_Unbounded_Card  [simp]: "Closed_Unbounded(Card)"
  apply (simp add: Closed_Unbounded_def Closed_def Unbounded_def)
  apply (blast intro: lt_csucc Card_csucc)
  done


subsubsection\<open>The intersection of any set-indexed family of c.u. classes is
      c.u.\<close>

text\<open>The constructions below come from Kunen, \emph{Set Theory}, page 78.\<close>
locale cub_family =
  fixes P and A
  fixes next_greater \<comment> \<open>the next ordinal satisfying class \<^term>\<open>A\<close>\<close>
  fixes sup_greater  \<comment> \<open>sup of those ordinals over all \<^term>\<open>A\<close>\<close>
  assumes closed:    "a\<in>A \<Longrightarrow> Closed(P(a))"
      and unbounded: "a\<in>A \<Longrightarrow> Unbounded(P(a))"
      and A_non0: "A\<noteq>0"
  defines "next_greater(a,x) \<equiv> \<mu> y. x<y \<and> P(a,y)"
      and "sup_greater(x) \<equiv> \<Union>a\<in>A. next_greater(a,x)"

begin

text\<open>Trivial that the intersection is closed.\<close>
lemma Closed_INT: "Closed(\<lambda>x. \<forall>i\<in>A. P(i,x))"
  by (blast intro: ClosedI ClosedD [OF closed])

text\<open>All remaining effort goes to show that the intersection is unbounded.\<close>

lemma Ord_sup_greater:
  "Ord(sup_greater(x))"
  by (simp add: sup_greater_def next_greater_def)

lemma Ord_next_greater:
  "Ord(next_greater(a,x))"
  by (simp add: next_greater_def)

text\<open>\<^term>\<open>next_greater\<close> works as expected: it returns a larger value
and one that belongs to class \<^term>\<open>P(a)\<close>.\<close>
lemma next_greater_lemma:
  "\<lbrakk>Ord(x); a\<in>A\<rbrakk> \<Longrightarrow> P(a, next_greater(a,x)) \<and> x < next_greater(a,x)"
  apply (simp add: next_greater_def)
  apply (rule exE [OF UnboundedD [OF unbounded]])
    apply assumption+
  apply (blast intro: LeastI2 lt_Ord2) 
  done

lemma next_greater_in_P:
  "\<lbrakk>Ord(x); a\<in>A\<rbrakk> \<Longrightarrow> P(a, next_greater(a,x))"
  by (blast dest: next_greater_lemma)

lemma next_greater_gt:
  "\<lbrakk>Ord(x); a\<in>A\<rbrakk> \<Longrightarrow> x < next_greater(a,x)"
  by (blast dest: next_greater_lemma)

lemma sup_greater_gt:
  "Ord(x) \<Longrightarrow> x < sup_greater(x)"
  apply (simp add: sup_greater_def)
  apply (insert A_non0)
  apply (blast intro: UN_upper_lt next_greater_gt Ord_next_greater)
  done

lemma next_greater_le_sup_greater:
  "a\<in>A \<Longrightarrow> next_greater(a,x) \<le> sup_greater(x)"
  apply (simp add: sup_greater_def) 
  apply (blast intro: UN_upper_le Ord_next_greater)
  done

lemma omega_sup_greater_eq_UN:
  "\<lbrakk>Ord(x); a\<in>A\<rbrakk> 
      \<Longrightarrow> sup_greater^\<omega> (x) = 
          (\<Union>n\<in>nat. next_greater(a, sup_greater^n (x)))"
  apply (simp add: iterates_omega_def)
  apply (rule le_anti_sym)
   apply (rule le_implies_UN_le_UN) 
   apply (blast intro: leI next_greater_gt Ord_iterates Ord_sup_greater)  
  txt\<open>Opposite bound:
@{subgoals[display,indent=0,margin=65]}
\<close>
  apply (rule UN_least_le) 
   apply (blast intro: Ord_iterates Ord_sup_greater)  
  apply (rule_tac a="succ(n)" in UN_upper_le)
    apply (simp_all add: next_greater_le_sup_greater) 
  apply (blast intro: Ord_iterates Ord_sup_greater)  
  done

lemma P_omega_sup_greater:
  "\<lbrakk>Ord(x); a\<in>A\<rbrakk> \<Longrightarrow> P(a, sup_greater^\<omega> (x))"
  apply (simp add: omega_sup_greater_eq_UN)
  apply (rule ClosedD [OF closed]) 
     apply (blast intro: ltD, auto)
   apply (blast intro: Ord_iterates Ord_next_greater Ord_sup_greater)
  apply (blast intro: next_greater_in_P Ord_iterates Ord_sup_greater)
  done

lemma omega_sup_greater_gt:
  "Ord(x) \<Longrightarrow> x < sup_greater^\<omega> (x)"
  apply (simp add: iterates_omega_def)
  apply (rule UN_upper_lt [of 1], simp_all) 
   apply (blast intro: sup_greater_gt) 
  apply (blast intro: Ord_iterates Ord_sup_greater)
  done

lemma Unbounded_INT: "Unbounded(\<lambda>x. \<forall>a\<in>A. P(a,x))"
    unfolding Unbounded_def  
  apply (blast intro!: omega_sup_greater_gt P_omega_sup_greater) 
  done

lemma Closed_Unbounded_INT: 
  "Closed_Unbounded(\<lambda>x. \<forall>a\<in>A. P(a,x))"
  by (simp add: Closed_Unbounded_def Closed_INT Unbounded_INT)

end


theorem Closed_Unbounded_INT:
  "(\<And>a. a\<in>A \<Longrightarrow> Closed_Unbounded(P(a)))
     \<Longrightarrow> Closed_Unbounded(\<lambda>x. \<forall>a\<in>A. P(a, x))"
  apply (case_tac "A=0", simp)
  apply (rule cub_family.Closed_Unbounded_INT [OF cub_family.intro])
    apply (simp_all add: Closed_Unbounded_def)
  done

lemma Int_iff_INT2:
  "P(x) \<and> Q(x)  \<longleftrightarrow>  (\<forall>i\<in>2. (i=0 \<longrightarrow> P(x)) \<and> (i=1 \<longrightarrow> Q(x)))"
  by auto

theorem Closed_Unbounded_Int:
  "\<lbrakk>Closed_Unbounded(P); Closed_Unbounded(Q)\<rbrakk> 
      \<Longrightarrow> Closed_Unbounded(\<lambda>x. P(x) \<and> Q(x))"
  apply (simp only: Int_iff_INT2)
  apply (rule Closed_Unbounded_INT, auto) 
  done


subsection \<open>Normal Functions\<close> 

definition
  mono_le_subset :: "(i\<Rightarrow>i) \<Rightarrow> o" where
    "mono_le_subset(M) \<equiv> \<forall>i j. i\<le>j \<longrightarrow> M(i) \<subseteq> M(j)"

definition
  mono_Ord :: "(i\<Rightarrow>i) \<Rightarrow> o" where
    "mono_Ord(F) \<equiv> \<forall>i j. i<j \<longrightarrow> F(i) < F(j)"

definition
  cont_Ord :: "(i\<Rightarrow>i) \<Rightarrow> o" where
    "cont_Ord(F) \<equiv> \<forall>l. Limit(l) \<longrightarrow> F(l) = (\<Union>i<l. F(i))"

definition
  Normal :: "(i\<Rightarrow>i) \<Rightarrow> o" where
    "Normal(F) \<equiv> mono_Ord(F) \<and> cont_Ord(F)"


subsubsection\<open>Immediate properties of the definitions\<close>

lemma NormalI:
  "\<lbrakk>\<And>i j. i<j \<Longrightarrow> F(i) < F(j);  \<And>l. Limit(l) \<Longrightarrow> F(l) = (\<Union>i<l. F(i))\<rbrakk>
      \<Longrightarrow> Normal(F)"
  by (simp add: Normal_def mono_Ord_def cont_Ord_def)

lemma mono_Ord_imp_Ord: "\<lbrakk>Ord(i); mono_Ord(F)\<rbrakk> \<Longrightarrow> Ord(F(i))"
  apply (auto simp add: mono_Ord_def)
  apply (blast intro: lt_Ord) 
  done

lemma mono_Ord_imp_mono: "\<lbrakk>i<j; mono_Ord(F)\<rbrakk> \<Longrightarrow> F(i) < F(j)"
  by (simp add: mono_Ord_def)

lemma Normal_imp_Ord [simp]: "\<lbrakk>Normal(F); Ord(i)\<rbrakk> \<Longrightarrow> Ord(F(i))"
  by (simp add: Normal_def mono_Ord_imp_Ord) 

lemma Normal_imp_cont: "\<lbrakk>Normal(F); Limit(l)\<rbrakk> \<Longrightarrow> F(l) = (\<Union>i<l. F(i))"
  by (simp add: Normal_def cont_Ord_def)

lemma Normal_imp_mono: "\<lbrakk>i<j; Normal(F)\<rbrakk> \<Longrightarrow> F(i) < F(j)"
  by (simp add: Normal_def mono_Ord_def)

lemma Normal_increasing:
  assumes i: "Ord(i)" and F: "Normal(F)" shows"i \<le> F(i)"
using i
proof (induct i rule: trans_induct3)
  case 0 thus ?case by (simp add: subset_imp_le F)
next
  case (succ i) 
  hence "F(i) < F(succ(i))" using F
    by (simp add: Normal_def mono_Ord_def)
  thus ?case using succ.hyps
    by (blast intro: lt_trans1)
next
  case (limit l) 
  hence "l = (\<Union>y<l. y)" 
    by (simp add: Limit_OUN_eq)
  also have "... \<le> (\<Union>y<l. F(y))" using limit
    by (blast intro: ltD le_implies_OUN_le_OUN)
  finally have "l \<le> (\<Union>y<l. F(y))" .
  moreover have "(\<Union>y<l. F(y)) \<le> F(l)" using limit F
    by (simp add: Normal_imp_cont lt_Ord)
  ultimately show ?case
    by (blast intro: le_trans) 
qed


subsubsection\<open>The class of fixedpoints is closed and unbounded\<close>

text\<open>The proof is from Drake, pages 113--114.\<close>

lemma mono_Ord_imp_le_subset: "mono_Ord(F) \<Longrightarrow> mono_le_subset(F)"
  apply (simp add: mono_le_subset_def, clarify)
  apply (subgoal_tac "F(i)\<le>F(j)", blast dest: le_imp_subset) 
  apply (simp add: le_iff) 
  apply (blast intro: lt_Ord2 mono_Ord_imp_Ord mono_Ord_imp_mono) 
  done

text\<open>The following equation is taken for granted in any set theory text.\<close>
lemma cont_Ord_Union:
  "\<lbrakk>cont_Ord(F); mono_le_subset(F); X=0 \<longrightarrow> F(0)=0; \<forall>x\<in>X. Ord(x)\<rbrakk> 
      \<Longrightarrow> F(\<Union>(X)) = (\<Union>y\<in>X. F(y))"
  apply (frule Ord_set_cases)
  apply (erule disjE, force) 
  apply (thin_tac "X=0 \<longrightarrow> Q" for Q, auto)
  txt\<open>The trival case of \<^term>\<open>\<Union>X \<in> X\<close>\<close>
   apply (rule equalityI, blast intro: Ord_Union_eq_succD) 
   apply (simp add: mono_le_subset_def UN_subset_iff le_subset_iff) 
   apply (blast elim: equalityE)
  txt\<open>The limit case, \<^term>\<open>Limit(\<Union>X)\<close>:
@{subgoals[display,indent=0,margin=65]}
\<close>
  apply (simp add: OUN_Union_eq cont_Ord_def)
  apply (rule equalityI) 
  txt\<open>First inclusion:\<close>
   apply (rule UN_least [OF OUN_least])
   apply (simp add: mono_le_subset_def, blast intro: leI) 
  txt\<open>Second inclusion:\<close>
  apply (rule UN_least) 
  apply (frule Union_upper_le, blast, blast)
  apply (erule leE, drule ltD, elim UnionE)
   apply (simp add: OUnion_def)
   apply blast+
  done

lemma Normal_Union:
  "\<lbrakk>X\<noteq>0; \<forall>x\<in>X. Ord(x); Normal(F)\<rbrakk> \<Longrightarrow> F(\<Union>(X)) = (\<Union>y\<in>X. F(y))"
  apply (simp add: Normal_def) 
  apply (blast intro: mono_Ord_imp_le_subset cont_Ord_Union) 
  done

lemma Normal_imp_fp_Closed: "Normal(F) \<Longrightarrow> Closed(\<lambda>i. F(i) = i)"
  apply (simp add: Closed_def ball_conj_distrib, clarify)
  apply (frule Ord_set_cases)
  apply (auto simp add: Normal_Union)
  done


lemma iterates_Normal_increasing:
  "\<lbrakk>n\<in>nat;  x < F(x);  Normal(F)\<rbrakk> 
      \<Longrightarrow> F^n (x) < F^(succ(n)) (x)"  
  apply (induct n rule: nat_induct)
   apply (simp_all add: Normal_imp_mono)
  done

lemma Ord_iterates_Normal:
     "\<lbrakk>n\<in>nat;  Normal(F);  Ord(x)\<rbrakk> \<Longrightarrow> Ord(F^n (x))"  
by (simp) 

text\<open>THIS RESULT IS UNUSED\<close>
lemma iterates_omega_Limit:
  "\<lbrakk>Normal(F);  x < F(x)\<rbrakk> \<Longrightarrow> Limit(F^\<omega> (x))"  
  apply (frule lt_Ord) 
  apply (simp add: iterates_omega_def)
  apply (rule increasing_LimitI) 
    \<comment> \<open>this lemma is @{thm increasing_LimitI [no_vars]}\<close>
   apply (blast intro: UN_upper_lt [of "1"]   Normal_imp_Ord
      Ord_iterates lt_imp_0_lt
      iterates_Normal_increasing, clarify)
  apply (rule bexI) 
   apply (blast intro: Ord_in_Ord [OF Ord_iterates_Normal]) 
  apply (rule UN_I, erule nat_succI) 
  apply (blast intro:  iterates_Normal_increasing Ord_iterates_Normal
      ltD [OF lt_trans1, OF succ_leI, OF ltI]) 
  done

lemma iterates_omega_fixedpoint:
     "\<lbrakk>Normal(F); Ord(a)\<rbrakk> \<Longrightarrow> F(F^\<omega> (a)) = F^\<omega> (a)" 
apply (frule Normal_increasing, assumption)
apply (erule leE) 
 apply (simp_all add: iterates_omega_triv [OF sym])  (*for subgoal 2*)
apply (simp add:  iterates_omega_def Normal_Union) 
apply (rule equalityI, force simp add: nat_succI) 
txt\<open>Opposite inclusion:
@{subgoals[display,indent=0,margin=65]}
\<close>
apply clarify
apply (rule UN_I, assumption) 
apply (frule iterates_Normal_increasing, assumption, assumption, simp)
apply (blast intro: Ord_trans ltD Ord_iterates_Normal Normal_imp_Ord [of F]) 
done

lemma iterates_omega_increasing:
     "\<lbrakk>Normal(F); Ord(a)\<rbrakk> \<Longrightarrow> a \<le> F^\<omega> (a)"   
  unfolding iterates_omega_def
apply (rule UN_upper_le [of 0], simp_all)
done

lemma Normal_imp_fp_Unbounded: "Normal(F) \<Longrightarrow> Unbounded(\<lambda>i. F(i) = i)"
apply (unfold Unbounded_def, clarify)
apply (rule_tac x="F^\<omega> (succ(i))" in exI)
apply (simp add: iterates_omega_fixedpoint) 
apply (blast intro: lt_trans2 [OF _ iterates_omega_increasing])
done


theorem Normal_imp_fp_Closed_Unbounded: 
     "Normal(F) \<Longrightarrow> Closed_Unbounded(\<lambda>i. F(i) = i)"
by (simp add: Closed_Unbounded_def Normal_imp_fp_Closed
              Normal_imp_fp_Unbounded)


subsubsection\<open>Function \<open>normalize\<close>\<close>

text\<open>Function \<open>normalize\<close> maps a function \<open>F\<close> to a 
      normal function that bounds it above.  The result is normal if and
      only if \<open>F\<close> is continuous: succ is not bounded above by any 
      normal function, by @{thm [source] Normal_imp_fp_Unbounded}.
\<close>
definition
  normalize :: "[i\<Rightarrow>i, i] \<Rightarrow> i" where
    "normalize(F,a) \<equiv> transrec2(a, F(0), \<lambda>x r. F(succ(x)) \<union> succ(r))"


lemma Ord_normalize [simp, intro]:
     "\<lbrakk>Ord(a); \<And>x. Ord(x) \<Longrightarrow> Ord(F(x))\<rbrakk> \<Longrightarrow> Ord(normalize(F, a))"
apply (induct a rule: trans_induct3)
apply (simp_all add: ltD def_transrec2 [OF normalize_def])
done

lemma normalize_increasing:
  assumes ab: "a < b" and F: "\<And>x. Ord(x) \<Longrightarrow> Ord(F(x))"
  shows "normalize(F,a) < normalize(F,b)"
proof -
  { fix x
    have "Ord(b)" using ab by (blast intro: lt_Ord2) 
    hence "x < b \<Longrightarrow> normalize(F,x) < normalize(F,b)"
    proof (induct b arbitrary: x rule: trans_induct3)
      case 0 thus ?case by simp
    next
      case (succ b)
      thus ?case
        by (auto simp add: le_iff def_transrec2 [OF normalize_def] intro: Un_upper2_lt F)
    next
      case (limit l)
      hence sc: "succ(x) < l" 
        by (blast intro: Limit_has_succ) 
      hence "normalize(F,x) < normalize(F,succ(x))" 
        by (blast intro: limit elim: ltE) 
      hence "normalize(F,x) < (\<Union>j<l. normalize(F,j))"
        by (blast intro: OUN_upper_lt lt_Ord F sc) 
      thus ?case using limit
        by (simp add: def_transrec2 [OF normalize_def])
    qed
  } thus ?thesis using ab .
qed

theorem Normal_normalize:
  "(\<And>x. Ord(x) \<Longrightarrow> Ord(F(x))) \<Longrightarrow> Normal(normalize(F))"
  apply (rule NormalI) 
   apply (blast intro!: normalize_increasing)
  apply (simp add: def_transrec2 [OF normalize_def])
  done

theorem le_normalize:
  assumes a: "Ord(a)" and coF: "cont_Ord(F)" and F: "\<And>x. Ord(x) \<Longrightarrow> Ord(F(x))"
  shows "F(a) \<le> normalize(F,a)"
using a
proof (induct a rule: trans_induct3)
  case 0 thus ?case by (simp add: F def_transrec2 [OF normalize_def])
next
  case (succ a)
  thus ?case
    by (simp add: def_transrec2 [OF normalize_def] Un_upper1_le F )
next
  case (limit l) 
  thus ?case using F coF [unfolded cont_Ord_def]
    by (simp add: def_transrec2 [OF normalize_def] le_implies_OUN_le_OUN ltD) 
qed


subsection \<open>The Alephs\<close>
text \<open>This is the well-known transfinite enumeration of the cardinal 
numbers.\<close>

definition
  Aleph :: "i \<Rightarrow> i"  (\<open>\<aleph>_\<close> [90] 90) where
    "Aleph(a) \<equiv> transrec2(a, nat, \<lambda>x r. csucc(r))"

lemma Card_Aleph [simp, intro]:
  "Ord(a) \<Longrightarrow> Card(Aleph(a))"
  apply (erule trans_induct3) 
    apply (simp_all add: Card_csucc Card_nat Card_is_Ord
      def_transrec2 [OF Aleph_def])
  done

lemma Aleph_increasing:
  assumes ab: "a < b" shows "Aleph(a) < Aleph(b)"
proof -
  { fix x
    have "Ord(b)" using ab by (blast intro: lt_Ord2) 
    hence "x < b \<Longrightarrow> Aleph(x) < Aleph(b)"
    proof (induct b arbitrary: x rule: trans_induct3)
      case 0 thus ?case by simp
    next
      case (succ b)
      thus ?case
        by (force simp add: le_iff def_transrec2 [OF Aleph_def] 
                  intro: lt_trans lt_csucc Card_is_Ord)
    next
      case (limit l)
      hence sc: "succ(x) < l" 
        by (blast intro: Limit_has_succ) 
      hence "\<aleph> x < (\<Union>j<l. \<aleph>j)" using limit
        by (blast intro: OUN_upper_lt Card_is_Ord ltD lt_Ord)
      thus ?case using limit
        by (simp add: def_transrec2 [OF Aleph_def])
    qed
  } thus ?thesis using ab .
qed

theorem Normal_Aleph: "Normal(Aleph)"
  apply (rule NormalI) 
   apply (blast intro!: Aleph_increasing)
  apply (simp add: def_transrec2 [OF Aleph_def])
  done

end
