(*  Title:      ZF/Induct/Mutil.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

section \<open>The Mutilated Chess Board Problem, formalized inductively\<close>

theory Mutil imports ZF begin

text \<open>
  Originator is Max Black, according to J A Robinson.  Popularized as
  the Mutilated Checkerboard Problem by J McCarthy.
\<close>

consts
  domino :: i
  tiling :: "i \<Rightarrow> i"

inductive
  domains "domino" \<subseteq> "Pow(nat \<times> nat)"
  intros
    horiz: "\<lbrakk>i \<in> nat;  j \<in> nat\<rbrakk> \<Longrightarrow> {\<langle>i,j\<rangle>, <i,succ(j)>} \<in> domino"
    vertl: "\<lbrakk>i \<in> nat;  j \<in> nat\<rbrakk> \<Longrightarrow> {\<langle>i,j\<rangle>, <succ(i),j>} \<in> domino"
  type_intros empty_subsetI cons_subsetI PowI SigmaI nat_succI

inductive
  domains "tiling(A)" \<subseteq> "Pow(\<Union>(A))"
  intros
    empty: "0 \<in> tiling(A)"
    Un: "\<lbrakk>a \<in> A;  t \<in> tiling(A);  a \<inter> t = 0\<rbrakk> \<Longrightarrow> a \<union> t \<in> tiling(A)"
  type_intros empty_subsetI Union_upper Un_least PowI
  type_elims PowD [elim_format]

definition
  evnodd :: "[i, i] \<Rightarrow> i"  where
  "evnodd(A,b) \<equiv> {z \<in> A. \<exists>i j. z = \<langle>i,j\<rangle> \<and> (i #+ j) mod 2 = b}"


subsection \<open>Basic properties of evnodd\<close>

lemma evnodd_iff: "\<langle>i,j\<rangle>: evnodd(A,b) \<longleftrightarrow> \<langle>i,j\<rangle>: A \<and> (i#+j) mod 2 = b"
  by (unfold evnodd_def) blast

lemma evnodd_subset: "evnodd(A, b) \<subseteq> A"
  by (unfold evnodd_def) blast

lemma Finite_evnodd: "Finite(X) \<Longrightarrow> Finite(evnodd(X,b))"
  by (rule lepoll_Finite, rule subset_imp_lepoll, rule evnodd_subset)

lemma evnodd_Un: "evnodd(A \<union> B, b) = evnodd(A,b) \<union> evnodd(B,b)"
  by (simp add: evnodd_def Collect_Un)

lemma evnodd_Diff: "evnodd(A - B, b) = evnodd(A,b) - evnodd(B,b)"
  by (simp add: evnodd_def Collect_Diff)

lemma evnodd_cons [simp]:
  "evnodd(cons(\<langle>i,j\<rangle>,C), b) =
    (if (i#+j) mod 2 = b then cons(\<langle>i,j\<rangle>, evnodd(C,b)) else evnodd(C,b))"
  by (simp add: evnodd_def Collect_cons)

lemma evnodd_0 [simp]: "evnodd(0, b) = 0"
  by (simp add: evnodd_def)


subsection \<open>Dominoes\<close>

lemma domino_Finite: "d \<in> domino \<Longrightarrow> Finite(d)"
  by (blast intro!: Finite_cons Finite_0 elim: domino.cases)

lemma domino_singleton:
    "\<lbrakk>d \<in> domino; b<2\<rbrakk> \<Longrightarrow> \<exists>i' j'. evnodd(d,b) = {<i',j'>}"
  apply (erule domino.cases)
   apply (rule_tac [2] k1 = "i#+j" in mod2_cases [THEN disjE])
     apply (rule_tac k1 = "i#+j" in mod2_cases [THEN disjE])
       apply (rule add_type | assumption)+
      (*Four similar cases: case (i#+j) mod 2 = b, 2#-b, ...*)
      apply (auto simp add: mod_succ succ_neq_self dest: ltD)
  done


subsection \<open>Tilings\<close>

text \<open>The union of two disjoint tilings is a tiling\<close>

lemma tiling_UnI:
    "t \<in> tiling(A) \<Longrightarrow> u \<in> tiling(A) \<Longrightarrow> t \<inter> u = 0 \<Longrightarrow> t \<union> u \<in> tiling(A)"
  apply (induct set: tiling)
   apply (simp add: tiling.intros)
  apply (simp add: Un_assoc subset_empty_iff [THEN iff_sym])
  apply (blast intro: tiling.intros)
  done

lemma tiling_domino_Finite: "t \<in> tiling(domino) \<Longrightarrow> Finite(t)"
  apply (induct set: tiling)
   apply (rule Finite_0)
  apply (blast intro!: Finite_Un intro: domino_Finite)
  done

lemma tiling_domino_0_1: "t \<in> tiling(domino) \<Longrightarrow> |evnodd(t,0)| = |evnodd(t,1)|"
  apply (induct set: tiling)
   apply (simp add: evnodd_def)
  apply (rule_tac b1 = 0 in domino_singleton [THEN exE])
    prefer 2
    apply simp
   apply assumption
  apply (rule_tac b1 = 1 in domino_singleton [THEN exE])
    prefer 2
    apply simp
   apply assumption
  apply safe
  apply (subgoal_tac "\<forall>p b. p \<in> evnodd (a,b) \<longrightarrow> p\<notin>evnodd (t,b)")
   apply (simp add: evnodd_Un Un_cons tiling_domino_Finite
     evnodd_subset [THEN subset_Finite] Finite_imp_cardinal_cons)
  apply (blast dest!: evnodd_subset [THEN subsetD] elim: equalityE)
  done

lemma dominoes_tile_row:
    "\<lbrakk>i \<in> nat;  n \<in> nat\<rbrakk> \<Longrightarrow> {i} * (n #+ n) \<in> tiling(domino)"
  apply (induct_tac n)
   apply (simp add: tiling.intros)
  apply (simp add: Un_assoc [symmetric] Sigma_succ2)
  apply (rule tiling.intros)
    prefer 2 apply assumption
   apply (rename_tac n')
   apply (subgoal_tac (*seems the easiest way of turning one to the other*)
     "{i}*{succ (n'#+n') } \<union> {i}*{n'#+n'} =
       {<i,n'#+n'>, <i,succ (n'#+n') >}")
    prefer 2 apply blast
  apply (simp add: domino.horiz)
  apply (blast elim: mem_irrefl mem_asym)
  done

lemma dominoes_tile_matrix:
    "\<lbrakk>m \<in> nat;  n \<in> nat\<rbrakk> \<Longrightarrow> m * (n #+ n) \<in> tiling(domino)"
  apply (induct_tac m)
   apply (simp add: tiling.intros)
  apply (simp add: Sigma_succ1)
  apply (blast intro: tiling_UnI dominoes_tile_row elim: mem_irrefl)
  done

lemma eq_lt_E: "\<lbrakk>x=y; x<y\<rbrakk> \<Longrightarrow> P"
  by auto

theorem mutil_not_tiling: "\<lbrakk>m \<in> nat;  n \<in> nat;
         t = (succ(m)#+succ(m))*(succ(n)#+succ(n));
         t' = t - {\<langle>0,0\<rangle>} - {<succ(m#+m), succ(n#+n)>}\<rbrakk>
      \<Longrightarrow> t' \<notin> tiling(domino)"
  apply (rule notI)
  apply (drule tiling_domino_0_1)
  apply (erule_tac x = "|A|" for A in eq_lt_E)
  apply (subgoal_tac "t \<in> tiling (domino)")
   prefer 2 (*Requires a small simpset that won't move the succ applications*)
   apply (simp only: nat_succI add_type dominoes_tile_matrix)
  apply (simp add: evnodd_Diff mod2_add_self mod2_succ_succ
    tiling_domino_0_1 [symmetric])
  apply (rule lt_trans)
   apply (rule Finite_imp_cardinal_Diff,
     simp add: tiling_domino_Finite Finite_evnodd Finite_Diff,
     simp add: evnodd_iff nat_0_le [THEN ltD] mod2_add_self)+
  done

end
