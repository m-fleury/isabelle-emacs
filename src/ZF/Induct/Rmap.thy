(*  Title:      ZF/Induct/Rmap.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section \<open>An operator to ``map'' a relation over a list\<close>

theory Rmap imports ZF begin

consts
  rmap :: "i\<Rightarrow>i"

inductive
  domains "rmap(r)" \<subseteq> "list(domain(r)) \<times> list(range(r))"
  intros
    NilI:  "\<langle>Nil,Nil\<rangle> \<in> rmap(r)"

    ConsI: "\<lbrakk>\<langle>x,y\<rangle>: r;  \<langle>xs,ys\<rangle> \<in> rmap(r)\<rbrakk>
            \<Longrightarrow> <Cons(x,xs), Cons(y,ys)> \<in> rmap(r)"

  type_intros domainI rangeI list.intros

lemma rmap_mono: "r \<subseteq> s \<Longrightarrow> rmap(r) \<subseteq> rmap(s)"
    unfolding rmap.defs
  apply (rule lfp_mono)
    apply (rule rmap.bnd_mono)+
  apply (assumption | rule Sigma_mono list_mono domain_mono range_mono basic_monos)+
  done

inductive_cases
      Nil_rmap_case [elim!]: "\<langle>Nil,zs\<rangle> \<in> rmap(r)"
  and Cons_rmap_case [elim!]: "<Cons(x,xs),zs> \<in> rmap(r)"

declare rmap.intros [intro]

lemma rmap_rel_type: "r \<subseteq> A \<times> B \<Longrightarrow> rmap(r) \<subseteq> list(A) \<times> list(B)"
  apply (rule rmap.dom_subset [THEN subset_trans])
  apply (assumption |
    rule domain_rel_subset range_rel_subset Sigma_mono list_mono)+
  done

lemma rmap_total: "A \<subseteq> domain(r) \<Longrightarrow> list(A) \<subseteq> domain(rmap(r))"
  apply (rule subsetI)
  apply (erule list.induct)
   apply blast+
  done

lemma rmap_functional: "function(r) \<Longrightarrow> function(rmap(r))"
    unfolding function_def
  apply (rule impI [THEN allI, THEN allI])
  apply (erule rmap.induct)
   apply blast+
  done

text \<open>
  \medskip If \<open>f\<close> is a function then \<open>rmap(f)\<close> behaves
  as expected.
\<close>

lemma rmap_fun_type: "f \<in> A->B \<Longrightarrow> rmap(f): list(A)->list(B)"
  by (simp add: Pi_iff rmap_rel_type rmap_functional rmap_total)

lemma rmap_Nil: "rmap(f)`Nil = Nil"
  by (unfold apply_def) blast

lemma rmap_Cons: "\<lbrakk>f \<in> A->B;  x \<in> A;  xs: list(A)\<rbrakk>
      \<Longrightarrow> rmap(f) ` Cons(x,xs) = Cons(f`x, rmap(f)`xs)"
  by (blast intro: apply_equality apply_Pair rmap_fun_type rmap.intros)

end
