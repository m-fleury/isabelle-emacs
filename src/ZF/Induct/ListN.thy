(*  Title:      ZF/Induct/ListN.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section \<open>Lists of n elements\<close>

theory ListN imports ZF begin

text \<open>
  Inductive definition of lists of \<open>n\<close> elements; see
  @{cite "paulin-tlca"}.
\<close>

consts listn :: "i\<Rightarrow>i"
inductive
  domains "listn(A)" \<subseteq> "nat \<times> list(A)"
  intros
    NilI: "\<langle>0,Nil\<rangle> \<in> listn(A)"
    ConsI: "\<lbrakk>a \<in> A; \<langle>n,l\<rangle> \<in> listn(A)\<rbrakk> \<Longrightarrow> <succ(n), Cons(a,l)> \<in> listn(A)"
  type_intros nat_typechecks list.intros


lemma list_into_listn: "l \<in> list(A) \<Longrightarrow> <length(l),l> \<in> listn(A)"
  by (induct set: list) (simp_all add: listn.intros)

lemma listn_iff: "\<langle>n,l\<rangle> \<in> listn(A) \<longleftrightarrow> l \<in> list(A) \<and> length(l)=n"
  apply (rule iffI)
   apply (erule listn.induct)
    apply auto
  apply (blast intro: list_into_listn)
  done

lemma listn_image_eq: "listn(A)``{n} = {l \<in> list(A). length(l)=n}"
  apply (rule equality_iffI)
  apply (simp add: listn_iff separation image_singleton_iff)
  done

lemma listn_mono: "A \<subseteq> B \<Longrightarrow> listn(A) \<subseteq> listn(B)"
    unfolding listn.defs
  apply (rule lfp_mono)
    apply (rule listn.bnd_mono)+
  apply (assumption | rule univ_mono Sigma_mono list_mono basic_monos)+
  done

lemma listn_append:
    "\<lbrakk>\<langle>n,l\<rangle> \<in> listn(A); <n',l'> \<in> listn(A)\<rbrakk> \<Longrightarrow> <n#+n', l@l'> \<in> listn(A)"
  apply (erule listn.induct)
   apply (frule listn.dom_subset [THEN subsetD])
   apply (simp_all add: listn.intros)
  done

inductive_cases
      Nil_listn_case: "\<langle>i,Nil\<rangle> \<in> listn(A)"
  and Cons_listn_case: "<i,Cons(x,l)> \<in> listn(A)"

inductive_cases
      zero_listn_case: "\<langle>0,l\<rangle> \<in> listn(A)"
  and succ_listn_case: "<succ(i),l> \<in> listn(A)"

end
