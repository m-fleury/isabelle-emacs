(*  Title:      ZF/Induct/Datatypes.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section \<open>Sample datatype definitions\<close>

theory Datatypes imports ZF begin

subsection \<open>A type with four constructors\<close>

text \<open>
  It has four contructors, of arities 0--3, and two parameters \<open>A\<close> and \<open>B\<close>.
\<close>

consts
  data :: "[i, i] \<Rightarrow> i"

datatype "data(A, B)" =
    Con0
  | Con1 ("a \<in> A")
  | Con2 ("a \<in> A", "b \<in> B")
  | Con3 ("a \<in> A", "b \<in> B", "d \<in> data(A, B)")

lemma data_unfold: "data(A, B) = ({0} + A) + (A \<times> B + A \<times> B \<times> data(A, B))"
  by (fast intro!: data.intros [unfolded data.con_defs]
    elim: data.cases [unfolded data.con_defs])

text \<open>
  \medskip Lemmas to justify using \<^term>\<open>data\<close> in other recursive
  type definitions.
\<close>

lemma data_mono: "\<lbrakk>A \<subseteq> C; B \<subseteq> D\<rbrakk> \<Longrightarrow> data(A, B) \<subseteq> data(C, D)"
    unfolding data.defs
  apply (rule lfp_mono)
   apply (rule data.bnd_mono)+
  apply (rule univ_mono Un_mono basic_monos | assumption)+
  done

lemma data_univ: "data(univ(A), univ(A)) \<subseteq> univ(A)"
    unfolding data.defs data.con_defs
  apply (rule lfp_lowerbound)
   apply (rule_tac [2] subset_trans [OF A_subset_univ Un_upper1, THEN univ_mono])
  apply (fast intro!: zero_in_univ Inl_in_univ Inr_in_univ Pair_in_univ)
  done

lemma data_subset_univ:
    "\<lbrakk>A \<subseteq> univ(C); B \<subseteq> univ(C)\<rbrakk> \<Longrightarrow> data(A, B) \<subseteq> univ(C)"
  by (rule subset_trans [OF data_mono data_univ])


subsection \<open>Example of a big enumeration type\<close>

text \<open>
  Can go up to at least 100 constructors, but it takes nearly 7
  minutes \dots\ (back in 1994 that is).
\<close>

consts
  enum :: i

datatype enum =
    C00 | C01 | C02 | C03 | C04 | C05 | C06 | C07 | C08 | C09
  | C10 | C11 | C12 | C13 | C14 | C15 | C16 | C17 | C18 | C19
  | C20 | C21 | C22 | C23 | C24 | C25 | C26 | C27 | C28 | C29
  | C30 | C31 | C32 | C33 | C34 | C35 | C36 | C37 | C38 | C39
  | C40 | C41 | C42 | C43 | C44 | C45 | C46 | C47 | C48 | C49
  | C50 | C51 | C52 | C53 | C54 | C55 | C56 | C57 | C58 | C59

end
