(*  Title:      ZF/Induct/Brouwer.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section \<open>Infinite branching datatype definitions\<close>

theory Brouwer imports ZFC begin

subsection \<open>The Brouwer ordinals\<close>

consts
  brouwer :: i

datatype \<subseteq> "Vfrom(0, csucc(nat))"
    "brouwer" = Zero | Suc ("b \<in> brouwer") | Lim ("h \<in> nat -> brouwer")
  monos Pi_mono
  type_intros inf_datatype_intros

lemma brouwer_unfold: "brouwer = {0} + brouwer + (nat -> brouwer)"
  by (fast intro!: brouwer.intros [unfolded brouwer.con_defs]
    elim: brouwer.cases [unfolded brouwer.con_defs])

lemma brouwer_induct2 [consumes 1, case_names Zero Suc Lim]:
  assumes b: "b \<in> brouwer"
    and cases:
      "P(Zero)"
      "\<And>b. \<lbrakk>b \<in> brouwer;  P(b)\<rbrakk> \<Longrightarrow> P(Suc(b))"
      "\<And>h. \<lbrakk>h \<in> nat -> brouwer;  \<forall>i \<in> nat. P(h`i)\<rbrakk> \<Longrightarrow> P(Lim(h))"
  shows "P(b)"
  \<comment> \<open>A nicer induction rule than the standard one.\<close>
  using b
  apply induct
    apply (rule cases(1))
   apply (erule (1) cases(2))
  apply (rule cases(3))
   apply (fast elim: fun_weaken_type)
  apply (fast dest: apply_type)
  done


subsection \<open>The Martin-Löf wellordering type\<close>

consts
  Well :: "[i, i \<Rightarrow> i] \<Rightarrow> i"

datatype \<subseteq> "Vfrom(A \<union> (\<Union>x \<in> A. B(x)), csucc(nat \<union> |\<Union>x \<in> A. B(x)|))"
    \<comment> \<open>The union with \<open>nat\<close> ensures that the cardinal is infinite.\<close>
  "Well(A, B)" = Sup ("a \<in> A", "f \<in> B(a) -> Well(A, B)")
  monos Pi_mono
  type_intros le_trans [OF UN_upper_cardinal le_nat_Un_cardinal] inf_datatype_intros

lemma Well_unfold: "Well(A, B) = (\<Sum>x \<in> A. B(x) -> Well(A, B))"
  by (fast intro!: Well.intros [unfolded Well.con_defs]
    elim: Well.cases [unfolded Well.con_defs])


lemma Well_induct2 [consumes 1, case_names step]:
  assumes w: "w \<in> Well(A, B)"
    and step: "\<And>a f. \<lbrakk>a \<in> A;  f \<in> B(a) -> Well(A,B);  \<forall>y \<in> B(a). P(f`y)\<rbrakk> \<Longrightarrow> P(Sup(a,f))"
  shows "P(w)"
  \<comment> \<open>A nicer induction rule than the standard one.\<close>
  using w
  apply induct
  apply (assumption | rule step)+
   apply (fast elim: fun_weaken_type)
  apply (fast dest: apply_type)
  done

lemma Well_bool_unfold: "Well(bool, \<lambda>x. x) = 1 + (1 -> Well(bool, \<lambda>x. x))"
  \<comment> \<open>In fact it's isomorphic to \<open>nat\<close>, but we need a recursion operator\<close>
  \<comment> \<open>for \<open>Well\<close> to prove this.\<close>
  apply (rule Well_unfold [THEN trans])
  apply (simp add: Sigma_bool succ_def)
  done

end
