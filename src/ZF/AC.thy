(*  Title:      ZF/AC.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section\<open>The Axiom of Choice\<close>

theory AC imports ZF begin

text\<open>This definition comes from Halmos (1960), page 59.\<close>
axiomatization where
  AC: "\<lbrakk>a \<in> A;  \<And>x. x \<in> A \<Longrightarrow> (\<exists>y. y \<in> B(x))\<rbrakk> \<Longrightarrow> \<exists>z. z \<in> Pi(A,B)"

(*The same as AC, but no premise @{term"a \<in> A"}*)
lemma AC_Pi: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> (\<exists>y. y \<in> B(x))\<rbrakk> \<Longrightarrow> \<exists>z. z \<in> Pi(A,B)"
apply (case_tac "A=0")
apply (simp add: Pi_empty1)
(*The non-trivial case*)
apply (blast intro: AC)
done

(*Using dtac, this has the advantage of DELETING the universal quantifier*)
lemma AC_ball_Pi: "\<forall>x \<in> A. \<exists>y. y \<in> B(x) \<Longrightarrow> \<exists>y. y \<in> Pi(A,B)"
apply (rule AC_Pi)
apply (erule bspec, assumption)
done

lemma AC_Pi_Pow: "\<exists>f. f \<in> (\<Prod>X \<in> Pow(C)-{0}. X)"
apply (rule_tac B1 = "\<lambda>x. x" in AC_Pi [THEN exE])
apply (erule_tac [2] exI, blast)
done

lemma AC_func:
     "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> (\<exists>y. y \<in> x)\<rbrakk> \<Longrightarrow> \<exists>f \<in> A->\<Union>(A). \<forall>x \<in> A. f`x \<in> x"
apply (rule_tac B1 = "\<lambda>x. x" in AC_Pi [THEN exE])
prefer 2 apply (blast dest: apply_type intro: Pi_type, blast)
done

lemma non_empty_family: "\<lbrakk>0 \<notin> A;  x \<in> A\<rbrakk> \<Longrightarrow> \<exists>y. y \<in> x"
by (subgoal_tac "x \<noteq> 0", blast+)

lemma AC_func0: "0 \<notin> A \<Longrightarrow> \<exists>f \<in> A->\<Union>(A). \<forall>x \<in> A. f`x \<in> x"
apply (rule AC_func)
apply (simp_all add: non_empty_family)
done

lemma AC_func_Pow: "\<exists>f \<in> (Pow(C)-{0}) -> C. \<forall>x \<in> Pow(C)-{0}. f`x \<in> x"
apply (rule AC_func0 [THEN bexE])
apply (rule_tac [2] bexI)
prefer 2 apply assumption
apply (erule_tac [2] fun_weaken_type, blast+)
done

lemma AC_Pi0: "0 \<notin> A \<Longrightarrow> \<exists>f. f \<in> (\<Prod>x \<in> A. x)"
apply (rule AC_Pi)
apply (simp_all add: non_empty_family)
done

end
