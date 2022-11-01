(*  Title:      ZF/ex/CoUnit.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section \<open>Trivial codatatype definitions, one of which goes wrong!\<close>

theory CoUnit imports ZF begin

text \<open>
  See discussion in: L C Paulson.  A Concrete Final Coalgebra Theorem
  for ZF Set Theory.  Report 334, Cambridge University Computer
  Laboratory.  1994.

  \bigskip

  This degenerate definition does not work well because the one
  constructor's definition is trivial!  The same thing occurs with
  Aczel's Special Final Coalgebra Theorem.
\<close>

consts
  counit :: i
codatatype
  "counit" = Con ("x \<in> counit")

inductive_cases ConE: "Con(x) \<in> counit"
  \<comment> \<open>USELESS because folding on \<^term>\<open>Con(xa) \<equiv> xa\<close> fails.\<close>

lemma Con_iff: "Con(x) = Con(y) \<longleftrightarrow> x = y"
  \<comment> \<open>Proving freeness results.\<close>
  by (auto elim!: counit.free_elims)

lemma counit_eq_univ: "counit = quniv(0)"
  \<comment> \<open>Should be a singleton, not everything!\<close>
  apply (rule counit.dom_subset [THEN equalityI])
  apply (rule subsetI)
  apply (erule counit.coinduct)
   apply (rule subset_refl)
    unfolding counit.con_defs
  apply fast
  done


text \<open>
  \medskip A similar example, but the constructor is non-degenerate
  and it works!  The resulting set is a singleton.
\<close>

consts
  counit2 :: i
codatatype
  "counit2" = Con2 ("x \<in> counit2", "y \<in> counit2")


inductive_cases Con2E: "Con2(x, y) \<in> counit2"

lemma Con2_iff: "Con2(x, y) = Con2(x', y') \<longleftrightarrow> x = x' \<and> y = y'"
  \<comment> \<open>Proving freeness results.\<close>
  by (fast elim!: counit2.free_elims)

lemma Con2_bnd_mono: "bnd_mono(univ(0), \<lambda>x. Con2(x, x))"
    unfolding counit2.con_defs
  apply (rule bnd_monoI)
   apply (assumption | rule subset_refl QPair_subset_univ QPair_mono)+
  done

lemma lfp_Con2_in_counit2: "lfp(univ(0), \<lambda>x. Con2(x,x)) \<in> counit2"
  apply (rule singletonI [THEN counit2.coinduct])
  apply (rule qunivI [THEN singleton_subsetI])
  apply (rule subset_trans [OF lfp_subset empty_subsetI [THEN univ_mono]])
  apply (fast intro!: Con2_bnd_mono [THEN lfp_unfold])
  done

lemma counit2_Int_Vset_subset [rule_format]:
  "Ord(i) \<Longrightarrow> \<forall>x y. x \<in> counit2 \<longrightarrow> y \<in> counit2 \<longrightarrow> x \<inter> Vset(i) \<subseteq> y"
  \<comment> \<open>Lemma for proving finality.\<close>
  apply (erule trans_induct)
  apply (tactic "safe_tac (put_claset subset_cs \<^context>)")
  apply (erule counit2.cases)
  apply (erule counit2.cases)
    unfolding counit2.con_defs
  apply (tactic \<open>fast_tac (put_claset subset_cs \<^context>
    addSIs [@{thm QPair_Int_Vset_subset_UN} RS @{thm subset_trans}, @{thm QPair_mono}]
    addSEs [@{thm Ord_in_Ord}, @{thm Pair_inject}]) 1\<close>)
  done

lemma counit2_implies_equal: "\<lbrakk>x \<in> counit2;  y \<in> counit2\<rbrakk> \<Longrightarrow> x = y"
  apply (rule equalityI)
  apply (assumption | rule conjI counit2_Int_Vset_subset [THEN Int_Vset_subset])+
  done

lemma counit2_eq_univ: "counit2 = {lfp(univ(0), \<lambda>x. Con2(x,x))}"
  apply (rule equalityI)
   apply (rule_tac [2] lfp_Con2_in_counit2 [THEN singleton_subsetI])
  apply (rule subsetI)
  apply (drule lfp_Con2_in_counit2 [THEN counit2_implies_equal])
  apply (erule subst)
  apply (rule singletonI)
  done

end
