(*  Title:      ZF/UNITY/Distributor.thy
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

A multiple-client allocator from a single-client allocator:
Distributor specification.
*)

theory Distributor imports AllocBase Follows  Guar GenPrefix begin

text\<open>Distributor specification (the number of outputs is Nclients)\<close>

text\<open>spec (14)\<close>

definition
  distr_follows :: "[i, i, i, i \<Rightarrow>i] \<Rightarrow>i"  where
    "distr_follows(A, In, iIn, Out) \<equiv>
     (lift(In) IncreasingWrt prefix(A)/list(A)) \<inter>
     (lift(iIn) IncreasingWrt prefix(nat)/list(nat)) \<inter>
     Always({s \<in> state. \<forall>elt \<in> set_of_list(s`iIn). elt < Nclients})
         guarantees
         (\<Inter>n \<in> Nclients.
          lift(Out(n))
              Fols
          (\<lambda>s. sublist(s`In, {k \<in> nat. k<length(s`iIn) \<and> nth(k, s`iIn) = n}))
          Wrt prefix(A)/list(A))"

definition
  distr_allowed_acts :: "[i\<Rightarrow>i]\<Rightarrow>i"  where
    "distr_allowed_acts(Out) \<equiv>
     {D \<in> program. AllowedActs(D) =
     cons(id(state), \<Union>G \<in> (\<Inter>n\<in>nat. preserves(lift(Out(n)))). Acts(G))}"

definition
  distr_spec :: "[i, i, i, i \<Rightarrow>i]\<Rightarrow>i"  where
    "distr_spec(A, In, iIn, Out) \<equiv>
     distr_follows(A, In, iIn, Out) \<inter> distr_allowed_acts(Out)"

locale distr =
  fixes In  \<comment> \<open>items to distribute\<close>
    and iIn \<comment> \<open>destinations of items to distribute\<close>
    and Out \<comment> \<open>distributed items\<close>
    and A   \<comment> \<open>the type of items being distributed\<close>
    and D
 assumes
     var_assumes [simp]:  "In \<in> var \<and> iIn \<in> var \<and> (\<forall>n. Out(n):var)"
 and all_distinct_vars:   "\<forall>n. all_distinct([In, iIn, Out(n)])"
 and type_assumes [simp]: "type_of(In)=list(A) \<and>  type_of(iIn)=list(nat) \<and>
                          (\<forall>n. type_of(Out(n))=list(A))"
 and default_val_assumes [simp]:
                         "default_val(In)=Nil \<and>
                          default_val(iIn)=Nil \<and>
                          (\<forall>n. default_val(Out(n))=Nil)"
 and distr_spec:  "D \<in> distr_spec(A, In, iIn, Out)"


lemma (in distr) In_value_type [simp,TC]: "s \<in> state \<Longrightarrow> s`In \<in> list(A)"
  unfolding state_def
apply (drule_tac a = In in apply_type, auto)
done

lemma (in distr) iIn_value_type [simp,TC]:
     "s \<in> state \<Longrightarrow> s`iIn \<in> list(nat)"
  unfolding state_def
apply (drule_tac a = iIn in apply_type, auto)
done

lemma (in distr) Out_value_type [simp,TC]:
     "s \<in> state \<Longrightarrow> s`Out(n):list(A)"
  unfolding state_def
apply (drule_tac a = "Out (n)" in apply_type)
apply auto
done

lemma (in distr) D_in_program [simp,TC]: "D \<in> program"
apply (cut_tac distr_spec)
apply (auto simp add: distr_spec_def distr_allowed_acts_def)
done

lemma (in distr) D_ok_iff:
     "G \<in> program \<Longrightarrow>
        D ok G \<longleftrightarrow> ((\<forall>n \<in> nat. G \<in> preserves(lift(Out(n)))) \<and> D \<in> Allowed(G))"
apply (cut_tac distr_spec)
apply (auto simp add: INT_iff distr_spec_def distr_allowed_acts_def
                      Allowed_def ok_iff_Allowed)
apply (drule safety_prop_Acts_iff [THEN [2] rev_iffD1])
apply (auto intro: safety_prop_Inter)
done

lemma (in distr) distr_Increasing_Out:
"D \<in> ((lift(In) IncreasingWrt prefix(A)/list(A)) \<inter>
      (lift(iIn) IncreasingWrt prefix(nat)/list(nat)) \<inter>
      Always({s \<in> state. \<forall>elt \<in> set_of_list(s`iIn). elt<Nclients}))
      guarantees
          (\<Inter>n \<in> Nclients. lift(Out(n)) IncreasingWrt
                            prefix(A)/list(A))"
apply (cut_tac D_in_program distr_spec)
apply (simp (no_asm_use) add: distr_spec_def distr_follows_def)
apply (auto intro!: guaranteesI intro: Follows_imp_Increasing_left 
            dest!: guaranteesD)
done

lemma (in distr) distr_bag_Follows_lemma:
"\<lbrakk>\<forall>n \<in> nat. G \<in> preserves(lift(Out(n)));
   D \<squnion> G \<in> Always({s \<in> state.
          \<forall>elt \<in> set_of_list(s`iIn). elt < Nclients})\<rbrakk>
  \<Longrightarrow> D \<squnion> G \<in> Always
          ({s \<in> state. msetsum(\<lambda>n. bag_of (sublist(s`In,
                       {k \<in> nat. k < length(s`iIn) \<and>
                          nth(k, s`iIn)= n})),
                         Nclients, A) =
              bag_of(sublist(s`In, length(s`iIn)))})"
apply (cut_tac D_in_program)
apply (subgoal_tac "G \<in> program")
 prefer 2 apply (blast dest: preserves_type [THEN subsetD])
apply (erule Always_Diff_Un_eq [THEN iffD1])
apply (rule state_AlwaysI [THEN Always_weaken], auto)
apply (rename_tac s)
apply (subst bag_of_sublist_UN_disjoint [symmetric])
   apply (simp (no_asm_simp) add: nat_into_Finite)
  apply blast
 apply (simp (no_asm_simp))
apply (simp add: set_of_list_conv_nth [of _ nat])
apply (subgoal_tac
       "(\<Union>i \<in> Nclients. {k\<in>nat. k < length(s`iIn) \<and> nth(k, s`iIn) = i}) =
        length(s`iIn) ")
apply (simp (no_asm_simp))
apply (rule equalityI)
apply (force simp add: ltD, safe)
apply (rename_tac m)
apply (subgoal_tac "length (s ` iIn) \<in> nat")
apply typecheck
apply (subgoal_tac "m \<in> nat")
apply (drule_tac x = "nth(m, s`iIn) " and P = "\<lambda>elt. X (elt) \<longrightarrow> elt<Nclients" for X in bspec)
apply (simp add: ltI)
apply (simp_all add: Ord_mem_iff_lt)
apply (blast dest: ltD)
apply (blast intro: lt_trans)
done

theorem (in distr) distr_bag_Follows:
 "D \<in> ((lift(In) IncreasingWrt prefix(A)/list(A)) \<inter>
       (lift(iIn) IncreasingWrt prefix(nat)/list(nat)) \<inter>
        Always({s \<in> state. \<forall>elt \<in> set_of_list(s`iIn). elt < Nclients}))
      guarantees
       (\<Inter>n \<in> Nclients.
        (\<lambda>s. msetsum(\<lambda>i. bag_of(s`Out(i)),  Nclients, A))
        Fols
        (\<lambda>s. bag_of(sublist(s`In, length(s`iIn))))
        Wrt MultLe(A, r)/Mult(A))"
apply (cut_tac distr_spec)
apply (rule guaranteesI, clarify)
apply (rule distr_bag_Follows_lemma [THEN Always_Follows2])
apply (simp add: D_ok_iff, auto)
apply (rule Follows_state_ofD1)
apply (rule Follows_msetsum_UN)
   apply (simp_all add: nat_into_Finite bag_of_multiset [of _ A])
apply (auto simp add: distr_spec_def distr_follows_def)
apply (drule guaranteesD, assumption)
apply (simp_all cong add: Follows_cong
                add: refl_prefix
                   mono_bag_of [THEN subset_Follows_comp, THEN subsetD, 
                                unfolded metacomp_def])
done

end
