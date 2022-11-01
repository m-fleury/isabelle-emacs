(*  Title:      ZF/UNITY/Merge.thy
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

A multiple-client allocator from a single-client allocator: Merge
specification.
*)

theory Merge imports AllocBase Follows  Guar GenPrefix begin

(** Merge specification (the number of inputs is Nclients) ***)
(** Parameter A represents the type of items to Merge **)

definition
  (*spec (10)*)
  merge_increasing :: "[i, i, i] \<Rightarrow>i"  where
    "merge_increasing(A, Out, iOut) \<equiv> program guarantees
         (lift(Out) IncreasingWrt  prefix(A)/list(A)) Int
         (lift(iOut) IncreasingWrt prefix(nat)/list(nat))"

definition
  (*spec (11)*)
  merge_eq_Out :: "[i, i] \<Rightarrow>i"  where
  "merge_eq_Out(Out, iOut) \<equiv> program guarantees
         Always({s \<in> state. length(s`Out) = length(s`iOut)})"

definition
  (*spec (12)*)
  merge_bounded :: "i\<Rightarrow>i"  where
  "merge_bounded(iOut) \<equiv> program guarantees
         Always({s \<in> state. \<forall>elt \<in> set_of_list(s`iOut). elt<Nclients})"
  
definition
  (*spec (13)*)
  (* Parameter A represents the type of tokens *)
  merge_follows :: "[i, i\<Rightarrow>i, i, i] \<Rightarrow>i"  where
    "merge_follows(A, In, Out, iOut) \<equiv>
     (\<Inter>n \<in> Nclients. lift(In(n)) IncreasingWrt prefix(A)/list(A))
                   guarantees
     (\<Inter>n \<in> Nclients. 
        (\<lambda>s. sublist(s`Out, {k \<in> nat. k < length(s`iOut) \<and>
                      nth(k, s`iOut) = n})) Fols lift(In(n))
         Wrt prefix(A)/list(A))"

definition
  (*spec: preserves part*)
  merge_preserves :: "[i\<Rightarrow>i] \<Rightarrow>i"  where
    "merge_preserves(In) \<equiv> \<Inter>n \<in> nat. preserves(lift(In(n)))"

definition
(* environmental constraints*)
  merge_allowed_acts :: "[i, i] \<Rightarrow>i"  where
  "merge_allowed_acts(Out, iOut) \<equiv>
         {F \<in> program. AllowedActs(F) =
            cons(id(state), (\<Union>G \<in> preserves(lift(Out)) \<inter>
                                   preserves(lift(iOut)). Acts(G)))}"
  
definition
  merge_spec :: "[i, i \<Rightarrow>i, i, i]\<Rightarrow>i"  where
  "merge_spec(A, In, Out, iOut) \<equiv>
   merge_increasing(A, Out, iOut) \<inter> merge_eq_Out(Out, iOut) \<inter>
   merge_bounded(iOut) \<inter>  merge_follows(A, In, Out, iOut)
   \<inter> merge_allowed_acts(Out, iOut) \<inter> merge_preserves(In)"

(** State definitions.  OUTPUT variables are locals **)
locale merge =
  fixes In   \<comment> \<open>merge's INPUT histories: streams to merge\<close>
    and Out  \<comment> \<open>merge's OUTPUT history: merged items\<close>
    and iOut \<comment> \<open>merge's OUTPUT history: origins of merged items\<close>
    and A    \<comment> \<open>the type of items being merged\<close>
    and M
 assumes var_assumes [simp]:
           "(\<forall>n. In(n):var) \<and> Out \<in> var \<and> iOut \<in> var"
     and all_distinct_vars:
           "\<forall>n. all_distinct([In(n), Out, iOut])"
     and type_assumes [simp]:
           "(\<forall>n. type_of(In(n))=list(A)) \<and>
            type_of(Out)=list(A) \<and>
            type_of(iOut)=list(nat)"
     and default_val_assumes [simp]: 
           "(\<forall>n. default_val(In(n))=Nil) \<and>
            default_val(Out)=Nil \<and>
            default_val(iOut)=Nil"
     and merge_spec:  "M \<in> merge_spec(A, In, Out, iOut)"


lemma (in merge) In_value_type [TC,simp]: "s \<in> state \<Longrightarrow> s`In(n) \<in> list(A)"
  unfolding state_def
apply (drule_tac a = "In (n)" in apply_type)
apply auto
done

lemma (in merge) Out_value_type [TC,simp]: "s \<in> state \<Longrightarrow> s`Out \<in> list(A)"
  unfolding state_def
apply (drule_tac a = Out in apply_type, auto)
done

lemma (in merge) iOut_value_type [TC,simp]: "s \<in> state \<Longrightarrow> s`iOut \<in> list(nat)"
  unfolding state_def
apply (drule_tac a = iOut in apply_type, auto)
done

lemma (in merge) M_in_program [intro,simp]: "M \<in> program"
apply (cut_tac merge_spec)
apply (auto dest: guarantees_type [THEN subsetD]
            simp add: merge_spec_def merge_increasing_def)
done

lemma (in merge) merge_Allowed: 
     "Allowed(M) = (preserves(lift(Out)) \<inter> preserves(lift(iOut)))"
apply (insert merge_spec preserves_type [of "lift (Out)"])
apply (auto simp add: merge_spec_def merge_allowed_acts_def Allowed_def safety_prop_Acts_iff)
done

lemma (in merge) M_ok_iff: 
     "G \<in> program \<Longrightarrow>  
       M ok G \<longleftrightarrow> (G \<in> preserves(lift(Out)) \<and>   
                   G \<in> preserves(lift(iOut)) \<and> M \<in> Allowed(G))"
apply (cut_tac merge_spec)
apply (auto simp add: merge_Allowed ok_iff_Allowed)
done

lemma (in merge) merge_Always_Out_eq_iOut: 
     "\<lbrakk>G \<in> preserves(lift(Out)); G \<in> preserves(lift(iOut));  
         M \<in> Allowed(G)\<rbrakk>
      \<Longrightarrow> M \<squnion> G \<in> Always({s \<in> state. length(s`Out)=length(s`iOut)})"
apply (frule preserves_type [THEN subsetD])
apply (subgoal_tac "G \<in> program")
 prefer 2 apply assumption
apply (frule M_ok_iff)
apply (cut_tac merge_spec)
apply (force dest: guaranteesD simp add: merge_spec_def merge_eq_Out_def)
done

lemma (in merge) merge_Bounded: 
     "\<lbrakk>G \<in> preserves(lift(iOut)); G \<in> preserves(lift(Out));  
         M \<in> Allowed(G)\<rbrakk> \<Longrightarrow>  
       M \<squnion> G: Always({s \<in> state. \<forall>elt \<in> set_of_list(s`iOut). elt<Nclients})"
apply (frule preserves_type [THEN subsetD])
apply (frule M_ok_iff)
apply (cut_tac merge_spec)
apply (force dest: guaranteesD simp add: merge_spec_def merge_bounded_def)
done

lemma (in merge) merge_bag_Follows_lemma: 
"\<lbrakk>G \<in> preserves(lift(iOut));  
    G: preserves(lift(Out)); M \<in> Allowed(G)\<rbrakk>  
  \<Longrightarrow> M \<squnion> G \<in> Always  
    ({s \<in> state. msetsum(\<lambda>i. bag_of(sublist(s`Out,  
      {k \<in> nat. k < length(s`iOut) \<and> nth(k, s`iOut)=i})),  
                   Nclients, A) = bag_of(s`Out)})"
apply (rule Always_Diff_Un_eq [THEN iffD1]) 
apply (rule_tac [2] state_AlwaysI [THEN Always_weaken]) 
apply (rule Always_Int_I [OF merge_Always_Out_eq_iOut merge_Bounded], auto)
apply (subst bag_of_sublist_UN_disjoint [symmetric])
apply (auto simp add: nat_into_Finite set_of_list_conv_nth  [OF iOut_value_type])
apply (subgoal_tac " (\<Union>i \<in> Nclients. {k \<in> nat. k < length (x`iOut) \<and> nth (k, x`iOut) = i}) = length (x`iOut) ")
apply (auto simp add: sublist_upt_eq_take [OF Out_value_type] 
                      length_type  [OF iOut_value_type]  
                      take_all [OF _ Out_value_type] 
                      length_type [OF iOut_value_type])
apply (rule equalityI)
apply (blast dest: ltD, clarify)
apply (subgoal_tac "length (x ` iOut) \<in> nat")
 prefer 2 apply (simp add: length_type [OF iOut_value_type]) 
apply (subgoal_tac "xa \<in> nat")
apply (simp_all add: Ord_mem_iff_lt)
prefer 2 apply (blast intro: lt_trans)
apply (drule_tac x = "nth (xa, x`iOut)" and P = "\<lambda>elt. X (elt) \<longrightarrow> elt<Nclients" for X in bspec)
apply (simp add: ltI nat_into_Ord)
apply (blast dest: ltD)
done

theorem (in merge) merge_bag_Follows: 
    "M \<in> (\<Inter>n \<in> Nclients. lift(In(n)) IncreasingWrt prefix(A)/list(A))  
            guarantees   
      (\<lambda>s. bag_of(s`Out)) Fols  
      (\<lambda>s. msetsum(\<lambda>i. bag_of(s`In(i)),Nclients, A)) Wrt MultLe(A, r)/Mult(A)"
apply (cut_tac merge_spec)
apply (rule merge_bag_Follows_lemma [THEN Always_Follows1, THEN guaranteesI])
     apply (simp_all add: M_ok_iff, clarify)
apply (rule Follows_state_ofD1 [OF Follows_msetsum_UN])
   apply (simp_all add: nat_into_Finite bag_of_multiset [of _ A])
apply (simp add: INT_iff merge_spec_def merge_follows_def, clarify)
apply (cut_tac merge_spec)
apply (subgoal_tac "M ok G")
 prefer 2 apply (force intro: M_ok_iff [THEN iffD2])
apply (drule guaranteesD, assumption)
  apply (simp add: merge_spec_def merge_follows_def, blast)
apply (simp cong add: Follows_cong
            add: refl_prefix
               mono_bag_of [THEN subset_Follows_comp, THEN subsetD, 
                            unfolded metacomp_def])
done

end
