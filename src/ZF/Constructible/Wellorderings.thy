(*  Title:      ZF/Constructible/Wellorderings.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>Relativized Wellorderings\<close>

theory Wellorderings imports Relative begin

text\<open>We define functions analogous to \<^term>\<open>ordermap\<close> \<^term>\<open>ordertype\<close> 
      but without using recursion.  Instead, there is a direct appeal
      to Replacement.  This will be the basis for a version relativized
      to some class \<open>M\<close>.  The main result is Theorem I 7.6 in Kunen,
      page 17.\<close>


subsection\<open>Wellorderings\<close>

definition
  irreflexive :: "[i\<Rightarrow>o,i,i]\<Rightarrow>o" where
    "irreflexive(M,A,r) \<equiv> \<forall>x[M]. x\<in>A \<longrightarrow> \<langle>x,x\<rangle> \<notin> r"
  
definition
  transitive_rel :: "[i\<Rightarrow>o,i,i]\<Rightarrow>o" where
    "transitive_rel(M,A,r) \<equiv> 
        \<forall>x[M]. x\<in>A \<longrightarrow> (\<forall>y[M]. y\<in>A \<longrightarrow> (\<forall>z[M]. z\<in>A \<longrightarrow> 
                          \<langle>x,y\<rangle>\<in>r \<longrightarrow> \<langle>y,z\<rangle>\<in>r \<longrightarrow> \<langle>x,z\<rangle>\<in>r))"

definition
  linear_rel :: "[i\<Rightarrow>o,i,i]\<Rightarrow>o" where
    "linear_rel(M,A,r) \<equiv> 
        \<forall>x[M]. x\<in>A \<longrightarrow> (\<forall>y[M]. y\<in>A \<longrightarrow> \<langle>x,y\<rangle>\<in>r | x=y | \<langle>y,x\<rangle>\<in>r)"

definition
  wellfounded :: "[i\<Rightarrow>o,i]\<Rightarrow>o" where
    \<comment> \<open>EVERY non-empty set has an \<open>r\<close>-minimal element\<close>
    "wellfounded(M,r) \<equiv> 
        \<forall>x[M]. x\<noteq>0 \<longrightarrow> (\<exists>y[M]. y\<in>x \<and> \<not>(\<exists>z[M]. z\<in>x \<and> \<langle>z,y\<rangle> \<in> r))"
definition
  wellfounded_on :: "[i\<Rightarrow>o,i,i]\<Rightarrow>o" where
    \<comment> \<open>every non-empty SUBSET OF \<open>A\<close> has an \<open>r\<close>-minimal element\<close>
    "wellfounded_on(M,A,r) \<equiv> 
        \<forall>x[M]. x\<noteq>0 \<longrightarrow> x\<subseteq>A \<longrightarrow> (\<exists>y[M]. y\<in>x \<and> \<not>(\<exists>z[M]. z\<in>x \<and> \<langle>z,y\<rangle> \<in> r))"

definition
  wellordered :: "[i\<Rightarrow>o,i,i]\<Rightarrow>o" where
    \<comment> \<open>linear and wellfounded on \<open>A\<close>\<close>
    "wellordered(M,A,r) \<equiv> 
        transitive_rel(M,A,r) \<and> linear_rel(M,A,r) \<and> wellfounded_on(M,A,r)"


subsubsection \<open>Trivial absoluteness proofs\<close>

lemma (in M_basic) irreflexive_abs [simp]: 
     "M(A) \<Longrightarrow> irreflexive(M,A,r) \<longleftrightarrow> irrefl(A,r)"
by (simp add: irreflexive_def irrefl_def)

lemma (in M_basic) transitive_rel_abs [simp]: 
     "M(A) \<Longrightarrow> transitive_rel(M,A,r) \<longleftrightarrow> trans[A](r)"
by (simp add: transitive_rel_def trans_on_def)

lemma (in M_basic) linear_rel_abs [simp]: 
     "M(A) \<Longrightarrow> linear_rel(M,A,r) \<longleftrightarrow> linear(A,r)"
by (simp add: linear_rel_def linear_def)

lemma (in M_basic) wellordered_is_trans_on: 
    "\<lbrakk>wellordered(M,A,r); M(A)\<rbrakk> \<Longrightarrow> trans[A](r)"
by (auto simp add: wellordered_def)

lemma (in M_basic) wellordered_is_linear: 
    "\<lbrakk>wellordered(M,A,r); M(A)\<rbrakk> \<Longrightarrow> linear(A,r)"
by (auto simp add: wellordered_def)

lemma (in M_basic) wellordered_is_wellfounded_on: 
    "\<lbrakk>wellordered(M,A,r); M(A)\<rbrakk> \<Longrightarrow> wellfounded_on(M,A,r)"
by (auto simp add: wellordered_def)

lemma (in M_basic) wellfounded_imp_wellfounded_on: 
    "\<lbrakk>wellfounded(M,r); M(A)\<rbrakk> \<Longrightarrow> wellfounded_on(M,A,r)"
by (auto simp add: wellfounded_def wellfounded_on_def)

lemma (in M_basic) wellfounded_on_subset_A:
     "\<lbrakk>wellfounded_on(M,A,r);  B<=A\<rbrakk> \<Longrightarrow> wellfounded_on(M,B,r)"
by (simp add: wellfounded_on_def, blast)


subsubsection \<open>Well-founded relations\<close>

lemma  (in M_basic) wellfounded_on_iff_wellfounded:
     "wellfounded_on(M,A,r) \<longleftrightarrow> wellfounded(M, r \<inter> A*A)"
apply (simp add: wellfounded_on_def wellfounded_def, safe)
 apply force
apply (drule_tac x=x in rspec, assumption, blast) 
done

lemma (in M_basic) wellfounded_on_imp_wellfounded:
     "\<lbrakk>wellfounded_on(M,A,r); r \<subseteq> A*A\<rbrakk> \<Longrightarrow> wellfounded(M,r)"
by (simp add: wellfounded_on_iff_wellfounded subset_Int_iff)

lemma (in M_basic) wellfounded_on_field_imp_wellfounded:
     "wellfounded_on(M, field(r), r) \<Longrightarrow> wellfounded(M,r)"
by (simp add: wellfounded_def wellfounded_on_iff_wellfounded, fast)

lemma (in M_basic) wellfounded_iff_wellfounded_on_field:
     "M(r) \<Longrightarrow> wellfounded(M,r) \<longleftrightarrow> wellfounded_on(M, field(r), r)"
by (blast intro: wellfounded_imp_wellfounded_on
                 wellfounded_on_field_imp_wellfounded)

(*Consider the least z in domain(r) such that P(z) does not hold...*)
lemma (in M_basic) wellfounded_induct: 
     "\<lbrakk>wellfounded(M,r); M(a); M(r); separation(M, \<lambda>x. \<not>P(x));  
         \<forall>x. M(x) \<and> (\<forall>y. \<langle>y,x\<rangle> \<in> r \<longrightarrow> P(y)) \<longrightarrow> P(x)\<rbrakk>
      \<Longrightarrow> P(a)"
apply (simp (no_asm_use) add: wellfounded_def)
apply (drule_tac x="{z \<in> domain(r). \<not>P(z)}" in rspec)
apply (blast dest: transM)+
done

lemma (in M_basic) wellfounded_on_induct: 
     "\<lbrakk>a\<in>A;  wellfounded_on(M,A,r);  M(A);  
       separation(M, \<lambda>x. x\<in>A \<longrightarrow> \<not>P(x));  
       \<forall>x\<in>A. M(x) \<and> (\<forall>y\<in>A. \<langle>y,x\<rangle> \<in> r \<longrightarrow> P(y)) \<longrightarrow> P(x)\<rbrakk>
      \<Longrightarrow> P(a)"
apply (simp (no_asm_use) add: wellfounded_on_def)
apply (drule_tac x="{z\<in>A. z\<in>A \<longrightarrow> \<not>P(z)}" in rspec)
apply (blast intro: transM)+
done


subsubsection \<open>Kunen's lemma IV 3.14, page 123\<close>

lemma (in M_basic) linear_imp_relativized: 
     "linear(A,r) \<Longrightarrow> linear_rel(M,A,r)" 
by (simp add: linear_def linear_rel_def) 

lemma (in M_basic) trans_on_imp_relativized: 
     "trans[A](r) \<Longrightarrow> transitive_rel(M,A,r)" 
by (unfold transitive_rel_def trans_on_def, blast) 

lemma (in M_basic) wf_on_imp_relativized: 
     "wf[A](r) \<Longrightarrow> wellfounded_on(M,A,r)" 
apply (clarsimp simp: wellfounded_on_def wf_def wf_on_def) 
apply (drule_tac x=x in spec, blast) 
done

lemma (in M_basic) wf_imp_relativized: 
     "wf(r) \<Longrightarrow> wellfounded(M,r)" 
apply (simp add: wellfounded_def wf_def, clarify) 
apply (drule_tac x=x in spec, blast) 
done

lemma (in M_basic) well_ord_imp_relativized: 
     "well_ord(A,r) \<Longrightarrow> wellordered(M,A,r)" 
by (simp add: wellordered_def well_ord_def tot_ord_def part_ord_def
       linear_imp_relativized trans_on_imp_relativized wf_on_imp_relativized)

text\<open>The property being well founded (and hence of being well ordered) is not absolute: 
the set that doesn't contain a minimal element may not exist in the class M. 
However, every set that is well founded in a transitive model M is well founded (page 124).\<close>

subsection\<open>Relativized versions of order-isomorphisms and order types\<close>

lemma (in M_basic) order_isomorphism_abs [simp]: 
     "\<lbrakk>M(A); M(B); M(f)\<rbrakk> 
      \<Longrightarrow> order_isomorphism(M,A,r,B,s,f) \<longleftrightarrow> f \<in> ord_iso(A,r,B,s)"
by (simp add: order_isomorphism_def ord_iso_def)

lemma (in M_trans) pred_set_abs [simp]: 
     "\<lbrakk>M(r); M(B)\<rbrakk> \<Longrightarrow> pred_set(M,A,x,r,B) \<longleftrightarrow> B = Order.pred(A,x,r)"
apply (simp add: pred_set_def Order.pred_def)
apply (blast dest: transM) 
done

lemma (in M_basic) pred_closed [intro,simp]: 
  "\<lbrakk>M(A); M(r); M(x)\<rbrakk> \<Longrightarrow> M(Order.pred(A, x, r))"
  using pred_separation [of r x] by (simp add: Order.pred_def) 

lemma (in M_basic) membership_abs [simp]: 
     "\<lbrakk>M(r); M(A)\<rbrakk> \<Longrightarrow> membership(M,A,r) \<longleftrightarrow> r = Memrel(A)"
apply (simp add: membership_def Memrel_def, safe)
  apply (rule equalityI) 
   apply clarify 
   apply (frule transM, assumption)
   apply blast
  apply clarify 
  apply (subgoal_tac "M(\<langle>xb,ya\<rangle>)", blast) 
  apply (blast dest: transM) 
 apply auto 
done

lemma (in M_basic) M_Memrel_iff:
     "M(A) \<Longrightarrow> Memrel(A) = {z \<in> A*A. \<exists>x[M]. \<exists>y[M]. z = \<langle>x,y\<rangle> \<and> x \<in> y}"
unfolding Memrel_def by (blast dest: transM)

lemma (in M_basic) Memrel_closed [intro,simp]: 
     "M(A) \<Longrightarrow> M(Memrel(A))"
  using Memrel_separation by (simp add: M_Memrel_iff) 


subsection \<open>Main results of Kunen, Chapter 1 section 6\<close>

text\<open>Subset properties-- proved outside the locale\<close>

lemma linear_rel_subset: 
    "\<lbrakk>linear_rel(M, A, r); B \<subseteq> A\<rbrakk> \<Longrightarrow> linear_rel(M, B, r)"
by (unfold linear_rel_def, blast)

lemma transitive_rel_subset: 
    "\<lbrakk>transitive_rel(M, A, r); B \<subseteq> A\<rbrakk> \<Longrightarrow> transitive_rel(M, B, r)"
by (unfold transitive_rel_def, blast)

lemma wellfounded_on_subset: 
    "\<lbrakk>wellfounded_on(M, A, r); B \<subseteq> A\<rbrakk> \<Longrightarrow> wellfounded_on(M, B, r)"
by (unfold wellfounded_on_def subset_def, blast)

lemma wellordered_subset: 
    "\<lbrakk>wellordered(M, A, r); B \<subseteq> A\<rbrakk> \<Longrightarrow> wellordered(M, B, r)"
  unfolding wellordered_def
apply (blast intro: linear_rel_subset transitive_rel_subset 
                    wellfounded_on_subset)
done

lemma (in M_basic) wellfounded_on_asym:
     "\<lbrakk>wellfounded_on(M,A,r);  \<langle>a,x\<rangle>\<in>r;  a\<in>A; x\<in>A;  M(A)\<rbrakk> \<Longrightarrow> \<langle>x,a\<rangle>\<notin>r"
apply (simp add: wellfounded_on_def) 
apply (drule_tac x="{x,a}" in rspec) 
apply (blast dest: transM)+
done

lemma (in M_basic) wellordered_asym:
     "\<lbrakk>wellordered(M,A,r);  \<langle>a,x\<rangle>\<in>r;  a\<in>A; x\<in>A;  M(A)\<rbrakk> \<Longrightarrow> \<langle>x,a\<rangle>\<notin>r"
by (simp add: wellordered_def, blast dest: wellfounded_on_asym)

end
