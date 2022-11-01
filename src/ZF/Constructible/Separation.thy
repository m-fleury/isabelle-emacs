(*  Title:      ZF/Constructible/Separation.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section\<open>Early Instances of Separation and Strong Replacement\<close>

theory Separation imports L_axioms WF_absolute begin

text\<open>This theory proves all instances needed for locale \<open>M_basic\<close>\<close>

text\<open>Helps us solve for de Bruijn indices!\<close>
lemma nth_ConsI: "\<lbrakk>nth(n,l) = x; n \<in> nat\<rbrakk> \<Longrightarrow> nth(succ(n), Cons(a,l)) = x"
by simp

lemmas nth_rules = nth_0 nth_ConsI nat_0I nat_succI
lemmas sep_rules = nth_0 nth_ConsI FOL_iff_sats function_iff_sats
                   fun_plus_iff_sats

lemma Collect_conj_in_DPow:
     "\<lbrakk>{x\<in>A. P(x)} \<in> DPow(A);  {x\<in>A. Q(x)} \<in> DPow(A)\<rbrakk>
      \<Longrightarrow> {x\<in>A. P(x) \<and> Q(x)} \<in> DPow(A)"
by (simp add: Int_in_DPow Collect_Int_Collect_eq [symmetric])

lemma Collect_conj_in_DPow_Lset:
     "\<lbrakk>z \<in> Lset(j); {x \<in> Lset(j). P(x)} \<in> DPow(Lset(j))\<rbrakk>
      \<Longrightarrow> {x \<in> Lset(j). x \<in> z \<and> P(x)} \<in> DPow(Lset(j))"
apply (frule mem_Lset_imp_subset_Lset)
apply (simp add: Collect_conj_in_DPow Collect_mem_eq
                 subset_Int_iff2 elem_subset_in_DPow)
done

lemma separation_CollectI:
     "(\<And>z. L(z) \<Longrightarrow> L({x \<in> z . P(x)})) \<Longrightarrow> separation(L, \<lambda>x. P(x))"
apply (unfold separation_def, clarify)
apply (rule_tac x="{x\<in>z. P(x)}" in rexI)
apply simp_all
done

text\<open>Reduces the original comprehension to the reflected one\<close>
lemma reflection_imp_L_separation:
      "\<lbrakk>\<forall>x\<in>Lset(j). P(x) \<longleftrightarrow> Q(x);
          {x \<in> Lset(j) . Q(x)} \<in> DPow(Lset(j));
          Ord(j);  z \<in> Lset(j)\<rbrakk> \<Longrightarrow> L({x \<in> z . P(x)})"
apply (rule_tac i = "succ(j)" in L_I)
 prefer 2 apply simp
apply (subgoal_tac "{x \<in> z. P(x)} = {x \<in> Lset(j). x \<in> z \<and> (Q(x))}")
 prefer 2
 apply (blast dest: mem_Lset_imp_subset_Lset)
apply (simp add: Lset_succ Collect_conj_in_DPow_Lset)
done

text\<open>Encapsulates the standard proof script for proving instances of 
      Separation.\<close>
lemma gen_separation:
 assumes reflection: "REFLECTS [P,Q]"
     and Lu:         "L(u)"
     and collI: "\<And>j. u \<in> Lset(j)
                \<Longrightarrow> Collect(Lset(j), Q(j)) \<in> DPow(Lset(j))"
 shows "separation(L,P)"
apply (rule separation_CollectI)
apply (rule_tac A="{u,z}" in subset_LsetE, blast intro: Lu)
apply (rule ReflectsE [OF reflection], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule collI, assumption)
done

text\<open>As above, but typically \<^term>\<open>u\<close> is a finite enumeration such as
  \<^term>\<open>{a,b}\<close>; thus the new subgoal gets the assumption
  \<^term>\<open>{a,b} \<subseteq> Lset(i)\<close>, which is logically equivalent to 
  \<^term>\<open>a \<in> Lset(i)\<close> and \<^term>\<open>b \<in> Lset(i)\<close>.\<close>
lemma gen_separation_multi:
 assumes reflection: "REFLECTS [P,Q]"
     and Lu:         "L(u)"
     and collI: "\<And>j. u \<subseteq> Lset(j)
                \<Longrightarrow> Collect(Lset(j), Q(j)) \<in> DPow(Lset(j))"
 shows "separation(L,P)"
apply (rule gen_separation [OF reflection Lu])
apply (drule mem_Lset_imp_subset_Lset)
apply (erule collI) 
done


subsection\<open>Separation for Intersection\<close>

lemma Inter_Reflects:
     "REFLECTS[\<lambda>x. \<forall>y[L]. y\<in>A \<longrightarrow> x \<in> y,
               \<lambda>i x. \<forall>y\<in>Lset(i). y\<in>A \<longrightarrow> x \<in> y]"
by (intro FOL_reflections)

lemma Inter_separation:
     "L(A) \<Longrightarrow> separation(L, \<lambda>x. \<forall>y[L]. y\<in>A \<longrightarrow> x\<in>y)"
apply (rule gen_separation [OF Inter_Reflects], simp)
apply (rule DPow_LsetI)
 txt\<open>I leave this one example of a manual proof.  The tedium of manually
      instantiating \<^term>\<open>i\<close>, \<^term>\<open>j\<close> and \<^term>\<open>env\<close> is obvious.\<close>
apply (rule ball_iff_sats)
apply (rule imp_iff_sats)
apply (rule_tac [2] i=1 and j=0 and env="[y,x,A]" in mem_iff_sats)
apply (rule_tac i=0 and j=2 in mem_iff_sats)
apply (simp_all add: succ_Un_distrib [symmetric])
done

subsection\<open>Separation for Set Difference\<close>

lemma Diff_Reflects:
     "REFLECTS[\<lambda>x. x \<notin> B, \<lambda>i x. x \<notin> B]"
by (intro FOL_reflections)  

lemma Diff_separation:
     "L(B) \<Longrightarrow> separation(L, \<lambda>x. x \<notin> B)"
apply (rule gen_separation [OF Diff_Reflects], simp)
apply (rule_tac env="[B]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done

subsection\<open>Separation for Cartesian Product\<close>

lemma cartprod_Reflects:
     "REFLECTS[\<lambda>z. \<exists>x[L]. x\<in>A \<and> (\<exists>y[L]. y\<in>B \<and> pair(L,x,y,z)),
                \<lambda>i z. \<exists>x\<in>Lset(i). x\<in>A \<and> (\<exists>y\<in>Lset(i). y\<in>B \<and>
                                   pair(##Lset(i),x,y,z))]"
by (intro FOL_reflections function_reflections)

lemma cartprod_separation:
     "\<lbrakk>L(A); L(B)\<rbrakk>
      \<Longrightarrow> separation(L, \<lambda>z. \<exists>x[L]. x\<in>A \<and> (\<exists>y[L]. y\<in>B \<and> pair(L,x,y,z)))"
apply (rule gen_separation_multi [OF cartprod_Reflects, of "{A,B}"], auto)
apply (rule_tac env="[A,B]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done

subsection\<open>Separation for Image\<close>

lemma image_Reflects:
     "REFLECTS[\<lambda>y. \<exists>p[L]. p\<in>r \<and> (\<exists>x[L]. x\<in>A \<and> pair(L,x,y,p)),
           \<lambda>i y. \<exists>p\<in>Lset(i). p\<in>r \<and> (\<exists>x\<in>Lset(i). x\<in>A \<and> pair(##Lset(i),x,y,p))]"
by (intro FOL_reflections function_reflections)

lemma image_separation:
     "\<lbrakk>L(A); L(r)\<rbrakk>
      \<Longrightarrow> separation(L, \<lambda>y. \<exists>p[L]. p\<in>r \<and> (\<exists>x[L]. x\<in>A \<and> pair(L,x,y,p)))"
apply (rule gen_separation_multi [OF image_Reflects, of "{A,r}"], auto)
apply (rule_tac env="[A,r]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection\<open>Separation for Converse\<close>

lemma converse_Reflects:
  "REFLECTS[\<lambda>z. \<exists>p[L]. p\<in>r \<and> (\<exists>x[L]. \<exists>y[L]. pair(L,x,y,p) \<and> pair(L,y,x,z)),
     \<lambda>i z. \<exists>p\<in>Lset(i). p\<in>r \<and> (\<exists>x\<in>Lset(i). \<exists>y\<in>Lset(i).
                     pair(##Lset(i),x,y,p) \<and> pair(##Lset(i),y,x,z))]"
by (intro FOL_reflections function_reflections)

lemma converse_separation:
     "L(r) \<Longrightarrow> separation(L,
         \<lambda>z. \<exists>p[L]. p\<in>r \<and> (\<exists>x[L]. \<exists>y[L]. pair(L,x,y,p) \<and> pair(L,y,x,z)))"
apply (rule gen_separation [OF converse_Reflects], simp)
apply (rule_tac env="[r]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection\<open>Separation for Restriction\<close>

lemma restrict_Reflects:
     "REFLECTS[\<lambda>z. \<exists>x[L]. x\<in>A \<and> (\<exists>y[L]. pair(L,x,y,z)),
        \<lambda>i z. \<exists>x\<in>Lset(i). x\<in>A \<and> (\<exists>y\<in>Lset(i). pair(##Lset(i),x,y,z))]"
by (intro FOL_reflections function_reflections)

lemma restrict_separation:
   "L(A) \<Longrightarrow> separation(L, \<lambda>z. \<exists>x[L]. x\<in>A \<and> (\<exists>y[L]. pair(L,x,y,z)))"
apply (rule gen_separation [OF restrict_Reflects], simp)
apply (rule_tac env="[A]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection\<open>Separation for Composition\<close>

lemma comp_Reflects:
     "REFLECTS[\<lambda>xz. \<exists>x[L]. \<exists>y[L]. \<exists>z[L]. \<exists>xy[L]. \<exists>yz[L].
                  pair(L,x,z,xz) \<and> pair(L,x,y,xy) \<and> pair(L,y,z,yz) \<and>
                  xy\<in>s \<and> yz\<in>r,
        \<lambda>i xz. \<exists>x\<in>Lset(i). \<exists>y\<in>Lset(i). \<exists>z\<in>Lset(i). \<exists>xy\<in>Lset(i). \<exists>yz\<in>Lset(i).
                  pair(##Lset(i),x,z,xz) \<and> pair(##Lset(i),x,y,xy) \<and>
                  pair(##Lset(i),y,z,yz) \<and> xy\<in>s \<and> yz\<in>r]"
by (intro FOL_reflections function_reflections)

lemma comp_separation:
     "\<lbrakk>L(r); L(s)\<rbrakk>
      \<Longrightarrow> separation(L, \<lambda>xz. \<exists>x[L]. \<exists>y[L]. \<exists>z[L]. \<exists>xy[L]. \<exists>yz[L].
                  pair(L,x,z,xz) \<and> pair(L,x,y,xy) \<and> pair(L,y,z,yz) \<and>
                  xy\<in>s \<and> yz\<in>r)"
apply (rule gen_separation_multi [OF comp_Reflects, of "{r,s}"], auto)
txt\<open>Subgoals after applying general ``separation'' rule:
     @{subgoals[display,indent=0,margin=65]}\<close>
apply (rule_tac env="[r,s]" in DPow_LsetI)
txt\<open>Subgoals ready for automatic synthesis of a formula:
     @{subgoals[display,indent=0,margin=65]}\<close>
apply (rule sep_rules | simp)+
done


subsection\<open>Separation for Predecessors in an Order\<close>

lemma pred_Reflects:
     "REFLECTS[\<lambda>y. \<exists>p[L]. p\<in>r \<and> pair(L,y,x,p),
                    \<lambda>i y. \<exists>p \<in> Lset(i). p\<in>r \<and> pair(##Lset(i),y,x,p)]"
by (intro FOL_reflections function_reflections)

lemma pred_separation:
     "\<lbrakk>L(r); L(x)\<rbrakk> \<Longrightarrow> separation(L, \<lambda>y. \<exists>p[L]. p\<in>r \<and> pair(L,y,x,p))"
apply (rule gen_separation_multi [OF pred_Reflects, of "{r,x}"], auto)
apply (rule_tac env="[r,x]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection\<open>Separation for the Membership Relation\<close>

lemma Memrel_Reflects:
     "REFLECTS[\<lambda>z. \<exists>x[L]. \<exists>y[L]. pair(L,x,y,z) \<and> x \<in> y,
            \<lambda>i z. \<exists>x \<in> Lset(i). \<exists>y \<in> Lset(i). pair(##Lset(i),x,y,z) \<and> x \<in> y]"
by (intro FOL_reflections function_reflections)

lemma Memrel_separation:
     "separation(L, \<lambda>z. \<exists>x[L]. \<exists>y[L]. pair(L,x,y,z) \<and> x \<in> y)"
apply (rule gen_separation [OF Memrel_Reflects nonempty])
apply (rule_tac env="[]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection\<open>Replacement for FunSpace\<close>

lemma funspace_succ_Reflects:
 "REFLECTS[\<lambda>z. \<exists>p[L]. p\<in>A \<and> (\<exists>f[L]. \<exists>b[L]. \<exists>nb[L]. \<exists>cnbf[L].
            pair(L,f,b,p) \<and> pair(L,n,b,nb) \<and> is_cons(L,nb,f,cnbf) \<and>
            upair(L,cnbf,cnbf,z)),
        \<lambda>i z. \<exists>p \<in> Lset(i). p\<in>A \<and> (\<exists>f \<in> Lset(i). \<exists>b \<in> Lset(i).
              \<exists>nb \<in> Lset(i). \<exists>cnbf \<in> Lset(i).
                pair(##Lset(i),f,b,p) \<and> pair(##Lset(i),n,b,nb) \<and>
                is_cons(##Lset(i),nb,f,cnbf) \<and> upair(##Lset(i),cnbf,cnbf,z))]"
by (intro FOL_reflections function_reflections)

lemma funspace_succ_replacement:
     "L(n) \<Longrightarrow>
      strong_replacement(L, \<lambda>p z. \<exists>f[L]. \<exists>b[L]. \<exists>nb[L]. \<exists>cnbf[L].
                pair(L,f,b,p) \<and> pair(L,n,b,nb) \<and> is_cons(L,nb,f,cnbf) \<and>
                upair(L,cnbf,cnbf,z))"
apply (rule strong_replacementI)
apply (rule_tac u="{n,B}" in gen_separation_multi [OF funspace_succ_Reflects], 
       auto)
apply (rule_tac env="[n,B]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection\<open>Separation for a Theorem about \<^term>\<open>is_recfun\<close>\<close>

lemma is_recfun_reflects:
  "REFLECTS[\<lambda>x. \<exists>xa[L]. \<exists>xb[L].
                pair(L,x,a,xa) \<and> xa \<in> r \<and> pair(L,x,b,xb) \<and> xb \<in> r \<and>
                (\<exists>fx[L]. \<exists>gx[L]. fun_apply(L,f,x,fx) \<and> fun_apply(L,g,x,gx) \<and>
                                   fx \<noteq> gx),
   \<lambda>i x. \<exists>xa \<in> Lset(i). \<exists>xb \<in> Lset(i).
          pair(##Lset(i),x,a,xa) \<and> xa \<in> r \<and> pair(##Lset(i),x,b,xb) \<and> xb \<in> r \<and>
                (\<exists>fx \<in> Lset(i). \<exists>gx \<in> Lset(i). fun_apply(##Lset(i),f,x,fx) \<and>
                  fun_apply(##Lset(i),g,x,gx) \<and> fx \<noteq> gx)]"
by (intro FOL_reflections function_reflections fun_plus_reflections)

lemma is_recfun_separation:
     \<comment> \<open>for well-founded recursion\<close>
     "\<lbrakk>L(r); L(f); L(g); L(a); L(b)\<rbrakk>
     \<Longrightarrow> separation(L,
            \<lambda>x. \<exists>xa[L]. \<exists>xb[L].
                pair(L,x,a,xa) \<and> xa \<in> r \<and> pair(L,x,b,xb) \<and> xb \<in> r \<and>
                (\<exists>fx[L]. \<exists>gx[L]. fun_apply(L,f,x,fx) \<and> fun_apply(L,g,x,gx) \<and>
                                   fx \<noteq> gx))"
apply (rule gen_separation_multi [OF is_recfun_reflects, of "{r,f,g,a,b}"], 
            auto)
apply (rule_tac env="[r,f,g,a,b]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection\<open>Instantiating the locale \<open>M_basic\<close>\<close>
text\<open>Separation (and Strong Replacement) for basic set-theoretic constructions
such as intersection, Cartesian Product and image.\<close>

lemma M_basic_axioms_L: "M_basic_axioms(L)"
  apply (rule M_basic_axioms.intro)
       apply (assumption | rule
         Inter_separation Diff_separation cartprod_separation image_separation
         converse_separation restrict_separation
         comp_separation pred_separation Memrel_separation
         funspace_succ_replacement is_recfun_separation power_ax)+
  done

theorem M_basic_L: " M_basic(L)"
by (rule M_basic.intro [OF M_trivial_L M_basic_axioms_L])

interpretation L: M_basic L by (rule M_basic_L)


end
