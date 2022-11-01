(*  Title:      ZF/Constructible/Rank_Separation.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>Separation for Facts About Order Types, Rank Functions and 
      Well-Founded Relations\<close>

theory Rank_Separation imports Rank Rec_Separation begin


text\<open>This theory proves all instances needed for locales
 \<open>M_ordertype\<close> and  \<open>M_wfrank\<close>.  But the material is not
 needed for proving the relative consistency of AC.\<close>

subsection\<open>The Locale \<open>M_ordertype\<close>\<close>

subsubsection\<open>Separation for Order-Isomorphisms\<close>

lemma well_ord_iso_Reflects:
  "REFLECTS[\<lambda>x. x\<in>A \<longrightarrow>
                (\<exists>y[L]. \<exists>p[L]. fun_apply(L,f,x,y) \<and> pair(L,y,x,p) \<and> p \<in> r),
        \<lambda>i x. x\<in>A \<longrightarrow> (\<exists>y \<in> Lset(i). \<exists>p \<in> Lset(i).
                fun_apply(##Lset(i),f,x,y) \<and> pair(##Lset(i),y,x,p) \<and> p \<in> r)]"
by (intro FOL_reflections function_reflections)

lemma well_ord_iso_separation:
     "\<lbrakk>L(A); L(f); L(r)\<rbrakk>
      \<Longrightarrow> separation (L, \<lambda>x. x\<in>A \<longrightarrow> (\<exists>y[L]. (\<exists>p[L].
                     fun_apply(L,f,x,y) \<and> pair(L,y,x,p) \<and> p \<in> r)))"
apply (rule gen_separation_multi [OF well_ord_iso_Reflects, of "{A,f,r}"], 
       auto)
apply (rule_tac env="[A,f,r]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsubsection\<open>Separation for \<^term>\<open>obase\<close>\<close>

lemma obase_reflects:
  "REFLECTS[\<lambda>a. \<exists>x[L]. \<exists>g[L]. \<exists>mx[L]. \<exists>par[L].
             ordinal(L,x) \<and> membership(L,x,mx) \<and> pred_set(L,A,a,r,par) \<and>
             order_isomorphism(L,par,r,x,mx,g),
        \<lambda>i a. \<exists>x \<in> Lset(i). \<exists>g \<in> Lset(i). \<exists>mx \<in> Lset(i). \<exists>par \<in> Lset(i).
             ordinal(##Lset(i),x) \<and> membership(##Lset(i),x,mx) \<and> pred_set(##Lset(i),A,a,r,par) \<and>
             order_isomorphism(##Lset(i),par,r,x,mx,g)]"
by (intro FOL_reflections function_reflections fun_plus_reflections)

lemma obase_separation:
     \<comment> \<open>part of the order type formalization\<close>
     "\<lbrakk>L(A); L(r)\<rbrakk>
      \<Longrightarrow> separation(L, \<lambda>a. \<exists>x[L]. \<exists>g[L]. \<exists>mx[L]. \<exists>par[L].
             ordinal(L,x) \<and> membership(L,x,mx) \<and> pred_set(L,A,a,r,par) \<and>
             order_isomorphism(L,par,r,x,mx,g))"
apply (rule gen_separation_multi [OF obase_reflects, of "{A,r}"], auto)
apply (rule_tac env="[A,r]" in DPow_LsetI)
apply (rule ordinal_iff_sats sep_rules | simp)+
done


subsubsection\<open>Separation for a Theorem about \<^term>\<open>obase\<close>\<close>

lemma obase_equals_reflects:
  "REFLECTS[\<lambda>x. x\<in>A \<longrightarrow> \<not>(\<exists>y[L]. \<exists>g[L].
                ordinal(L,y) \<and> (\<exists>my[L]. \<exists>pxr[L].
                membership(L,y,my) \<and> pred_set(L,A,x,r,pxr) \<and>
                order_isomorphism(L,pxr,r,y,my,g))),
        \<lambda>i x. x\<in>A \<longrightarrow> \<not>(\<exists>y \<in> Lset(i). \<exists>g \<in> Lset(i).
                ordinal(##Lset(i),y) \<and> (\<exists>my \<in> Lset(i). \<exists>pxr \<in> Lset(i).
                membership(##Lset(i),y,my) \<and> pred_set(##Lset(i),A,x,r,pxr) \<and>
                order_isomorphism(##Lset(i),pxr,r,y,my,g)))]"
by (intro FOL_reflections function_reflections fun_plus_reflections)

lemma obase_equals_separation:
     "\<lbrakk>L(A); L(r)\<rbrakk>
      \<Longrightarrow> separation (L, \<lambda>x. x\<in>A \<longrightarrow> \<not>(\<exists>y[L]. \<exists>g[L].
                              ordinal(L,y) \<and> (\<exists>my[L]. \<exists>pxr[L].
                              membership(L,y,my) \<and> pred_set(L,A,x,r,pxr) \<and>
                              order_isomorphism(L,pxr,r,y,my,g))))"
apply (rule gen_separation_multi [OF obase_equals_reflects, of "{A,r}"], auto)
apply (rule_tac env="[A,r]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsubsection\<open>Replacement for \<^term>\<open>omap\<close>\<close>

lemma omap_reflects:
 "REFLECTS[\<lambda>z. \<exists>a[L]. a\<in>B \<and> (\<exists>x[L]. \<exists>g[L]. \<exists>mx[L]. \<exists>par[L].
     ordinal(L,x) \<and> pair(L,a,x,z) \<and> membership(L,x,mx) \<and>
     pred_set(L,A,a,r,par) \<and> order_isomorphism(L,par,r,x,mx,g)),
 \<lambda>i z. \<exists>a \<in> Lset(i). a\<in>B \<and> (\<exists>x \<in> Lset(i). \<exists>g \<in> Lset(i). \<exists>mx \<in> Lset(i).
        \<exists>par \<in> Lset(i).
         ordinal(##Lset(i),x) \<and> pair(##Lset(i),a,x,z) \<and>
         membership(##Lset(i),x,mx) \<and> pred_set(##Lset(i),A,a,r,par) \<and>
         order_isomorphism(##Lset(i),par,r,x,mx,g))]"
by (intro FOL_reflections function_reflections fun_plus_reflections)

lemma omap_replacement:
     "\<lbrakk>L(A); L(r)\<rbrakk>
      \<Longrightarrow> strong_replacement(L,
             \<lambda>a z. \<exists>x[L]. \<exists>g[L]. \<exists>mx[L]. \<exists>par[L].
             ordinal(L,x) \<and> pair(L,a,x,z) \<and> membership(L,x,mx) \<and>
             pred_set(L,A,a,r,par) \<and> order_isomorphism(L,par,r,x,mx,g))"
apply (rule strong_replacementI)
apply (rule_tac u="{A,r,B}" in gen_separation_multi [OF omap_reflects], auto)
apply (rule_tac env="[A,B,r]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done



subsection\<open>Instantiating the locale \<open>M_ordertype\<close>\<close>
text\<open>Separation (and Strong Replacement) for basic set-theoretic constructions
such as intersection, Cartesian Product and image.\<close>

lemma M_ordertype_axioms_L: "M_ordertype_axioms(L)"
  apply (rule M_ordertype_axioms.intro)
       apply (assumption | rule well_ord_iso_separation
         obase_separation obase_equals_separation
         omap_replacement)+
  done

theorem M_ordertype_L: "M_ordertype(L)"
  apply (rule M_ordertype.intro)
   apply (rule M_basic_L)
  apply (rule M_ordertype_axioms_L) 
  done


subsection\<open>The Locale \<open>M_wfrank\<close>\<close>

subsubsection\<open>Separation for \<^term>\<open>wfrank\<close>\<close>

lemma wfrank_Reflects:
 "REFLECTS[\<lambda>x. \<forall>rplus[L]. tran_closure(L,r,rplus) \<longrightarrow>
              \<not> (\<exists>f[L]. M_is_recfun(L, \<lambda>x f y. is_range(L,f,y), rplus, x, f)),
      \<lambda>i x. \<forall>rplus \<in> Lset(i). tran_closure(##Lset(i),r,rplus) \<longrightarrow>
         \<not> (\<exists>f \<in> Lset(i).
            M_is_recfun(##Lset(i), \<lambda>x f y. is_range(##Lset(i),f,y),
                        rplus, x, f))]"
by (intro FOL_reflections function_reflections is_recfun_reflection tran_closure_reflection)

lemma wfrank_separation:
     "L(r) \<Longrightarrow>
      separation (L, \<lambda>x. \<forall>rplus[L]. tran_closure(L,r,rplus) \<longrightarrow>
         \<not> (\<exists>f[L]. M_is_recfun(L, \<lambda>x f y. is_range(L,f,y), rplus, x, f)))"
apply (rule gen_separation [OF wfrank_Reflects], simp)
apply (rule_tac env="[r]" in DPow_LsetI)
apply (rule sep_rules tran_closure_iff_sats is_recfun_iff_sats | simp)+
done


subsubsection\<open>Replacement for \<^term>\<open>wfrank\<close>\<close>

lemma wfrank_replacement_Reflects:
 "REFLECTS[\<lambda>z. \<exists>x[L]. x \<in> A \<and>
        (\<forall>rplus[L]. tran_closure(L,r,rplus) \<longrightarrow>
         (\<exists>y[L]. \<exists>f[L]. pair(L,x,y,z)  \<and>
                        M_is_recfun(L, \<lambda>x f y. is_range(L,f,y), rplus, x, f) \<and>
                        is_range(L,f,y))),
 \<lambda>i z. \<exists>x \<in> Lset(i). x \<in> A \<and>
      (\<forall>rplus \<in> Lset(i). tran_closure(##Lset(i),r,rplus) \<longrightarrow>
       (\<exists>y \<in> Lset(i). \<exists>f \<in> Lset(i). pair(##Lset(i),x,y,z)  \<and>
         M_is_recfun(##Lset(i), \<lambda>x f y. is_range(##Lset(i),f,y), rplus, x, f) \<and>
         is_range(##Lset(i),f,y)))]"
by (intro FOL_reflections function_reflections fun_plus_reflections
             is_recfun_reflection tran_closure_reflection)

lemma wfrank_strong_replacement:
     "L(r) \<Longrightarrow>
      strong_replacement(L, \<lambda>x z.
         \<forall>rplus[L]. tran_closure(L,r,rplus) \<longrightarrow>
         (\<exists>y[L]. \<exists>f[L]. pair(L,x,y,z)  \<and>
                        M_is_recfun(L, \<lambda>x f y. is_range(L,f,y), rplus, x, f) \<and>
                        is_range(L,f,y)))"
apply (rule strong_replacementI)
apply (rule_tac u="{r,B}" 
         in gen_separation_multi [OF wfrank_replacement_Reflects], 
       auto)
apply (rule_tac env="[r,B]" in DPow_LsetI)
apply (rule sep_rules tran_closure_iff_sats is_recfun_iff_sats | simp)+
done


subsubsection\<open>Separation for Proving \<open>Ord_wfrank_range\<close>\<close>

lemma Ord_wfrank_Reflects:
 "REFLECTS[\<lambda>x. \<forall>rplus[L]. tran_closure(L,r,rplus) \<longrightarrow>
          \<not> (\<forall>f[L]. \<forall>rangef[L].
             is_range(L,f,rangef) \<longrightarrow>
             M_is_recfun(L, \<lambda>x f y. is_range(L,f,y), rplus, x, f) \<longrightarrow>
             ordinal(L,rangef)),
      \<lambda>i x. \<forall>rplus \<in> Lset(i). tran_closure(##Lset(i),r,rplus) \<longrightarrow>
          \<not> (\<forall>f \<in> Lset(i). \<forall>rangef \<in> Lset(i).
             is_range(##Lset(i),f,rangef) \<longrightarrow>
             M_is_recfun(##Lset(i), \<lambda>x f y. is_range(##Lset(i),f,y),
                         rplus, x, f) \<longrightarrow>
             ordinal(##Lset(i),rangef))]"
by (intro FOL_reflections function_reflections is_recfun_reflection
          tran_closure_reflection ordinal_reflection)

lemma  Ord_wfrank_separation:
     "L(r) \<Longrightarrow>
      separation (L, \<lambda>x.
         \<forall>rplus[L]. tran_closure(L,r,rplus) \<longrightarrow>
          \<not> (\<forall>f[L]. \<forall>rangef[L].
             is_range(L,f,rangef) \<longrightarrow>
             M_is_recfun(L, \<lambda>x f y. is_range(L,f,y), rplus, x, f) \<longrightarrow>
             ordinal(L,rangef)))"
apply (rule gen_separation [OF Ord_wfrank_Reflects], simp)
apply (rule_tac env="[r]" in DPow_LsetI)
apply (rule sep_rules tran_closure_iff_sats is_recfun_iff_sats | simp)+
done


subsubsection\<open>Instantiating the locale \<open>M_wfrank\<close>\<close>

lemma M_wfrank_axioms_L: "M_wfrank_axioms(L)"
  apply (rule M_wfrank_axioms.intro)
   apply (assumption | rule
     wfrank_separation wfrank_strong_replacement Ord_wfrank_separation)+
  done

theorem M_wfrank_L: "M_wfrank(L)"
  apply (rule M_wfrank.intro)
   apply (rule M_trancl_L)
  apply (rule M_wfrank_axioms_L) 
  done

lemmas exists_wfrank = M_wfrank.exists_wfrank [OF M_wfrank_L]
  and M_wellfoundedrank = M_wfrank.M_wellfoundedrank [OF M_wfrank_L]
  and Ord_wfrank_range = M_wfrank.Ord_wfrank_range [OF M_wfrank_L]
  and Ord_range_wellfoundedrank = M_wfrank.Ord_range_wellfoundedrank [OF M_wfrank_L]
  and function_wellfoundedrank = M_wfrank.function_wellfoundedrank [OF M_wfrank_L]
  and domain_wellfoundedrank = M_wfrank.domain_wellfoundedrank [OF M_wfrank_L]
  and wellfoundedrank_type = M_wfrank.wellfoundedrank_type [OF M_wfrank_L]
  and Ord_wellfoundedrank = M_wfrank.Ord_wellfoundedrank [OF M_wfrank_L]
  and wellfoundedrank_eq = M_wfrank.wellfoundedrank_eq [OF M_wfrank_L]
  and wellfoundedrank_lt = M_wfrank.wellfoundedrank_lt [OF M_wfrank_L]
  and wellfounded_imp_subset_rvimage = M_wfrank.wellfounded_imp_subset_rvimage [OF M_wfrank_L]
  and wellfounded_imp_wf = M_wfrank.wellfounded_imp_wf [OF M_wfrank_L]
  and wellfounded_on_imp_wf_on = M_wfrank.wellfounded_on_imp_wf_on [OF M_wfrank_L]
  and wf_abs = M_wfrank.wf_abs [OF M_wfrank_L]
  and wf_on_abs = M_wfrank.wf_on_abs [OF M_wfrank_L]

end
