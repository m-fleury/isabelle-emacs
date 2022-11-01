(*  Title:      ZF/Constructible/WFrec.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section\<open>Relativized Well-Founded Recursion\<close>

theory WFrec imports Wellorderings begin


subsection\<open>General Lemmas\<close>

(*Many of these might be useful in WF.thy*)

lemma apply_recfun2:
    "\<lbrakk>is_recfun(r,a,H,f); \<langle>x,i\<rangle>:f\<rbrakk> \<Longrightarrow> i = H(x, restrict(f,r-``{x}))"
apply (frule apply_recfun) 
 apply (blast dest: is_recfun_type fun_is_rel) 
apply (simp add: function_apply_equality [OF _ is_recfun_imp_function])
done

text\<open>Expresses \<open>is_recfun\<close> as a recursion equation\<close>
lemma is_recfun_iff_equation:
     "is_recfun(r,a,H,f) \<longleftrightarrow>
           f \<in> r -`` {a} \<rightarrow> range(f) \<and>
           (\<forall>x \<in> r-``{a}. f`x = H(x, restrict(f, r-``{x})))"  
apply (rule iffI) 
 apply (simp add: is_recfun_type apply_recfun Ball_def vimage_singleton_iff, 
        clarify)  
apply (simp add: is_recfun_def) 
apply (rule fun_extension) 
  apply assumption
 apply (fast intro: lam_type, simp) 
done

lemma is_recfun_imp_in_r: "\<lbrakk>is_recfun(r,a,H,f); \<langle>x,i\<rangle> \<in> f\<rbrakk> \<Longrightarrow> \<langle>x, a\<rangle> \<in> r"
by (blast dest: is_recfun_type fun_is_rel)

lemma trans_Int_eq:
      "\<lbrakk>trans(r); \<langle>y,x\<rangle> \<in> r\<rbrakk> \<Longrightarrow> r -`` {x} \<inter> r -`` {y} = r -`` {y}"
by (blast intro: transD) 

lemma is_recfun_restrict_idem:
     "is_recfun(r,a,H,f) \<Longrightarrow> restrict(f, r -`` {a}) = f"
apply (drule is_recfun_type)
apply (auto simp add: Pi_iff subset_Sigma_imp_relation restrict_idem)  
done

lemma is_recfun_cong_lemma:
  "\<lbrakk>is_recfun(r,a,H,f); r = r'; a = a'; f = f'; 
      \<And>x g. \<lbrakk><x,a'> \<in> r'; relation(g); domain(g) \<subseteq> r' -``{x}\<rbrakk> 
             \<Longrightarrow> H(x,g) = H'(x,g)\<rbrakk>
   \<Longrightarrow> is_recfun(r',a',H',f')"
apply (simp add: is_recfun_def) 
apply (erule trans) 
apply (rule lam_cong) 
apply (simp_all add: vimage_singleton_iff Int_lower2)  
done

text\<open>For \<open>is_recfun\<close> we need only pay attention to functions
      whose domains are initial segments of \<^term>\<open>r\<close>.\<close>
lemma is_recfun_cong:
  "\<lbrakk>r = r'; a = a'; f = f'; 
      \<And>x g. \<lbrakk><x,a'> \<in> r'; relation(g); domain(g) \<subseteq> r' -``{x}\<rbrakk> 
             \<Longrightarrow> H(x,g) = H'(x,g)\<rbrakk>
   \<Longrightarrow> is_recfun(r,a,H,f) \<longleftrightarrow> is_recfun(r',a',H',f')"
apply (rule iffI)
txt\<open>Messy: fast and blast don't work for some reason\<close>
apply (erule is_recfun_cong_lemma, auto) 
apply (erule is_recfun_cong_lemma)
apply (blast intro: sym)+
done

subsection\<open>Reworking of the Recursion Theory Within \<^term>\<open>M\<close>\<close>

lemma (in M_basic) is_recfun_separation':
    "\<lbrakk>f \<in> r -`` {a} \<rightarrow> range(f); g \<in> r -`` {b} \<rightarrow> range(g);
        M(r); M(f); M(g); M(a); M(b)\<rbrakk> 
     \<Longrightarrow> separation(M, \<lambda>x. \<not> (\<langle>x, a\<rangle> \<in> r \<longrightarrow> \<langle>x, b\<rangle> \<in> r \<longrightarrow> f ` x = g ` x))"
apply (insert is_recfun_separation [of r f g a b]) 
apply (simp add: vimage_singleton_iff)
done

text\<open>Stated using \<^term>\<open>trans(r)\<close> rather than
      \<^term>\<open>transitive_rel(M,A,r)\<close> because the latter rewrites to
      the former anyway, by \<open>transitive_rel_abs\<close>.
      As always, theorems should be expressed in simplified form.
      The last three M-premises are redundant because of \<^term>\<open>M(r)\<close>, 
      but without them we'd have to undertake
      more work to set up the induction formula.\<close>
lemma (in M_basic) is_recfun_equal [rule_format]: 
    "\<lbrakk>is_recfun(r,a,H,f);  is_recfun(r,b,H,g);  
       wellfounded(M,r);  trans(r);
       M(f); M(g); M(r); M(x); M(a); M(b)\<rbrakk> 
     \<Longrightarrow> \<langle>x,a\<rangle> \<in> r \<longrightarrow> \<langle>x,b\<rangle> \<in> r \<longrightarrow> f`x=g`x"
apply (frule_tac f=f in is_recfun_type) 
apply (frule_tac f=g in is_recfun_type) 
apply (simp add: is_recfun_def)
apply (erule_tac a=x in wellfounded_induct, assumption+)
txt\<open>Separation to justify the induction\<close>
 apply (blast intro: is_recfun_separation') 
txt\<open>Now the inductive argument itself\<close>
apply clarify 
apply (erule ssubst)+
apply (simp (no_asm_simp) add: vimage_singleton_iff restrict_def)
apply (rename_tac x1)
apply (rule_tac t="\<lambda>z. H(x1,z)" in subst_context) 
apply (subgoal_tac "\<forall>y \<in> r-``{x1}. \<forall>z. \<langle>y,z\<rangle>\<in>f \<longleftrightarrow> \<langle>y,z\<rangle>\<in>g")
 apply (blast intro: transD) 
apply (simp add: apply_iff) 
apply (blast intro: transD sym) 
done

lemma (in M_basic) is_recfun_cut: 
    "\<lbrakk>is_recfun(r,a,H,f);  is_recfun(r,b,H,g);  
       wellfounded(M,r); trans(r); 
       M(f); M(g); M(r); \<langle>b,a\<rangle> \<in> r\<rbrakk>   
      \<Longrightarrow> restrict(f, r-``{b}) = g"
apply (frule_tac f=f in is_recfun_type) 
apply (rule fun_extension) 
apply (blast intro: transD restrict_type2) 
apply (erule is_recfun_type, simp) 
apply (blast intro: is_recfun_equal transD dest: transM) 
done

lemma (in M_basic) is_recfun_functional:
     "\<lbrakk>is_recfun(r,a,H,f);  is_recfun(r,a,H,g);  
       wellfounded(M,r); trans(r); M(f); M(g); M(r)\<rbrakk> \<Longrightarrow> f=g"
apply (rule fun_extension)
apply (erule is_recfun_type)+
apply (blast intro!: is_recfun_equal dest: transM) 
done 

text\<open>Tells us that \<open>is_recfun\<close> can (in principle) be relativized.\<close>
lemma (in M_basic) is_recfun_relativize:
  "\<lbrakk>M(r); M(f); \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk> 
   \<Longrightarrow> is_recfun(r,a,H,f) \<longleftrightarrow>
       (\<forall>z[M]. z \<in> f \<longleftrightarrow> 
        (\<exists>x[M]. \<langle>x,a\<rangle> \<in> r \<and> z = <x, H(x, restrict(f, r-``{x}))>))"
apply (simp add: is_recfun_def lam_def)
apply (safe intro!: equalityI) 
   apply (drule equalityD1 [THEN subsetD], assumption) 
   apply (blast dest: pair_components_in_M) 
  apply (blast elim!: equalityE dest: pair_components_in_M)
 apply (frule transM, assumption) 
 apply simp  
 apply blast
apply (subgoal_tac "is_function(M,f)")
 txt\<open>We use \<^term>\<open>is_function\<close> rather than \<^term>\<open>function\<close> because
      the subgoal's easier to prove with relativized quantifiers!\<close>
 prefer 2 apply (simp add: is_function_def) 
apply (frule pair_components_in_M, assumption) 
apply (simp add: is_recfun_imp_function function_restrictI) 
done

lemma (in M_basic) is_recfun_restrict:
     "\<lbrakk>wellfounded(M,r); trans(r); is_recfun(r,x,H,f); \<langle>y,x\<rangle> \<in> r; 
       M(r); M(f); 
       \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk>
       \<Longrightarrow> is_recfun(r, y, H, restrict(f, r -`` {y}))"
apply (frule pair_components_in_M, assumption, clarify) 
apply (simp (no_asm_simp) add: is_recfun_relativize restrict_iff
           trans_Int_eq)
apply safe
  apply (simp_all add: vimage_singleton_iff is_recfun_type [THEN apply_iff]) 
  apply (frule_tac x=xa in pair_components_in_M, assumption)
  apply (frule_tac x=xa in apply_recfun, blast intro: transD)  
  apply (simp add: is_recfun_type [THEN apply_iff] 
                   is_recfun_imp_function function_restrictI)
apply (blast intro: apply_recfun dest: transD)
done
 
lemma (in M_basic) restrict_Y_lemma:
   "\<lbrakk>wellfounded(M,r); trans(r); M(r);
       \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g));  M(Y);
       \<forall>b[M]. 
           b \<in> Y \<longleftrightarrow>
           (\<exists>x[M]. \<langle>x,a1\<rangle> \<in> r \<and>
            (\<exists>y[M]. b = \<langle>x,y\<rangle> \<and> (\<exists>g[M]. is_recfun(r,x,H,g) \<and> y = H(x,g))));
          \<langle>x,a1\<rangle> \<in> r; is_recfun(r,x,H,f); M(f)\<rbrakk>
       \<Longrightarrow> restrict(Y, r -`` {x}) = f"
apply (subgoal_tac "\<forall>y \<in> r-``{x}. \<forall>z. \<langle>y,z\<rangle>:Y \<longleftrightarrow> \<langle>y,z\<rangle>:f") 
 apply (simp (no_asm_simp) add: restrict_def) 
 apply (thin_tac "rall(M,P)" for P)+  \<comment> \<open>essential for efficiency\<close>
 apply (frule is_recfun_type [THEN fun_is_rel], blast)
apply (frule pair_components_in_M, assumption, clarify) 
apply (rule iffI)
 apply (frule_tac y="\<langle>y,z\<rangle>" in transM, assumption)
 apply (clarsimp simp add: vimage_singleton_iff is_recfun_type [THEN apply_iff]
                           apply_recfun is_recfun_cut) 
txt\<open>Opposite inclusion: something in f, show in Y\<close>
apply (frule_tac y="\<langle>y,z\<rangle>" in transM, assumption)  
apply (simp add: vimage_singleton_iff) 
apply (rule conjI) 
 apply (blast dest: transD) 
apply (rule_tac x="restrict(f, r -`` {y})" in rexI) 
apply (simp_all add: is_recfun_restrict
                     apply_recfun is_recfun_type [THEN apply_iff]) 
done

text\<open>For typical applications of Replacement for recursive definitions\<close>
lemma (in M_basic) univalent_is_recfun:
     "\<lbrakk>wellfounded(M,r); trans(r); M(r)\<rbrakk>
      \<Longrightarrow> univalent (M, A, \<lambda>x p. 
              \<exists>y[M]. p = \<langle>x,y\<rangle> \<and> (\<exists>f[M]. is_recfun(r,x,H,f) \<and> y = H(x,f)))"
apply (simp add: univalent_def) 
apply (blast dest: is_recfun_functional) 
done


text\<open>Proof of the inductive step for \<open>exists_is_recfun\<close>, since
      we must prove two versions.\<close>
lemma (in M_basic) exists_is_recfun_indstep:
    "\<lbrakk>\<forall>y. \<langle>y, a1\<rangle> \<in> r \<longrightarrow> (\<exists>f[M]. is_recfun(r, y, H, f)); 
       wellfounded(M,r); trans(r); M(r); M(a1);
       strong_replacement(M, \<lambda>x z. 
              \<exists>y[M]. \<exists>g[M]. pair(M,x,y,z) \<and> is_recfun(r,x,H,g) \<and> y = H(x,g)); 
       \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk>   
      \<Longrightarrow> \<exists>f[M]. is_recfun(r,a1,H,f)"
apply (drule_tac A="r-``{a1}" in strong_replacementD)
  apply blast 
 txt\<open>Discharge the "univalent" obligation of Replacement\<close>
 apply (simp add: univalent_is_recfun) 
txt\<open>Show that the constructed object satisfies \<open>is_recfun\<close>\<close> 
apply clarify 
apply (rule_tac x=Y in rexI)  
txt\<open>Unfold only the top-level occurrence of \<^term>\<open>is_recfun\<close>\<close>
apply (simp (no_asm_simp) add: is_recfun_relativize [of concl: _ a1])
txt\<open>The big iff-formula defining \<^term>\<open>Y\<close> is now redundant\<close>
apply safe 
 apply (simp add: vimage_singleton_iff restrict_Y_lemma [of r H _ a1]) 
txt\<open>one more case\<close>
apply (simp (no_asm_simp) add: Bex_def vimage_singleton_iff)
apply (drule_tac x1=x in spec [THEN mp], assumption, clarify) 
apply (rename_tac f) 
apply (rule_tac x=f in rexI) 
apply (simp_all add: restrict_Y_lemma [of r H])
txt\<open>FIXME: should not be needed!\<close>
apply (subst restrict_Y_lemma [of r H])
apply (simp add: vimage_singleton_iff)+
apply blast+
done

text\<open>Relativized version, when we have the (currently weaker) premise
      \<^term>\<open>wellfounded(M,r)\<close>\<close>
lemma (in M_basic) wellfounded_exists_is_recfun:
    "\<lbrakk>wellfounded(M,r);  trans(r);  
       separation(M, \<lambda>x. \<not> (\<exists>f[M]. is_recfun(r, x, H, f)));
       strong_replacement(M, \<lambda>x z. 
          \<exists>y[M]. \<exists>g[M]. pair(M,x,y,z) \<and> is_recfun(r,x,H,g) \<and> y = H(x,g)); 
       M(r);  M(a);  
       \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk>   
      \<Longrightarrow> \<exists>f[M]. is_recfun(r,a,H,f)"
apply (rule wellfounded_induct, assumption+, clarify)
apply (rule exists_is_recfun_indstep, assumption+)
done

lemma (in M_basic) wf_exists_is_recfun [rule_format]:
    "\<lbrakk>wf(r);  trans(r);  M(r);  
       strong_replacement(M, \<lambda>x z. 
         \<exists>y[M]. \<exists>g[M]. pair(M,x,y,z) \<and> is_recfun(r,x,H,g) \<and> y = H(x,g)); 
       \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk>   
      \<Longrightarrow> M(a) \<longrightarrow> (\<exists>f[M]. is_recfun(r,a,H,f))"
apply (rule wf_induct, assumption+)
apply (frule wf_imp_relativized)
apply (intro impI)
apply (rule exists_is_recfun_indstep) 
      apply (blast dest: transM del: rev_rallE, assumption+)
done


subsection\<open>Relativization of the ZF Predicate \<^term>\<open>is_recfun\<close>\<close>

definition
  M_is_recfun :: "[i\<Rightarrow>o, [i,i,i]\<Rightarrow>o, i, i, i] \<Rightarrow> o" where
   "M_is_recfun(M,MH,r,a,f) \<equiv> 
     \<forall>z[M]. z \<in> f \<longleftrightarrow> 
            (\<exists>x[M]. \<exists>y[M]. \<exists>xa[M]. \<exists>sx[M]. \<exists>r_sx[M]. \<exists>f_r_sx[M]. 
               pair(M,x,y,z) \<and> pair(M,x,a,xa) \<and> upair(M,x,x,sx) \<and>
               pre_image(M,r,sx,r_sx) \<and> restriction(M,f,r_sx,f_r_sx) \<and>
               xa \<in> r \<and> MH(x, f_r_sx, y))"

definition
  is_wfrec :: "[i\<Rightarrow>o, [i,i,i]\<Rightarrow>o, i, i, i] \<Rightarrow> o" where
   "is_wfrec(M,MH,r,a,z) \<equiv> 
      \<exists>f[M]. M_is_recfun(M,MH,r,a,f) \<and> MH(a,f,z)"

definition
  wfrec_replacement :: "[i\<Rightarrow>o, [i,i,i]\<Rightarrow>o, i] \<Rightarrow> o" where
   "wfrec_replacement(M,MH,r) \<equiv>
        strong_replacement(M, 
             \<lambda>x z. \<exists>y[M]. pair(M,x,y,z) \<and> is_wfrec(M,MH,r,x,y))"

lemma (in M_basic) is_recfun_abs:
     "\<lbrakk>\<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g));  M(r); M(a); M(f); 
         relation2(M,MH,H)\<rbrakk> 
      \<Longrightarrow> M_is_recfun(M,MH,r,a,f) \<longleftrightarrow> is_recfun(r,a,H,f)"
apply (simp add: M_is_recfun_def relation2_def is_recfun_relativize)
apply (rule rall_cong)
apply (blast dest: transM)
done

lemma M_is_recfun_cong [cong]:
     "\<lbrakk>r = r'; a = a'; f = f'; 
       \<And>x g y. \<lbrakk>M(x); M(g); M(y)\<rbrakk> \<Longrightarrow> MH(x,g,y) \<longleftrightarrow> MH'(x,g,y)\<rbrakk>
      \<Longrightarrow> M_is_recfun(M,MH,r,a,f) \<longleftrightarrow> M_is_recfun(M,MH',r',a',f')"
by (simp add: M_is_recfun_def) 

lemma (in M_basic) is_wfrec_abs:
     "\<lbrakk>\<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g)); 
         relation2(M,MH,H);  M(r); M(a); M(z)\<rbrakk>
      \<Longrightarrow> is_wfrec(M,MH,r,a,z) \<longleftrightarrow> 
          (\<exists>g[M]. is_recfun(r,a,H,g) \<and> z = H(a,g))"
by (simp add: is_wfrec_def relation2_def is_recfun_abs)

text\<open>Relating \<^term>\<open>wfrec_replacement\<close> to native constructs\<close>
lemma (in M_basic) wfrec_replacement':
  "\<lbrakk>wfrec_replacement(M,MH,r);
     \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g)); 
     relation2(M,MH,H);  M(r)\<rbrakk> 
   \<Longrightarrow> strong_replacement(M, \<lambda>x z. \<exists>y[M]. 
                pair(M,x,y,z) \<and> (\<exists>g[M]. is_recfun(r,x,H,g) \<and> y = H(x,g)))"
by (simp add: wfrec_replacement_def is_wfrec_abs) 

lemma wfrec_replacement_cong [cong]:
     "\<lbrakk>\<And>x y z. \<lbrakk>M(x); M(y); M(z)\<rbrakk> \<Longrightarrow> MH(x,y,z) \<longleftrightarrow> MH'(x,y,z);
         r=r'\<rbrakk> 
      \<Longrightarrow> wfrec_replacement(M, \<lambda>x y. MH(x,y), r) \<longleftrightarrow> 
          wfrec_replacement(M, \<lambda>x y. MH'(x,y), r')" 
by (simp add: is_wfrec_def wfrec_replacement_def) 


end

