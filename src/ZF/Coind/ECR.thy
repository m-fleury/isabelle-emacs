(*  Title:      ZF/Coind/ECR.thy
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

theory ECR imports Static Dynamic begin

(* The extended correspondence relation *)

consts
  HasTyRel :: i
coinductive
  domains "HasTyRel" \<subseteq> "Val * Ty"
  intros
    htr_constI [intro!]:
      "\<lbrakk>c \<in> Const; t \<in> Ty; isof(c,t)\<rbrakk> \<Longrightarrow> <v_const(c),t> \<in> HasTyRel"
    htr_closI [intro]:
      "\<lbrakk>x \<in> ExVar; e \<in> Exp; t \<in> Ty; ve \<in> ValEnv; te \<in> TyEnv; 
          <te,e_fn(x,e),t> \<in> ElabRel;  
          ve_dom(ve) = te_dom(te);   
          {<ve_app(ve,y),te_app(te,y)>.y \<in> ve_dom(ve)} \<in> Pow(HasTyRel)\<rbrakk> 
       \<Longrightarrow> <v_clos(x,e,ve),t> \<in> HasTyRel" 
  monos  Pow_mono
  type_intros Val_ValEnv.intros
  
(* Pointwise extension to environments *)
 
definition
  hastyenv :: "[i,i] \<Rightarrow> o"  where
    "hastyenv(ve,te) \<equiv>                        
         ve_dom(ve) = te_dom(te) \<and>          
         (\<forall>x \<in> ve_dom(ve). <ve_app(ve,x),te_app(te,x)> \<in> HasTyRel)"

(* Specialised co-induction rule *)

lemma htr_closCI [intro]:
     "\<lbrakk>x \<in> ExVar; e \<in> Exp; t \<in> Ty; ve \<in> ValEnv; te \<in> TyEnv;   
         <te, e_fn(x, e), t> \<in> ElabRel; ve_dom(ve) = te_dom(te);  
         {<ve_app(ve,y),te_app(te,y)>.y \<in> ve_dom(ve)} \<in>
           Pow({<v_clos(x,e,ve),t>} \<union> HasTyRel)\<rbrakk>     
      \<Longrightarrow> <v_clos(x, e, ve),t> \<in> HasTyRel"
apply (rule singletonI [THEN HasTyRel.coinduct], auto)
done

(* Specialised elimination rules *)

inductive_cases
    htr_constE [elim!]: "<v_const(c),t> \<in> HasTyRel"
  and htr_closE [elim]: "<v_clos(x,e,ve),t> \<in> HasTyRel"


(* Properties of the pointwise extension to environments *)

lemmas HasTyRel_non_zero =
       HasTyRel.dom_subset [THEN subsetD, THEN SigmaD1, THEN ValNEE]

lemma hastyenv_owr: 
  "\<lbrakk>ve \<in> ValEnv; te \<in> TyEnv; hastyenv(ve,te); \<langle>v,t\<rangle> \<in> HasTyRel\<rbrakk> 
   \<Longrightarrow> hastyenv(ve_owr(ve,x,v),te_owr(te,x,t))"
by (auto simp add: hastyenv_def ve_app_owr HasTyRel_non_zero)

lemma basic_consistency_lem: 
  "\<lbrakk>ve \<in> ValEnv; te \<in> TyEnv; isofenv(ve,te)\<rbrakk> \<Longrightarrow> hastyenv(ve,te)"
  unfolding isofenv_def hastyenv_def
apply (force intro: te_appI ve_domI) 
done


(* ############################################################ *)
(* The Consistency theorem                                      *)
(* ############################################################ *)

lemma consistency_const:
     "\<lbrakk>c \<in> Const; hastyenv(ve,te);<te,e_const(c),t> \<in> ElabRel\<rbrakk> 
      \<Longrightarrow> <v_const(c), t> \<in> HasTyRel"
by blast


lemma consistency_var: 
  "\<lbrakk>x \<in> ve_dom(ve); hastyenv(ve,te); <te,e_var(x),t> \<in> ElabRel\<rbrakk> \<Longrightarrow>      
   <ve_app(ve,x),t> \<in> HasTyRel"
by (unfold hastyenv_def, blast)

lemma consistency_fn: 
  "\<lbrakk>ve \<in> ValEnv; x \<in> ExVar; e \<in> Exp; hastyenv(ve,te);        
           <te,e_fn(x,e),t> \<in> ElabRel   
\<rbrakk> \<Longrightarrow> <v_clos(x, e, ve), t> \<in> HasTyRel"
by (unfold hastyenv_def, blast)

declare ElabRel.dom_subset [THEN subsetD, dest]

declare Ty.intros [simp, intro!]
declare TyEnv.intros [simp, intro!]
declare Val_ValEnv.intros [simp, intro!]

lemma consistency_fix: 
  "\<lbrakk>ve \<in> ValEnv; x \<in> ExVar; e \<in> Exp; f \<in> ExVar; cl \<in> Val;                
      v_clos(x,e,ve_owr(ve,f,cl)) = cl;                           
      hastyenv(ve,te); <te,e_fix(f,x,e),t> \<in> ElabRel\<rbrakk> \<Longrightarrow>        
   \<langle>cl,t\<rangle> \<in> HasTyRel"
  unfolding hastyenv_def
apply (erule elab_fixE, safe)
apply hypsubst_thin
apply (rule subst, assumption) 
apply (rule_tac te="te_owr(te, f, t_fun(t1, t2))" in htr_closCI)
apply simp_all
apply (blast intro: ve_owrI) 
apply (rule ElabRel.fnI)
apply (simp_all add: ValNEE, force)
done


lemma consistency_app1:
 "\<lbrakk>ve \<in> ValEnv; e1 \<in> Exp; e2 \<in> Exp; c1 \<in> Const; c2 \<in> Const;    
     <ve,e1,v_const(c1)> \<in> EvalRel;                       
     \<forall>t te.                                          
       hastyenv(ve,te) \<longrightarrow> <te,e1,t> \<in> ElabRel \<longrightarrow> <v_const(c1),t> \<in> HasTyRel;
     <ve, e2, v_const(c2)> \<in> EvalRel;                   
     \<forall>t te.                                          
       hastyenv(ve,te) \<longrightarrow> <te,e2,t> \<in> ElabRel \<longrightarrow> <v_const(c2),t> \<in> HasTyRel;
     hastyenv(ve, te);                                  
     <te,e_app(e1,e2),t> \<in> ElabRel\<rbrakk> 
  \<Longrightarrow> <v_const(c_app(c1, c2)),t> \<in> HasTyRel"
by (blast intro!: c_appI intro: isof_app)

lemma consistency_app2:
 "\<lbrakk>ve \<in> ValEnv; vem \<in> ValEnv; e1 \<in> Exp; e2 \<in> Exp; em \<in> Exp; xm \<in> ExVar; 
     v \<in> Val;   
     <ve,e1,v_clos(xm,em,vem)> \<in> EvalRel;        
     \<forall>t te. hastyenv(ve,te) \<longrightarrow>                     
            <te,e1,t> \<in> ElabRel \<longrightarrow> <v_clos(xm,em,vem),t> \<in> HasTyRel;         
     <ve,e2,v2> \<in> EvalRel;                       
     \<forall>t te. hastyenv(ve,te) \<longrightarrow> <te,e2,t> \<in> ElabRel \<longrightarrow> \<langle>v2,t\<rangle> \<in> HasTyRel;
     <ve_owr(vem,xm,v2),em,v> \<in> EvalRel;         
     \<forall>t te. hastyenv(ve_owr(vem,xm,v2),te) \<longrightarrow>      
            <te,em,t> \<in> ElabRel \<longrightarrow> \<langle>v,t\<rangle> \<in> HasTyRel;
     hastyenv(ve,te); <te,e_app(e1,e2),t> \<in> ElabRel\<rbrakk> 
   \<Longrightarrow> \<langle>v,t\<rangle> \<in> HasTyRel"
apply (erule elab_appE)
apply (drule spec [THEN spec, THEN mp, THEN mp], assumption+)
apply (drule spec [THEN spec, THEN mp, THEN mp], assumption+)
apply (erule htr_closE)
apply (erule elab_fnE, simp)
apply clarify
apply (drule spec [THEN spec, THEN mp, THEN mp])
prefer 2 apply assumption+
apply (rule hastyenv_owr, assumption)
apply assumption 
apply (simp add: hastyenv_def, blast+)
done

lemma consistency [rule_format]:
   "<ve,e,v> \<in> EvalRel 
    \<Longrightarrow> (\<forall>t te. hastyenv(ve,te) \<longrightarrow> <te,e,t> \<in> ElabRel \<longrightarrow> \<langle>v,t\<rangle> \<in> HasTyRel)"
apply (erule EvalRel.induct)
apply (simp_all add: consistency_const consistency_var consistency_fn 
                     consistency_fix consistency_app1)
apply (blast intro: consistency_app2)
done

lemma basic_consistency:
     "\<lbrakk>ve \<in> ValEnv; te \<in> TyEnv; isofenv(ve,te);                    
         <ve,e,v_const(c)> \<in> EvalRel; <te,e,t> \<in> ElabRel\<rbrakk> 
      \<Longrightarrow> isof(c,t)"
by (blast dest: consistency intro!: basic_consistency_lem)

end
