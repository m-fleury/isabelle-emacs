(*  Title:      ZF/AC/DC.thy
    Author:     Krzysztof Grabczewski

The proofs concerning the Axiom of Dependent Choice.
*)

theory DC
imports AC_Equiv Hartog Cardinal_aux
begin

lemma RepFun_lepoll: "Ord(a) \<Longrightarrow> {P(b). b \<in> a} \<lesssim> a"
  unfolding lepoll_def
apply (rule_tac x = "\<lambda>z \<in> RepFun (a,P) . \<mu> i. z=P (i) " in exI)
apply (rule_tac d="\<lambda>z. P (z)" in lam_injective)
 apply (fast intro!: Least_in_Ord)
apply (rule sym) 
apply (fast intro: LeastI Ord_in_Ord) 
done

text\<open>Trivial in the presence of AC, but here we need a wellordering of X\<close>
lemma image_Ord_lepoll: "\<lbrakk>f \<in> X->Y; Ord(X)\<rbrakk> \<Longrightarrow> f``X \<lesssim> X"
  unfolding lepoll_def
apply (rule_tac x = "\<lambda>x \<in> f``X. \<mu> y. f`y = x" in exI)
apply (rule_tac d = "\<lambda>z. f`z" in lam_injective)
apply (fast intro!: Least_in_Ord apply_equality, clarify) 
apply (rule LeastI) 
 apply (erule apply_equality, assumption+) 
apply (blast intro: Ord_in_Ord)
done

lemma range_subset_domain: 
      "\<lbrakk>R \<subseteq> X*X;   \<And>g. g \<in> X \<Longrightarrow> \<exists>u. \<langle>g,u\<rangle> \<in> R\<rbrakk> 
       \<Longrightarrow> range(R) \<subseteq> domain(R)"
by blast 

lemma cons_fun_type: "g \<in> n->X \<Longrightarrow> cons(\<langle>n,x\<rangle>, g) \<in> succ(n) -> cons(x, X)"
  unfolding succ_def
apply (fast intro!: fun_extend elim!: mem_irrefl)
done

lemma cons_fun_type2:
     "\<lbrakk>g \<in> n->X; x \<in> X\<rbrakk> \<Longrightarrow> cons(\<langle>n,x\<rangle>, g) \<in> succ(n) -> X"
by (erule cons_absorb [THEN subst], erule cons_fun_type)

lemma cons_image_n: "n \<in> nat \<Longrightarrow> cons(\<langle>n,x\<rangle>, g)``n = g``n"
by (fast elim!: mem_irrefl)

lemma cons_val_n: "g \<in> n->X \<Longrightarrow> cons(\<langle>n,x\<rangle>, g)`n = x"
by (fast intro!: apply_equality elim!: cons_fun_type)

lemma cons_image_k: "k \<in> n \<Longrightarrow> cons(\<langle>n,x\<rangle>, g)``k = g``k"
by (fast elim: mem_asym)

lemma cons_val_k: "\<lbrakk>k \<in> n; g \<in> n->X\<rbrakk> \<Longrightarrow> cons(\<langle>n,x\<rangle>, g)`k = g`k"
by (fast intro!: apply_equality consI2 elim!: cons_fun_type apply_Pair)

lemma domain_cons_eq_succ: "domain(f)=x \<Longrightarrow> domain(cons(\<langle>x,y\<rangle>, f)) = succ(x)"
by (simp add: domain_cons succ_def)

lemma restrict_cons_eq: "g \<in> n->X \<Longrightarrow> restrict(cons(\<langle>n,x\<rangle>, g), n) = g"
apply (simp add: restrict_def Pi_iff)
apply (blast intro: elim: mem_irrefl)  
done

lemma succ_in_succ: "\<lbrakk>Ord(k); i \<in> k\<rbrakk> \<Longrightarrow> succ(i) \<in> succ(k)"
apply (rule Ord_linear [of "succ(i)" "succ(k)", THEN disjE])
apply (fast elim: Ord_in_Ord mem_irrefl mem_asym)+
done

lemma restrict_eq_imp_val_eq: 
      "\<lbrakk>restrict(f, domain(g)) = g; x \<in> domain(g)\<rbrakk> 
       \<Longrightarrow> f`x = g`x" 
by (erule subst, simp add: restrict)

lemma domain_eq_imp_fun_type: "\<lbrakk>domain(f)=A; f \<in> B->C\<rbrakk> \<Longrightarrow> f \<in> A->C"
by (frule domain_of_fun, fast)

lemma ex_in_domain: "\<lbrakk>R \<subseteq> A * B; R \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>x. x \<in> domain(R)"
by (fast elim!: not_emptyE)


definition
  DC  :: "i \<Rightarrow> o"  where
    "DC(a) \<equiv> \<forall>X R. R \<subseteq> Pow(X)*X  \<and>
                    (\<forall>Y \<in> Pow(X). Y \<prec> a \<longrightarrow> (\<exists>x \<in> X. \<langle>Y,x\<rangle> \<in> R)) 
                    \<longrightarrow> (\<exists>f \<in> a->X. \<forall>b<a. <f``b,f`b> \<in> R)"

definition
  DC0 :: o  where
    "DC0 \<equiv> \<forall>A B R. R \<subseteq> A*B \<and> R\<noteq>0 \<and> range(R) \<subseteq> domain(R) 
                    \<longrightarrow> (\<exists>f \<in> nat->domain(R). \<forall>n \<in> nat. <f`n,f`succ(n)>:R)"

definition
  ff  :: "[i, i, i, i] \<Rightarrow> i"  where
    "ff(b, X, Q, R) \<equiv>
           transrec(b, \<lambda>c r. THE x. first(x, {x \<in> X. <r``c, x> \<in> R}, Q))"


locale DC0_imp =
  fixes XX and RR and X and R

  assumes all_ex: "\<forall>Y \<in> Pow(X). Y \<prec> nat \<longrightarrow> (\<exists>x \<in> X. \<langle>Y, x\<rangle> \<in> R)"

  defines XX_def: "XX \<equiv> (\<Union>n \<in> nat. {f \<in> n->X. \<forall>k \<in> n. <f``k, f`k> \<in> R})"
     and RR_def:  "RR \<equiv> {\<langle>z1,z2\<rangle>:XX*XX. domain(z2)=succ(domain(z1))  
                                       \<and> restrict(z2, domain(z1)) = z1}"
begin

(* ********************************************************************** *)
(* DC \<Longrightarrow> DC(omega)                                                       *)
(*                                                                        *)
(* The scheme of the proof:                                               *)
(*                                                                        *)
(* Assume DC. Let R and X satisfy the premise of DC(omega).               *)
(*                                                                        *)
(* Define XX and RR as follows:                                           *)
(*                                                                        *)
(*       XX = (\<Union>n \<in> nat. {f \<in> n->X. \<forall>k \<in> n. <f``k, f`k> \<in> R})           *)
(*       f RR g iff domain(g)=succ(domain(f)) \<and>                           *)
(*              restrict(g, domain(f)) = f                                *)
(*                                                                        *)
(* Then RR satisfies the hypotheses of DC.                                *)
(* So applying DC:                                                        *)
(*                                                                        *)
(*       \<exists>f \<in> nat->XX. \<forall>n \<in> nat. f`n RR f`succ(n)                        *)
(*                                                                        *)
(* Thence                                                                 *)
(*                                                                        *)
(*       ff = {<n, f`succ(n)`n>. n \<in> nat}                                 *)
(*                                                                        *)
(* is the desired function.                                               *)
(*                                                                        *)
(* ********************************************************************** *)

lemma lemma1_1: "RR \<subseteq> XX*XX"
by (unfold RR_def, fast)

lemma lemma1_2: "RR \<noteq> 0"
  unfolding RR_def XX_def
apply (rule all_ex [THEN ballE])
apply (erule_tac [2] notE [OF _ empty_subsetI [THEN PowI]])
apply (erule_tac impE [OF _ nat_0I [THEN n_lesspoll_nat]])
apply (erule bexE)
apply (rule_tac a = "<0, {\<langle>0, x\<rangle>}>" in not_emptyI)
apply (rule CollectI)
apply (rule SigmaI)
apply (rule nat_0I [THEN UN_I])
apply (simp (no_asm_simp) add: nat_0I [THEN UN_I])
apply (rule nat_1I [THEN UN_I])
apply (force intro!: singleton_fun [THEN Pi_type]
             simp add: singleton_0 [symmetric])
apply (simp add: singleton_0)
done

lemma lemma1_3: "range(RR) \<subseteq> domain(RR)"
  unfolding RR_def XX_def
apply (rule range_subset_domain, blast, clarify)
apply (frule fun_is_rel [THEN image_subset, THEN PowI, 
                         THEN all_ex [THEN bspec]])
apply (erule impE[OF _ lesspoll_trans1[OF image_Ord_lepoll 
                                          [OF _ nat_into_Ord] n_lesspoll_nat]],
       assumption+)
apply (erule bexE)
apply (rule_tac x = "cons (\<langle>n,x\<rangle>, g) " in exI)
apply (rule CollectI)
apply (force elim!: cons_fun_type2 
             simp add: cons_image_n cons_val_n cons_image_k cons_val_k)
apply (simp add: domain_of_fun succ_def restrict_cons_eq)
done

lemma lemma2:
     "\<lbrakk>\<forall>n \<in> nat. <f`n, f`succ(n)> \<in> RR;  f \<in> nat -> XX;  n \<in> nat\<rbrakk>   
      \<Longrightarrow> \<exists>k \<in> nat. f`succ(n) \<in> k -> X \<and> n \<in> k   
                  \<and> <f`succ(n)``n, f`succ(n)`n> \<in> R"
apply (induct_tac "n")
apply (drule apply_type [OF _ nat_1I])
apply (drule bspec [OF _ nat_0I])
apply (simp add: XX_def, safe)
apply (rule rev_bexI, assumption)
apply (subgoal_tac "0 \<in> y", force)
apply (force simp add: RR_def
             intro: ltD elim!: nat_0_le [THEN leE])
(** LEVEL 7, other subgoal **)
apply (drule bspec [OF _ nat_succI], assumption)
apply (subgoal_tac "f ` succ (succ (x)) \<in> succ (k) ->X")
apply (drule apply_type [OF _ nat_succI [THEN nat_succI]], assumption)
apply (simp (no_asm_use) add: XX_def RR_def)
apply safe
apply (frule_tac a="succ(k)" in domain_of_fun [symmetric, THEN trans], 
       assumption)
apply (frule_tac a=y in domain_of_fun [symmetric, THEN trans], 
       assumption)
apply (fast elim!: nat_into_Ord [THEN succ_in_succ] 
            dest!: bspec [OF _ nat_into_Ord [THEN succ_in_succ]])
apply (drule domain_of_fun)
apply (simp add: XX_def RR_def, clarify) 
apply (blast dest: domain_of_fun [symmetric, THEN trans] )
done

lemma lemma3_1:
     "\<lbrakk>\<forall>n \<in> nat. <f`n, f`succ(n)> \<in> RR;  f \<in> nat -> XX;  m \<in> nat\<rbrakk>   
      \<Longrightarrow>  {f`succ(x)`x. x \<in> m} = {f`succ(m)`x. x \<in> m}"
apply (subgoal_tac "\<forall>x \<in> m. f`succ (m) `x = f`succ (x) `x")
apply simp
apply (induct_tac "m", blast)
apply (rule ballI)
apply (erule succE)
 apply (rule restrict_eq_imp_val_eq)
  apply (drule bspec [OF _ nat_succI], assumption)
  apply (simp add: RR_def)
 apply (drule lemma2, assumption+)
 apply (fast dest!: domain_of_fun)
apply (drule_tac x = xa in bspec, assumption)
apply (erule sym [THEN trans, symmetric])
apply (rule restrict_eq_imp_val_eq [symmetric])
 apply (drule bspec [OF _ nat_succI], assumption)
 apply (simp add: RR_def)
apply (drule lemma2, assumption+)
apply (blast dest!: domain_of_fun 
             intro: nat_into_Ord OrdmemD [THEN subsetD])
done

lemma lemma3:
     "\<lbrakk>\<forall>n \<in> nat. <f`n, f`succ(n)> \<in> RR;  f \<in> nat -> XX;  m \<in> nat\<rbrakk>  
      \<Longrightarrow> (\<lambda>x \<in> nat. f`succ(x)`x) `` m = f`succ(m)``m"
apply (erule natE, simp)
apply (subst image_lam)
 apply (fast elim!: OrdmemD [OF nat_succI Ord_nat])
apply (subst lemma3_1, assumption+)
 apply fast
apply (fast dest!: lemma2 
            elim!: image_fun [symmetric, OF _ OrdmemD [OF _ nat_into_Ord]])
done

end

theorem DC0_imp_DC_nat: "DC0 \<Longrightarrow> DC(nat)"
apply (unfold DC_def DC0_def, clarify)
apply (elim allE)
apply (erule impE)
   (*these three results comprise Lemma 1*)
apply (blast intro!: DC0_imp.lemma1_1 [OF DC0_imp.intro] DC0_imp.lemma1_2 [OF DC0_imp.intro] DC0_imp.lemma1_3 [OF DC0_imp.intro])
apply (erule bexE)
apply (rule_tac x = "\<lambda>n \<in> nat. f`succ (n) `n" in rev_bexI)
 apply (rule lam_type, blast dest!: DC0_imp.lemma2 [OF DC0_imp.intro] intro: fun_weaken_type)
apply (rule oallI)
apply (frule DC0_imp.lemma2 [OF DC0_imp.intro], assumption)
  apply (blast intro: fun_weaken_type)
 apply (erule ltD) 
(** LEVEL 11: last subgoal **)
apply (subst DC0_imp.lemma3 [OF DC0_imp.intro], assumption+) 
  apply (fast elim!: fun_weaken_type)
 apply (erule ltD) 
apply (force simp add: lt_def) 
done


(* ************************************************************************
   DC(omega) \<Longrightarrow> DC                                                       
                                                                          
   The scheme of the proof:                                               
                                                                          
   Assume DC(omega). Let R and x satisfy the premise of DC.               
                                                                          
   Define XX and RR as follows:                                           
                                                                          
    XX = (\<Union>n \<in> nat. {f \<in> succ(n)->domain(R). \<forall>k \<in> n. <f`k, f`succ(k)> \<in> R})

    RR = {\<langle>z1,z2\<rangle>:Fin(XX)*XX. 
           (domain(z2)=succ(\<Union>f \<in> z1. domain(f)) \<and>
            (\<forall>f \<in> z1. restrict(z2, domain(f)) = f)) |      
           (\<not> (\<exists>g \<in> XX. domain(g)=succ(\<Union>f \<in> z1. domain(f)) \<and>
                        (\<forall>f \<in> z1. restrict(g, domain(f)) = f)) \<and>           
            z2={\<langle>0,x\<rangle>})}                                          
                                                                          
   Then XX and RR satisfy the hypotheses of DC(omega).                    
   So applying DC:                                                        
                                                                          
         \<exists>f \<in> nat->XX. \<forall>n \<in> nat. f``n RR f`n                             
                                                                          
   Thence                                                                 
                                                                          
         ff = {<n, f`n`n>. n \<in> nat}                                         
                                                                          
   is the desired function.                                               
                                                                          
************************************************************************* *)

lemma singleton_in_funs: 
 "x \<in> X \<Longrightarrow> {\<langle>0,x\<rangle>} \<in> 
            (\<Union>n \<in> nat. {f \<in> succ(n)->X. \<forall>k \<in> n. <f`k, f`succ(k)> \<in> R})"
apply (rule nat_0I [THEN UN_I])
apply (force simp add: singleton_0 [symmetric]
             intro!: singleton_fun [THEN Pi_type])
done


locale imp_DC0 =
  fixes XX and RR and x and R and f and allRR
  defines XX_def: "XX \<equiv> (\<Union>n \<in> nat.
                      {f \<in> succ(n)->domain(R). \<forall>k \<in> n. <f`k, f`succ(k)> \<in> R})"
      and RR_def:
         "RR \<equiv> {\<langle>z1,z2\<rangle>:Fin(XX)*XX. 
                  (domain(z2)=succ(\<Union>f \<in> z1. domain(f))  
                    \<and> (\<forall>f \<in> z1. restrict(z2, domain(f)) = f))
                  | (\<not> (\<exists>g \<in> XX. domain(g)=succ(\<Union>f \<in> z1. domain(f))  
                     \<and> (\<forall>f \<in> z1. restrict(g, domain(f)) = f)) \<and> z2={\<langle>0,x\<rangle>})}"
      and allRR_def:
        "allRR \<equiv> \<forall>b<nat.
                   <f``b, f`b> \<in>  
                    {\<langle>z1,z2\<rangle>\<in>Fin(XX)*XX. (domain(z2)=succ(\<Union>f \<in> z1. domain(f))
                                    \<and> (\<Union>f \<in> z1. domain(f)) = b  
                                    \<and> (\<forall>f \<in> z1. restrict(z2,domain(f)) = f))}"
begin

lemma lemma4:
     "\<lbrakk>range(R) \<subseteq> domain(R);  x \<in> domain(R)\<rbrakk>   
      \<Longrightarrow> RR \<subseteq> Pow(XX)*XX \<and>   
             (\<forall>Y \<in> Pow(XX). Y \<prec> nat \<longrightarrow> (\<exists>x \<in> XX. \<langle>Y,x\<rangle>:RR))"
apply (rule conjI)
apply (force dest!: FinD [THEN PowI] simp add: RR_def)
apply (rule impI [THEN ballI])
apply (drule Finite_Fin [OF lesspoll_nat_is_Finite PowD], assumption)
apply (case_tac
       "\<exists>g \<in> XX. domain (g) =
             succ(\<Union>f \<in> Y. domain(f)) \<and> (\<forall>f\<in>Y. restrict(g, domain(f)) = f)")
apply (simp add: RR_def, blast)
apply (safe del: domainE)
  unfolding XX_def RR_def
apply (rule rev_bexI, erule singleton_in_funs)
apply (simp add: nat_0I [THEN rev_bexI] cons_fun_type2)
done

lemma UN_image_succ_eq:
     "\<lbrakk>f \<in> nat->X; n \<in> nat\<rbrakk> 
      \<Longrightarrow> (\<Union>x \<in> f``succ(n). P(x)) =  P(f`n) \<union> (\<Union>x \<in> f``n. P(x))"
by (simp add: image_fun OrdmemD) 

lemma UN_image_succ_eq_succ:
     "\<lbrakk>(\<Union>x \<in> f``n. P(x)) = y; P(f`n) = succ(y);   
         f \<in> nat -> X; n \<in> nat\<rbrakk> \<Longrightarrow> (\<Union>x \<in> f``succ(n). P(x)) = succ(y)"
by (simp add: UN_image_succ_eq, blast)

lemma apply_domain_type:
     "\<lbrakk>h \<in> succ(n) -> D;  n \<in> nat; domain(h)=succ(y)\<rbrakk> \<Longrightarrow> h`y \<in> D"
by (fast elim: apply_type dest!: trans [OF sym domain_of_fun])

lemma image_fun_succ:
     "\<lbrakk>h \<in> nat -> X; n \<in> nat\<rbrakk> \<Longrightarrow> h``succ(n) = cons(h`n, h``n)"
by (simp add: image_fun OrdmemD) 

lemma f_n_type:
     "\<lbrakk>domain(f`n) = succ(k); f \<in> nat -> XX;  n \<in> nat\<rbrakk>    
      \<Longrightarrow> f`n \<in> succ(k) -> domain(R)"
  unfolding XX_def
apply (drule apply_type, assumption)
apply (fast elim: domain_eq_imp_fun_type)
done

lemma f_n_pairs_in_R [rule_format]: 
     "\<lbrakk>h \<in> nat -> XX;  domain(h`n) = succ(k);  n \<in> nat\<rbrakk>   
      \<Longrightarrow> \<forall>i \<in> k. <h`n`i, h`n`succ(i)> \<in> R"
  unfolding XX_def
apply (drule apply_type, assumption)
apply (elim UN_E CollectE)
apply (drule domain_of_fun [symmetric, THEN trans], assumption, simp)
done

lemma restrict_cons_eq_restrict: 
     "\<lbrakk>restrict(h, domain(u))=u;  h \<in> n->X;  domain(u) \<subseteq> n\<rbrakk>   
      \<Longrightarrow> restrict(cons(\<langle>n, y\<rangle>, h), domain(u)) = u"
  unfolding restrict_def
apply (simp add: restrict_def Pi_iff)
apply (erule sym [THEN trans, symmetric])
apply (blast elim: mem_irrefl)  
done

lemma all_in_image_restrict_eq:
     "\<lbrakk>\<forall>x \<in> f``n. restrict(f`n, domain(x))=x;   
         f \<in> nat -> XX;   
         n \<in> nat;  domain(f`n) = succ(n);   
         (\<Union>x \<in> f``n. domain(x)) \<subseteq> n\<rbrakk>  
      \<Longrightarrow> \<forall>x \<in> f``succ(n). restrict(cons(<succ(n),y>, f`n), domain(x)) = x"
apply (rule ballI)
apply (simp add: image_fun_succ)
apply (drule f_n_type, assumption+)
apply (erule disjE)
 apply (simp add: domain_of_fun restrict_cons_eq) 
apply (blast intro!: restrict_cons_eq_restrict)
done

lemma simplify_recursion: 
     "\<lbrakk>\<forall>b<nat. <f``b, f`b> \<in> RR;   
         f \<in> nat -> XX; range(R) \<subseteq> domain(R); x \<in> domain(R)\<rbrakk>    
      \<Longrightarrow> allRR"
  unfolding RR_def allRR_def
apply (rule oallI, drule ltD)
apply (erule nat_induct)
apply (drule_tac x=0 in ospec, blast intro: Limit_has_0) 
apply (force simp add: singleton_fun [THEN domain_of_fun] singleton_in_funs) 
(*induction step*) (** LEVEL 5 **)
(*prevent simplification of \<not>\<exists> to \<forall>\<not> *)
apply (simp only: separation split)
apply (drule_tac x="succ(xa)" in ospec, blast intro: ltI)
apply (elim conjE disjE)
apply (force elim!: trans subst_context
             intro!: UN_image_succ_eq_succ)
apply (erule notE)
apply (simp add: XX_def UN_image_succ_eq_succ)
apply (elim conjE bexE)
apply (drule apply_domain_type, assumption+)
apply (erule domainE)+
apply (frule f_n_type)
apply (simp add: XX_def, assumption+)
apply (rule rev_bexI, erule nat_succI)
apply (rename_tac m i j y z) 
apply (rule_tac x = "cons(<succ(m), z>, f`m)" in bexI)
prefer 2 apply (blast intro: cons_fun_type2) 
apply (rule conjI)
prefer 2 apply (fast del: ballI subsetI
                 elim: trans [OF _ subst_context, THEN domain_cons_eq_succ]
                       subst_context
                       all_in_image_restrict_eq [simplified XX_def]
                       trans equalityD1)
(*one remaining subgoal*)
apply (rule ballI)
apply (erule succE)
(** LEVEL 25 **)
 apply (simp add: cons_val_n cons_val_k)
(*assumption+ will not perform the required backtracking!*)
apply (drule f_n_pairs_in_R [simplified XX_def, OF _ domain_of_fun], 
       assumption, assumption, assumption)
apply (simp add: nat_into_Ord [THEN succ_in_succ] succI2 cons_val_k)
done


lemma lemma2: 
     "\<lbrakk>allRR; f \<in> nat->XX; range(R) \<subseteq> domain(R); x \<in> domain(R); n \<in> nat\<rbrakk>
      \<Longrightarrow> f`n \<in> succ(n) -> domain(R) \<and> (\<forall>i \<in> n. <f`n`i, f`n`succ(i)>:R)"
  unfolding allRR_def
apply (drule ospec)
apply (erule ltI [OF _ Ord_nat])
apply (erule CollectE, simp)
apply (rule conjI)
prefer 2 apply (fast elim!: f_n_pairs_in_R trans subst_context)
  unfolding XX_def
apply (fast elim!: trans [THEN domain_eq_imp_fun_type] subst_context)
done

lemma lemma3:
     "\<lbrakk>allRR; f \<in> nat->XX; n\<in>nat; range(R) \<subseteq> domain(R);  x \<in> domain(R)\<rbrakk>
      \<Longrightarrow> f`n`n = f`succ(n)`n"
apply (frule lemma2 [THEN conjunct1, THEN domain_of_fun], assumption+)
  unfolding allRR_def
apply (drule ospec) 
apply (drule ltI [OF nat_succI Ord_nat], assumption, simp)
apply (elim conjE ballE)
apply (erule restrict_eq_imp_val_eq [symmetric], force) 
apply (simp add: image_fun OrdmemD) 
done

end


theorem DC_nat_imp_DC0: "DC(nat) \<Longrightarrow> DC0"
  unfolding DC_def DC0_def
apply (intro allI impI)
apply (erule asm_rl conjE ex_in_domain [THEN exE] allE)+
apply (erule impE [OF _ imp_DC0.lemma4], assumption+)
apply (erule bexE)
apply (drule imp_DC0.simplify_recursion, assumption+)
apply (rule_tac x = "\<lambda>n \<in> nat. f`n`n" in bexI)
apply (rule_tac [2] lam_type)
apply (erule_tac [2] apply_type [OF imp_DC0.lemma2 [THEN conjunct1] succI1])
apply (rule ballI)
apply (frule_tac n="succ(n)" in imp_DC0.lemma2, 
       (assumption|erule nat_succI)+)
apply (drule imp_DC0.lemma3, auto)
done

(* ********************************************************************** *)
(* \<forall>K. Card(K) \<longrightarrow> DC(K) \<Longrightarrow> WO3                                       *)
(* ********************************************************************** *)

lemma fun_Ord_inj:
      "\<lbrakk>f \<in> a->X;  Ord(a); 
          \<And>b c. \<lbrakk>b<c; c \<in> a\<rbrakk> \<Longrightarrow> f`b\<noteq>f`c\<rbrakk>    
       \<Longrightarrow> f \<in> inj(a, X)"
apply (unfold inj_def, simp) 
apply (intro ballI impI)
apply (rule_tac j=x in Ord_in_Ord [THEN Ord_linear_lt], assumption+)
apply (blast intro: Ord_in_Ord, auto) 
apply (atomize, blast dest: not_sym) 
done

lemma value_in_image: "\<lbrakk>f \<in> X->Y; A \<subseteq> X; a \<in> A\<rbrakk> \<Longrightarrow> f`a \<in> f``A"
by (fast elim!: image_fun [THEN ssubst])

lemma lesspoll_lemma: "\<lbrakk>\<not> A \<prec> B; C \<prec> B\<rbrakk> \<Longrightarrow> A - C \<noteq> 0"
  unfolding lesspoll_def
apply (fast dest!: Diff_eq_0_iff [THEN iffD1, THEN subset_imp_lepoll]
            intro!: eqpollI elim: notE
            elim!: eqpollE lepoll_trans)
done

theorem DC_WO3: "(\<forall>K. Card(K) \<longrightarrow> DC(K)) \<Longrightarrow> WO3"
  unfolding DC_def WO3_def
apply (rule allI)
apply (case_tac "A \<prec> Hartog (A)")
apply (fast dest!: lesspoll_imp_ex_lt_eqpoll 
            intro!: Ord_Hartog leI [THEN le_imp_subset])
apply (erule allE impE)+
apply (rule Card_Hartog)
apply (erule_tac x = A in allE)
apply (erule_tac x = "{\<langle>z1,z2\<rangle> \<in> Pow (A) *A . z1 \<prec> Hartog (A) \<and> z2 \<notin> z1}" 
                 in allE)
apply simp
apply (erule impE, fast elim: lesspoll_lemma [THEN not_emptyE])
apply (erule bexE)
apply (rule Hartog_lepoll_selfE) 
apply (rule lepoll_def [THEN def_imp_iff, THEN iffD2])
apply (rule exI, rule fun_Ord_inj, assumption, rule Ord_Hartog)
apply (drule value_in_image) 
apply (drule OrdmemD, rule Ord_Hartog, assumption+, erule ltD) 
apply (drule ospec)
apply (blast intro: ltI Ord_Hartog, force) 
done

(* ********************************************************************** *)
(* WO1 \<Longrightarrow> \<forall>K. Card(K) \<longrightarrow> DC(K)                                       *)
(* ********************************************************************** *)

lemma images_eq:
     "\<lbrakk>\<forall>x \<in> A. f`x=g`x; f \<in> Df->Cf; g \<in> Dg->Cg; A \<subseteq> Df; A \<subseteq> Dg\<rbrakk> 
      \<Longrightarrow> f``A = g``A"
apply (simp (no_asm_simp) add: image_fun)
done

lemma lam_images_eq:
     "\<lbrakk>Ord(a); b \<in> a\<rbrakk> \<Longrightarrow> (\<lambda>x \<in> a. h(x))``b = (\<lambda>x \<in> b. h(x))``b"
apply (rule images_eq)
    apply (rule ballI)
    apply (drule OrdmemD [THEN subsetD], assumption+)
    apply simp
   apply (fast elim!: RepFunI OrdmemD intro!: lam_type)+
done

lemma lam_type_RepFun: "(\<lambda>b \<in> a. h(b)) \<in> a -> {h(b). b \<in> a}"
by (fast intro!: lam_type RepFunI)

lemma lemmaX:
     "\<lbrakk>\<forall>Y \<in> Pow(X). Y \<prec> K \<longrightarrow> (\<exists>x \<in> X. \<langle>Y, x\<rangle> \<in> R);   
         b \<in> K; Z \<in> Pow(X); Z \<prec> K\<rbrakk>   
      \<Longrightarrow> {x \<in> X. \<langle>Z,x\<rangle> \<in> R} \<noteq> 0"
by blast


lemma WO1_DC_lemma:
     "\<lbrakk>Card(K); well_ord(X,Q);   
         \<forall>Y \<in> Pow(X). Y \<prec> K \<longrightarrow> (\<exists>x \<in> X. \<langle>Y, x\<rangle> \<in> R); b \<in> K\<rbrakk>   
      \<Longrightarrow> ff(b, X, Q, R) \<in> {x \<in> X. <(\<lambda>c \<in> b. ff(c, X, Q, R))``b, x> \<in> R}"
apply (rule_tac P = "b \<in> K" in impE, (erule_tac [2] asm_rl)+)
apply (rule_tac i=b in Card_is_Ord [THEN Ord_in_Ord, THEN trans_induct], 
       assumption+)
apply (rule impI)
apply (rule ff_def [THEN def_transrec, THEN ssubst])
apply (erule the_first_in, fast)
apply (simp add: image_fun [OF lam_type_RepFun subset_refl])
apply (erule lemmaX, assumption)
 apply (blast intro: Card_is_Ord OrdmemD [THEN subsetD])
apply (blast intro: lesspoll_trans1 in_Card_imp_lesspoll RepFun_lepoll)
done

theorem WO1_DC_Card: "WO1 \<Longrightarrow> \<forall>K. Card(K) \<longrightarrow> DC(K)"
  unfolding DC_def WO1_def
apply (rule allI impI)+
apply (erule allE exE conjE)+
apply (rule_tac x = "\<lambda>b \<in> K. ff (b, X, Ra, R) " in bexI)
 apply (simp add: lam_images_eq [OF Card_is_Ord ltD])
 apply (fast elim!: ltE WO1_DC_lemma [THEN CollectD2])
apply (rule_tac lam_type)
apply (rule WO1_DC_lemma [THEN CollectD1], assumption+)
done

end
