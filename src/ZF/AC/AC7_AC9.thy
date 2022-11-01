(*  Title:      ZF/AC/AC7_AC9.thy
    Author:     Krzysztof Grabczewski

The proofs needed to state that AC7, AC8 and AC9 are equivalent to the previous
instances of AC.
*)

theory AC7_AC9
imports AC_Equiv
begin

(* ********************************************************************** *)
(* Lemmas used in the proofs AC7 \<Longrightarrow> AC6 and AC9 \<Longrightarrow> AC1                  *)
(*  - Sigma_fun_space_not0                                                *)
(*  - Sigma_fun_space_eqpoll                                              *)
(* ********************************************************************** *)

lemma Sigma_fun_space_not0: "\<lbrakk>0\<notin>A; B \<in> A\<rbrakk> \<Longrightarrow> (nat->\<Union>(A)) * B \<noteq> 0"
by (blast dest!: Sigma_empty_iff [THEN iffD1] Union_empty_iff [THEN iffD1])

lemma inj_lemma: 
        "C \<in> A \<Longrightarrow> (\<lambda>g \<in> (nat->\<Union>(A))*C.   
                (\<lambda>n \<in> nat. if(n=0, snd(g), fst(g)`(n #- 1))))   
                \<in> inj((nat->\<Union>(A))*C, (nat->\<Union>(A)) ) "
  unfolding inj_def
apply (rule CollectI)
apply (fast intro!: lam_type if_type apply_type fst_type snd_type, auto) 
apply (rule fun_extension, assumption+)
apply (drule lam_eqE [OF _ nat_succI], assumption, simp) 
apply (drule lam_eqE [OF _ nat_0I], simp) 
done

lemma Sigma_fun_space_eqpoll:
     "\<lbrakk>C \<in> A; 0\<notin>A\<rbrakk> \<Longrightarrow> (nat->\<Union>(A)) * C \<approx> (nat->\<Union>(A))"
apply (rule eqpollI)
apply (simp add: lepoll_def)
apply (fast intro!: inj_lemma)
apply (fast elim!: prod_lepoll_self not_sym [THEN not_emptyE] subst_elem 
            elim: swap)
done


(* ********************************************************************** *)
(* AC6 \<Longrightarrow> AC7                                                            *)
(* ********************************************************************** *)

lemma AC6_AC7: "AC6 \<Longrightarrow> AC7"
by (unfold AC6_def AC7_def, blast)

(* ********************************************************************** *)
(* AC7 \<Longrightarrow> AC6, Rubin & Rubin p. 12, Theorem 2.8                          *)
(* The case of the empty family of sets added in order to complete        *)
(* the proof.                                                             *)
(* ********************************************************************** *)

lemma lemma1_1: "y \<in> (\<Prod>B \<in> A. Y*B) \<Longrightarrow> (\<lambda>B \<in> A. snd(y`B)) \<in> (\<Prod>B \<in> A. B)"
by (fast intro!: lam_type snd_type apply_type)

lemma lemma1_2:
     "y \<in> (\<Prod>B \<in> {Y*C. C \<in> A}. B) \<Longrightarrow> (\<lambda>B \<in> A. y`(Y*B)) \<in> (\<Prod>B \<in> A. Y*B)"
apply (fast intro!: lam_type apply_type)
done

lemma AC7_AC6_lemma1:
     "(\<Prod>B \<in> {(nat->\<Union>(A))*C. C \<in> A}. B) \<noteq> 0 \<Longrightarrow> (\<Prod>B \<in> A. B) \<noteq> 0"
by (fast intro!: equals0I lemma1_1 lemma1_2)

lemma AC7_AC6_lemma2: "0 \<notin> A \<Longrightarrow> 0 \<notin> {(nat -> \<Union>(A)) * C. C \<in> A}"
by (blast dest: Sigma_fun_space_not0)

lemma AC7_AC6: "AC7 \<Longrightarrow> AC6"
  unfolding AC6_def AC7_def
apply (rule allI)
apply (rule impI)
apply (case_tac "A=0", simp)
apply (rule AC7_AC6_lemma1)
apply (erule allE) 
apply (blast del: notI
             intro!: AC7_AC6_lemma2 intro: eqpoll_sym eqpoll_trans 
                    Sigma_fun_space_eqpoll)
done


(* ********************************************************************** *)
(* AC1 \<Longrightarrow> AC8                                                            *)
(* ********************************************************************** *)

lemma AC1_AC8_lemma1: 
        "\<forall>B \<in> A. \<exists>B1 B2. B=\<langle>B1,B2\<rangle> \<and> B1 \<approx> B2   
        \<Longrightarrow> 0 \<notin> { bij(fst(B),snd(B)). B \<in> A }"
apply (unfold eqpoll_def, auto)
done

lemma AC1_AC8_lemma2:
     "\<lbrakk>f \<in> (\<Prod>X \<in> RepFun(A,p). X); D \<in> A\<rbrakk> \<Longrightarrow> (\<lambda>x \<in> A. f`p(x))`D \<in> p(D)" 
apply (simp, fast elim!: apply_type)
done

lemma AC1_AC8: "AC1 \<Longrightarrow> AC8"
  unfolding AC1_def AC8_def
apply (fast dest: AC1_AC8_lemma1 AC1_AC8_lemma2)
done


(* ********************************************************************** *)
(* AC8 \<Longrightarrow> AC9                                                            *)
(*  - this proof replaces the following two from Rubin & Rubin:           *)
(*    AC8 \<Longrightarrow> AC1 and AC1 \<Longrightarrow> AC9                                         *)
(* ********************************************************************** *)

lemma AC8_AC9_lemma:
     "\<forall>B1 \<in> A. \<forall>B2 \<in> A. B1 \<approx> B2 
      \<Longrightarrow> \<forall>B \<in> A*A. \<exists>B1 B2. B=\<langle>B1,B2\<rangle> \<and> B1 \<approx> B2"
by fast

lemma AC8_AC9: "AC8 \<Longrightarrow> AC9"
  unfolding AC8_def AC9_def
apply (intro allI impI)
apply (erule allE)
apply (erule impE, erule AC8_AC9_lemma, force) 
done


(* ********************************************************************** *)
(* AC9 \<Longrightarrow> AC1                                                            *)
(* The idea of this proof comes from "Equivalents of the Axiom of Choice" *)
(* by Rubin & Rubin. But (x * y) is not necessarily equipollent to        *)
(* (x * y) \<union> {0} when y is a set of total functions acting from nat to   *)
(* \<Union>(A) -- therefore we have used the set (y * nat) instead of y.     *)
(* ********************************************************************** *)

lemma snd_lepoll_SigmaI: "b \<in> B \<Longrightarrow> X \<lesssim> B \<times> X"
by (blast intro: lepoll_trans prod_lepoll_self eqpoll_imp_lepoll 
                 prod_commute_eqpoll) 

lemma nat_lepoll_lemma:
     "\<lbrakk>0 \<notin> A; B \<in> A\<rbrakk> \<Longrightarrow> nat \<lesssim> ((nat \<rightarrow> \<Union>(A)) \<times> B) \<times> nat"
by (blast dest: Sigma_fun_space_not0 intro: snd_lepoll_SigmaI)

lemma AC9_AC1_lemma1:
     "\<lbrakk>0\<notin>A;  A\<noteq>0;   
         C = {((nat->\<Union>(A))*B)*nat. B \<in> A}  \<union>  
             {cons(0,((nat->\<Union>(A))*B)*nat). B \<in> A};  
         B1 \<in> C;  B2 \<in> C\<rbrakk>   
      \<Longrightarrow> B1 \<approx> B2"
by (blast intro!: nat_lepoll_lemma Sigma_fun_space_eqpoll
                     nat_cons_eqpoll [THEN eqpoll_trans] 
                     prod_eqpoll_cong [OF _ eqpoll_refl]
             intro: eqpoll_trans eqpoll_sym )

lemma AC9_AC1_lemma2:
     "\<forall>B1 \<in> {(F*B)*N. B \<in> A} \<union> {cons(0,(F*B)*N). B \<in> A}.   
      \<forall>B2 \<in> {(F*B)*N. B \<in> A} \<union> {cons(0,(F*B)*N). B \<in> A}.   
        f`\<langle>B1,B2\<rangle> \<in> bij(B1, B2)   
      \<Longrightarrow> (\<lambda>B \<in> A. snd(fst((f`<cons(0,(F*B)*N),(F*B)*N>)`0))) \<in> (\<Prod>X \<in> A. X)"
apply (intro lam_type snd_type fst_type)
apply (rule apply_type [OF _ consI1]) 
apply (fast intro!: fun_weaken_type bij_is_fun)
done

lemma AC9_AC1: "AC9 \<Longrightarrow> AC1"
  unfolding AC1_def AC9_def
apply (intro allI impI)
apply (erule allE)
apply (case_tac "A\<noteq>0")
apply (blast dest: AC9_AC1_lemma1 AC9_AC1_lemma2, force) 
done

end
