(*  Title:      ZF/AC/AC17_AC1.thy
    Author:     Krzysztof Grabczewski

The equivalence of AC0, AC1 and AC17

Also, the proofs needed to show that each of AC2, AC3, ..., AC6 is equivalent
to AC0 and AC1.
*)

theory AC17_AC1
imports HH
begin


(** AC0 is equivalent to AC1.  
    AC0 comes from Suppes, AC1 from Rubin & Rubin **)

lemma AC0_AC1_lemma: "\<lbrakk>f:(\<Prod>X \<in> A. X); D \<subseteq> A\<rbrakk> \<Longrightarrow> \<exists>g. g:(\<Prod>X \<in> D. X)"
by (fast intro!: lam_type apply_type)

lemma AC0_AC1: "AC0 \<Longrightarrow> AC1"
  unfolding AC0_def AC1_def
apply (blast intro: AC0_AC1_lemma)
done

lemma AC1_AC0: "AC1 \<Longrightarrow> AC0"
by (unfold AC0_def AC1_def, blast)


(**** The proof of AC1 \<Longrightarrow> AC17 ****)

lemma AC1_AC17_lemma: "f \<in> (\<Prod>X \<in> Pow(A) - {0}. X) \<Longrightarrow> f \<in> (Pow(A) - {0} -> A)"
apply (rule Pi_type, assumption)
apply (drule apply_type, assumption, fast)
done

lemma AC1_AC17: "AC1 \<Longrightarrow> AC17"
  unfolding AC1_def AC17_def
apply (rule allI)
apply (rule ballI)
apply (erule_tac x = "Pow (A) -{0}" in allE)
apply (erule impE, fast)
apply (erule exE)
apply (rule bexI)
apply (erule_tac [2] AC1_AC17_lemma)
apply (rule apply_type, assumption)
apply (fast dest!: AC1_AC17_lemma elim!: apply_type)
done


(**** The proof of AC17 \<Longrightarrow> AC1 ****)

(* *********************************************************************** *)
(* more properties of HH                                                   *)
(* *********************************************************************** *)

lemma UN_eq_imp_well_ord:
     "\<lbrakk>x - (\<Union>j \<in> \<mu> i. HH(\<lambda>X \<in> Pow(x)-{0}. {f`X}, x, i) = {x}.  
        HH(\<lambda>X \<in> Pow(x)-{0}. {f`X}, x, j)) = 0;   
        f \<in> Pow(x)-{0} -> x\<rbrakk>   
        \<Longrightarrow> \<exists>r. well_ord(x,r)"
apply (rule exI)
apply (erule well_ord_rvimage 
        [OF bij_Least_HH_x [THEN bij_converse_bij, THEN bij_is_inj] 
            Ord_Least [THEN well_ord_Memrel]], assumption)
done

(* *********************************************************************** *)
(* theorems closer to the proof                                            *)
(* *********************************************************************** *)

lemma not_AC1_imp_ex:
     "\<not>AC1 \<Longrightarrow> \<exists>A. \<forall>f \<in> Pow(A)-{0} -> A. \<exists>u \<in> Pow(A)-{0}. f`u \<notin> u"
  unfolding AC1_def
apply (erule swap)
apply (rule allI)
apply (erule swap)
apply (rule_tac x = "\<Union>(A)" in exI)
apply (blast intro: lam_type)
done

lemma AC17_AC1_aux1:
     "\<lbrakk>\<forall>f \<in> Pow(x) - {0} -> x. \<exists>u \<in> Pow(x) - {0}. f`u\<notin>u;   
         \<exists>f \<in> Pow(x)-{0}->x.  
            x - (\<Union>a \<in> (\<mu> i. HH(\<lambda>X \<in> Pow(x)-{0}. {f`X},x,i)={x}).   
            HH(\<lambda>X \<in> Pow(x)-{0}. {f`X},x,a)) = 0\<rbrakk>  
        \<Longrightarrow> P"
apply (erule bexE)
apply (erule UN_eq_imp_well_ord [THEN exE], assumption)
apply (erule ex_choice_fun_Pow [THEN exE])
apply (erule ballE) 
apply (fast intro: apply_type del: DiffE)
apply (erule notE)
apply (rule Pi_type, assumption)
apply (blast dest: apply_type) 
done

lemma AC17_AC1_aux2:
      "\<not> (\<exists>f \<in> Pow(x)-{0}->x. x - F(f) = 0)   
       \<Longrightarrow> (\<lambda>f \<in> Pow(x)-{0}->x . x - F(f))   
           \<in> (Pow(x) -{0} -> x) -> Pow(x) - {0}"
by (fast intro!: lam_type dest!: Diff_eq_0_iff [THEN iffD1])

lemma AC17_AC1_aux3:
     "\<lbrakk>f`Z \<in> Z; Z \<in> Pow(x)-{0}\<rbrakk> 
      \<Longrightarrow> (\<lambda>X \<in> Pow(x)-{0}. {f`X})`Z \<in> Pow(Z)-{0}"
by auto

lemma AC17_AC1_aux4:
     "\<exists>f \<in> F. f`((\<lambda>f \<in> F. Q(f))`f) \<in> (\<lambda>f \<in> F. Q(f))`f   
      \<Longrightarrow> \<exists>f \<in> F. f`Q(f) \<in> Q(f)"
by simp

lemma AC17_AC1: "AC17 \<Longrightarrow> AC1"
  unfolding AC17_def
apply (rule classical)
apply (erule not_AC1_imp_ex [THEN exE])
apply (case_tac 
       "\<exists>f \<in> Pow(x)-{0} -> x. 
        x - (\<Union>a \<in> (\<mu> i. HH (\<lambda>X \<in> Pow (x) -{0}. {f`X},x,i) ={x}) . HH (\<lambda>X \<in> Pow (x) -{0}. {f`X},x,a)) = 0")
apply (erule AC17_AC1_aux1, assumption)
apply (drule AC17_AC1_aux2)
apply (erule allE)
apply (drule bspec, assumption)
apply (drule AC17_AC1_aux4)
apply (erule bexE)
apply (drule apply_type, assumption)
apply (simp add: HH_Least_eq_x del: Diff_iff ) 
apply (drule AC17_AC1_aux3, assumption) 
apply (fast dest!: subst_elem [OF _ HH_Least_eq_x [symmetric]]
                   f_subset_imp_HH_subset elim!: mem_irrefl)
done


(* **********************************************************************
    AC1 \<Longrightarrow> AC2 \<Longrightarrow> AC1
    AC1 \<Longrightarrow> AC4 \<Longrightarrow> AC3 \<Longrightarrow> AC1
    AC4 \<Longrightarrow> AC5 \<Longrightarrow> AC4
    AC1 \<longleftrightarrow> AC6
************************************************************************* *)

(* ********************************************************************** *)
(* AC1 \<Longrightarrow> AC2                                                            *)
(* ********************************************************************** *)

lemma AC1_AC2_aux1:
     "\<lbrakk>f:(\<Prod>X \<in> A. X);  B \<in> A;  0\<notin>A\<rbrakk> \<Longrightarrow> {f`B} \<subseteq> B \<inter> {f`C. C \<in> A}"
by (fast elim!: apply_type)

lemma AC1_AC2_aux2: 
        "\<lbrakk>pairwise_disjoint(A); B \<in> A; C \<in> A; D \<in> B; D \<in> C\<rbrakk> \<Longrightarrow> f`B = f`C"
by (unfold pairwise_disjoint_def, fast)

lemma AC1_AC2: "AC1 \<Longrightarrow> AC2"
  unfolding AC1_def AC2_def
apply (rule allI)
apply (rule impI)  
apply (elim asm_rl conjE allE exE impE, assumption)
apply (intro exI ballI equalityI)
prefer 2 apply (rule AC1_AC2_aux1, assumption+)
apply (fast elim!: AC1_AC2_aux2 elim: apply_type)
done


(* ********************************************************************** *)
(* AC2 \<Longrightarrow> AC1                                                            *)
(* ********************************************************************** *)

lemma AC2_AC1_aux1: "0\<notin>A \<Longrightarrow> 0 \<notin> {B*{B}. B \<in> A}"
by (fast dest!: sym [THEN Sigma_empty_iff [THEN iffD1]])

lemma AC2_AC1_aux2: "\<lbrakk>X*{X} \<inter> C = {y}; X \<in> A\<rbrakk>   
               \<Longrightarrow> (THE y. X*{X} \<inter> C = {y}): X*A"
apply (rule subst_elem [of y])
apply (blast elim!: equalityE)
apply (auto simp add: singleton_eq_iff) 
done

lemma AC2_AC1_aux3:
     "\<forall>D \<in> {E*{E}. E \<in> A}. \<exists>y. D \<inter> C = {y}   
      \<Longrightarrow> (\<lambda>x \<in> A. fst(THE z. (x*{x} \<inter> C = {z}))) \<in> (\<Prod>X \<in> A. X)"
apply (rule lam_type)
apply (drule bspec, blast)
apply (blast intro: AC2_AC1_aux2 fst_type)
done

lemma AC2_AC1: "AC2 \<Longrightarrow> AC1"
  unfolding AC1_def AC2_def pairwise_disjoint_def
apply (intro allI impI)
apply (elim allE impE)
prefer 2 apply (fast elim!: AC2_AC1_aux3) 
apply (blast intro!: AC2_AC1_aux1)
done


(* ********************************************************************** *)
(* AC1 \<Longrightarrow> AC4                                                            *)
(* ********************************************************************** *)

lemma empty_notin_images: "0 \<notin> {R``{x}. x \<in> domain(R)}"
by blast

lemma AC1_AC4: "AC1 \<Longrightarrow> AC4"
  unfolding AC1_def AC4_def
apply (intro allI impI)
apply (drule spec, drule mp [OF _ empty_notin_images]) 
apply (best intro!: lam_type elim!: apply_type)
done


(* ********************************************************************** *)
(* AC4 \<Longrightarrow> AC3                                                            *)
(* ********************************************************************** *)

lemma AC4_AC3_aux1: "f \<in> A->B \<Longrightarrow> (\<Union>z \<in> A. {z}*f`z) \<subseteq> A*\<Union>(B)"
by (fast dest!: apply_type)

lemma AC4_AC3_aux2: "domain(\<Union>z \<in> A. {z}*f(z)) = {a \<in> A. f(a)\<noteq>0}"
by blast

lemma AC4_AC3_aux3: "x \<in> A \<Longrightarrow> (\<Union>z \<in> A. {z}*f(z))``{x} = f(x)"
by fast

lemma AC4_AC3: "AC4 \<Longrightarrow> AC3"
  unfolding AC3_def AC4_def
apply (intro allI ballI)
apply (elim allE impE)
apply (erule AC4_AC3_aux1)
apply (simp add: AC4_AC3_aux2 AC4_AC3_aux3 cong add: Pi_cong)
done

(* ********************************************************************** *)
(* AC3 \<Longrightarrow> AC1                                                            *)
(* ********************************************************************** *)

lemma AC3_AC1_lemma:
     "b\<notin>A \<Longrightarrow> (\<Prod>x \<in> {a \<in> A. id(A)`a\<noteq>b}. id(A)`x) = (\<Prod>x \<in> A. x)"
apply (simp add: id_def cong add: Pi_cong)
apply (rule_tac b = A in subst_context, fast)
done

lemma AC3_AC1: "AC3 \<Longrightarrow> AC1"
  unfolding AC1_def AC3_def
apply (fast intro!: id_type elim: AC3_AC1_lemma [THEN subst])
done

(* ********************************************************************** *)
(* AC4 \<Longrightarrow> AC5                                                            *)
(* ********************************************************************** *)

lemma AC4_AC5: "AC4 \<Longrightarrow> AC5"
  unfolding range_def AC4_def AC5_def
apply (intro allI ballI)
apply (elim allE impE)
apply (erule fun_is_rel [THEN converse_type])
apply (erule exE)
apply (rename_tac g)
apply (rule_tac x=g in bexI)
apply (blast dest: apply_equality range_type) 
apply (blast intro: Pi_type dest: apply_type fun_is_rel)
done


(* ********************************************************************** *)
(* AC5 \<Longrightarrow> AC4, Rubin & Rubin, p. 11                                      *)
(* ********************************************************************** *)

lemma AC5_AC4_aux1: "R \<subseteq> A*B \<Longrightarrow> (\<lambda>x \<in> R. fst(x)) \<in> R -> A"
by (fast intro!: lam_type fst_type)

lemma AC5_AC4_aux2: "R \<subseteq> A*B \<Longrightarrow> range(\<lambda>x \<in> R. fst(x)) = domain(R)"
by (unfold lam_def, force)

lemma AC5_AC4_aux3: "\<lbrakk>\<exists>f \<in> A->C. P(f,domain(f)); A=B\<rbrakk> \<Longrightarrow>  \<exists>f \<in> B->C. P(f,B)"
apply (erule bexE)
apply (frule domain_of_fun, fast)
done

lemma AC5_AC4_aux4: "\<lbrakk>R \<subseteq> A*B; g \<in> C->R; \<forall>x \<in> C. (\<lambda>z \<in> R. fst(z))` (g`x) = x\<rbrakk>  
                \<Longrightarrow> (\<lambda>x \<in> C. snd(g`x)): (\<Prod>x \<in> C. R``{x})"
apply (rule lam_type)
apply (force dest: apply_type)
done

lemma AC5_AC4: "AC5 \<Longrightarrow> AC4"
apply (unfold AC4_def AC5_def, clarify)
apply (elim allE ballE)
apply (drule AC5_AC4_aux3 [OF _ AC5_AC4_aux2], assumption)
apply (fast elim!: AC5_AC4_aux4)
apply (blast intro: AC5_AC4_aux1) 
done


(* ********************************************************************** *)
(* AC1 \<longleftrightarrow> AC6                                                            *)
(* ********************************************************************** *)

lemma AC1_iff_AC6: "AC1 \<longleftrightarrow> AC6"
by (unfold AC1_def AC6_def, blast)

end
