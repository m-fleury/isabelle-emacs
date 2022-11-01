(*  Title:      ZF/AC/AC16_lemmas.thy
    Author:     Krzysztof Grabczewski

Lemmas used in the proofs concerning AC16
*)

theory AC16_lemmas
imports AC_Equiv Hartog Cardinal_aux
begin

lemma cons_Diff_eq: "a\<notin>A \<Longrightarrow> cons(a,A)-{a}=A"
by fast

lemma nat_1_lepoll_iff: "1\<lesssim>X \<longleftrightarrow> (\<exists>x. x \<in> X)"
  unfolding lepoll_def
apply (rule iffI)
apply (fast intro: inj_is_fun [THEN apply_type])
apply (erule exE)
apply (rule_tac x = "\<lambda>a \<in> 1. x" in exI)
apply (fast intro!: lam_injective)
done

lemma eqpoll_1_iff_singleton: "X\<approx>1 \<longleftrightarrow> (\<exists>x. X={x})"
apply (rule iffI)
apply (erule eqpollE)
apply (drule nat_1_lepoll_iff [THEN iffD1])
apply (fast intro!: lepoll_1_is_sing)
apply (fast intro!: singleton_eqpoll_1)
done

lemma cons_eqpoll_succ: "\<lbrakk>x\<approx>n; y\<notin>x\<rbrakk> \<Longrightarrow> cons(y,x)\<approx>succ(n)"
  unfolding succ_def
apply (fast elim!: cons_eqpoll_cong mem_irrefl)
done

lemma subsets_eqpoll_1_eq: "{Y \<in> Pow(X). Y\<approx>1} = {{x}. x \<in> X}"
apply (rule equalityI)
apply (rule subsetI)
apply (erule CollectE)
apply (drule eqpoll_1_iff_singleton [THEN iffD1])
apply (fast intro!: RepFunI)
apply (rule subsetI)
apply (erule RepFunE)
apply (rule CollectI, fast)
apply (fast intro!: singleton_eqpoll_1)
done

lemma eqpoll_RepFun_sing: "X\<approx>{{x}. x \<in> X}"
  unfolding eqpoll_def bij_def
apply (rule_tac x = "\<lambda>x \<in> X. {x}" in exI)
apply (rule IntI)
apply (unfold inj_def surj_def, simp)
apply (fast intro!: lam_type RepFunI intro: singleton_eq_iff [THEN iffD1], simp)
apply (fast intro!: lam_type)
done

lemma subsets_eqpoll_1_eqpoll: "{Y \<in> Pow(X). Y\<approx>1}\<approx>X"
apply (rule subsets_eqpoll_1_eq [THEN ssubst])
apply (rule eqpoll_RepFun_sing [THEN eqpoll_sym])
done

lemma InfCard_Least_in:
     "\<lbrakk>InfCard(x); y \<subseteq> x; y \<approx> succ(z)\<rbrakk> \<Longrightarrow> (\<mu> i. i \<in> y) \<in> y"
apply (erule eqpoll_sym [THEN eqpoll_imp_lepoll, 
                         THEN succ_lepoll_imp_not_empty, THEN not_emptyE])
apply (fast intro: LeastI 
            dest!: InfCard_is_Card [THEN Card_is_Ord] 
            elim: Ord_in_Ord)
done

lemma subsets_lepoll_lemma1:
     "\<lbrakk>InfCard(x); n \<in> nat\<rbrakk> 
      \<Longrightarrow> {y \<in> Pow(x). y\<approx>succ(succ(n))} \<lesssim> x*{y \<in> Pow(x). y\<approx>succ(n)}"
  unfolding lepoll_def
apply (rule_tac x = "\<lambda>y \<in> {y \<in> Pow(x) . y\<approx>succ (succ (n))}. 
                      <\<mu> i. i \<in> y, y-{\<mu> i. i \<in> y}>" in exI)
apply (rule_tac d = "\<lambda>z. cons (fst(z), snd(z))" in lam_injective)
 apply (blast intro!: Diff_sing_eqpoll intro: InfCard_Least_in)
apply (simp, blast intro: InfCard_Least_in)
done

lemma set_of_Ord_succ_Union: "(\<forall>y \<in> z. Ord(y)) \<Longrightarrow> z \<subseteq> succ(\<Union>(z))"
apply (rule subsetI)
apply (case_tac "\<forall>y \<in> z. y \<subseteq> x", blast )
apply (simp, erule bexE) 
apply (rule_tac i=y and j=x in Ord_linear_le)
apply (blast dest: le_imp_subset elim: leE ltE)+
done

lemma subset_not_mem: "j \<subseteq> i \<Longrightarrow> i \<notin> j"
by (fast elim!: mem_irrefl)

lemma succ_Union_not_mem:
     "(\<And>y. y \<in> z \<Longrightarrow> Ord(y)) \<Longrightarrow> succ(\<Union>(z)) \<notin> z"
apply (rule set_of_Ord_succ_Union [THEN subset_not_mem], blast)
done

lemma Union_cons_eq_succ_Union:
     "\<Union>(cons(succ(\<Union>(z)),z)) = succ(\<Union>(z))"
by fast

lemma Un_Ord_disj: "\<lbrakk>Ord(i); Ord(j)\<rbrakk> \<Longrightarrow> i \<union> j = i | i \<union> j = j"
by (fast dest!: le_imp_subset elim: Ord_linear_le)

lemma Union_eq_Un: "x \<in> X \<Longrightarrow> \<Union>(X) = x \<union> \<Union>(X-{x})"
by fast

lemma Union_in_lemma [rule_format]:
     "n \<in> nat \<Longrightarrow> \<forall>z. (\<forall>y \<in> z. Ord(y)) \<and> z\<approx>n \<and> z\<noteq>0 \<longrightarrow> \<Union>(z) \<in> z"
apply (induct_tac "n")
apply (fast dest!: eqpoll_imp_lepoll [THEN lepoll_0_is_0])
apply (intro allI impI)
apply (erule natE)
apply (fast dest!: eqpoll_1_iff_singleton [THEN iffD1]
            intro!: Union_singleton, clarify) 
apply (elim not_emptyE)
apply (erule_tac x = "z-{xb}" in allE)
apply (erule impE)
apply (fast elim!: Diff_sing_eqpoll
                   Diff_sing_eqpoll [THEN eqpoll_succ_imp_not_empty])
apply (subgoal_tac "xb \<union> \<Union>(z - {xb}) \<in> z")
apply (simp add: Union_eq_Un [symmetric])
apply (frule bspec, assumption)
apply (drule bspec) 
apply (erule Diff_subset [THEN subsetD])
apply (drule Un_Ord_disj, assumption, auto) 
done

lemma Union_in: "\<lbrakk>\<forall>x \<in> z. Ord(x); z\<approx>n; z\<noteq>0; n \<in> nat\<rbrakk> \<Longrightarrow> \<Union>(z) \<in> z"
by (blast intro: Union_in_lemma)

lemma succ_Union_in_x:
     "\<lbrakk>InfCard(x); z \<in> Pow(x); z\<approx>n; n \<in> nat\<rbrakk> \<Longrightarrow> succ(\<Union>(z)) \<in> x"
apply (rule Limit_has_succ [THEN ltE])
prefer 3 apply assumption
apply (erule InfCard_is_Limit)
apply (case_tac "z=0")
apply (simp, fast intro!: InfCard_is_Limit [THEN Limit_has_0])
apply (rule ltI [OF PowD [THEN subsetD] InfCard_is_Card [THEN Card_is_Ord]], assumption)
apply (blast intro: Union_in
                    InfCard_is_Card [THEN Card_is_Ord, THEN Ord_in_Ord])+
done

lemma succ_lepoll_succ_succ:
     "\<lbrakk>InfCard(x); n \<in> nat\<rbrakk> 
      \<Longrightarrow> {y \<in> Pow(x). y\<approx>succ(n)} \<lesssim> {y \<in> Pow(x). y\<approx>succ(succ(n))}"
  unfolding lepoll_def
apply (rule_tac x = "\<lambda>z \<in> {y\<in>Pow(x). y\<approx>succ(n)}. cons(succ(\<Union>(z)), z)" 
       in exI)
apply (rule_tac d = "\<lambda>z. z-{\<Union>(z) }" in lam_injective)
apply (blast intro!: succ_Union_in_x succ_Union_not_mem
             intro: cons_eqpoll_succ Ord_in_Ord
             dest!: InfCard_is_Card [THEN Card_is_Ord])
apply (simp only: Union_cons_eq_succ_Union) 
apply (rule cons_Diff_eq)
apply (fast dest!: InfCard_is_Card [THEN Card_is_Ord]
            elim: Ord_in_Ord 
            intro!: succ_Union_not_mem)
done

lemma subsets_eqpoll_X:
     "\<lbrakk>InfCard(X); n \<in> nat\<rbrakk> \<Longrightarrow> {Y \<in> Pow(X). Y\<approx>succ(n)} \<approx> X"
apply (induct_tac "n")
apply (rule subsets_eqpoll_1_eqpoll)
apply (rule eqpollI)
apply (rule subsets_lepoll_lemma1 [THEN lepoll_trans], assumption+)
apply (rule eqpoll_trans [THEN eqpoll_imp_lepoll]) 
 apply (erule eqpoll_refl [THEN prod_eqpoll_cong])
apply (erule InfCard_square_eqpoll)
apply (fast elim: eqpoll_sym [THEN eqpoll_imp_lepoll, THEN lepoll_trans] 
            intro!: succ_lepoll_succ_succ)
done

lemma image_vimage_eq:
     "\<lbrakk>f \<in> surj(A,B); y \<subseteq> B\<rbrakk> \<Longrightarrow> f``(converse(f)``y) = y"
  unfolding surj_def
apply (fast dest: apply_equality2 elim: apply_iff [THEN iffD2])
done

lemma vimage_image_eq: "\<lbrakk>f \<in> inj(A,B); y \<subseteq> A\<rbrakk> \<Longrightarrow> converse(f)``(f``y) = y"
by (fast elim!: inj_is_fun [THEN apply_Pair] dest: inj_equality)

lemma subsets_eqpoll:
     "A\<approx>B \<Longrightarrow> {Y \<in> Pow(A). Y\<approx>n}\<approx>{Y \<in> Pow(B). Y\<approx>n}"
  unfolding eqpoll_def
apply (erule exE)
apply (rule_tac x = "\<lambda>X \<in> {Y \<in> Pow (A) . \<exists>f. f \<in> bij (Y, n) }. f``X" in exI)
apply (rule_tac d = "\<lambda>Z. converse (f) ``Z" in lam_bijective)
apply (fast intro!: bij_is_inj [THEN restrict_bij, THEN bij_converse_bij, 
                                THEN comp_bij] 
            elim!: bij_is_fun [THEN fun_is_rel, THEN image_subset])
apply (blast intro!:  bij_is_inj [THEN restrict_bij] 
                      comp_bij bij_converse_bij
                      bij_is_fun [THEN fun_is_rel, THEN image_subset])
apply (fast elim!: bij_is_inj [THEN vimage_image_eq])
apply (fast elim!: bij_is_surj [THEN image_vimage_eq])
done

lemma WO2_imp_ex_Card: "WO2 \<Longrightarrow> \<exists>a. Card(a) \<and> X\<approx>a"
  unfolding WO2_def
apply (drule spec [of _ X])
apply (blast intro: Card_cardinal eqpoll_trans
          well_ord_Memrel [THEN well_ord_cardinal_eqpoll, THEN eqpoll_sym])
done

lemma lepoll_infinite: "\<lbrakk>X\<lesssim>Y; \<not>Finite(X)\<rbrakk> \<Longrightarrow> \<not>Finite(Y)"
by (blast intro: lepoll_Finite)

lemma infinite_Card_is_InfCard: "\<lbrakk>\<not>Finite(X); Card(X)\<rbrakk> \<Longrightarrow> InfCard(X)"
  unfolding InfCard_def
apply (fast elim!: Card_is_Ord [THEN nat_le_infinite_Ord])
done

lemma WO2_infinite_subsets_eqpoll_X: "\<lbrakk>WO2; n \<in> nat; \<not>Finite(X)\<rbrakk>   
        \<Longrightarrow> {Y \<in> Pow(X). Y\<approx>succ(n)}\<approx>X"
apply (drule WO2_imp_ex_Card)
apply (elim allE exE conjE)
apply (frule eqpoll_imp_lepoll [THEN lepoll_infinite], assumption)
apply (drule infinite_Card_is_InfCard, assumption)
apply (blast intro: subsets_eqpoll subsets_eqpoll_X eqpoll_sym eqpoll_trans) 
done

lemma well_ord_imp_ex_Card: "well_ord(X,R) \<Longrightarrow> \<exists>a. Card(a) \<and> X\<approx>a"
by (fast elim!: well_ord_cardinal_eqpoll [THEN eqpoll_sym] 
         intro!: Card_cardinal)

lemma well_ord_infinite_subsets_eqpoll_X:
     "\<lbrakk>well_ord(X,R); n \<in> nat; \<not>Finite(X)\<rbrakk> \<Longrightarrow> {Y \<in> Pow(X). Y\<approx>succ(n)}\<approx>X"
apply (drule well_ord_imp_ex_Card)
apply (elim allE exE conjE)
apply (frule eqpoll_imp_lepoll [THEN lepoll_infinite], assumption)
apply (drule infinite_Card_is_InfCard, assumption)
apply (blast intro: subsets_eqpoll subsets_eqpoll_X eqpoll_sym eqpoll_trans) 
done

end
