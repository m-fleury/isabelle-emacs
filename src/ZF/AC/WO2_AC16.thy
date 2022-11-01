(*  Title:      ZF/AC/WO2_AC16.thy
    Author:     Krzysztof Grabczewski

The proof of WO2 \<Longrightarrow> AC16(k #+ m, k)
  
The main part of the proof is the inductive reasoning concerning
properties of constructed family T_gamma.
The proof deals with three cases for ordinals: 0, succ and limit ordinal.
The first instance is trivial, the third not difficult, but the second
is very complicated requiring many lemmas.
We also need to prove that at any stage gamma the set 
(s - \<Union>(...) - k_gamma)   (Rubin & Rubin page 15)
contains m distinct elements (in fact is equipollent to s)
*)

theory WO2_AC16 imports AC_Equiv AC16_lemmas Cardinal_aux begin

(**** A recursive definition used in the proof of WO2 \<Longrightarrow> AC16 ****)

definition
  recfunAC16 :: "[i,i,i,i] \<Rightarrow> i"  where
    "recfunAC16(f,h,i,a) \<equiv> 
         transrec2(i, 0, 
              \<lambda>g r. if (\<exists>y \<in> r. h`g \<subseteq> y) then r
                    else r \<union> {f`(\<mu> i. h`g \<subseteq> f`i \<and> 
                         (\<forall>b<a. (h`b \<subseteq> f`i \<longrightarrow> (\<forall>t \<in> r. \<not> h`b \<subseteq> t))))})"

(* ********************************************************************** *)
(* Basic properties of recfunAC16                                         *)
(* ********************************************************************** *)

lemma recfunAC16_0: "recfunAC16(f,h,0,a) = 0"
by (simp add: recfunAC16_def)

lemma recfunAC16_succ: 
     "recfunAC16(f,h,succ(i),a) =   
      (if (\<exists>y \<in> recfunAC16(f,h,i,a). h ` i \<subseteq> y) then recfunAC16(f,h,i,a)  
       else recfunAC16(f,h,i,a) \<union>  
            {f ` (\<mu> j. h ` i \<subseteq> f ` j \<and>   
             (\<forall>b<a. (h`b \<subseteq> f`j   
              \<longrightarrow> (\<forall>t \<in> recfunAC16(f,h,i,a). \<not> h`b \<subseteq> t))))})"
apply (simp add: recfunAC16_def)
done

lemma recfunAC16_Limit: "Limit(i)   
        \<Longrightarrow> recfunAC16(f,h,i,a) = (\<Union>j<i. recfunAC16(f,h,j,a))"
by (simp add: recfunAC16_def transrec2_Limit)

(* ********************************************************************** *)
(* Monotonicity of transrec2                                              *)
(* ********************************************************************** *)

lemma transrec2_mono_lemma [rule_format]:
     "\<lbrakk>\<And>g r. r \<subseteq> B(g,r);  Ord(i)\<rbrakk>   
      \<Longrightarrow> j<i \<longrightarrow> transrec2(j, 0, B) \<subseteq> transrec2(i, 0, B)"
apply (erule trans_induct)
apply (rule Ord_cases, assumption+, fast)
apply (simp (no_asm_simp))
apply (blast elim!: leE) 
apply (simp add: transrec2_Limit) 
apply (blast intro: OUN_I ltI Ord_in_Ord [THEN le_refl]
             elim!: Limit_has_succ [THEN ltE])
done

lemma transrec2_mono:
     "\<lbrakk>\<And>g r. r \<subseteq> B(g,r); j\<le>i\<rbrakk> 
      \<Longrightarrow> transrec2(j, 0, B) \<subseteq> transrec2(i, 0, B)"
apply (erule leE)
apply (rule transrec2_mono_lemma)
apply (auto intro: lt_Ord2 ) 
done

(* ********************************************************************** *)
(* Monotonicity of recfunAC16                                             *)
(* ********************************************************************** *)

lemma recfunAC16_mono: 
       "i\<le>j \<Longrightarrow> recfunAC16(f, g, i, a) \<subseteq> recfunAC16(f, g, j, a)"
  unfolding recfunAC16_def
apply (rule transrec2_mono, auto) 
done

(* ********************************************************************** *)
(* case of limit ordinal                                                  *)
(* ********************************************************************** *)


lemma lemma3_1:
    "\<lbrakk>\<forall>y<x. \<forall>z<a. z<y | (\<exists>Y \<in> F(y). f(z)<=Y) \<longrightarrow> (\<exists>! Y. Y \<in> F(y) \<and> f(z)<=Y);
        \<forall>i j. i\<le>j \<longrightarrow> F(i) \<subseteq> F(j); j\<le>i; i<x; z<a;
        V \<in> F(i); f(z)<=V; W \<in> F(j); f(z)<=W\<rbrakk>   
     \<Longrightarrow> V = W"
apply (erule asm_rl allE impE)+
apply (drule subsetD, assumption, blast) 
done


lemma lemma3:
    "\<lbrakk>\<forall>y<x. \<forall>z<a. z<y | (\<exists>Y \<in> F(y). f(z)<=Y) \<longrightarrow> (\<exists>! Y. Y \<in> F(y) \<and> f(z)<=Y);
        \<forall>i j. i\<le>j \<longrightarrow> F(i) \<subseteq> F(j); i<x; j<x; z<a;   
        V \<in> F(i); f(z)<=V; W \<in> F(j); f(z)<=W\<rbrakk>   
     \<Longrightarrow> V = W"
apply (rule_tac j=j in Ord_linear_le [OF lt_Ord lt_Ord], assumption+)
apply (erule lemma3_1 [symmetric], assumption+)
apply (erule lemma3_1, assumption+)
done

lemma lemma4:
     "\<lbrakk>\<forall>y<x. F(y) \<subseteq> X \<and>   
                (\<forall>x<a. x < y | (\<exists>Y \<in> F(y). h(x) \<subseteq> Y) \<longrightarrow>   
                 (\<exists>! Y. Y \<in> F(y) \<and> h(x) \<subseteq> Y)); 
         x < a\<rbrakk>   
      \<Longrightarrow> \<forall>y<x. \<forall>z<a. z < y | (\<exists>Y \<in> F(y). h(z) \<subseteq> Y) \<longrightarrow>   
                       (\<exists>! Y. Y \<in> F(y) \<and> h(z) \<subseteq> Y)"
apply (intro oallI impI)
apply (drule ospec, assumption, clarify)
apply (blast elim!: oallE ) 
done

lemma lemma5:
     "\<lbrakk>\<forall>y<x. F(y) \<subseteq> X \<and>   
               (\<forall>x<a. x < y | (\<exists>Y \<in> F(y). h(x) \<subseteq> Y) \<longrightarrow>   
                (\<exists>! Y. Y \<in> F(y) \<and> h(x) \<subseteq> Y));  
         x < a; Limit(x); \<forall>i j. i\<le>j \<longrightarrow> F(i) \<subseteq> F(j)\<rbrakk>   
      \<Longrightarrow> (\<Union>x<x. F(x)) \<subseteq> X \<and>   
          (\<forall>xa<a. xa < x | (\<exists>x \<in> \<Union>x<x. F(x). h(xa) \<subseteq> x)   
                \<longrightarrow> (\<exists>! Y. Y \<in> (\<Union>x<x. F(x)) \<and> h(xa) \<subseteq> Y))"
apply (rule conjI)
apply (rule subsetI)
apply (erule OUN_E)
apply (drule ospec, assumption, fast)
apply (drule lemma4, assumption)
apply (rule oallI)
apply (rule impI)
apply (erule disjE)
apply (frule ospec, erule Limit_has_succ, assumption) 
apply (drule_tac A = a and x = xa in ospec, assumption)
apply (erule impE, rule le_refl [THEN disjI1], erule lt_Ord) 
apply (blast intro: lemma3 Limit_has_succ) 
apply (blast intro: lemma3) 
done

(* ********************************************************************** *)
(* case of successor ordinal                                              *)
(* ********************************************************************** *)

(*
  First quite complicated proof of the fact used in the recursive construction
  of the family T_gamma (WO2 \<Longrightarrow> AC16(k #+ m, k)) - the fact that at any stage
  gamma the set (s - \<Union>(...) - k_gamma) is equipollent to s
  (Rubin & Rubin page 15).
*)

(* ********************************************************************** *)
(* dbl_Diff_eqpoll_Card                                                   *)
(* ********************************************************************** *)


lemma dbl_Diff_eqpoll_Card:
      "\<lbrakk>A\<approx>a; Card(a); \<not>Finite(a); B\<prec>a; C\<prec>a\<rbrakk> \<Longrightarrow> A - B - C\<approx>a"
by (blast intro: Diff_lesspoll_eqpoll_Card) 

(* ********************************************************************** *)
(* Case of finite ordinals                                                *)
(* ********************************************************************** *)


lemma Finite_lesspoll_infinite_Ord: 
      "\<lbrakk>Finite(X); \<not>Finite(a); Ord(a)\<rbrakk> \<Longrightarrow> X\<prec>a"
  unfolding lesspoll_def
apply (rule conjI)
apply (drule nat_le_infinite_Ord [THEN le_imp_lepoll], assumption)
  unfolding Finite_def
apply (blast intro: leI [THEN le_imp_subset, THEN subset_imp_lepoll]
                    ltI eqpoll_imp_lepoll lepoll_trans) 
apply (blast intro: eqpoll_sym [THEN eqpoll_trans])
done

lemma Union_lesspoll:
     "\<lbrakk>\<forall>x \<in> X. x \<lesssim> n \<and> x \<subseteq> T; well_ord(T, R); X \<lesssim> b;   
         b<a; \<not>Finite(a); Card(a); n \<in> nat\<rbrakk>   
      \<Longrightarrow> \<Union>(X)\<prec>a"
apply (case_tac "Finite (X)")
apply (blast intro: Card_is_Ord Finite_lesspoll_infinite_Ord 
                    lepoll_nat_imp_Finite Finite_Union)
apply (drule lepoll_imp_ex_le_eqpoll) 
apply (erule lt_Ord) 
apply (elim exE conjE)
apply (frule eqpoll_imp_lepoll [THEN lepoll_infinite], assumption)
apply (erule eqpoll_sym [THEN eqpoll_def [THEN def_imp_iff, THEN iffD1],
                         THEN exE])
apply (frule bij_is_surj [THEN surj_image_eq])
apply (drule image_fun [OF bij_is_fun subset_refl])
apply (drule sym [THEN trans], assumption)
apply (blast intro: lt_Ord UN_lepoll lt_Card_imp_lesspoll
                    lt_trans1 lesspoll_trans1)
done

(* ********************************************************************** *)
(* recfunAC16_lepoll_index                                                *)
(* ********************************************************************** *)

lemma Un_sing_eq_cons: "A \<union> {a} = cons(a, A)"
by fast

lemma Un_lepoll_succ: "A \<lesssim> B \<Longrightarrow> A \<union> {a} \<lesssim> succ(B)"
apply (simp add: Un_sing_eq_cons succ_def)
apply (blast elim!: mem_irrefl intro: cons_lepoll_cong)
done

lemma Diff_UN_succ_empty: "Ord(a) \<Longrightarrow> F(a) - (\<Union>b<succ(a). F(b)) = 0"
by (fast intro!: le_refl)

lemma Diff_UN_succ_subset: "Ord(a) \<Longrightarrow> F(a) \<union> X - (\<Union>b<succ(a). F(b)) \<subseteq> X"
by blast

lemma recfunAC16_Diff_lepoll_1:
     "Ord(x) 
      \<Longrightarrow> recfunAC16(f, g, x, a) - (\<Union>i<x. recfunAC16(f, g, i, a)) \<lesssim> 1"
apply (erule Ord_cases)
  apply (simp add: recfunAC16_0 empty_subsetI [THEN subset_imp_lepoll])
(*Limit case*)
prefer 2 apply (simp add: recfunAC16_Limit Diff_cancel 
                          empty_subsetI [THEN subset_imp_lepoll])
(*succ case*)
apply (simp add: recfunAC16_succ
                 Diff_UN_succ_empty [of _ "\<lambda>j. recfunAC16(f,g,j,a)"]
                 empty_subsetI [THEN subset_imp_lepoll])
apply (best intro: Diff_UN_succ_subset [THEN subset_imp_lepoll]
                   singleton_eqpoll_1 [THEN eqpoll_imp_lepoll] lepoll_trans)
done

lemma in_Least_Diff:
     "\<lbrakk>z \<in> F(x); Ord(x)\<rbrakk>   
      \<Longrightarrow> z \<in> F(\<mu> i. z \<in> F(i)) - (\<Union>j<(\<mu> i. z \<in> F(i)). F(j))"
by (fast elim: less_LeastE elim!: LeastI)

lemma Least_eq_imp_ex:
     "\<lbrakk>(\<mu> i. w \<in> F(i)) = (\<mu> i. z \<in> F(i));   
         w \<in> (\<Union>i<a. F(i)); z \<in> (\<Union>i<a. F(i))\<rbrakk>   
      \<Longrightarrow> \<exists>b<a. w \<in> (F(b) - (\<Union>c<b. F(c))) \<and> z \<in> (F(b) - (\<Union>c<b. F(c)))"
apply (elim OUN_E)
apply (drule in_Least_Diff, erule lt_Ord) 
apply (frule in_Least_Diff, erule lt_Ord) 
apply (rule oexI, force) 
apply (blast intro: lt_Ord Least_le [THEN lt_trans1]) 
done


lemma two_in_lepoll_1: "\<lbrakk>A \<lesssim> 1; a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a=b"
by (fast dest!: lepoll_1_is_sing)


lemma UN_lepoll_index:
     "\<lbrakk>\<forall>i<a. F(i)-(\<Union>j<i. F(j)) \<lesssim> 1; Limit(a)\<rbrakk>   
      \<Longrightarrow> (\<Union>x<a. F(x)) \<lesssim> a"
apply (rule lepoll_def [THEN def_imp_iff [THEN iffD2]])
apply (rule_tac x = "\<lambda>z \<in> (\<Union>x<a. F (x)). \<mu> i. z \<in> F (i) " in exI)
  unfolding inj_def
apply (rule CollectI)
apply (rule lam_type)
apply (erule OUN_E)
apply (erule Least_in_Ord)
apply (erule ltD)
apply (erule lt_Ord2)
apply (intro ballI)
apply (simp (no_asm_simp))
apply (rule impI)
apply (drule Least_eq_imp_ex, assumption+)
apply (fast elim!: two_in_lepoll_1)
done


lemma recfunAC16_lepoll_index: "Ord(y) \<Longrightarrow> recfunAC16(f, h, y, a) \<lesssim> y"
apply (erule trans_induct3)
(*0 case*)
apply (simp (no_asm_simp) add: recfunAC16_0 lepoll_refl)
(*succ case*)
apply (simp (no_asm_simp) add: recfunAC16_succ)
apply (blast dest!: succI1 [THEN rev_bspec] 
             intro: subset_succI [THEN subset_imp_lepoll] Un_lepoll_succ  
                    lepoll_trans)
apply (simp (no_asm_simp) add: recfunAC16_Limit)
apply (blast intro: lt_Ord [THEN recfunAC16_Diff_lepoll_1] UN_lepoll_index)
done


lemma Union_recfunAC16_lesspoll:
     "\<lbrakk>recfunAC16(f,g,y,a) \<subseteq> {X \<in> Pow(A). X\<approx>n};   
         A\<approx>a;  y<a;  \<not>Finite(a);  Card(a);  n \<in> nat\<rbrakk>   
      \<Longrightarrow> \<Union>(recfunAC16(f,g,y,a))\<prec>a"
apply (erule eqpoll_def [THEN def_imp_iff, THEN iffD1, THEN exE])
apply (rule_tac T=A in Union_lesspoll, simp_all)
apply (blast intro!: eqpoll_imp_lepoll)
apply (blast intro: bij_is_inj Card_is_Ord [THEN well_ord_Memrel]
                    well_ord_rvimage)
apply (erule lt_Ord [THEN recfunAC16_lepoll_index])
done

lemma dbl_Diff_eqpoll:
     "\<lbrakk>recfunAC16(f, h, y, a) \<subseteq> {X \<in> Pow(A) . X\<approx>succ(k #+ m)};   
         Card(a); \<not> Finite(a); A\<approx>a;   
         k \<in> nat;  y<a;   
         h \<in> bij(a, {Y \<in> Pow(A). Y\<approx>succ(k)})\<rbrakk>   
      \<Longrightarrow> A - \<Union>(recfunAC16(f, h, y, a)) - h`y\<approx>a"
apply (rule dbl_Diff_eqpoll_Card, simp_all)
apply (simp add: Union_recfunAC16_lesspoll)
apply (rule Finite_lesspoll_infinite_Ord) 
apply (rule Finite_def [THEN def_imp_iff, THEN iffD2]) 
apply (blast dest: ltD bij_is_fun [THEN apply_type], assumption)  
apply (blast intro: Card_is_Ord) 
done

(* back to the proof *)

lemmas disj_Un_eqpoll_nat_sum = 
    eqpoll_trans [THEN eqpoll_trans, 
                  OF disj_Un_eqpoll_sum sum_eqpoll_cong nat_sum_eqpoll_sum]


lemma Un_in_Collect: "\<lbrakk>x \<in> Pow(A - B - h`i); x\<approx>m;   
        h \<in> bij(a, {x \<in> Pow(A) . x\<approx>k}); i<a; k \<in> nat; m \<in> nat\<rbrakk>   
        \<Longrightarrow> h ` i \<union> x \<in> {x \<in> Pow(A) . x\<approx>k #+ m}"
by (blast intro: disj_Un_eqpoll_nat_sum
          dest:  ltD bij_is_fun [THEN apply_type])


(* ********************************************************************** *)
(* Lemmas simplifying assumptions                                         *)
(* ********************************************************************** *)

lemma lemma6:
     "\<lbrakk>\<forall>y<succ(j). F(y)<=X \<and> (\<forall>x<a. x<y | P(x,y) \<longrightarrow> Q(x,y)); succ(j)<a\<rbrakk>
      \<Longrightarrow> F(j)<=X \<and> (\<forall>x<a. x<j | P(x,j) \<longrightarrow> Q(x,j))"
by (blast intro!: lt_Ord succI1 [THEN ltI, THEN lt_Ord, THEN le_refl]) 


lemma lemma7:
     "\<lbrakk>\<forall>x<a. x<j | P(x,j) \<longrightarrow> Q(x,j);  succ(j)<a\<rbrakk>   
      \<Longrightarrow> P(j,j) \<longrightarrow> (\<forall>x<a. x\<le>j | P(x,j) \<longrightarrow> Q(x,j))"
by (fast elim!: leE)

(* ********************************************************************** *)
(* Lemmas needed to prove ex_next_set, which means that for any successor *)
(* ordinal there is a set satisfying certain properties                   *)
(* ********************************************************************** *)

lemma ex_subset_eqpoll:
     "\<lbrakk>A\<approx>a; \<not> Finite(a); Ord(a); m \<in> nat\<rbrakk> \<Longrightarrow> \<exists>X \<in> Pow(A). X\<approx>m"
apply (rule lepoll_imp_eqpoll_subset [of m A, THEN exE]) 
 apply (rule lepoll_trans, rule leI [THEN le_imp_lepoll])
  apply (blast intro: lt_trans2 [OF ltI nat_le_infinite_Ord] Ord_nat)
apply (erule eqpoll_sym [THEN eqpoll_imp_lepoll]) 
apply (fast elim!: eqpoll_sym)
done

lemma subset_Un_disjoint: "\<lbrakk>A \<subseteq> B \<union> C; A \<inter> C = 0\<rbrakk> \<Longrightarrow> A \<subseteq> B"
by blast


lemma Int_empty:
     "\<lbrakk>X \<in> Pow(A - \<Union>(B) -C); T \<in> B; F \<subseteq> T\<rbrakk> \<Longrightarrow> F \<inter> X = 0"
by blast


(* ********************************************************************** *)
(* equipollent subset (and finite) is the whole set                       *)
(* ********************************************************************** *)


lemma subset_imp_eq_lemma:
     "m \<in> nat \<Longrightarrow> \<forall>A B. A \<subseteq> B \<and> m \<lesssim> A \<and> B \<lesssim> m \<longrightarrow> A=B"
apply (induct_tac "m")
apply (fast dest!: lepoll_0_is_0)
apply (intro allI impI)
apply (elim conjE)
apply (rule succ_lepoll_imp_not_empty [THEN not_emptyE], assumption)
apply (frule subsetD [THEN Diff_sing_lepoll], assumption+)
apply (frule lepoll_Diff_sing)
apply (erule allE impE)+
apply (rule conjI)
prefer 2 apply fast
apply fast
apply (blast elim: equalityE) 
done


lemma subset_imp_eq: "\<lbrakk>A \<subseteq> B; m \<lesssim> A; B \<lesssim> m; m \<in> nat\<rbrakk> \<Longrightarrow> A=B"
by (blast dest!: subset_imp_eq_lemma)


lemma bij_imp_arg_eq:
     "\<lbrakk>f \<in> bij(a, {Y \<in> X. Y\<approx>succ(k)}); k \<in> nat; f`b \<subseteq> f`y; b<a; y<a\<rbrakk> 
      \<Longrightarrow> b=y"
apply (drule subset_imp_eq)
apply (erule_tac [3] nat_succI)
  unfolding bij_def inj_def
apply (blast intro: eqpoll_sym eqpoll_imp_lepoll
             dest:  ltD apply_type)+
done


lemma ex_next_set:
     "\<lbrakk>recfunAC16(f, h, y, a) \<subseteq> {X \<in> Pow(A) . X\<approx>succ(k #+ m)};   
         Card(a); \<not> Finite(a); A\<approx>a;   
         k \<in> nat; m \<in> nat; y<a;   
         h \<in> bij(a, {Y \<in> Pow(A). Y\<approx>succ(k)});   
         \<not> (\<exists>Y \<in> recfunAC16(f, h, y, a). h`y \<subseteq> Y)\<rbrakk>   
      \<Longrightarrow> \<exists>X \<in> {Y \<in> Pow(A). Y\<approx>succ(k #+ m)}. h`y \<subseteq> X \<and>   
                (\<forall>b<a. h`b \<subseteq> X \<longrightarrow>   
                (\<forall>T \<in> recfunAC16(f, h, y, a). \<not> h`b \<subseteq> T))"
apply (erule_tac m1=m in dbl_Diff_eqpoll [THEN ex_subset_eqpoll, THEN bexE], 
       assumption+)
apply (erule Card_is_Ord, assumption)
apply (frule Un_in_Collect, (erule asm_rl nat_succI)+) 
apply (erule CollectE)
apply (rule rev_bexI, simp)
apply (rule conjI, blast) 
apply (intro ballI impI oallI notI)
apply (drule subset_Un_disjoint, rule Int_empty, assumption+)
apply (blast dest: bij_imp_arg_eq) 
done

(* ********************************************************************** *)
(* Lemma ex_next_Ord states that for any successor                        *)
(* ordinal there is a number of the set satisfying certain properties     *)
(* ********************************************************************** *)

lemma ex_next_Ord:
     "\<lbrakk>recfunAC16(f, h, y, a) \<subseteq> {X \<in> Pow(A) . X\<approx>succ(k #+ m)};   
         Card(a); \<not> Finite(a); A\<approx>a;   
         k \<in> nat; m \<in> nat; y<a;   
         h \<in> bij(a, {Y \<in> Pow(A). Y\<approx>succ(k)});   
         f \<in> bij(a, {Y \<in> Pow(A). Y\<approx>succ(k #+ m)});   
         \<not> (\<exists>Y \<in> recfunAC16(f, h, y, a). h`y \<subseteq> Y)\<rbrakk>   
      \<Longrightarrow> \<exists>c<a. h`y \<subseteq> f`c \<and>   
                (\<forall>b<a. h`b \<subseteq> f`c \<longrightarrow>   
                (\<forall>T \<in> recfunAC16(f, h, y, a). \<not> h`b \<subseteq> T))"
apply (drule ex_next_set, assumption+)
apply (erule bexE)
apply (rule_tac x="converse(f)`X" in oexI)
apply (simp add: right_inverse_bij)
apply (blast intro: bij_converse_bij bij_is_fun [THEN apply_type] ltI
                    Card_is_Ord)
done


(* ********************************************************************** *)
(* Lemma simplifying assumptions                                          *)
(* ********************************************************************** *)

lemma lemma8:
     "\<lbrakk>\<forall>x<a. x<j | (\<exists>xa \<in> F(j). P(x, xa))   
         \<longrightarrow> (\<exists>! Y. Y \<in> F(j) \<and> P(x, Y)); F(j) \<subseteq> X;   
         L \<in> X; P(j, L) \<and> (\<forall>x<a. P(x, L) \<longrightarrow> (\<forall>xa \<in> F(j). \<not>P(x, xa)))\<rbrakk>   
      \<Longrightarrow> F(j) \<union> {L} \<subseteq> X \<and>   
          (\<forall>x<a. x\<le>j | (\<exists>xa \<in> (F(j) \<union> {L}). P(x, xa)) \<longrightarrow>   
                 (\<exists>! Y. Y \<in> (F(j) \<union> {L}) \<and> P(x, Y)))"
apply (rule conjI)
apply (fast intro!: singleton_subsetI)
apply (rule oallI)
apply (blast elim!: leE oallE)
done

(* ********************************************************************** *)
(* The main part of the proof: inductive proof of the property of T_gamma *)
(* lemma main_induct                                                      *)
(* ********************************************************************** *)

lemma main_induct:
     "\<lbrakk>b < a; f \<in> bij(a, {Y \<in> Pow(A) . Y\<approx>succ(k #+ m)});   
         h \<in> bij(a, {Y \<in> Pow(A) . Y\<approx>succ(k)});   
         \<not>Finite(a); Card(a); A\<approx>a; k \<in> nat; m \<in> nat\<rbrakk>   
      \<Longrightarrow> recfunAC16(f, h, b, a) \<subseteq> {X \<in> Pow(A) . X\<approx>succ(k #+ m)} \<and>   
          (\<forall>x<a. x < b | (\<exists>Y \<in> recfunAC16(f, h, b, a). h ` x \<subseteq> Y) \<longrightarrow>   
          (\<exists>! Y. Y \<in> recfunAC16(f, h, b, a) \<and> h ` x \<subseteq> Y))"
apply (erule lt_induct)
apply (frule lt_Ord)
apply (erule Ord_cases)
(* case 0 *)
apply (simp add: recfunAC16_0)
(* case Limit *)
prefer 2  apply (simp add: recfunAC16_Limit)
          apply (rule lemma5, assumption+)
          apply (blast dest!: recfunAC16_mono)
(* case succ *)
apply clarify 
apply (erule lemma6 [THEN conjE], assumption)
apply (simp (no_asm_simp) split del: split_if add: recfunAC16_succ)
apply (rule conjI [THEN split_if [THEN iffD2]])
 apply (simp, erule lemma7, assumption)
apply (rule impI)
apply (rule ex_next_Ord [THEN oexE], 
       assumption+, rule le_refl [THEN lt_trans], assumption+) 
apply (erule lemma8, assumption)
 apply (rule bij_is_fun [THEN apply_type], assumption)
 apply (erule Least_le [THEN lt_trans2, THEN ltD])
  apply (erule lt_Ord) 
 apply (erule succ_leI)
apply (erule LeastI) 
apply (erule lt_Ord) 
done

(* ********************************************************************** *)
(* Lemma to simplify the inductive proof                                  *)
(*   - the desired property is a consequence of the inductive assumption  *)
(* ********************************************************************** *)

lemma lemma_simp_induct:
     "\<lbrakk>\<forall>b. b<a \<longrightarrow> F(b) \<subseteq> S \<and> (\<forall>x<a. (x<b | (\<exists>Y \<in> F(b). f`x \<subseteq> Y))  
                                   \<longrightarrow> (\<exists>! Y. Y \<in> F(b) \<and> f`x \<subseteq> Y));
         f \<in> a->f``(a); Limit(a); 
         \<forall>i j. i\<le>j \<longrightarrow> F(i) \<subseteq> F(j)\<rbrakk>   
        \<Longrightarrow> (\<Union>j<a. F(j)) \<subseteq> S \<and>   
            (\<forall>x \<in> f``a. \<exists>! Y. Y \<in> (\<Union>j<a. F(j)) \<and> x \<subseteq> Y)"
apply (rule conjI)
apply (rule subsetI)
apply (erule OUN_E, blast) 
apply (rule ballI)
apply (erule imageE)
apply (drule ltI, erule Limit_is_Ord) 
apply (drule Limit_has_succ, assumption) 
apply (frule_tac x1="succ(xa)" in spec [THEN mp], assumption)
apply (erule conjE)
apply (drule ospec) 
(** LEVEL 10 **)
apply (erule leI [THEN succ_leE])
apply (erule impE)
apply (fast elim!: leI [THEN succ_leE, THEN lt_Ord, THEN le_refl])
apply (drule apply_equality, assumption) 
apply (elim conjE ex1E)
(** LEVEL 15 **)
apply (rule ex1I, blast) 
apply (elim conjE OUN_E)
apply (erule_tac i="succ(xa)" and j=aa 
       in Ord_linear_le [OF lt_Ord lt_Ord], assumption)
prefer 2 
apply (drule spec [THEN spec, THEN mp, THEN subsetD], assumption+, blast) 
(** LEVEL 20 **)
apply (drule_tac x1=aa in spec [THEN mp], assumption)
apply (frule succ_leE)
apply (drule spec [THEN spec, THEN mp, THEN subsetD], assumption+, blast) 
done

(* ********************************************************************** *)
(* The target theorem                                                     *)
(* ********************************************************************** *)

theorem WO2_AC16: "\<lbrakk>WO2; 0<m; k \<in> nat; m \<in> nat\<rbrakk> \<Longrightarrow> AC16(k #+ m,k)"
  unfolding AC16_def
apply (rule allI)
apply (rule impI)
apply (frule WO2_infinite_subsets_eqpoll_X, assumption+)
apply (frule_tac n="k #+ m" in WO2_infinite_subsets_eqpoll_X, simp, simp) 
apply (frule WO2_imp_ex_Card)
apply (elim exE conjE)
apply (drule eqpoll_trans [THEN eqpoll_sym, 
                           THEN eqpoll_def [THEN def_imp_iff, THEN iffD1]],
       assumption)
apply (drule eqpoll_trans [THEN eqpoll_sym, 
                           THEN eqpoll_def [THEN def_imp_iff, THEN iffD1]], 
       assumption+)
apply (elim exE)
apply (rename_tac h)
apply (rule_tac x = "\<Union>j<a. recfunAC16 (h,f,j,a) " in exI)
apply (rule_tac P="\<lambda>z. Y \<and> (\<forall>x \<in> z. Z(x))"  for Y Z
       in bij_is_surj [THEN surj_image_eq, THEN subst], assumption)
apply (rule lemma_simp_induct)
apply (blast del: conjI notI
             intro!: main_induct eqpoll_imp_lepoll [THEN lepoll_infinite] ) 
apply (blast intro: bij_is_fun [THEN surj_image, THEN surj_is_fun])
apply (erule eqpoll_imp_lepoll [THEN lepoll_infinite, 
                                THEN infinite_Card_is_InfCard, 
                                THEN InfCard_is_Limit], 
       assumption+)
apply (blast dest!: recfunAC16_mono)
done

end
