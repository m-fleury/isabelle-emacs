(*  Title:      ZF/Induct/FoldSet.thy
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory

A "fold" functional for finite sets.  For n non-negative we have
fold f e {x1,...,xn} = f x1 (... (f xn e)) where f is at
least left-commutative.  
*)

theory FoldSet imports ZF begin

consts fold_set :: "[i, i, [i,i]\<Rightarrow>i, i] \<Rightarrow> i"

inductive
  domains "fold_set(A, B, f,e)" \<subseteq> "Fin(A)*B"
  intros
    emptyI: "e\<in>B \<Longrightarrow> \<langle>0, e\<rangle>\<in>fold_set(A, B, f,e)"
    consI:  "\<lbrakk>x\<in>A; x \<notin>C;  \<langle>C,y\<rangle> \<in> fold_set(A, B,f,e); f(x,y):B\<rbrakk>
                \<Longrightarrow>  <cons(x,C), f(x,y)>\<in>fold_set(A, B, f, e)"
  type_intros Fin.intros
  
definition
  fold :: "[i, [i,i]\<Rightarrow>i, i, i] \<Rightarrow> i"  (\<open>fold[_]'(_,_,_')\<close>)  where
   "fold[B](f,e, A) \<equiv> THE x. \<langle>A, x\<rangle>\<in>fold_set(A, B, f,e)"

definition
   setsum :: "[i\<Rightarrow>i, i] \<Rightarrow> i"  where
   "setsum(g, C) \<equiv> if Finite(C) then
                     fold[int](\<lambda>x y. g(x) $+ y, #0, C) else #0"

(** foldSet **)

inductive_cases empty_fold_setE: "\<langle>0, x\<rangle> \<in> fold_set(A, B, f,e)"
inductive_cases cons_fold_setE: "<cons(x,C), y> \<in> fold_set(A, B, f,e)"

(* add-hoc lemmas *)                                                

lemma cons_lemma1: "\<lbrakk>x\<notin>C; x\<notin>B\<rbrakk> \<Longrightarrow> cons(x,B)=cons(x,C) \<longleftrightarrow> B = C"
by (auto elim: equalityE)

lemma cons_lemma2: "\<lbrakk>cons(x, B)=cons(y, C); x\<noteq>y; x\<notin>B; y\<notin>C\<rbrakk>  
    \<Longrightarrow>  B - {y} = C-{x} \<and> x\<in>C \<and> y\<in>B"
apply (auto elim: equalityE)
done

(* fold_set monotonicity *)
lemma fold_set_mono_lemma:
     "\<langle>C, x\<rangle> \<in> fold_set(A, B, f, e)  
      \<Longrightarrow> \<forall>D. A<=D \<longrightarrow> \<langle>C, x\<rangle> \<in> fold_set(D, B, f, e)"
apply (erule fold_set.induct)
apply (auto intro: fold_set.intros)
done

lemma fold_set_mono: " C<=A \<Longrightarrow> fold_set(C, B, f, e) \<subseteq> fold_set(A, B, f, e)"
apply clarify
apply (frule fold_set.dom_subset [THEN subsetD], clarify)
apply (auto dest: fold_set_mono_lemma)
done

lemma fold_set_lemma:
     "\<langle>C, x\<rangle>\<in>fold_set(A, B, f, e) \<Longrightarrow> \<langle>C, x\<rangle>\<in>fold_set(C, B, f, e) \<and> C<=A"
apply (erule fold_set.induct)
apply (auto intro!: fold_set.intros intro: fold_set_mono [THEN subsetD])
done

(* Proving that fold_set is deterministic *)
lemma Diff1_fold_set:
     "\<lbrakk><C-{x},y> \<in> fold_set(A, B, f,e);  x\<in>C; x\<in>A; f(x, y):B\<rbrakk>  
      \<Longrightarrow> <C, f(x, y)> \<in> fold_set(A, B, f, e)"
apply (frule fold_set.dom_subset [THEN subsetD])
apply (erule cons_Diff [THEN subst], rule fold_set.intros, auto)
done


locale fold_typing =
 fixes A and B and e and f
 assumes ftype [intro,simp]:  "\<lbrakk>x \<in> A; y \<in> B\<rbrakk> \<Longrightarrow> f(x,y) \<in> B"
     and etype [intro,simp]:  "e \<in> B"
     and fcomm:  "\<lbrakk>x \<in> A; y \<in> A; z \<in> B\<rbrakk> \<Longrightarrow> f(x, f(y, z))=f(y, f(x, z))"


lemma (in fold_typing) Fin_imp_fold_set:
     "C\<in>Fin(A) \<Longrightarrow> (\<exists>x. \<langle>C, x\<rangle> \<in> fold_set(A, B, f,e))"
apply (erule Fin_induct)
apply (auto dest: fold_set.dom_subset [THEN subsetD] 
            intro: fold_set.intros etype ftype)
done

lemma Diff_sing_imp:
     "\<lbrakk>C - {b} = D - {a}; a \<noteq> b; b \<in> C\<rbrakk> \<Longrightarrow> C = cons(b,D) - {a}"
by (blast elim: equalityE)

lemma (in fold_typing) fold_set_determ_lemma [rule_format]: 
"n\<in>nat
 \<Longrightarrow> \<forall>C. |C|<n \<longrightarrow>  
   (\<forall>x. \<langle>C, x\<rangle> \<in> fold_set(A, B, f,e)\<longrightarrow> 
           (\<forall>y. \<langle>C, y\<rangle> \<in> fold_set(A, B, f,e) \<longrightarrow> y=x))"
apply (erule nat_induct)
 apply (auto simp add: le_iff)
apply (erule fold_set.cases)
 apply (force elim!: empty_fold_setE)
apply (erule fold_set.cases)
 apply (force elim!: empty_fold_setE, clarify)
(*force simplification of "|C| < |cons(...)|"*)
apply (frule_tac a = Ca in fold_set.dom_subset [THEN subsetD, THEN SigmaD1])
apply (frule_tac a = Cb in fold_set.dom_subset [THEN subsetD, THEN SigmaD1])
apply (simp add: Fin_into_Finite [THEN Finite_imp_cardinal_cons])
apply (case_tac "x=xb", auto) 
apply (simp add: cons_lemma1, blast)
txt\<open>case \<^term>\<open>x\<noteq>xb\<close>\<close>
apply (drule cons_lemma2, safe)
apply (frule Diff_sing_imp, assumption+) 
txt\<open>* LEVEL 17\<close>
apply (subgoal_tac "|Ca| \<le> |Cb|")
 prefer 2
 apply (rule succ_le_imp_le)
 apply (simp add: Fin_into_Finite Finite_imp_succ_cardinal_Diff 
                  Fin_into_Finite [THEN Finite_imp_cardinal_cons])
apply (rule_tac C1 = "Ca-{xb}" in Fin_imp_fold_set [THEN exE])
 apply (blast intro: Diff_subset [THEN Fin_subset])
txt\<open>* LEVEL 24 *\<close>
apply (frule Diff1_fold_set, blast, blast)
apply (blast dest!: ftype fold_set.dom_subset [THEN subsetD])
apply (subgoal_tac "ya = f(xb,xa) ")
 prefer 2 apply (blast del: equalityCE)
apply (subgoal_tac "<Cb-{x}, xa> \<in> fold_set(A,B,f,e)")
 prefer 2 apply simp
apply (subgoal_tac "yb = f (x, xa) ")
 apply (drule_tac [2] C = Cb in Diff1_fold_set, simp_all)
  apply (blast intro: fcomm dest!: fold_set.dom_subset [THEN subsetD])
 apply (blast intro: ftype dest!: fold_set.dom_subset [THEN subsetD], blast) 
done

lemma (in fold_typing) fold_set_determ: 
     "\<lbrakk>\<langle>C, x\<rangle>\<in>fold_set(A, B, f, e);  
         \<langle>C, y\<rangle>\<in>fold_set(A, B, f, e)\<rbrakk> \<Longrightarrow> y=x"
apply (frule fold_set.dom_subset [THEN subsetD], clarify)
apply (drule Fin_into_Finite)
apply (unfold Finite_def, clarify)
apply (rule_tac n = "succ (n)" in fold_set_determ_lemma) 
apply (auto intro: eqpoll_imp_lepoll [THEN lepoll_cardinal_le])
done

(** The fold function **)

lemma (in fold_typing) fold_equality: 
     "\<langle>C,y\<rangle> \<in> fold_set(A,B,f,e) \<Longrightarrow> fold[B](f,e,C) = y"
  unfolding fold_def
apply (frule fold_set.dom_subset [THEN subsetD], clarify)
apply (rule the_equality)
 apply (rule_tac [2] A=C in fold_typing.fold_set_determ)
apply (force dest: fold_set_lemma)
apply (auto dest: fold_set_lemma)
apply (simp add: fold_typing_def, auto) 
apply (auto dest: fold_set_lemma intro: ftype etype fcomm)
done

lemma fold_0 [simp]: "e \<in> B \<Longrightarrow> fold[B](f,e,0) = e"
  unfolding fold_def
apply (blast elim!: empty_fold_setE intro: fold_set.intros)
done

text\<open>This result is the right-to-left direction of the subsequent result\<close>
lemma (in fold_typing) fold_set_imp_cons: 
     "\<lbrakk>\<langle>C, y\<rangle> \<in> fold_set(C, B, f, e); C \<in> Fin(A); c \<in> A; c\<notin>C\<rbrakk>
      \<Longrightarrow> <cons(c, C), f(c,y)> \<in> fold_set(cons(c, C), B, f, e)"
apply (frule FinD [THEN fold_set_mono, THEN subsetD])
 apply assumption
apply (frule fold_set.dom_subset [of A, THEN subsetD])
apply (blast intro!: fold_set.consI intro: fold_set_mono [THEN subsetD])
done

lemma (in fold_typing) fold_cons_lemma [rule_format]: 
"\<lbrakk>C \<in> Fin(A); c \<in> A; c\<notin>C\<rbrakk>   
     \<Longrightarrow> <cons(c, C), v> \<in> fold_set(cons(c, C), B, f, e) \<longleftrightarrow>   
         (\<exists>y. \<langle>C, y\<rangle> \<in> fold_set(C, B, f, e) \<and> v = f(c, y))"
apply auto
 prefer 2 apply (blast intro: fold_set_imp_cons) 
 apply (frule_tac Fin.consI [of c, THEN FinD, THEN fold_set_mono, THEN subsetD], assumption+)
apply (frule_tac fold_set.dom_subset [of A, THEN subsetD])
apply (drule FinD) 
apply (rule_tac A1 = "cons(c,C)" and f1=f and B1=B and C1=C and e1=e in fold_typing.Fin_imp_fold_set [THEN exE])
apply (blast intro: fold_typing.intro ftype etype fcomm) 
apply (blast intro: Fin_subset [of _ "cons(c,C)"] Finite_into_Fin 
             dest: Fin_into_Finite)  
apply (rule_tac x = x in exI)
apply (auto intro: fold_set.intros)
apply (drule_tac fold_set_lemma [of C], blast)
apply (blast intro!: fold_set.consI
             intro: fold_set_determ fold_set_mono [THEN subsetD] 
             dest: fold_set.dom_subset [THEN subsetD]) 
done

lemma (in fold_typing) fold_cons: 
     "\<lbrakk>C\<in>Fin(A); c\<in>A; c\<notin>C\<rbrakk> 
      \<Longrightarrow> fold[B](f, e, cons(c, C)) = f(c, fold[B](f, e, C))"
  unfolding fold_def
apply (simp add: fold_cons_lemma)
apply (rule the_equality, auto) 
 apply (subgoal_tac [2] "\<langle>C, y\<rangle> \<in> fold_set(A, B, f, e)")
  apply (drule Fin_imp_fold_set)
apply (auto dest: fold_set_lemma  simp add: fold_def [symmetric] fold_equality) 
apply (blast intro: fold_set_mono [THEN subsetD] dest!: FinD) 
done

lemma (in fold_typing) fold_type [simp,TC]: 
     "C\<in>Fin(A) \<Longrightarrow> fold[B](f,e,C):B"
apply (erule Fin_induct)
apply (simp_all add: fold_cons ftype etype)
done

lemma (in fold_typing) fold_commute [rule_format]: 
     "\<lbrakk>C\<in>Fin(A); c\<in>A\<rbrakk>  
      \<Longrightarrow> (\<forall>y\<in>B. f(c, fold[B](f, y, C)) = fold[B](f, f(c, y), C))"
apply (erule Fin_induct)
apply (simp_all add: fold_typing.fold_cons [of A B _ f] 
                     fold_typing.fold_type [of A B _ f] 
                     fold_typing_def fcomm)
done

lemma (in fold_typing) fold_nest_Un_Int: 
     "\<lbrakk>C\<in>Fin(A); D\<in>Fin(A)\<rbrakk>
      \<Longrightarrow> fold[B](f, fold[B](f, e, D), C) =
          fold[B](f, fold[B](f, e, (C \<inter> D)), C \<union> D)"
apply (erule Fin_induct, auto)
apply (simp add: Un_cons Int_cons_left fold_type fold_commute
                 fold_typing.fold_cons [of A _ _ f] 
                 fold_typing_def fcomm cons_absorb)
done

lemma (in fold_typing) fold_nest_Un_disjoint:
     "\<lbrakk>C\<in>Fin(A); D\<in>Fin(A); C \<inter> D = 0\<rbrakk>  
      \<Longrightarrow> fold[B](f,e,C \<union> D) =  fold[B](f, fold[B](f,e,D), C)"
by (simp add: fold_nest_Un_Int)

lemma Finite_cons_lemma: "Finite(C) \<Longrightarrow> C\<in>Fin(cons(c, C))"
apply (drule Finite_into_Fin)
apply (blast intro: Fin_mono [THEN subsetD])
done

subsection\<open>The Operator \<^term>\<open>setsum\<close>\<close>

lemma setsum_0 [simp]: "setsum(g, 0) = #0"
by (simp add: setsum_def)

lemma setsum_cons [simp]: 
     "Finite(C) \<Longrightarrow> 
      setsum(g, cons(c,C)) = 
        (if c \<in> C then setsum(g,C) else g(c) $+ setsum(g,C))"
apply (auto simp add: setsum_def Finite_cons cons_absorb)
apply (rule_tac A = "cons (c, C)" in fold_typing.fold_cons)
apply (auto intro: fold_typing.intro Finite_cons_lemma)
done

lemma setsum_K0: "setsum((\<lambda>i. #0), C) = #0"
apply (case_tac "Finite (C) ")
 prefer 2 apply (simp add: setsum_def)
apply (erule Finite_induct, auto)
done

(*The reversed orientation looks more natural, but LOOPS as a simprule!*)
lemma setsum_Un_Int:
     "\<lbrakk>Finite(C); Finite(D)\<rbrakk>  
      \<Longrightarrow> setsum(g, C \<union> D) $+ setsum(g, C \<inter> D)  
        = setsum(g, C) $+ setsum(g, D)"
apply (erule Finite_induct)
apply (simp_all add: Int_cons_right cons_absorb Un_cons Int_commute Finite_Un
                     Int_lower1 [THEN subset_Finite]) 
done

lemma setsum_type [simp,TC]: "setsum(g, C):int"
apply (case_tac "Finite (C) ")
 prefer 2 apply (simp add: setsum_def)
apply (erule Finite_induct, auto)
done

lemma setsum_Un_disjoint:
     "\<lbrakk>Finite(C); Finite(D); C \<inter> D = 0\<rbrakk>  
      \<Longrightarrow> setsum(g, C \<union> D) = setsum(g, C) $+ setsum(g,D)"
apply (subst setsum_Un_Int [symmetric])
apply (subgoal_tac [3] "Finite (C \<union> D) ")
apply (auto intro: Finite_Un)
done

lemma Finite_RepFun [rule_format (no_asm)]:
     "Finite(I) \<Longrightarrow> (\<forall>i\<in>I. Finite(C(i))) \<longrightarrow> Finite(RepFun(I, C))"
apply (erule Finite_induct, auto)
done

lemma setsum_UN_disjoint [rule_format (no_asm)]:
     "Finite(I)  
      \<Longrightarrow> (\<forall>i\<in>I. Finite(C(i))) \<longrightarrow>  
          (\<forall>i\<in>I. \<forall>j\<in>I. i\<noteq>j \<longrightarrow> C(i) \<inter> C(j) = 0) \<longrightarrow>  
          setsum(f, \<Union>i\<in>I. C(i)) = setsum (\<lambda>i. setsum(f, C(i)), I)"
apply (erule Finite_induct, auto)
apply (subgoal_tac "\<forall>i\<in>B. x \<noteq> i")
 prefer 2 apply blast
apply (subgoal_tac "C (x) \<inter> (\<Union>i\<in>B. C (i)) = 0")
 prefer 2 apply blast
apply (subgoal_tac "Finite (\<Union>i\<in>B. C (i)) \<and> Finite (C (x)) \<and> Finite (B) ")
apply (simp (no_asm_simp) add: setsum_Un_disjoint)
apply (auto intro: Finite_Union Finite_RepFun)
done


lemma setsum_addf: "setsum(\<lambda>x. f(x) $+ g(x),C) = setsum(f, C) $+ setsum(g, C)"
apply (case_tac "Finite (C) ")
 prefer 2 apply (simp add: setsum_def)
apply (erule Finite_induct, auto)
done


lemma fold_set_cong:
     "\<lbrakk>A=A'; B=B'; e=e'; (\<forall>x\<in>A'. \<forall>y\<in>B'. f(x,y) = f'(x,y))\<rbrakk> 
      \<Longrightarrow> fold_set(A,B,f,e) = fold_set(A',B',f',e')"
apply (simp add: fold_set_def)
apply (intro refl iff_refl lfp_cong Collect_cong disj_cong ex_cong, auto)
done

lemma fold_cong:
"\<lbrakk>B=B'; A=A'; e=e';   
    \<And>x y. \<lbrakk>x\<in>A'; y\<in>B'\<rbrakk> \<Longrightarrow> f(x,y) = f'(x,y)\<rbrakk> \<Longrightarrow>  
   fold[B](f,e,A) = fold[B'](f', e', A')"
apply (simp add: fold_def)
apply (subst fold_set_cong)
apply (rule_tac [5] refl, simp_all)
done

lemma setsum_cong:
 "\<lbrakk>A=B; \<And>x. x\<in>B \<Longrightarrow> f(x) = g(x)\<rbrakk> \<Longrightarrow>  
     setsum(f, A) = setsum(g, B)"
by (simp add: setsum_def cong add: fold_cong)

lemma setsum_Un:
     "\<lbrakk>Finite(A); Finite(B)\<rbrakk>  
      \<Longrightarrow> setsum(f, A \<union> B) =  
          setsum(f, A) $+ setsum(f, B) $- setsum(f, A \<inter> B)"
apply (subst setsum_Un_Int [symmetric], auto)
done


lemma setsum_zneg_or_0 [rule_format (no_asm)]:
     "Finite(A) \<Longrightarrow> (\<forall>x\<in>A. g(x) $\<le> #0) \<longrightarrow> setsum(g, A) $\<le> #0"
apply (erule Finite_induct)
apply (auto intro: zneg_or_0_add_zneg_or_0_imp_zneg_or_0)
done

lemma setsum_succD_lemma [rule_format]:
     "Finite(A)  
      \<Longrightarrow> \<forall>n\<in>nat. setsum(f,A) = $# succ(n) \<longrightarrow> (\<exists>a\<in>A. #0 $< f(a))"
apply (erule Finite_induct)
apply (auto simp del: int_of_0 int_of_succ simp add: not_zless_iff_zle int_of_0 [symmetric])
apply (subgoal_tac "setsum (f, B) $\<le> #0")
apply simp_all
prefer 2 apply (blast intro: setsum_zneg_or_0)
apply (subgoal_tac "$# 1 $\<le> f (x) $+ setsum (f, B) ")
apply (drule zdiff_zle_iff [THEN iffD2])
apply (subgoal_tac "$# 1 $\<le> $# 1 $- setsum (f,B) ")
apply (drule_tac x = "$# 1" in zle_trans)
apply (rule_tac [2] j = "#1" in zless_zle_trans, auto)
done

lemma setsum_succD:
     "\<lbrakk>setsum(f, A) = $# succ(n); n\<in>nat\<rbrakk>\<Longrightarrow> \<exists>a\<in>A. #0 $< f(a)"
apply (case_tac "Finite (A) ")
apply (blast intro: setsum_succD_lemma)
  unfolding setsum_def
apply (auto simp del: int_of_0 int_of_succ simp add: int_succ_int_1 [symmetric] int_of_0 [symmetric])
done

lemma g_zpos_imp_setsum_zpos [rule_format]:
     "Finite(A) \<Longrightarrow> (\<forall>x\<in>A. #0 $\<le> g(x)) \<longrightarrow> #0 $\<le> setsum(g, A)"
apply (erule Finite_induct)
apply (simp (no_asm))
apply (auto intro: zpos_add_zpos_imp_zpos)
done

lemma g_zpos_imp_setsum_zpos2 [rule_format]:
     "\<lbrakk>Finite(A); \<forall>x. #0 $\<le> g(x)\<rbrakk> \<Longrightarrow> #0 $\<le> setsum(g, A)"
apply (erule Finite_induct)
apply (auto intro: zpos_add_zpos_imp_zpos)
done

lemma g_zspos_imp_setsum_zspos [rule_format]:
     "Finite(A)  
      \<Longrightarrow> (\<forall>x\<in>A. #0 $< g(x)) \<longrightarrow> A \<noteq> 0 \<longrightarrow> (#0 $< setsum(g, A))"
apply (erule Finite_induct)
apply (auto intro: zspos_add_zspos_imp_zspos)
done

lemma setsum_Diff [rule_format]:
     "Finite(A) \<Longrightarrow> \<forall>a. M(a) = #0 \<longrightarrow> setsum(M, A) = setsum(M, A-{a})"
apply (erule Finite_induct) 
apply (simp_all add: Diff_cons_eq Finite_Diff) 
done

end
