(*  Title:      ZF/Resid/Reduction.thy
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
*)

theory Reduction imports Residuals begin

(**** Lambda-terms ****)

consts
  lambda        :: "i"
  unmark        :: "i\<Rightarrow>i"

abbreviation
  Apl :: "[i,i]\<Rightarrow>i" where
  "Apl(n,m) \<equiv> App(0,n,m)"
  
inductive
  domains       "lambda" \<subseteq> redexes
  intros
    Lambda_Var:  "               n \<in> nat \<Longrightarrow>     Var(n) \<in> lambda"
    Lambda_Fun:  "            u \<in> lambda \<Longrightarrow>     Fun(u) \<in> lambda"
    Lambda_App:  "\<lbrakk>u \<in> lambda; v \<in> lambda\<rbrakk> \<Longrightarrow> Apl(u,v) \<in> lambda"
  type_intros    redexes.intros bool_typechecks

declare lambda.intros [intro]

primrec
  "unmark(Var(n)) = Var(n)"
  "unmark(Fun(u)) = Fun(unmark(u))"
  "unmark(App(b,f,a)) = Apl(unmark(f), unmark(a))"


declare lambda.intros [simp] 
declare lambda.dom_subset [THEN subsetD, simp, intro]


(* ------------------------------------------------------------------------- *)
(*        unmark lemmas                                                      *)
(* ------------------------------------------------------------------------- *)

lemma unmark_type [intro, simp]:
     "u \<in> redexes \<Longrightarrow> unmark(u) \<in> lambda"
by (erule redexes.induct, simp_all)

lemma lambda_unmark: "u \<in> lambda \<Longrightarrow> unmark(u) = u"
by (erule lambda.induct, simp_all)


(* ------------------------------------------------------------------------- *)
(*         lift and subst preserve lambda                                    *)
(* ------------------------------------------------------------------------- *)

lemma liftL_type [rule_format]:
     "v \<in> lambda \<Longrightarrow> \<forall>k \<in> nat. lift_rec(v,k) \<in> lambda"
by (erule lambda.induct, simp_all add: lift_rec_Var)

lemma substL_type [rule_format, simp]:
     "v \<in> lambda \<Longrightarrow>  \<forall>n \<in> nat. \<forall>u \<in> lambda. subst_rec(u,v,n) \<in> lambda"
by (erule lambda.induct, simp_all add: liftL_type subst_Var)


(* ------------------------------------------------------------------------- *)
(*        type-rule for reduction definitions                               *)
(* ------------------------------------------------------------------------- *)

lemmas red_typechecks = substL_type nat_typechecks lambda.intros 
                        bool_typechecks

consts
  Sred1     :: "i"
  Sred      :: "i"
  Spar_red1 :: "i"
  Spar_red  :: "i"

abbreviation
  Sred1_rel (infixl \<open>-1->\<close> 50) where
  "a -1-> b \<equiv> \<langle>a,b\<rangle> \<in> Sred1"

abbreviation
  Sred_rel (infixl \<open>-\<longrightarrow>\<close> 50) where
  "a -\<longrightarrow> b \<equiv> \<langle>a,b\<rangle> \<in> Sred"

abbreviation
  Spar_red1_rel (infixl \<open>=1\<Rightarrow>\<close> 50) where
  "a =1\<Rightarrow> b \<equiv> \<langle>a,b\<rangle> \<in> Spar_red1"

abbreviation
  Spar_red_rel (infixl \<open>=\<Longrightarrow>\<close> 50) where
  "a =\<Longrightarrow> b \<equiv> \<langle>a,b\<rangle> \<in> Spar_red"
  
  
inductive
  domains       "Sred1" \<subseteq> "lambda*lambda"
  intros
    beta:       "\<lbrakk>m \<in> lambda; n \<in> lambda\<rbrakk> \<Longrightarrow> Apl(Fun(m),n) -1-> n/m"
    rfun:       "\<lbrakk>m -1-> n\<rbrakk> \<Longrightarrow> Fun(m) -1-> Fun(n)"
    apl_l:      "\<lbrakk>m2 \<in> lambda; m1 -1-> n1\<rbrakk> \<Longrightarrow> Apl(m1,m2) -1-> Apl(n1,m2)"
    apl_r:      "\<lbrakk>m1 \<in> lambda; m2 -1-> n2\<rbrakk> \<Longrightarrow> Apl(m1,m2) -1-> Apl(m1,n2)"
  type_intros    red_typechecks

declare Sred1.intros [intro, simp]

inductive
  domains       "Sred" \<subseteq> "lambda*lambda"
  intros
    one_step:   "m-1->n \<Longrightarrow> m-\<longrightarrow>n"
    refl:       "m \<in> lambda\<Longrightarrow>m -\<longrightarrow>m"
    trans:      "\<lbrakk>m-\<longrightarrow>n; n-\<longrightarrow>p\<rbrakk> \<Longrightarrow>m-\<longrightarrow>p"
  type_intros    Sred1.dom_subset [THEN subsetD] red_typechecks

declare Sred.one_step [intro, simp]
declare Sred.refl     [intro, simp]

inductive
  domains       "Spar_red1" \<subseteq> "lambda*lambda"
  intros
    beta:       "\<lbrakk>m =1\<Rightarrow> m'; n =1\<Rightarrow> n'\<rbrakk> \<Longrightarrow> Apl(Fun(m),n) =1\<Rightarrow> n'/m'"
    rvar:       "n \<in> nat \<Longrightarrow> Var(n) =1\<Rightarrow> Var(n)"
    rfun:       "m =1\<Rightarrow> m' \<Longrightarrow> Fun(m) =1\<Rightarrow> Fun(m')"
    rapl:       "\<lbrakk>m =1\<Rightarrow> m'; n =1\<Rightarrow> n'\<rbrakk> \<Longrightarrow> Apl(m,n) =1\<Rightarrow> Apl(m',n')"
  type_intros    red_typechecks

declare Spar_red1.intros [intro, simp]

inductive
  domains "Spar_red" \<subseteq> "lambda*lambda"
  intros
    one_step:   "m =1\<Rightarrow> n \<Longrightarrow> m =\<Longrightarrow> n"
    trans:      "\<lbrakk>m=\<Longrightarrow>n; n=\<Longrightarrow>p\<rbrakk> \<Longrightarrow> m=\<Longrightarrow>p"
  type_intros    Spar_red1.dom_subset [THEN subsetD] red_typechecks

declare Spar_red.one_step [intro, simp]



(* ------------------------------------------------------------------------- *)
(*     Setting up rule lists for reduction                                   *)
(* ------------------------------------------------------------------------- *)

lemmas red1D1 [simp] = Sred1.dom_subset [THEN subsetD, THEN SigmaD1]
lemmas red1D2 [simp] = Sred1.dom_subset [THEN subsetD, THEN SigmaD2]
lemmas redD1 [simp] = Sred.dom_subset [THEN subsetD, THEN SigmaD1]
lemmas redD2 [simp] = Sred.dom_subset [THEN subsetD, THEN SigmaD2]

lemmas par_red1D1 [simp] = Spar_red1.dom_subset [THEN subsetD, THEN SigmaD1]
lemmas par_red1D2 [simp] = Spar_red1.dom_subset [THEN subsetD, THEN SigmaD2]
lemmas par_redD1 [simp] = Spar_red.dom_subset [THEN subsetD, THEN SigmaD1]
lemmas par_redD2 [simp] = Spar_red.dom_subset [THEN subsetD, THEN SigmaD2]

declare bool_typechecks [intro]

inductive_cases  [elim!]: "Fun(t) =1\<Rightarrow> Fun(u)"



(* ------------------------------------------------------------------------- *)
(*     Lemmas for reduction                                                  *)
(* ------------------------------------------------------------------------- *)

lemma red_Fun: "m-\<longrightarrow>n \<Longrightarrow> Fun(m) -\<longrightarrow> Fun(n)"
apply (erule Sred.induct)
apply (rule_tac [3] Sred.trans, simp_all)
done

lemma red_Apll: "\<lbrakk>n \<in> lambda; m -\<longrightarrow> m'\<rbrakk> \<Longrightarrow> Apl(m,n)-\<longrightarrow>Apl(m',n)"
apply (erule Sred.induct)
apply (rule_tac [3] Sred.trans, simp_all)
done

lemma red_Aplr: "\<lbrakk>n \<in> lambda; m -\<longrightarrow> m'\<rbrakk> \<Longrightarrow> Apl(n,m)-\<longrightarrow>Apl(n,m')"
apply (erule Sred.induct)
apply (rule_tac [3] Sred.trans, simp_all)
done

lemma red_Apl: "\<lbrakk>m -\<longrightarrow> m'; n-\<longrightarrow>n'\<rbrakk> \<Longrightarrow> Apl(m,n)-\<longrightarrow>Apl(m',n')"
apply (rule_tac n = "Apl (m',n) " in Sred.trans)
apply (simp_all add: red_Apll red_Aplr)
done

lemma red_beta: "\<lbrakk>m \<in> lambda; m':lambda; n \<in> lambda; n':lambda; m -\<longrightarrow> m'; n-\<longrightarrow>n'\<rbrakk> \<Longrightarrow>  
               Apl(Fun(m),n)-\<longrightarrow> n'/m'"
apply (rule_tac n = "Apl (Fun (m'),n') " in Sred.trans)
apply (simp_all add: red_Apl red_Fun)
done


(* ------------------------------------------------------------------------- *)
(*      Lemmas for parallel reduction                                        *)
(* ------------------------------------------------------------------------- *)


lemma refl_par_red1: "m \<in> lambda\<Longrightarrow> m =1\<Rightarrow> m"
by (erule lambda.induct, simp_all)

lemma red1_par_red1: "m-1->n \<Longrightarrow> m=1\<Rightarrow>n"
by (erule Sred1.induct, simp_all add: refl_par_red1)

lemma red_par_red: "m-\<longrightarrow>n \<Longrightarrow> m=\<Longrightarrow>n"
apply (erule Sred.induct)
apply (rule_tac [3] Spar_red.trans)
apply (simp_all add: refl_par_red1 red1_par_red1)
done

lemma par_red_red: "m=\<Longrightarrow>n \<Longrightarrow> m-\<longrightarrow>n"
apply (erule Spar_red.induct)
apply (erule Spar_red1.induct)
apply (rule_tac [5] Sred.trans)
apply (simp_all add: red_Fun red_beta red_Apl)
done


(* ------------------------------------------------------------------------- *)
(*      Simulation                                                           *)
(* ------------------------------------------------------------------------- *)

lemma simulation: "m=1\<Rightarrow>n \<Longrightarrow> \<exists>v. m|>v = n \<and> m \<sim> v \<and> regular(v)"
by (erule Spar_red1.induct, force+)


(* ------------------------------------------------------------------------- *)
(*           commuting of unmark and subst                                   *)
(* ------------------------------------------------------------------------- *)

lemma unmmark_lift_rec:
     "u \<in> redexes \<Longrightarrow> \<forall>k \<in> nat. unmark(lift_rec(u,k)) = lift_rec(unmark(u),k)"
by (erule redexes.induct, simp_all add: lift_rec_Var)

lemma unmmark_subst_rec:
 "v \<in> redexes \<Longrightarrow> \<forall>k \<in> nat. \<forall>u \<in> redexes.   
                  unmark(subst_rec(u,v,k)) = subst_rec(unmark(u),unmark(v),k)"
by (erule redexes.induct, simp_all add: unmmark_lift_rec subst_Var)


(* ------------------------------------------------------------------------- *)
(*        Completeness                                                       *)
(* ------------------------------------------------------------------------- *)

lemma completeness_l [rule_format]:
     "u \<sim> v \<Longrightarrow> regular(v) \<longrightarrow> unmark(u) =1\<Rightarrow> unmark(u|>v)"
apply (erule Scomp.induct)
apply (auto simp add: unmmark_subst_rec)
done

lemma completeness: "\<lbrakk>u \<in> lambda; u \<sim> v; regular(v)\<rbrakk> \<Longrightarrow> u =1\<Rightarrow> unmark(u|>v)"
by (drule completeness_l, simp_all add: lambda_unmark)

end

