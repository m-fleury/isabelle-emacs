(*  Title:      ZF/Induct/Primrec.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section \<open>Primitive Recursive Functions: the inductive definition\<close>

theory Primrec imports ZF begin

text \<open>
  Proof adopted from @{cite szasz93}.

  See also @{cite \<open>page 250, exercise 11\<close> mendelson}.
\<close>


subsection \<open>Basic definitions\<close>

definition
  SC :: "i"  where
  "SC \<equiv> \<lambda>l \<in> list(nat). list_case(0, \<lambda>x xs. succ(x), l)"

definition
  CONSTANT :: "i\<Rightarrow>i"  where
  "CONSTANT(k) \<equiv> \<lambda>l \<in> list(nat). k"

definition
  PROJ :: "i\<Rightarrow>i"  where
  "PROJ(i) \<equiv> \<lambda>l \<in> list(nat). list_case(0, \<lambda>x xs. x, drop(i,l))"

definition
  COMP :: "[i,i]\<Rightarrow>i"  where
  "COMP(g,fs) \<equiv> \<lambda>l \<in> list(nat). g ` map(\<lambda>f. f`l, fs)"

definition
  PREC :: "[i,i]\<Rightarrow>i"  where
  "PREC(f,g) \<equiv>
     \<lambda>l \<in> list(nat). list_case(0,
                      \<lambda>x xs. rec(x, f`xs, \<lambda>y r. g ` Cons(r, Cons(y, xs))), l)"
  \<comment> \<open>Note that \<open>g\<close> is applied first to \<^term>\<open>PREC(f,g)`y\<close> and then to \<open>y\<close>!\<close>

consts
  ACK :: "i\<Rightarrow>i"
primrec
  "ACK(0) = SC"
  "ACK(succ(i)) = PREC (CONSTANT (ACK(i) ` [1]), COMP(ACK(i), [PROJ(0)]))"

abbreviation
  ack :: "[i,i]\<Rightarrow>i" where
  "ack(x,y) \<equiv> ACK(x) ` [y]"


text \<open>
  \medskip Useful special cases of evaluation.
\<close>

lemma SC: "\<lbrakk>x \<in> nat;  l \<in> list(nat)\<rbrakk> \<Longrightarrow> SC ` (Cons(x,l)) = succ(x)"
  by (simp add: SC_def)

lemma CONSTANT: "l \<in> list(nat) \<Longrightarrow> CONSTANT(k) ` l = k"
  by (simp add: CONSTANT_def)

lemma PROJ_0: "\<lbrakk>x \<in> nat;  l \<in> list(nat)\<rbrakk> \<Longrightarrow> PROJ(0) ` (Cons(x,l)) = x"
  by (simp add: PROJ_def)

lemma COMP_1: "l \<in> list(nat) \<Longrightarrow> COMP(g,[f]) ` l = g` [f`l]"
  by (simp add: COMP_def)

lemma PREC_0: "l \<in> list(nat) \<Longrightarrow> PREC(f,g) ` (Cons(0,l)) = f`l"
  by (simp add: PREC_def)

lemma PREC_succ:
  "\<lbrakk>x \<in> nat;  l \<in> list(nat)\<rbrakk>
    \<Longrightarrow> PREC(f,g) ` (Cons(succ(x),l)) =
      g ` Cons(PREC(f,g)`(Cons(x,l)), Cons(x,l))"
  by (simp add: PREC_def)


subsection \<open>Inductive definition of the PR functions\<close>

consts
  prim_rec :: i

inductive
  domains prim_rec \<subseteq> "list(nat)->nat"
  intros
    "SC \<in> prim_rec"
    "k \<in> nat \<Longrightarrow> CONSTANT(k) \<in> prim_rec"
    "i \<in> nat \<Longrightarrow> PROJ(i) \<in> prim_rec"
    "\<lbrakk>g \<in> prim_rec; fs\<in>list(prim_rec)\<rbrakk> \<Longrightarrow> COMP(g,fs) \<in> prim_rec"
    "\<lbrakk>f \<in> prim_rec; g \<in> prim_rec\<rbrakk> \<Longrightarrow> PREC(f,g) \<in> prim_rec"
  monos list_mono
  con_defs SC_def CONSTANT_def PROJ_def COMP_def PREC_def
  type_intros nat_typechecks list.intros
    lam_type list_case_type drop_type map_type
    apply_type rec_type


lemma prim_rec_into_fun [TC]: "c \<in> prim_rec \<Longrightarrow> c \<in> list(nat) -> nat"
  by (erule subsetD [OF prim_rec.dom_subset])

lemmas [TC] = apply_type [OF prim_rec_into_fun]

declare prim_rec.intros [TC]
declare nat_into_Ord [TC]
declare rec_type [TC]

lemma ACK_in_prim_rec [TC]: "i \<in> nat \<Longrightarrow> ACK(i) \<in> prim_rec"
  by (induct set: nat) simp_all

lemma ack_type [TC]: "\<lbrakk>i \<in> nat;  j \<in> nat\<rbrakk> \<Longrightarrow>  ack(i,j) \<in> nat"
  by auto


subsection \<open>Ackermann's function cases\<close>

lemma ack_0: "j \<in> nat \<Longrightarrow> ack(0,j) = succ(j)"
  \<comment> \<open>PROPERTY A 1\<close>
  by (simp add: SC)

lemma ack_succ_0: "ack(succ(i), 0) = ack(i,1)"
  \<comment> \<open>PROPERTY A 2\<close>
  by (simp add: CONSTANT PREC_0)

lemma ack_succ_succ:
  "\<lbrakk>i\<in>nat;  j\<in>nat\<rbrakk> \<Longrightarrow> ack(succ(i), succ(j)) = ack(i, ack(succ(i), j))"
  \<comment> \<open>PROPERTY A 3\<close>
  by (simp add: CONSTANT PREC_succ COMP_1 PROJ_0)

lemmas [simp] = ack_0 ack_succ_0 ack_succ_succ ack_type
  and [simp del] = ACK.simps


lemma lt_ack2: "i \<in> nat \<Longrightarrow> j \<in> nat \<Longrightarrow> j < ack(i,j)"
  \<comment> \<open>PROPERTY A 4\<close>
  apply (induct i arbitrary: j set: nat)
   apply simp
  apply (induct_tac j)
   apply (erule_tac [2] succ_leI [THEN lt_trans1])
   apply (rule nat_0I [THEN nat_0_le, THEN lt_trans])
   apply auto
  done

lemma ack_lt_ack_succ2: "\<lbrakk>i\<in>nat; j\<in>nat\<rbrakk> \<Longrightarrow> ack(i,j) < ack(i, succ(j))"
  \<comment> \<open>PROPERTY A 5-, the single-step lemma\<close>
  by (induct set: nat) (simp_all add: lt_ack2)

lemma ack_lt_mono2: "\<lbrakk>j<k; i \<in> nat; k \<in> nat\<rbrakk> \<Longrightarrow> ack(i,j) < ack(i,k)"
  \<comment> \<open>PROPERTY A 5, monotonicity for \<open><\<close>\<close>
  apply (frule lt_nat_in_nat, assumption)
  apply (erule succ_lt_induct)
    apply assumption
   apply (rule_tac [2] lt_trans)
    apply (auto intro: ack_lt_ack_succ2)
  done

lemma ack_le_mono2: "\<lbrakk>j\<le>k;  i\<in>nat;  k\<in>nat\<rbrakk> \<Longrightarrow> ack(i,j) \<le> ack(i,k)"
  \<comment> \<open>PROPERTY A 5', monotonicity for \<open>\<le>\<close>\<close>
  apply (rule_tac f = "\<lambda>j. ack (i,j) " in Ord_lt_mono_imp_le_mono)
     apply (assumption | rule ack_lt_mono2 ack_type [THEN nat_into_Ord])+
  done

lemma ack2_le_ack1:
  "\<lbrakk>i\<in>nat;  j\<in>nat\<rbrakk> \<Longrightarrow> ack(i, succ(j)) \<le> ack(succ(i), j)"
  \<comment> \<open>PROPERTY A 6\<close>
  apply (induct_tac j)
   apply simp_all
  apply (rule ack_le_mono2)
    apply (rule lt_ack2 [THEN succ_leI, THEN le_trans])
      apply auto
  done

lemma ack_lt_ack_succ1: "\<lbrakk>i \<in> nat; j \<in> nat\<rbrakk> \<Longrightarrow> ack(i,j) < ack(succ(i),j)"
  \<comment> \<open>PROPERTY A 7-, the single-step lemma\<close>
  apply (rule ack_lt_mono2 [THEN lt_trans2])
     apply (rule_tac [4] ack2_le_ack1)
      apply auto
  done

lemma ack_lt_mono1: "\<lbrakk>i<j; j \<in> nat; k \<in> nat\<rbrakk> \<Longrightarrow> ack(i,k) < ack(j,k)"
  \<comment> \<open>PROPERTY A 7, monotonicity for \<open><\<close>\<close>
  apply (frule lt_nat_in_nat, assumption)
  apply (erule succ_lt_induct)
    apply assumption
   apply (rule_tac [2] lt_trans)
    apply (auto intro: ack_lt_ack_succ1)
  done

lemma ack_le_mono1: "\<lbrakk>i\<le>j; j \<in> nat; k \<in> nat\<rbrakk> \<Longrightarrow> ack(i,k) \<le> ack(j,k)"
  \<comment> \<open>PROPERTY A 7', monotonicity for \<open>\<le>\<close>\<close>
  apply (rule_tac f = "\<lambda>j. ack (j,k) " in Ord_lt_mono_imp_le_mono)
     apply (assumption | rule ack_lt_mono1 ack_type [THEN nat_into_Ord])+
  done

lemma ack_1: "j \<in> nat \<Longrightarrow> ack(1,j) = succ(succ(j))"
  \<comment> \<open>PROPERTY A 8\<close>
  by (induct set: nat) simp_all

lemma ack_2: "j \<in> nat \<Longrightarrow> ack(succ(1),j) = succ(succ(succ(j#+j)))"
  \<comment> \<open>PROPERTY A 9\<close>
  by (induct set: nat) (simp_all add: ack_1)

lemma ack_nest_bound:
  "\<lbrakk>i1 \<in> nat; i2 \<in> nat; j \<in> nat\<rbrakk>
    \<Longrightarrow> ack(i1, ack(i2,j)) < ack(succ(succ(i1#+i2)), j)"
  \<comment> \<open>PROPERTY A 10\<close>
  apply (rule lt_trans2 [OF _ ack2_le_ack1])
    apply simp
    apply (rule add_le_self [THEN ack_le_mono1, THEN lt_trans1])
       apply auto
  apply (force intro: add_le_self2 [THEN ack_lt_mono1, THEN ack_lt_mono2])
  done

lemma ack_add_bound:
  "\<lbrakk>i1 \<in> nat; i2 \<in> nat; j \<in> nat\<rbrakk>
    \<Longrightarrow> ack(i1,j) #+ ack(i2,j) < ack(succ(succ(succ(succ(i1#+i2)))), j)"
  \<comment> \<open>PROPERTY A 11\<close>
  apply (rule_tac j = "ack (succ (1), ack (i1 #+ i2, j))" in lt_trans)
   apply (simp add: ack_2)
   apply (rule_tac [2] ack_nest_bound [THEN lt_trans2])
      apply (rule add_le_mono [THEN leI, THEN leI])
         apply (auto intro: add_le_self add_le_self2 ack_le_mono1)
  done

lemma ack_add_bound2:
     "\<lbrakk>i < ack(k,j);  j \<in> nat;  k \<in> nat\<rbrakk>
      \<Longrightarrow> i#+j < ack(succ(succ(succ(succ(k)))), j)"
  \<comment> \<open>PROPERTY A 12.\<close>
  \<comment> \<open>Article uses existential quantifier but the ALF proof used \<^term>\<open>k#+#4\<close>.\<close>
  \<comment> \<open>Quantified version must be nested \<open>\<exists>k'. \<forall>i,j \<dots>\<close>.\<close>
  apply (rule_tac j = "ack (k,j) #+ ack (0,j) " in lt_trans)
   apply (rule_tac [2] ack_add_bound [THEN lt_trans2])
      apply (rule add_lt_mono)
         apply auto
  done


subsection \<open>Main result\<close>

declare list_add_type [simp]

lemma SC_case: "l \<in> list(nat) \<Longrightarrow> SC ` l < ack(1, list_add(l))"
    unfolding SC_def
  apply (erule list.cases)
   apply (simp add: succ_iff)
  apply (simp add: ack_1 add_le_self)
  done

lemma lt_ack1: "\<lbrakk>i \<in> nat; j \<in> nat\<rbrakk> \<Longrightarrow> i < ack(i,j)"
  \<comment> \<open>PROPERTY A 4'? Extra lemma needed for \<open>CONSTANT\<close> case, constant functions.\<close>
  apply (induct_tac i)
   apply (simp add: nat_0_le)
  apply (erule lt_trans1 [OF succ_leI ack_lt_ack_succ1])
   apply auto
  done

lemma CONSTANT_case:
    "\<lbrakk>l \<in> list(nat);  k \<in> nat\<rbrakk> \<Longrightarrow> CONSTANT(k) ` l < ack(k, list_add(l))"
  by (simp add: CONSTANT_def lt_ack1)

lemma PROJ_case [rule_format]:
    "l \<in> list(nat) \<Longrightarrow> \<forall>i \<in> nat. PROJ(i) ` l < ack(0, list_add(l))"
    unfolding PROJ_def
  apply simp
  apply (erule list.induct)
   apply (simp add: nat_0_le)
  apply simp
  apply (rule ballI)
  apply (erule_tac n = i in natE)
   apply (simp add: add_le_self)
  apply simp
  apply (erule bspec [THEN lt_trans2])
   apply (rule_tac [2] add_le_self2 [THEN succ_leI])
   apply auto
  done

text \<open>
  \medskip \<open>COMP\<close> case.
\<close>

lemma COMP_map_lemma:
  "fs \<in> list({f \<in> prim_rec. \<exists>kf \<in> nat. \<forall>l \<in> list(nat). f`l < ack(kf, list_add(l))})
    \<Longrightarrow> \<exists>k \<in> nat. \<forall>l \<in> list(nat).
      list_add(map(\<lambda>f. f ` l, fs)) < ack(k, list_add(l))"
  apply (induct set: list)
   apply (rule_tac x = 0 in bexI)
    apply (simp_all add: lt_ack1 nat_0_le)
  apply clarify
  apply (rule ballI [THEN bexI])
  apply (rule add_lt_mono [THEN lt_trans])
       apply (rule_tac [5] ack_add_bound)
         apply blast
        apply auto
  done

lemma COMP_case:
 "\<lbrakk>kg\<in>nat;
     \<forall>l \<in> list(nat). g`l < ack(kg, list_add(l));
     fs \<in> list({f \<in> prim_rec .
                 \<exists>kf \<in> nat. \<forall>l \<in> list(nat).
                        f`l < ack(kf, list_add(l))})\<rbrakk>
   \<Longrightarrow> \<exists>k \<in> nat. \<forall>l \<in> list(nat). COMP(g,fs)`l < ack(k, list_add(l))"
  apply (simp add: COMP_def)
  apply (frule list_CollectD)
  apply (erule COMP_map_lemma [THEN bexE])
  apply (rule ballI [THEN bexI])
   apply (erule bspec [THEN lt_trans])
    apply (rule_tac [2] lt_trans)
     apply (rule_tac [3] ack_nest_bound)
       apply (erule_tac [2] bspec [THEN ack_lt_mono2])
         apply auto
  done

text \<open>
  \medskip \<open>PREC\<close> case.
\<close>

lemma PREC_case_lemma:
 "\<lbrakk>\<forall>l \<in> list(nat). f`l #+ list_add(l) < ack(kf, list_add(l));
     \<forall>l \<in> list(nat). g`l #+ list_add(l) < ack(kg, list_add(l));
     f \<in> prim_rec;  kf\<in>nat;
     g \<in> prim_rec;  kg\<in>nat;
     l \<in> list(nat)\<rbrakk>
  \<Longrightarrow> PREC(f,g)`l #+ list_add(l) < ack(succ(kf#+kg), list_add(l))"
    unfolding PREC_def
  apply (erule list.cases)
   apply (simp add: lt_trans [OF nat_le_refl lt_ack2])
  apply simp
  apply (erule ssubst)  \<comment> \<open>get rid of the needless assumption\<close>
  apply (induct_tac a)
   apply simp_all
   txt \<open>base case\<close>
   apply (rule lt_trans, erule bspec, assumption)
   apply (simp add: add_le_self [THEN ack_lt_mono1])
  txt \<open>ind step\<close>
  apply (rule succ_leI [THEN lt_trans1])
   apply (rule_tac j = "g ` ll #+ mm" for ll mm in lt_trans1)
    apply (erule_tac [2] bspec)
    apply (rule nat_le_refl [THEN add_le_mono])
       apply typecheck
   apply (simp add: add_le_self2)
   txt \<open>final part of the simplification\<close>
  apply simp
  apply (rule add_le_self2 [THEN ack_le_mono1, THEN lt_trans1])
     apply (erule_tac [4] ack_lt_mono2)
      apply auto
  done

lemma PREC_case:
   "\<lbrakk>f \<in> prim_rec;  kf\<in>nat;
       g \<in> prim_rec;  kg\<in>nat;
       \<forall>l \<in> list(nat). f`l < ack(kf, list_add(l));
       \<forall>l \<in> list(nat). g`l < ack(kg, list_add(l))\<rbrakk>
    \<Longrightarrow> \<exists>k \<in> nat. \<forall>l \<in> list(nat). PREC(f,g)`l< ack(k, list_add(l))"
  apply (rule ballI [THEN bexI])
   apply (rule lt_trans1 [OF add_le_self PREC_case_lemma])
          apply typecheck
     apply (blast intro: ack_add_bound2 list_add_type)+
  done

lemma ack_bounds_prim_rec:
    "f \<in> prim_rec \<Longrightarrow> \<exists>k \<in> nat. \<forall>l \<in> list(nat). f`l < ack(k, list_add(l))"
  apply (induct set: prim_rec)
  apply (auto intro: SC_case CONSTANT_case PROJ_case COMP_case PREC_case)
  done

theorem ack_not_prim_rec:
    "(\<lambda>l \<in> list(nat). list_case(0, \<lambda>x xs. ack(x,x), l)) \<notin> prim_rec"
  apply (rule notI)
  apply (drule ack_bounds_prim_rec)
  apply force
  done

end
