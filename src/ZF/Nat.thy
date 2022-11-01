(*  Title:      ZF/Nat.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section\<open>The Natural numbers As a Least Fixed Point\<close>

theory Nat imports OrdQuant Bool begin

definition
  nat :: i  where
    "nat \<equiv> lfp(Inf, \<lambda>X. {0} \<union> {succ(i). i \<in> X})"

definition
  quasinat :: "i \<Rightarrow> o"  where
    "quasinat(n) \<equiv> n=0 | (\<exists>m. n = succ(m))"

definition
  (*Has an unconditional succ case, which is used in "recursor" below.*)
  nat_case :: "[i, i\<Rightarrow>i, i]\<Rightarrow>i"  where
    "nat_case(a,b,k) \<equiv> THE y. k=0 \<and> y=a | (\<exists>x. k=succ(x) \<and> y=b(x))"

definition
  nat_rec :: "[i, i, [i,i]\<Rightarrow>i]\<Rightarrow>i"  where
    "nat_rec(k,a,b) \<equiv>
          wfrec(Memrel(nat), k, \<lambda>n f. nat_case(a, \<lambda>m. b(m, f`m), n))"

  (*Internalized relations on the naturals*)

definition
  Le :: i  where
    "Le \<equiv> {\<langle>x,y\<rangle>:nat*nat. x \<le> y}"

definition
  Lt :: i  where
    "Lt \<equiv> {\<langle>x, y\<rangle>:nat*nat. x < y}"

definition
  Ge :: i  where
    "Ge \<equiv> {\<langle>x,y\<rangle>:nat*nat. y \<le> x}"

definition
  Gt :: i  where
    "Gt \<equiv> {\<langle>x,y\<rangle>:nat*nat. y < x}"

definition
  greater_than :: "i\<Rightarrow>i"  where
    "greater_than(n) \<equiv> {i \<in> nat. n < i}"

text\<open>No need for a less-than operator: a natural number is its list of
predecessors!\<close>


lemma nat_bnd_mono: "bnd_mono(Inf, \<lambda>X. {0} \<union> {succ(i). i \<in> X})"
apply (rule bnd_monoI)
apply (cut_tac infinity, blast, blast)
done

(* @{term"nat = {0} \<union> {succ(x). x \<in> nat}"} *)
lemmas nat_unfold = nat_bnd_mono [THEN nat_def [THEN def_lfp_unfold]]

(** Type checking of 0 and successor **)

lemma nat_0I [iff,TC]: "0 \<in> nat"
apply (subst nat_unfold)
apply (rule singletonI [THEN UnI1])
done

lemma nat_succI [intro!,TC]: "n \<in> nat \<Longrightarrow> succ(n) \<in> nat"
apply (subst nat_unfold)
apply (erule RepFunI [THEN UnI2])
done

lemma nat_1I [iff,TC]: "1 \<in> nat"
by (rule nat_0I [THEN nat_succI])

lemma nat_2I [iff,TC]: "2 \<in> nat"
by (rule nat_1I [THEN nat_succI])

lemma bool_subset_nat: "bool \<subseteq> nat"
by (blast elim!: boolE)

lemmas bool_into_nat = bool_subset_nat [THEN subsetD]


subsection\<open>Injectivity Properties and Induction\<close>

(*Mathematical induction*)
lemma nat_induct [case_names 0 succ, induct set: nat]:
    "\<lbrakk>n \<in> nat;  P(0);  \<And>x. \<lbrakk>x \<in> nat;  P(x)\<rbrakk> \<Longrightarrow> P(succ(x))\<rbrakk> \<Longrightarrow> P(n)"
by (erule def_induct [OF nat_def nat_bnd_mono], blast)

lemma natE:
 assumes "n \<in> nat"
 obtains ("0") "n=0" | (succ) x where "x \<in> nat" "n=succ(x)"
using assms
by (rule nat_unfold [THEN equalityD1, THEN subsetD, THEN UnE]) auto

lemma nat_into_Ord [simp]: "n \<in> nat \<Longrightarrow> Ord(n)"
by (erule nat_induct, auto)

(* @{term"i \<in> nat \<Longrightarrow> 0 \<le> i"}; same thing as @{term"0<succ(i)"}  *)
lemmas nat_0_le = nat_into_Ord [THEN Ord_0_le]

(* @{term"i \<in> nat \<Longrightarrow> i \<le> i"}; same thing as @{term"i<succ(i)"}  *)
lemmas nat_le_refl = nat_into_Ord [THEN le_refl]

lemma Ord_nat [iff]: "Ord(nat)"
apply (rule OrdI)
apply (erule_tac [2] nat_into_Ord [THEN Ord_is_Transset])
  unfolding Transset_def
apply (rule ballI)
apply (erule nat_induct, auto)
done

lemma Limit_nat [iff]: "Limit(nat)"
  unfolding Limit_def
apply (safe intro!: ltI Ord_nat)
apply (erule ltD)
done

lemma naturals_not_limit: "a \<in> nat \<Longrightarrow> \<not> Limit(a)"
by (induct a rule: nat_induct, auto)

lemma succ_natD: "succ(i): nat \<Longrightarrow> i \<in> nat"
by (rule Ord_trans [OF succI1], auto)

lemma nat_succ_iff [iff]: "succ(n): nat \<longleftrightarrow> n \<in> nat"
by (blast dest!: succ_natD)

lemma nat_le_Limit: "Limit(i) \<Longrightarrow> nat \<le> i"
apply (rule subset_imp_le)
apply (simp_all add: Limit_is_Ord)
apply (rule subsetI)
apply (erule nat_induct)
 apply (erule Limit_has_0 [THEN ltD])
apply (blast intro: Limit_has_succ [THEN ltD] ltI Limit_is_Ord)
done

(* \<lbrakk>succ(i): k;  k \<in> nat\<rbrakk> \<Longrightarrow> i \<in> k *)
lemmas succ_in_naturalD = Ord_trans [OF succI1 _ nat_into_Ord]

lemma lt_nat_in_nat: "\<lbrakk>m<n;  n \<in> nat\<rbrakk> \<Longrightarrow> m \<in> nat"
apply (erule ltE)
apply (erule Ord_trans, assumption, simp)
done

lemma le_in_nat: "\<lbrakk>m \<le> n; n \<in> nat\<rbrakk> \<Longrightarrow> m \<in> nat"
by (blast dest!: lt_nat_in_nat)


subsection\<open>Variations on Mathematical Induction\<close>

(*complete induction*)

lemmas complete_induct = Ord_induct [OF _ Ord_nat, case_names less, consumes 1]

lemma complete_induct_rule [case_names less, consumes 1]:
  "i \<in> nat \<Longrightarrow> (\<And>x. x \<in> nat \<Longrightarrow> (\<And>y. y \<in> x \<Longrightarrow> P(y)) \<Longrightarrow> P(x)) \<Longrightarrow> P(i)"
  using complete_induct [of i P] by simp

(*Induction starting from m rather than 0*)
lemma nat_induct_from:
  assumes "m \<le> n" "m \<in> nat" "n \<in> nat"
    and "P(m)"
    and "\<And>x. \<lbrakk>x \<in> nat;  m \<le> x;  P(x)\<rbrakk> \<Longrightarrow> P(succ(x))"
  shows "P(n)"
proof -
  from assms(3) have "m \<le> n \<longrightarrow> P(m) \<longrightarrow> P(n)"
    by (rule nat_induct) (use assms(5) in \<open>simp_all add: distrib_simps le_succ_iff\<close>)
  with assms(1,2,4) show ?thesis by blast
qed

(*Induction suitable for subtraction and less-than*)
lemma diff_induct [case_names 0 0_succ succ_succ, consumes 2]:
    "\<lbrakk>m \<in> nat;  n \<in> nat;
        \<And>x. x \<in> nat \<Longrightarrow> P(x,0);
        \<And>y. y \<in> nat \<Longrightarrow> P(0,succ(y));
        \<And>x y. \<lbrakk>x \<in> nat;  y \<in> nat;  P(x,y)\<rbrakk> \<Longrightarrow> P(succ(x),succ(y))\<rbrakk>
     \<Longrightarrow> P(m,n)"
apply (erule_tac x = m in rev_bspec)
apply (erule nat_induct, simp)
apply (rule ballI)
apply (rename_tac i j)
apply (erule_tac n=j in nat_induct, auto)
done


(** Induction principle analogous to trancl_induct **)

lemma succ_lt_induct_lemma [rule_format]:
     "m \<in> nat \<Longrightarrow> P(m,succ(m)) \<longrightarrow> (\<forall>x\<in>nat. P(m,x) \<longrightarrow> P(m,succ(x))) \<longrightarrow>
                 (\<forall>n\<in>nat. m<n \<longrightarrow> P(m,n))"
apply (erule nat_induct)
 apply (intro impI, rule nat_induct [THEN ballI])
   prefer 4 apply (intro impI, rule nat_induct [THEN ballI])
apply (auto simp add: le_iff)
done

lemma succ_lt_induct:
    "\<lbrakk>m<n;  n \<in> nat;
        P(m,succ(m));
        \<And>x. \<lbrakk>x \<in> nat;  P(m,x)\<rbrakk> \<Longrightarrow> P(m,succ(x))\<rbrakk>
     \<Longrightarrow> P(m,n)"
by (blast intro: succ_lt_induct_lemma lt_nat_in_nat)

subsection\<open>quasinat: to allow a case-split rule for \<^term>\<open>nat_case\<close>\<close>

text\<open>True if the argument is zero or any successor\<close>
lemma [iff]: "quasinat(0)"
by (simp add: quasinat_def)

lemma [iff]: "quasinat(succ(x))"
by (simp add: quasinat_def)

lemma nat_imp_quasinat: "n \<in> nat \<Longrightarrow> quasinat(n)"
by (erule natE, simp_all)

lemma non_nat_case: "\<not> quasinat(x) \<Longrightarrow> nat_case(a,b,x) = 0"
by (simp add: quasinat_def nat_case_def)

lemma nat_cases_disj: "k=0 | (\<exists>y. k = succ(y)) | \<not> quasinat(k)"
apply (case_tac "k=0", simp)
apply (case_tac "\<exists>m. k = succ(m)")
apply (simp_all add: quasinat_def)
done

lemma nat_cases:
     "\<lbrakk>k=0 \<Longrightarrow> P;  \<And>y. k = succ(y) \<Longrightarrow> P; \<not> quasinat(k) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (insert nat_cases_disj [of k], blast)

(** nat_case **)

lemma nat_case_0 [simp]: "nat_case(a,b,0) = a"
by (simp add: nat_case_def)

lemma nat_case_succ [simp]: "nat_case(a,b,succ(n)) = b(n)"
by (simp add: nat_case_def)

lemma nat_case_type [TC]:
    "\<lbrakk>n \<in> nat;  a \<in> C(0);  \<And>m. m \<in> nat \<Longrightarrow> b(m): C(succ(m))\<rbrakk>
     \<Longrightarrow> nat_case(a,b,n) \<in> C(n)"
by (erule nat_induct, auto)

lemma split_nat_case:
  "P(nat_case(a,b,k)) \<longleftrightarrow>
   ((k=0 \<longrightarrow> P(a)) \<and> (\<forall>x. k=succ(x) \<longrightarrow> P(b(x))) \<and> (\<not> quasinat(k) \<longrightarrow> P(0)))"
apply (rule nat_cases [of k])
apply (auto simp add: non_nat_case)
done


subsection\<open>Recursion on the Natural Numbers\<close>

(** nat_rec is used to define eclose and transrec, then becomes obsolete.
    The operator rec, from arith.thy, has fewer typing conditions **)

lemma nat_rec_0: "nat_rec(0,a,b) = a"
apply (rule nat_rec_def [THEN def_wfrec, THEN trans])
 apply (rule wf_Memrel)
apply (rule nat_case_0)
done

lemma nat_rec_succ: "m \<in> nat \<Longrightarrow> nat_rec(succ(m),a,b) = b(m, nat_rec(m,a,b))"
apply (rule nat_rec_def [THEN def_wfrec, THEN trans])
 apply (rule wf_Memrel)
apply (simp add: vimage_singleton_iff)
done

(** The union of two natural numbers is a natural number -- their maximum **)

lemma Un_nat_type [TC]: "\<lbrakk>i \<in> nat; j \<in> nat\<rbrakk> \<Longrightarrow> i \<union> j \<in> nat"
apply (rule Un_least_lt [THEN ltD])
apply (simp_all add: lt_def)
done

lemma Int_nat_type [TC]: "\<lbrakk>i \<in> nat; j \<in> nat\<rbrakk> \<Longrightarrow> i \<inter> j \<in> nat"
apply (rule Int_greatest_lt [THEN ltD])
apply (simp_all add: lt_def)
done

(*needed to simplify unions over nat*)
lemma nat_nonempty [simp]: "nat \<noteq> 0"
by blast

text\<open>A natural number is the set of its predecessors\<close>
lemma nat_eq_Collect_lt: "i \<in> nat \<Longrightarrow> {j\<in>nat. j<i} = i"
apply (rule equalityI)
apply (blast dest: ltD)
apply (auto simp add: Ord_mem_iff_lt)
apply (blast intro: lt_trans)
done

lemma Le_iff [iff]: "\<langle>x,y\<rangle> \<in> Le \<longleftrightarrow> x \<le> y \<and> x \<in> nat \<and> y \<in> nat"
by (force simp add: Le_def)

end
