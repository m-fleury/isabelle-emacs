(*  Title:      ZF/Arith.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

(*"Difference" is subtraction of natural numbers.
  There are no negative numbers; we have
     m #- n = 0  iff  m<=n   and     m #- n = succ(k) iff m>n.
  Also, rec(m, 0, \<lambda>z w.z) is pred(m).
*)

section\<open>Arithmetic Operators and Their Definitions\<close>

theory Arith imports Univ begin

text\<open>Proofs about elementary arithmetic: addition, multiplication, etc.\<close>

definition
  pred   :: "i\<Rightarrow>i"    (*inverse of succ*)  where
    "pred(y) \<equiv> nat_case(0, \<lambda>x. x, y)"

definition
  natify :: "i\<Rightarrow>i"    (*coerces non-nats to nats*)  where
    "natify \<equiv> Vrecursor(\<lambda>f a. if a = succ(pred(a)) then succ(f`pred(a))
                                                    else 0)"

consts
  raw_add  :: "[i,i]\<Rightarrow>i"
  raw_diff  :: "[i,i]\<Rightarrow>i"
  raw_mult  :: "[i,i]\<Rightarrow>i"

primrec
  "raw_add (0, n) = n"
  "raw_add (succ(m), n) = succ(raw_add(m, n))"

primrec
  raw_diff_0:     "raw_diff(m, 0) = m"
  raw_diff_succ:  "raw_diff(m, succ(n)) =
                     nat_case(0, \<lambda>x. x, raw_diff(m, n))"

primrec
  "raw_mult(0, n) = 0"
  "raw_mult(succ(m), n) = raw_add (n, raw_mult(m, n))"

definition
  add :: "[i,i]\<Rightarrow>i"                    (infixl \<open>#+\<close> 65)  where
    "m #+ n \<equiv> raw_add (natify(m), natify(n))"

definition
  diff :: "[i,i]\<Rightarrow>i"                    (infixl \<open>#-\<close> 65)  where
    "m #- n \<equiv> raw_diff (natify(m), natify(n))"

definition
  mult :: "[i,i]\<Rightarrow>i"                    (infixl \<open>#*\<close> 70)  where
    "m #* n \<equiv> raw_mult (natify(m), natify(n))"

definition
  raw_div  :: "[i,i]\<Rightarrow>i"  where
    "raw_div (m, n) \<equiv>
       transrec(m, \<lambda>j f. if j<n | n=0 then 0 else succ(f`(j#-n)))"

definition
  raw_mod  :: "[i,i]\<Rightarrow>i"  where
    "raw_mod (m, n) \<equiv>
       transrec(m, \<lambda>j f. if j<n | n=0 then j else f`(j#-n))"

definition
  div  :: "[i,i]\<Rightarrow>i"                    (infixl \<open>div\<close> 70)  where
    "m div n \<equiv> raw_div (natify(m), natify(n))"

definition
  mod  :: "[i,i]\<Rightarrow>i"                    (infixl \<open>mod\<close> 70)  where
    "m mod n \<equiv> raw_mod (natify(m), natify(n))"

declare rec_type [simp]
        nat_0_le [simp]


lemma zero_lt_lemma: "\<lbrakk>0<k; k \<in> nat\<rbrakk> \<Longrightarrow> \<exists>j\<in>nat. k = succ(j)"
apply (erule rev_mp)
apply (induct_tac "k", auto)
done

(* @{term"\<lbrakk>0 < k; k \<in> nat; \<And>j. \<lbrakk>j \<in> nat; k = succ(j)\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"} *)
lemmas zero_lt_natE = zero_lt_lemma [THEN bexE]


subsection\<open>\<open>natify\<close>, the Coercion to \<^term>\<open>nat\<close>\<close>

lemma pred_succ_eq [simp]: "pred(succ(y)) = y"
by (unfold pred_def, auto)

lemma natify_succ: "natify(succ(x)) = succ(natify(x))"
by (rule natify_def [THEN def_Vrecursor, THEN trans], auto)

lemma natify_0 [simp]: "natify(0) = 0"
by (rule natify_def [THEN def_Vrecursor, THEN trans], auto)

lemma natify_non_succ: "\<forall>z. x \<noteq> succ(z) \<Longrightarrow> natify(x) = 0"
by (rule natify_def [THEN def_Vrecursor, THEN trans], auto)

lemma natify_in_nat [iff,TC]: "natify(x) \<in> nat"
apply (rule_tac a=x in eps_induct)
apply (case_tac "\<exists>z. x = succ(z)")
apply (auto simp add: natify_succ natify_non_succ)
done

lemma natify_ident [simp]: "n \<in> nat \<Longrightarrow> natify(n) = n"
apply (induct_tac "n")
apply (auto simp add: natify_succ)
done

lemma natify_eqE: "\<lbrakk>natify(x) = y;  x \<in> nat\<rbrakk> \<Longrightarrow> x=y"
by auto


(*** Collapsing rules: to remove natify from arithmetic expressions ***)

lemma natify_idem [simp]: "natify(natify(x)) = natify(x)"
by simp

(** Addition **)

lemma add_natify1 [simp]: "natify(m) #+ n = m #+ n"
by (simp add: add_def)

lemma add_natify2 [simp]: "m #+ natify(n) = m #+ n"
by (simp add: add_def)

(** Multiplication **)

lemma mult_natify1 [simp]: "natify(m) #* n = m #* n"
by (simp add: mult_def)

lemma mult_natify2 [simp]: "m #* natify(n) = m #* n"
by (simp add: mult_def)

(** Difference **)

lemma diff_natify1 [simp]: "natify(m) #- n = m #- n"
by (simp add: diff_def)

lemma diff_natify2 [simp]: "m #- natify(n) = m #- n"
by (simp add: diff_def)

(** Remainder **)

lemma mod_natify1 [simp]: "natify(m) mod n = m mod n"
by (simp add: mod_def)

lemma mod_natify2 [simp]: "m mod natify(n) = m mod n"
by (simp add: mod_def)


(** Quotient **)

lemma div_natify1 [simp]: "natify(m) div n = m div n"
by (simp add: div_def)

lemma div_natify2 [simp]: "m div natify(n) = m div n"
by (simp add: div_def)


subsection\<open>Typing rules\<close>

(** Addition **)

lemma raw_add_type: "\<lbrakk>m\<in>nat;  n\<in>nat\<rbrakk> \<Longrightarrow> raw_add (m, n) \<in> nat"
by (induct_tac "m", auto)

lemma add_type [iff,TC]: "m #+ n \<in> nat"
by (simp add: add_def raw_add_type)

(** Multiplication **)

lemma raw_mult_type: "\<lbrakk>m\<in>nat;  n\<in>nat\<rbrakk> \<Longrightarrow> raw_mult (m, n) \<in> nat"
apply (induct_tac "m")
apply (simp_all add: raw_add_type)
done

lemma mult_type [iff,TC]: "m #* n \<in> nat"
by (simp add: mult_def raw_mult_type)


(** Difference **)

lemma raw_diff_type: "\<lbrakk>m\<in>nat;  n\<in>nat\<rbrakk> \<Longrightarrow> raw_diff (m, n) \<in> nat"
by (induct_tac "n", auto)

lemma diff_type [iff,TC]: "m #- n \<in> nat"
by (simp add: diff_def raw_diff_type)

lemma diff_0_eq_0 [simp]: "0 #- n = 0"
  unfolding diff_def
apply (rule natify_in_nat [THEN nat_induct], auto)
done

(*Must simplify BEFORE the induction: else we get a critical pair*)
lemma diff_succ_succ [simp]: "succ(m) #- succ(n) = m #- n"
apply (simp add: natify_succ diff_def)
apply (rule_tac x1 = n in natify_in_nat [THEN nat_induct], auto)
done

(*This defining property is no longer wanted*)
declare raw_diff_succ [simp del]

(*Natify has weakened this law, compared with the older approach*)
lemma diff_0 [simp]: "m #- 0 = natify(m)"
by (simp add: diff_def)

lemma diff_le_self: "m\<in>nat \<Longrightarrow> (m #- n) \<le> m"
apply (subgoal_tac " (m #- natify (n)) \<le> m")
apply (rule_tac [2] m = m and n = "natify (n) " in diff_induct)
apply (erule_tac [6] leE)
apply (simp_all add: le_iff)
done


subsection\<open>Addition\<close>

(*Natify has weakened this law, compared with the older approach*)
lemma add_0_natify [simp]: "0 #+ m = natify(m)"
by (simp add: add_def)

lemma add_succ [simp]: "succ(m) #+ n = succ(m #+ n)"
by (simp add: natify_succ add_def)

lemma add_0: "m \<in> nat \<Longrightarrow> 0 #+ m = m"
by simp

(*Associative law for addition*)
lemma add_assoc: "(m #+ n) #+ k = m #+ (n #+ k)"
apply (subgoal_tac "(natify(m) #+ natify(n)) #+ natify(k) =
                    natify(m) #+ (natify(n) #+ natify(k))")
apply (rule_tac [2] n = "natify(m)" in nat_induct)
apply auto
done

(*The following two lemmas are used for add_commute and sometimes
  elsewhere, since they are safe for rewriting.*)
lemma add_0_right_natify [simp]: "m #+ 0 = natify(m)"
apply (subgoal_tac "natify(m) #+ 0 = natify(m)")
apply (rule_tac [2] n = "natify(m)" in nat_induct)
apply auto
done

lemma add_succ_right [simp]: "m #+ succ(n) = succ(m #+ n)"
  unfolding add_def
apply (rule_tac n = "natify(m) " in nat_induct)
apply (auto simp add: natify_succ)
done

lemma add_0_right: "m \<in> nat \<Longrightarrow> m #+ 0 = m"
by auto

(*Commutative law for addition*)
lemma add_commute: "m #+ n = n #+ m"
apply (subgoal_tac "natify(m) #+ natify(n) = natify(n) #+ natify(m) ")
apply (rule_tac [2] n = "natify(m) " in nat_induct)
apply auto
done

(*for a/c rewriting*)
lemma add_left_commute: "m#+(n#+k)=n#+(m#+k)"
apply (rule add_commute [THEN trans])
apply (rule add_assoc [THEN trans])
apply (rule add_commute [THEN subst_context])
done

(*Addition is an AC-operator*)
lemmas add_ac = add_assoc add_commute add_left_commute

(*Cancellation law on the left*)
lemma raw_add_left_cancel:
     "\<lbrakk>raw_add(k, m) = raw_add(k, n);  k\<in>nat\<rbrakk> \<Longrightarrow> m=n"
apply (erule rev_mp)
apply (induct_tac "k", auto)
done

lemma add_left_cancel_natify: "k #+ m = k #+ n \<Longrightarrow> natify(m) = natify(n)"
  unfolding add_def
apply (drule raw_add_left_cancel, auto)
done

lemma add_left_cancel:
     "\<lbrakk>i = j;  i #+ m = j #+ n;  m\<in>nat;  n\<in>nat\<rbrakk> \<Longrightarrow> m = n"
by (force dest!: add_left_cancel_natify)

(*Thanks to Sten Agerholm*)
lemma add_le_elim1_natify: "k#+m \<le> k#+n \<Longrightarrow> natify(m) \<le> natify(n)"
apply (rule_tac P = "natify(k) #+m \<le> natify(k) #+n" in rev_mp)
apply (rule_tac [2] n = "natify(k) " in nat_induct)
apply auto
done

lemma add_le_elim1: "\<lbrakk>k#+m \<le> k#+n; m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> m \<le> n"
by (drule add_le_elim1_natify, auto)

lemma add_lt_elim1_natify: "k#+m < k#+n \<Longrightarrow> natify(m) < natify(n)"
apply (rule_tac P = "natify(k) #+m < natify(k) #+n" in rev_mp)
apply (rule_tac [2] n = "natify(k) " in nat_induct)
apply auto
done

lemma add_lt_elim1: "\<lbrakk>k#+m < k#+n; m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> m < n"
by (drule add_lt_elim1_natify, auto)

lemma zero_less_add: "\<lbrakk>n \<in> nat; m \<in> nat\<rbrakk> \<Longrightarrow> 0 < m #+ n \<longleftrightarrow> (0<m | 0<n)"
by (induct_tac "n", auto)


subsection\<open>Monotonicity of Addition\<close>

(*strict, in 1st argument; proof is by rule induction on 'less than'.
  Still need j\<in>nat, for consider j = omega.  Then we can have i<omega,
  which is the same as i\<in>nat, but natify(j)=0, so the conclusion fails.*)
lemma add_lt_mono1: "\<lbrakk>i<j; j\<in>nat\<rbrakk> \<Longrightarrow> i#+k < j#+k"
apply (frule lt_nat_in_nat, assumption)
apply (erule succ_lt_induct)
apply (simp_all add: leI)
done

text\<open>strict, in second argument\<close>
lemma add_lt_mono2: "\<lbrakk>i<j; j\<in>nat\<rbrakk> \<Longrightarrow> k#+i < k#+j"
by (simp add: add_commute [of k] add_lt_mono1)

text\<open>A [clumsy] way of lifting < monotonicity to \<open>\<le>\<close> monotonicity\<close>
lemma Ord_lt_mono_imp_le_mono:
  assumes lt_mono: "\<And>i j. \<lbrakk>i<j; j:k\<rbrakk> \<Longrightarrow> f(i) < f(j)"
      and ford:    "\<And>i. i:k \<Longrightarrow> Ord(f(i))"
      and leij:    "i \<le> j"
      and jink:    "j:k"
  shows "f(i) \<le> f(j)"
apply (insert leij jink)
apply (blast intro!: leCI lt_mono ford elim!: leE)
done

text\<open>\<open>\<le>\<close> monotonicity, 1st argument\<close>
lemma add_le_mono1: "\<lbrakk>i \<le> j; j\<in>nat\<rbrakk> \<Longrightarrow> i#+k \<le> j#+k"
apply (rule_tac f = "\<lambda>j. j#+k" in Ord_lt_mono_imp_le_mono, typecheck)
apply (blast intro: add_lt_mono1 add_type [THEN nat_into_Ord])+
done

text\<open>\<open>\<le>\<close> monotonicity, both arguments\<close>
lemma add_le_mono: "\<lbrakk>i \<le> j; k \<le> l; j\<in>nat; l\<in>nat\<rbrakk> \<Longrightarrow> i#+k \<le> j#+l"
apply (rule add_le_mono1 [THEN le_trans], assumption+)
apply (subst add_commute, subst add_commute, rule add_le_mono1, assumption+)
done

text\<open>Combinations of less-than and less-than-or-equals\<close>

lemma add_lt_le_mono: "\<lbrakk>i<j; k\<le>l; j\<in>nat; l\<in>nat\<rbrakk> \<Longrightarrow> i#+k < j#+l"
apply (rule add_lt_mono1 [THEN lt_trans2], assumption+)
apply (subst add_commute, subst add_commute, rule add_le_mono1, assumption+)
done

lemma add_le_lt_mono: "\<lbrakk>i\<le>j; k<l; j\<in>nat; l\<in>nat\<rbrakk> \<Longrightarrow> i#+k < j#+l"
by (subst add_commute, subst add_commute, erule add_lt_le_mono, assumption+)

text\<open>Less-than: in other words, strict in both arguments\<close>
lemma add_lt_mono: "\<lbrakk>i<j; k<l; j\<in>nat; l\<in>nat\<rbrakk> \<Longrightarrow> i#+k < j#+l"
apply (rule add_lt_le_mono)
apply (auto intro: leI)
done

(** Subtraction is the inverse of addition. **)

lemma diff_add_inverse: "(n#+m) #- n = natify(m)"
apply (subgoal_tac " (natify(n) #+ m) #- natify(n) = natify(m) ")
apply (rule_tac [2] n = "natify(n) " in nat_induct)
apply auto
done

lemma diff_add_inverse2: "(m#+n) #- n = natify(m)"
by (simp add: add_commute [of m] diff_add_inverse)

lemma diff_cancel: "(k#+m) #- (k#+n) = m #- n"
apply (subgoal_tac "(natify(k) #+ natify(m)) #- (natify(k) #+ natify(n)) =
                    natify(m) #- natify(n) ")
apply (rule_tac [2] n = "natify(k) " in nat_induct)
apply auto
done

lemma diff_cancel2: "(m#+k) #- (n#+k) = m #- n"
by (simp add: add_commute [of _ k] diff_cancel)

lemma diff_add_0: "n #- (n#+m) = 0"
apply (subgoal_tac "natify(n) #- (natify(n) #+ natify(m)) = 0")
apply (rule_tac [2] n = "natify(n) " in nat_induct)
apply auto
done

lemma pred_0 [simp]: "pred(0) = 0"
by (simp add: pred_def)

lemma eq_succ_imp_eq_m1: "\<lbrakk>i = succ(j); i\<in>nat\<rbrakk> \<Longrightarrow> j = i #- 1 \<and> j \<in>nat"
by simp

lemma pred_Un_distrib:
    "\<lbrakk>i\<in>nat; j\<in>nat\<rbrakk> \<Longrightarrow> pred(i \<union> j) = pred(i) \<union> pred(j)"
apply (erule_tac n=i in natE, simp)
apply (erule_tac n=j in natE, simp)
apply (simp add:  succ_Un_distrib [symmetric])
done

lemma pred_type [TC,simp]:
    "i \<in> nat \<Longrightarrow> pred(i) \<in> nat"
by (simp add: pred_def split: split_nat_case)

lemma nat_diff_pred: "\<lbrakk>i\<in>nat; j\<in>nat\<rbrakk> \<Longrightarrow> i #- succ(j) = pred(i #- j)"
apply (rule_tac m=i and n=j in diff_induct)
apply (auto simp add: pred_def nat_imp_quasinat split: split_nat_case)
done

lemma diff_succ_eq_pred: "i #- succ(j) = pred(i #- j)"
apply (insert nat_diff_pred [of "natify(i)" "natify(j)"])
apply (simp add: natify_succ [symmetric])
done

lemma nat_diff_Un_distrib:
    "\<lbrakk>i\<in>nat; j\<in>nat; k\<in>nat\<rbrakk> \<Longrightarrow> (i \<union> j) #- k = (i#-k) \<union> (j#-k)"
apply (rule_tac n=k in nat_induct)
apply (simp_all add: diff_succ_eq_pred pred_Un_distrib)
done

lemma diff_Un_distrib:
    "\<lbrakk>i\<in>nat; j\<in>nat\<rbrakk> \<Longrightarrow> (i \<union> j) #- k = (i#-k) \<union> (j#-k)"
by (insert nat_diff_Un_distrib [of i j "natify(k)"], simp)

text\<open>We actually prove \<^term>\<open>i #- j #- k = i #- (j #+ k)\<close>\<close>
lemma diff_diff_left [simplified]:
     "natify(i)#-natify(j)#-k = natify(i) #- (natify(j)#+k)"
by (rule_tac m="natify(i)" and n="natify(j)" in diff_induct, auto)


(** Lemmas for the CancelNumerals simproc **)

lemma eq_add_iff: "(u #+ m = u #+ n) \<longleftrightarrow> (0 #+ m = natify(n))"
apply auto
apply (blast dest: add_left_cancel_natify)
apply (simp add: add_def)
done

lemma less_add_iff: "(u #+ m < u #+ n) \<longleftrightarrow> (0 #+ m < natify(n))"
apply (auto simp add: add_lt_elim1_natify)
apply (drule add_lt_mono1)
apply (auto simp add: add_commute [of u])
done

lemma diff_add_eq: "((u #+ m) #- (u #+ n)) = ((0 #+ m) #- n)"
by (simp add: diff_cancel)

(*To tidy up the result of a simproc.  Only the RHS will be simplified.*)
lemma eq_cong2: "u = u' \<Longrightarrow> (t\<equiv>u) \<equiv> (t\<equiv>u')"
by auto

lemma iff_cong2: "u \<longleftrightarrow> u' \<Longrightarrow> (t\<equiv>u) \<equiv> (t\<equiv>u')"
by auto


subsection\<open>Multiplication\<close>

lemma mult_0 [simp]: "0 #* m = 0"
by (simp add: mult_def)

lemma mult_succ [simp]: "succ(m) #* n = n #+ (m #* n)"
by (simp add: add_def mult_def natify_succ raw_mult_type)

(*right annihilation in product*)
lemma mult_0_right [simp]: "m #* 0 = 0"
  unfolding mult_def
apply (rule_tac n = "natify(m) " in nat_induct)
apply auto
done

(*right successor law for multiplication*)
lemma mult_succ_right [simp]: "m #* succ(n) = m #+ (m #* n)"
apply (subgoal_tac "natify(m) #* succ (natify(n)) =
                    natify(m) #+ (natify(m) #* natify(n))")
apply (simp (no_asm_use) add: natify_succ add_def mult_def)
apply (rule_tac n = "natify(m) " in nat_induct)
apply (simp_all add: add_ac)
done

lemma mult_1_natify [simp]: "1 #* n = natify(n)"
by auto

lemma mult_1_right_natify [simp]: "n #* 1 = natify(n)"
by auto

lemma mult_1: "n \<in> nat \<Longrightarrow> 1 #* n = n"
by simp

lemma mult_1_right: "n \<in> nat \<Longrightarrow> n #* 1 = n"
by simp

(*Commutative law for multiplication*)
lemma mult_commute: "m #* n = n #* m"
apply (subgoal_tac "natify(m) #* natify(n) = natify(n) #* natify(m) ")
apply (rule_tac [2] n = "natify(m) " in nat_induct)
apply auto
done

(*addition distributes over multiplication*)
lemma add_mult_distrib: "(m #+ n) #* k = (m #* k) #+ (n #* k)"
apply (subgoal_tac "(natify(m) #+ natify(n)) #* natify(k) =
                    (natify(m) #* natify(k)) #+ (natify(n) #* natify(k))")
apply (rule_tac [2] n = "natify(m) " in nat_induct)
apply (simp_all add: add_assoc [symmetric])
done

(*Distributive law on the left*)
lemma add_mult_distrib_left: "k #* (m #+ n) = (k #* m) #+ (k #* n)"
apply (subgoal_tac "natify(k) #* (natify(m) #+ natify(n)) =
                    (natify(k) #* natify(m)) #+ (natify(k) #* natify(n))")
apply (rule_tac [2] n = "natify(m) " in nat_induct)
apply (simp_all add: add_ac)
done

(*Associative law for multiplication*)
lemma mult_assoc: "(m #* n) #* k = m #* (n #* k)"
apply (subgoal_tac "(natify(m) #* natify(n)) #* natify(k) =
                    natify(m) #* (natify(n) #* natify(k))")
apply (rule_tac [2] n = "natify(m) " in nat_induct)
apply (simp_all add: add_mult_distrib)
done

(*for a/c rewriting*)
lemma mult_left_commute: "m #* (n #* k) = n #* (m #* k)"
apply (rule mult_commute [THEN trans])
apply (rule mult_assoc [THEN trans])
apply (rule mult_commute [THEN subst_context])
done

lemmas mult_ac = mult_assoc mult_commute mult_left_commute


lemma lt_succ_eq_0_disj:
     "\<lbrakk>m\<in>nat; n\<in>nat\<rbrakk>
      \<Longrightarrow> (m < succ(n)) \<longleftrightarrow> (m = 0 | (\<exists>j\<in>nat. m = succ(j) \<and> j < n))"
by (induct_tac "m", auto)

lemma less_diff_conv [rule_format]:
     "\<lbrakk>j\<in>nat; k\<in>nat\<rbrakk> \<Longrightarrow> \<forall>i\<in>nat. (i < j #- k) \<longleftrightarrow> (i #+ k < j)"
by (erule_tac m = k in diff_induct, auto)

lemmas nat_typechecks = rec_type nat_0I nat_1I nat_succI Ord_nat

end
