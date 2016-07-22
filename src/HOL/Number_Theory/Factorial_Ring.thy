
(*  Title:      HOL/Number_Theory/Factorial_Ring.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Factorial (semi)rings\<close>

theory Factorial_Ring
imports 
  Main 
  "~~/src/HOL/Number_Theory/Primes"
  "~~/src/HOL/Library/Multiset"
begin

lemma (in semiring_gcd) dvd_productE:
  assumes "p dvd (a * b)"
  obtains x y where "p = x * y" "x dvd a" "y dvd b"
proof (cases "a = 0")
  case True
  thus ?thesis by (intro that[of p 1]) simp_all
next
  case False
  define x y where "x = gcd a p" and "y = p div x"
  have "p = x * y" by (simp add: x_def y_def)
  moreover have "x dvd a" by (simp add: x_def)
  moreover from assms have "p dvd gcd (b * a) (b * p)"
    by (intro gcd_greatest) (simp_all add: mult.commute)
  hence "p dvd b * gcd a p" by (simp add: gcd_mult_distrib)
  with False have "y dvd b" 
    by (simp add: x_def y_def div_dvd_iff_mult assms)
  ultimately show ?thesis by (rule that)
qed


context comm_semiring_1
begin

definition irreducible :: "'a \<Rightarrow> bool" where
  "irreducible p \<longleftrightarrow> p \<noteq> 0 \<and> \<not>p dvd 1 \<and> (\<forall>a b. p = a * b \<longrightarrow> a dvd 1 \<or> b dvd 1)"

lemma not_irreducible_zero [simp]: "\<not>irreducible 0"
  by (simp add: irreducible_def)

lemma irreducible_not_unit: "irreducible p \<Longrightarrow> \<not>p dvd 1"
  by (simp add: irreducible_def)

lemma not_irreducible_one [simp]: "\<not>irreducible 1"
  by (simp add: irreducible_def)

lemma irreducibleI:
  "p \<noteq> 0 \<Longrightarrow> \<not>p dvd 1 \<Longrightarrow> (\<And>a b. p = a * b \<Longrightarrow> a dvd 1 \<or> b dvd 1) \<Longrightarrow> irreducible p"
  by (simp add: irreducible_def)

lemma irreducibleD: "irreducible p \<Longrightarrow> p = a * b \<Longrightarrow> a dvd 1 \<or> b dvd 1"
  by (simp add: irreducible_def)

definition is_prime_elem :: "'a \<Rightarrow> bool" where
  "is_prime_elem p \<longleftrightarrow> p \<noteq> 0 \<and> \<not>p dvd 1 \<and> (\<forall>a b. p dvd (a * b) \<longrightarrow> p dvd a \<or> p dvd b)"

lemma not_is_prime_elem_zero [simp]: "\<not>is_prime_elem 0"
  by (simp add: is_prime_elem_def)

lemma is_prime_elem_not_unit: "is_prime_elem p \<Longrightarrow> \<not>p dvd 1"
  by (simp add: is_prime_elem_def)

lemma is_prime_elemI:
    "p \<noteq> 0 \<Longrightarrow> \<not>p dvd 1 \<Longrightarrow> (\<And>a b. p dvd (a * b) \<Longrightarrow> p dvd a \<or> p dvd b) \<Longrightarrow> is_prime_elem p"
  by (simp add: is_prime_elem_def)

lemma prime_divides_productD:
    "is_prime_elem p \<Longrightarrow> p dvd (a * b) \<Longrightarrow> p dvd a \<or> p dvd b"
  by (simp add: is_prime_elem_def)

lemma prime_dvd_mult_iff:
  "is_prime_elem p \<Longrightarrow> p dvd (a * b) \<longleftrightarrow> p dvd a \<or> p dvd b"
  by (auto simp: is_prime_elem_def)

lemma not_is_prime_elem_one [simp]:
  "\<not> is_prime_elem 1"
  by (auto dest: is_prime_elem_not_unit)

lemma is_prime_elem_not_zeroI:
  assumes "is_prime_elem p"
  shows "p \<noteq> 0"
  using assms by (auto intro: ccontr)

lemma is_prime_elem_imp_nonzero [simp]:
  "ASSUMPTION (is_prime_elem x) \<Longrightarrow> x \<noteq> 0"
  unfolding ASSUMPTION_def by (rule is_prime_elem_not_zeroI)

lemma is_prime_elem_imp_not_one [simp]:
  "ASSUMPTION (is_prime_elem x) \<Longrightarrow> x \<noteq> 1"
  unfolding ASSUMPTION_def by auto

end

lemma (in algebraic_semidom) mult_unit_dvd_iff': "is_unit a \<Longrightarrow> (a * b) dvd c \<longleftrightarrow> b dvd c"
  by (subst mult.commute) (rule mult_unit_dvd_iff)

context algebraic_semidom
begin

lemma prime_imp_irreducible:
  assumes "is_prime_elem p"
  shows   "irreducible p"
proof (rule irreducibleI)
  fix a b
  assume p_eq: "p = a * b"
  with assms have nz: "a \<noteq> 0" "b \<noteq> 0" by auto
  from p_eq have "p dvd a * b" by simp
  with \<open>is_prime_elem p\<close> have "p dvd a \<or> p dvd b" by (rule prime_divides_productD)
  with \<open>p = a * b\<close> have "a * b dvd 1 * b \<or> a * b dvd a * 1" by auto
  thus "a dvd 1 \<or> b dvd 1"
    by (simp only: dvd_times_left_cancel_iff[OF nz(1)] dvd_times_right_cancel_iff[OF nz(2)])
qed (insert assms, simp_all add: is_prime_elem_def)

lemma is_prime_elem_mono:
  assumes "is_prime_elem p" "\<not>q dvd 1" "q dvd p"
  shows   "is_prime_elem q"
proof -
  from \<open>q dvd p\<close> obtain r where r: "p = q * r" by (elim dvdE)
  hence "p dvd q * r" by simp
  with \<open>is_prime_elem p\<close> have "p dvd q \<or> p dvd r" by (rule prime_divides_productD)
  hence "p dvd q"
  proof
    assume "p dvd r"
    then obtain s where s: "r = p * s" by (elim dvdE)
    from r have "p * 1 = p * (q * s)" by (subst (asm) s) (simp add: mult_ac)
    with \<open>is_prime_elem p\<close> have "q dvd 1"
      by (subst (asm) mult_cancel_left) auto
    with \<open>\<not>q dvd 1\<close> show ?thesis by contradiction
  qed

  show ?thesis
  proof (rule is_prime_elemI)
    fix a b assume "q dvd (a * b)"
    with \<open>p dvd q\<close> have "p dvd (a * b)" by (rule dvd_trans)
    with \<open>is_prime_elem p\<close> have "p dvd a \<or> p dvd b" by (rule prime_divides_productD)
    with \<open>q dvd p\<close> show "q dvd a \<or> q dvd b" by (blast intro: dvd_trans)
  qed (insert assms, auto)
qed

lemma irreducibleD':
  assumes "irreducible a" "b dvd a"
  shows   "a dvd b \<or> is_unit b"
proof -
  from assms obtain c where c: "a = b * c" by (elim dvdE)
  from irreducibleD[OF assms(1) this] have "is_unit b \<or> is_unit c" .
  thus ?thesis by (auto simp: c mult_unit_dvd_iff)
qed

lemma irreducibleI':
  assumes "a \<noteq> 0" "\<not>is_unit a" "\<And>b. b dvd a \<Longrightarrow> a dvd b \<or> is_unit b"
  shows   "irreducible a"
proof (rule irreducibleI)
  fix b c assume a_eq: "a = b * c"
  hence "a dvd b \<or> is_unit b" by (intro assms) simp_all
  thus "is_unit b \<or> is_unit c"
  proof
    assume "a dvd b"
    hence "b * c dvd b * 1" by (simp add: a_eq)
    moreover from \<open>a \<noteq> 0\<close> a_eq have "b \<noteq> 0" by auto
    ultimately show ?thesis by (subst (asm) dvd_times_left_cancel_iff) auto
  qed blast
qed (simp_all add: assms(1,2))

lemma irreducible_altdef:
  "irreducible x \<longleftrightarrow> x \<noteq> 0 \<and> \<not>is_unit x \<and> (\<forall>b. b dvd x \<longrightarrow> x dvd b \<or> is_unit b)"
  using irreducibleI'[of x] irreducibleD'[of x] irreducible_not_unit[of x] by auto

lemma is_prime_elem_multD:
  assumes "is_prime_elem (a * b)"
  shows "is_unit a \<or> is_unit b"
proof -
  from assms have "a \<noteq> 0" "b \<noteq> 0" by (auto dest!: is_prime_elem_not_zeroI)
  moreover from assms prime_divides_productD [of "a * b"] have "a * b dvd a \<or> a * b dvd b"
    by auto
  ultimately show ?thesis
    using dvd_times_left_cancel_iff [of a b 1]
      dvd_times_right_cancel_iff [of b a 1]
    by auto
qed

lemma is_prime_elemD2:
  assumes "is_prime_elem p" and "a dvd p" and "\<not> is_unit a"
  shows "p dvd a"
proof -
  from \<open>a dvd p\<close> obtain b where "p = a * b" ..
  with \<open>is_prime_elem p\<close> is_prime_elem_multD \<open>\<not> is_unit a\<close> have "is_unit b" by auto
  with \<open>p = a * b\<close> show ?thesis
    by (auto simp add: mult_unit_dvd_iff)
qed

lemma irreducible_mult_unit_left:
  "is_unit a \<Longrightarrow> irreducible (a * p) \<longleftrightarrow> irreducible p"
  by (auto simp: irreducible_altdef mult.commute[of a] is_unit_mult_iff
        mult_unit_dvd_iff dvd_mult_unit_iff)

lemma is_prime_elem_mult_unit_left:
  "is_unit a \<Longrightarrow> is_prime_elem (a * p) \<longleftrightarrow> is_prime_elem p"
  by (auto simp: is_prime_elem_def mult.commute[of a] is_unit_mult_iff mult_unit_dvd_iff)

end

context normalization_semidom
begin

lemma irreducible_normalize_iff [simp]: "irreducible (normalize x) = irreducible x"
  using irreducible_mult_unit_left[of "1 div unit_factor x" x]
  by (cases "x = 0") (simp_all add: unit_div_commute)

lemma is_prime_elem_normalize_iff [simp]: "is_prime_elem (normalize x) = is_prime_elem x"
  using is_prime_elem_mult_unit_left[of "1 div unit_factor x" x]
  by (cases "x = 0") (simp_all add: unit_div_commute)

definition is_prime :: "'a \<Rightarrow> bool" where
  "is_prime p \<longleftrightarrow> is_prime_elem p \<and> normalize p = p"

lemma not_is_prime_0 [simp]: "\<not>is_prime 0" by (simp add: is_prime_def)

lemma not_is_prime_unit: "is_unit x \<Longrightarrow> \<not>is_prime x"
  using is_prime_elem_not_unit[of x] by (auto simp add: is_prime_def)

lemma not_is_prime_1 [simp]: "\<not>is_prime 1" by (simp add: not_is_prime_unit)

lemma is_primeI: "is_prime_elem x \<Longrightarrow> normalize x = x \<Longrightarrow> is_prime x"
  by (simp add: is_prime_def)

lemma prime_imp_prime_elem [dest]: "is_prime p \<Longrightarrow> is_prime_elem p"
  by (simp add: is_prime_def)

lemma normalize_is_prime: "is_prime p \<Longrightarrow> normalize p = p"
  by (simp add: is_prime_def)

lemma is_prime_normalize_iff [simp]: "is_prime (normalize p) \<longleftrightarrow> is_prime_elem p"
  by (auto simp add: is_prime_def)

lemma is_prime_elem_not_unit' [simp]:
  "ASSUMPTION (is_prime_elem x) \<Longrightarrow> \<not>is_unit x"
  unfolding ASSUMPTION_def by (rule is_prime_elem_not_unit)

lemma is_prime_imp_nonzero [simp]:
  "ASSUMPTION (is_prime x) \<Longrightarrow> x \<noteq> 0"
  unfolding ASSUMPTION_def is_prime_def by auto

lemma is_prime_imp_not_one [simp]:
  "ASSUMPTION (is_prime x) \<Longrightarrow> x \<noteq> 1"
  unfolding ASSUMPTION_def by auto

lemma is_prime_not_unit' [simp]:
  "ASSUMPTION (is_prime x) \<Longrightarrow> \<not>is_unit x"
  unfolding ASSUMPTION_def is_prime_def by auto

lemma is_prime_normalize' [simp]: "ASSUMPTION (is_prime x) \<Longrightarrow> normalize x = x"
  unfolding ASSUMPTION_def is_prime_def by simp

lemma unit_factor_is_prime: "is_prime x \<Longrightarrow> unit_factor x = 1"
  using unit_factor_normalize[of x] unfolding is_prime_def by auto

lemma unit_factor_is_prime' [simp]: "ASSUMPTION (is_prime x) \<Longrightarrow> unit_factor x = 1"
  unfolding ASSUMPTION_def by (rule unit_factor_is_prime)

lemma prime_imp_prime_elem' [simp]: "ASSUMPTION (is_prime x) \<Longrightarrow> is_prime_elem x"
  by (simp add: is_prime_def ASSUMPTION_def)

 lemma is_prime_elem_associated:
  assumes "is_prime_elem p" and "is_prime_elem q" and "q dvd p"
  shows "normalize q = normalize p"
using \<open>q dvd p\<close> proof (rule associatedI)
  from \<open>is_prime_elem q\<close> have "\<not> is_unit q"
    by (simp add: is_prime_elem_not_unit)
  with \<open>is_prime_elem p\<close> \<open>q dvd p\<close> show "p dvd q"
    by (blast intro: is_prime_elemD2)
qed

lemma prime_dvd_msetprodE:
  assumes "is_prime_elem p"
  assumes dvd: "p dvd msetprod A"
  obtains a where "a \<in># A" and "p dvd a"
proof -
  from dvd have "\<exists>a. a \<in># A \<and> p dvd a"
  proof (induct A)
    case empty then show ?case
    using \<open>is_prime_elem p\<close> by (simp add: is_prime_elem_not_unit)
  next
    case (add A a)
    then have "p dvd msetprod A * a" by simp
    with \<open>is_prime_elem p\<close> consider (A) "p dvd msetprod A" | (B) "p dvd a"
      by (blast dest: prime_divides_productD)
    then show ?case proof cases
      case B then show ?thesis by auto
    next
      case A
      with add.hyps obtain b where "b \<in># A" "p dvd b"
        by auto
      then show ?thesis by auto
    qed
  qed
  with that show thesis by blast
qed

lemma msetprod_subset_imp_dvd:
  assumes "A \<subseteq># B"
  shows   "msetprod A dvd msetprod B"
proof -
  from assms have "B = (B - A) + A" by (simp add: subset_mset.diff_add)
  also have "msetprod \<dots> = msetprod (B - A) * msetprod A" by simp
  also have "msetprod A dvd \<dots>" by simp
  finally show ?thesis .
qed

lemma prime_dvd_msetprod_iff: "is_prime p \<Longrightarrow> p dvd msetprod A \<longleftrightarrow> (\<exists>x. x \<in># A \<and> p dvd x)"
  by (induction A) (simp_all add: prime_dvd_mult_iff prime_imp_prime_elem, blast+)

lemma primes_dvd_imp_eq:
  assumes "is_prime p" "is_prime q" "p dvd q"
  shows   "p = q"
proof -
  from assms have "irreducible q" by (simp add: prime_imp_irreducible is_prime_def)
  from irreducibleD'[OF this \<open>p dvd q\<close>] assms have "q dvd p" by simp
  with \<open>p dvd q\<close> have "normalize p = normalize q" by (rule associatedI)
  with assms show "p = q" by simp
qed

lemma prime_dvd_msetprod_primes_iff:
  assumes "is_prime p" "\<And>q. q \<in># A \<Longrightarrow> is_prime q"
  shows   "p dvd msetprod A \<longleftrightarrow> p \<in># A"
proof -
  from assms(1) have "p dvd msetprod A \<longleftrightarrow> (\<exists>x. x \<in># A \<and> p dvd x)" by (rule prime_dvd_msetprod_iff)
  also from assms have "\<dots> \<longleftrightarrow> p \<in># A" by (auto dest: primes_dvd_imp_eq)
  finally show ?thesis .
qed

lemma msetprod_primes_dvd_imp_subset:
  assumes "msetprod A dvd msetprod B" "\<And>p. p \<in># A \<Longrightarrow> is_prime p" "\<And>p. p \<in># B \<Longrightarrow> is_prime p"
  shows   "A \<subseteq># B"
using assms
proof (induction A arbitrary: B)
  case empty
  thus ?case by simp
next
  case (add A p B)
  hence p: "is_prime p" by simp
  define B' where "B' = B - {#p#}"
  from add.prems have "p dvd msetprod B" by (simp add: dvd_mult_right)
  with add.prems have "p \<in># B"
    by (subst (asm) (2) prime_dvd_msetprod_primes_iff) simp_all
  hence B: "B = B' + {#p#}" by (simp add: B'_def)
  from add.prems p have "A \<subseteq># B'" by (intro add.IH) (simp_all add: B)
  thus ?case by (simp add: B)
qed

lemma normalize_msetprod_primes:
  "(\<And>p. p \<in># A \<Longrightarrow> is_prime p) \<Longrightarrow> normalize (msetprod A) = msetprod A"
proof (induction A)
  case (add A p)
  hence "is_prime p" by simp
  hence "normalize p = p" by simp
  with add show ?case by (simp add: normalize_mult)
qed simp_all

lemma msetprod_dvd_msetprod_primes_iff:
  assumes "\<And>x. x \<in># A \<Longrightarrow> is_prime x" "\<And>x. x \<in># B \<Longrightarrow> is_prime x"
  shows   "msetprod A dvd msetprod B \<longleftrightarrow> A \<subseteq># B"
  using assms by (auto intro: msetprod_subset_imp_dvd msetprod_primes_dvd_imp_subset)

lemma prime_dvd_power_iff:
  assumes "is_prime_elem p"
  shows "p dvd a ^ n \<longleftrightarrow> p dvd a \<and> n > 0"
  using assms by (induct n) (auto dest: is_prime_elem_not_unit prime_divides_productD)

lemma prime_power_dvd_multD:
  assumes "is_prime_elem p"
  assumes "p ^ n dvd a * b" and "n > 0" and "\<not> p dvd a"
  shows "p ^ n dvd b"
using \<open>p ^ n dvd a * b\<close> and \<open>n > 0\<close> proof (induct n arbitrary: b)
  case 0 then show ?case by simp
next
  case (Suc n) show ?case
  proof (cases "n = 0")
    case True with Suc \<open>is_prime_elem p\<close> \<open>\<not> p dvd a\<close> show ?thesis
      by (simp add: prime_dvd_mult_iff)
  next
    case False then have "n > 0" by simp
    from \<open>is_prime_elem p\<close> have "p \<noteq> 0" by auto
    from Suc.prems have *: "p * p ^ n dvd a * b"
      by simp
    then have "p dvd a * b"
      by (rule dvd_mult_left)
    with Suc \<open>is_prime_elem p\<close> \<open>\<not> p dvd a\<close> have "p dvd b"
      by (simp add: prime_dvd_mult_iff)
    moreover define c where "c = b div p"
    ultimately have b: "b = p * c" by simp
    with * have "p * p ^ n dvd p * (a * c)"
      by (simp add: ac_simps)
    with \<open>p \<noteq> 0\<close> have "p ^ n dvd a * c"
      by simp
    with Suc.hyps \<open>n > 0\<close> have "p ^ n dvd c"
      by blast
    with \<open>p \<noteq> 0\<close> show ?thesis
      by (simp add: b)
  qed
qed

lemma is_unit_msetprod_iff:
  "is_unit (msetprod A) \<longleftrightarrow> (\<forall>x. x \<in># A \<longrightarrow> is_unit x)"
  by (induction A) (auto simp: is_unit_mult_iff)

lemma multiset_emptyI: "(\<And>x. x \<notin># A) \<Longrightarrow> A = {#}"
  by (intro multiset_eqI) (simp_all add: count_eq_zero_iff)

lemma is_unit_msetprod_primes_iff:
  assumes "\<And>x. x \<in># A \<Longrightarrow> is_prime x"
  shows   "is_unit (msetprod A) \<longleftrightarrow> A = {#}"
proof
  assume unit: "is_unit (msetprod A)"
  show "A = {#}"
  proof (intro multiset_emptyI notI)
    fix x assume "x \<in># A"
    with unit have "is_unit x" by (subst (asm) is_unit_msetprod_iff) blast
    moreover from \<open>x \<in># A\<close> have "is_prime x" by (rule assms)
    ultimately show False by simp
  qed
qed simp_all

lemma msetprod_primes_irreducible_imp_prime:
  assumes irred: "irreducible (msetprod A)"
  assumes A: "\<And>x. x \<in># A \<Longrightarrow> is_prime x"
  assumes B: "\<And>x. x \<in># B \<Longrightarrow> is_prime x"
  assumes C: "\<And>x. x \<in># C \<Longrightarrow> is_prime x"
  assumes dvd: "msetprod A dvd msetprod B * msetprod C"
  shows   "msetprod A dvd msetprod B \<or> msetprod A dvd msetprod C"
proof -
  from dvd have "msetprod A dvd msetprod (B + C)"
    by simp
  with A B C have subset: "A \<subseteq># B + C"
    by (subst (asm) msetprod_dvd_msetprod_primes_iff) auto
  define A1 and A2 where "A1 = A #\<inter> B" and "A2 = A - A1"
  have "A = A1 + A2" unfolding A1_def A2_def
    by (rule sym, intro subset_mset.add_diff_inverse) simp_all
  from subset have "A1 \<subseteq># B" "A2 \<subseteq># C"
    by (auto simp: A1_def A2_def Multiset.subset_eq_diff_conv Multiset.union_commute)
  from \<open>A = A1 + A2\<close> have "msetprod A = msetprod A1 * msetprod A2" by simp
  from irred and this have "is_unit (msetprod A1) \<or> is_unit (msetprod A2)"
    by (rule irreducibleD)
  with A have "A1 = {#} \<or> A2 = {#}" unfolding A1_def A2_def
    by (subst (asm) (1 2) is_unit_msetprod_primes_iff) (auto dest: Multiset.in_diffD)
  with dvd \<open>A = A1 + A2\<close> \<open>A1 \<subseteq># B\<close> \<open>A2 \<subseteq># C\<close> show ?thesis
    by (auto intro: msetprod_subset_imp_dvd)
qed

lemma multiset_nonemptyE [elim]:
  assumes "A \<noteq> {#}"
  obtains x where "x \<in># A"
proof -
  have "\<exists>x. x \<in># A" by (rule ccontr) (insert assms, auto)
  with that show ?thesis by blast
qed

lemma msetprod_primes_finite_divisor_powers:
  assumes A: "\<And>x. x \<in># A \<Longrightarrow> is_prime x"
  assumes B: "\<And>x. x \<in># B \<Longrightarrow> is_prime x"
  assumes "A \<noteq> {#}"
  shows   "finite {n. msetprod A ^ n dvd msetprod B}"
proof -
  from \<open>A \<noteq> {#}\<close> obtain x where x: "x \<in># A" by blast
  define m where "m = count B x"
  have "{n. msetprod A ^ n dvd msetprod B} \<subseteq> {..m}"
  proof safe
    fix n assume dvd: "msetprod A ^ n dvd msetprod B"
    from x have "x ^ n dvd msetprod A ^ n" by (intro dvd_power_same dvd_msetprod)
    also note dvd
    also have "x ^ n = msetprod (replicate_mset n x)" by simp
    finally have "replicate_mset n x \<subseteq># B"
      by (rule msetprod_primes_dvd_imp_subset) (insert A B x, simp_all split: if_splits)
    thus "n \<le> m" by (simp add: count_le_replicate_mset_subset_eq m_def)
  qed
  moreover have "finite {..m}" by simp
  ultimately show ?thesis by (rule finite_subset)
qed

lemma normalize_msetprod:
  "normalize (msetprod A) = msetprod (image_mset normalize A)"
  by (induction A) (simp_all add: normalize_mult mult_ac)

end

context semiring_gcd
begin

lemma irreducible_imp_prime_gcd:
  assumes "irreducible x"
  shows   "is_prime_elem x"
proof (rule is_prime_elemI)
  fix a b assume "x dvd a * b"
  from dvd_productE[OF this] obtain y z where yz: "x = y * z" "y dvd a" "z dvd b" .
  from \<open>irreducible x\<close> and \<open>x = y * z\<close> have "is_unit y \<or> is_unit z" by (rule irreducibleD)
  with yz show "x dvd a \<or> x dvd b"
    by (auto simp: mult_unit_dvd_iff mult_unit_dvd_iff')
qed (insert assms, auto simp: irreducible_not_unit)

end


class factorial_semiring = normalization_semidom +
  assumes prime_factorization_exists:
            "x \<noteq> 0 \<Longrightarrow> \<exists>A. (\<forall>x. x \<in># A \<longrightarrow> is_prime_elem x) \<and> msetprod A = normalize x"
begin

lemma prime_factorization_exists':
  assumes "x \<noteq> 0"
  obtains A where "\<And>x. x \<in># A \<Longrightarrow> is_prime x" "msetprod A = normalize x"
proof -
  from prime_factorization_exists[OF assms] obtain A
    where A: "\<And>x. x \<in># A \<Longrightarrow> is_prime_elem x" "msetprod A = normalize x" by blast
  define A' where "A' = image_mset normalize A"
  have "msetprod A' = normalize (msetprod A)"
    by (simp add: A'_def normalize_msetprod)
  also note A(2)
  finally have "msetprod A' = normalize x" by simp
  moreover from A(1) have "\<forall>x. x \<in># A' \<longrightarrow> is_prime x" by (auto simp: is_prime_def A'_def)
  ultimately show ?thesis by (intro that[of A']) blast
qed

lemma irreducible_imp_prime:
  assumes "irreducible x"
  shows   "is_prime_elem x"
proof (rule is_prime_elemI)
  fix a b assume dvd: "x dvd a * b"
  from assms have "x \<noteq> 0" by auto
  show "x dvd a \<or> x dvd b"
  proof (cases "a = 0 \<or> b = 0")
    case False
    hence "a \<noteq> 0" "b \<noteq> 0" by blast+
    note nz = \<open>x \<noteq> 0\<close> this
    from nz[THEN prime_factorization_exists'] guess A B C . note ABC = this
    from assms ABC have "irreducible (msetprod A)" by simp
    from dvd msetprod_primes_irreducible_imp_prime[of A B C, OF this ABC(1,3,5)] ABC(2,4,6)
      show ?thesis by (simp add: normalize_mult [symmetric])
  qed auto
qed (insert assms, simp_all add: irreducible_def)

lemma finite_divisor_powers:
  assumes "y \<noteq> 0" "\<not>is_unit x"
  shows   "finite {n. x ^ n dvd y}"
proof (cases "x = 0")
  case True
  with assms have "{n. x ^ n dvd y} = {0}" by (auto simp: power_0_left)
  thus ?thesis by simp
next
  case False
  note nz = this \<open>y \<noteq> 0\<close>
  from nz[THEN prime_factorization_exists'] guess A B . note AB = this
  from AB assms have "A \<noteq> {#}" by (auto simp: normalize_1_iff)
  from AB(2,4) msetprod_primes_finite_divisor_powers [of A B, OF AB(1,3) this]
    show ?thesis by (simp add: normalize_power [symmetric])
qed

lemma finite_prime_divisors:
  assumes "x \<noteq> 0"
  shows   "finite {p. is_prime p \<and> p dvd x}"
proof -
  from prime_factorization_exists'[OF assms] guess A . note A = this
  have "{p. is_prime p \<and> p dvd x} \<subseteq> set_mset A"
  proof safe
    fix p assume p: "is_prime p" and dvd: "p dvd x"
    from dvd have "p dvd normalize x" by simp
    also from A have "normalize x = msetprod A" by simp
    finally show "p \<in># A" using p A by (subst (asm) prime_dvd_msetprod_primes_iff)
  qed
  moreover have "finite (set_mset A)" by simp
  ultimately show ?thesis by (rule finite_subset)
qed

lemma prime_iff_irreducible: "is_prime_elem x \<longleftrightarrow> irreducible x"
  by (blast intro: irreducible_imp_prime prime_imp_irreducible)

lemma prime_divisor_exists:
  assumes "a \<noteq> 0" "\<not>is_unit a"
  shows   "\<exists>b. b dvd a \<and> is_prime b"
proof -
  from prime_factorization_exists'[OF assms(1)] guess A . note A = this
  moreover from A and assms have "A \<noteq> {#}" by auto
  then obtain x where "x \<in># A" by blast
  with A(1) have *: "x dvd msetprod A" "is_prime x" by (auto simp: dvd_msetprod)
  with A have "x dvd a" by simp
  with * show ?thesis by blast
qed

lemma prime_divisors_induct [case_names zero unit factor]:
  assumes "P 0" "\<And>x. is_unit x \<Longrightarrow> P x" "\<And>p x. is_prime p \<Longrightarrow> P x \<Longrightarrow> P (p * x)"
  shows   "P x"
proof (cases "x = 0")
  case False
  from prime_factorization_exists'[OF this] guess A . note A = this
  from A(1) have "P (unit_factor x * msetprod A)"
  proof (induction A)
    case (add A p)
    from add.prems have "is_prime p" by simp
    moreover from add.prems have "P (unit_factor x * msetprod A)" by (intro add.IH) simp_all
    ultimately have "P (p * (unit_factor x * msetprod A))" by (rule assms(3))
    thus ?case by (simp add: mult_ac)
  qed (simp_all add: assms False)
  with A show ?thesis by simp
qed (simp_all add: assms(1))

lemma no_prime_divisors_imp_unit:
  assumes "a \<noteq> 0" "\<And>b. b dvd a \<Longrightarrow> normalize b = b \<Longrightarrow> \<not> is_prime_elem b"
  shows "is_unit a"
proof (rule ccontr)
  assume "\<not>is_unit a"
  from prime_divisor_exists[OF assms(1) this] guess b by (elim exE conjE)
  with assms(2)[of b] show False by (simp add: is_prime_def)
qed

lemma prime_divisorE:
  assumes "a \<noteq> 0" and "\<not> is_unit a"
  obtains p where "is_prime p" and "p dvd a"
  using assms no_prime_divisors_imp_unit unfolding is_prime_def by blast

definition multiplicity :: "'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "multiplicity p x = (if finite {n. p ^ n dvd x} then Max {n. p ^ n dvd x} else 0)"

lemma multiplicity_dvd: "p ^ multiplicity p x dvd x"
proof (cases "finite {n. p ^ n dvd x}")
  case True
  hence "multiplicity p x = Max {n. p ^ n dvd x}"
    by (simp add: multiplicity_def)
  also have "\<dots> \<in> {n. p ^ n dvd x}"
    by (rule Max_in) (auto intro!: True exI[of _ "0::nat"])
  finally show ?thesis by simp
qed (simp add: multiplicity_def)

lemma multiplicity_dvd': "n \<le> multiplicity p x \<Longrightarrow> p ^ n dvd x"
  by (rule dvd_trans[OF le_imp_power_dvd multiplicity_dvd])

lemma dvd_power_iff:
  assumes "x \<noteq> 0"
  shows   "x ^ m dvd x ^ n \<longleftrightarrow> is_unit x \<or> m \<le> n"
proof
  assume *: "x ^ m dvd x ^ n"
  {
    assume "m > n"
    note *
    also have "x ^ n = x ^ n * 1" by simp
    also from \<open>m > n\<close> have "m = n + (m - n)" by simp
    also have "x ^ \<dots> = x ^ n * x ^ (m - n)" by (rule power_add)
    finally have "x ^ (m - n) dvd 1"
      by (subst (asm) dvd_times_left_cancel_iff) (insert assms, simp_all)
    with \<open>m > n\<close> have "is_unit x" by (simp add: is_unit_power_iff)
  }
  thus "is_unit x \<or> m \<le> n" by force
qed (auto intro: unit_imp_dvd simp: is_unit_power_iff le_imp_power_dvd)

context
  fixes x p :: 'a
  assumes xp: "x \<noteq> 0" "\<not>is_unit p"
begin

lemma multiplicity_eq_Max: "multiplicity p x = Max {n. p ^ n dvd x}"
  using finite_divisor_powers[OF xp] by (simp add: multiplicity_def)

lemma multiplicity_geI:
  assumes "p ^ n dvd x"
  shows   "multiplicity p x \<ge> n"
proof -
  from assms have "n \<le> Max {n. p ^ n dvd x}"
    by (intro Max_ge finite_divisor_powers xp) simp_all
  thus ?thesis by (subst multiplicity_eq_Max)
qed

lemma multiplicity_lessI:
  assumes "\<not>p ^ n dvd x"
  shows   "multiplicity p x < n"
proof (rule ccontr)
  assume "\<not>(n > multiplicity p x)"
  hence "p ^ n dvd x" by (intro multiplicity_dvd') simp
  with assms show False by contradiction
qed

lemma power_dvd_iff_le_multiplicity:
  "p ^ n dvd x \<longleftrightarrow> n \<le> multiplicity p x"
  using multiplicity_geI[of n] multiplicity_lessI[of n] by (cases "p ^ n dvd x") auto

lemma multiplicity_eq_zero_iff:
  assumes "x \<noteq> 0" "\<not>is_unit p"
  shows   "multiplicity p x = 0 \<longleftrightarrow> \<not>p dvd x"
  using power_dvd_iff_le_multiplicity[of 1] by auto

lemma multiplicity_gt_zero_iff:
  assumes "x \<noteq> 0" "\<not>is_unit p"
  shows   "multiplicity p x > 0 \<longleftrightarrow> p dvd x"
  using power_dvd_iff_le_multiplicity[of 1] by auto

lemma multiplicity_decompose:
  "\<not>p dvd (x div p ^ multiplicity p x)"
proof
  assume *: "p dvd x div p ^ multiplicity p x"
  have "x = x div p ^ multiplicity p x * (p ^ multiplicity p x)"
    using multiplicity_dvd[of p x] by simp
  also from * have "x div p ^ multiplicity p x = (x div p ^ multiplicity p x div p) * p" by simp
  also have "x div p ^ multiplicity p x div p * p * p ^ multiplicity p x =
               x div p ^ multiplicity p x div p * p ^ Suc (multiplicity p x)"
    by (simp add: mult_assoc)
  also have "p ^ Suc (multiplicity p x) dvd \<dots>" by (rule dvd_triv_right)
  finally show False by (subst (asm) power_dvd_iff_le_multiplicity) simp
qed

lemma multiplicity_decompose':
  obtains y where "x = p ^ multiplicity p x * y" "\<not>p dvd y"
  using that[of "x div p ^ multiplicity p x"]
  by (simp add: multiplicity_decompose multiplicity_dvd)

end

lemma multiplicity_zero [simp]: "multiplicity p 0 = 0"
  by (simp add: multiplicity_def)

lemma multiplicity_unit_left: "is_unit p \<Longrightarrow> multiplicity p x = 0"
  by (simp add: multiplicity_def is_unit_power_iff unit_imp_dvd)

lemma multiplicity_unit_right:
  assumes "is_unit x"
  shows   "multiplicity p x = 0"
proof (cases "is_unit p \<or> x = 0")
  case False
  with multiplicity_lessI[of x p 1] this assms
    show ?thesis by (auto dest: dvd_unit_imp_unit)
qed (auto simp: multiplicity_unit_left)

lemma multiplicity_one [simp]: "multiplicity p 1 = 0"
  by (rule multiplicity_unit_right) simp_all

lemma multiplicity_eqI:
  assumes "p ^ n dvd x" "\<not>p ^ Suc n dvd x"
  shows   "multiplicity p x = n"
proof -
  consider "x = 0" | "is_unit p" | "x \<noteq> 0" "\<not>is_unit p" by blast
  thus ?thesis
  proof cases
    assume xp: "x \<noteq> 0" "\<not>is_unit p"
    from xp assms(1) have "multiplicity p x \<ge> n" by (intro multiplicity_geI)
    moreover from assms(2) xp have "multiplicity p x < Suc n" by (intro multiplicity_lessI)
    ultimately show ?thesis by simp
  next
    assume "is_unit p"
    hence "is_unit (p ^ Suc n)" by (simp add: is_unit_power_iff del: power_Suc)
    hence "p ^ Suc n dvd x" by (rule unit_imp_dvd)
    with \<open>\<not>p ^ Suc n dvd x\<close> show ?thesis by contradiction
  qed (insert assms, simp_all)
qed


context
  fixes x p :: 'a
  assumes xp: "x \<noteq> 0" "\<not>is_unit p"
begin

lemma multiplicity_times_same:
  assumes "p \<noteq> 0"
  shows   "multiplicity p (p * x) = Suc (multiplicity p x)"
proof (rule multiplicity_eqI)
  show "p ^ Suc (multiplicity p x) dvd p * x"
    by (auto intro!: mult_dvd_mono multiplicity_dvd)
  from xp assms show "\<not> p ^ Suc (Suc (multiplicity p x)) dvd p * x"
    using power_dvd_iff_le_multiplicity[OF xp, of "Suc (multiplicity p x)"] by simp
qed

end

lemma multiplicity_same_power': "multiplicity p (p ^ n) = (if p = 0 \<or> is_unit p then 0 else n)"
proof -
  consider "p = 0" | "is_unit p" |"p \<noteq> 0" "\<not>is_unit p" by blast
  thus ?thesis
  proof cases
    assume "p \<noteq> 0" "\<not>is_unit p"
    thus ?thesis by (induction n) (simp_all add: multiplicity_times_same)
  qed (simp_all add: power_0_left multiplicity_unit_left)
qed

lemma multiplicity_same_power:
  "p \<noteq> 0 \<Longrightarrow> \<not>is_unit p \<Longrightarrow> multiplicity p (p ^ n) = n"
  by (simp add: multiplicity_same_power')

lemma multiplicity_prime_times_other:
  assumes "is_prime_elem p" "\<not>p dvd q"
  shows   "multiplicity p (q * x) = multiplicity p x"
proof (cases "x = 0")
  case False
  show ?thesis
  proof (rule multiplicity_eqI)
    have "1 * p ^ multiplicity p x dvd q * x"
      by (intro mult_dvd_mono multiplicity_dvd) simp_all
    thus "p ^ multiplicity p x dvd q * x" by simp
  next
    define n where "n = multiplicity p x"
    from assms have "\<not>is_unit p" by simp
    from multiplicity_decompose'[OF False this] guess y . note y = this [folded n_def]
    from y have "p ^ Suc n dvd q * x \<longleftrightarrow> p ^ n * p dvd p ^ n * (q * y)" by (simp add: mult_ac)
    also from assms have "\<dots> \<longleftrightarrow> p dvd q * y" by simp
    also have "\<dots> \<longleftrightarrow> p dvd q \<or> p dvd y" by (rule prime_dvd_mult_iff) fact+
    also from assms y have "\<dots> \<longleftrightarrow> False" by simp
    finally show "\<not>(p ^ Suc n dvd q * x)" by blast
  qed
qed simp_all

lift_definition prime_factorization :: "'a \<Rightarrow> 'a multiset" is
  "\<lambda>x p. if is_prime p then multiplicity p x else 0"
  unfolding multiset_def
proof clarify
  fix x :: 'a
  show "finite {p. 0 < (if is_prime p then multiplicity p x else 0)}" (is "finite ?A")
  proof (cases "x = 0")
    case False
    from False have "?A \<subseteq> {p. is_prime p \<and> p dvd x}"
      by (auto simp: multiplicity_gt_zero_iff)
    moreover from False have "finite {p. is_prime p \<and> p dvd x}"
      by (rule finite_prime_divisors)
    ultimately show ?thesis by (rule finite_subset)
  qed simp_all
qed

lemma count_prime_factorization_nonprime:
  "\<not>is_prime p \<Longrightarrow> count (prime_factorization x) p = 0"
  by transfer simp

lemma count_prime_factorization_prime:
  "is_prime p \<Longrightarrow> count (prime_factorization x) p = multiplicity p x"
  by transfer simp

lemma count_prime_factorization:
  "count (prime_factorization x) p = (if is_prime p then multiplicity p x else 0)"
  by transfer simp

lemma unit_imp_no_irreducible_divisors:
  assumes "is_unit x" "irreducible p"
  shows   "\<not>p dvd x"
  using assms dvd_unit_imp_unit irreducible_not_unit by blast

lemma unit_imp_no_prime_divisors:
  assumes "is_unit x" "is_prime_elem p"
  shows   "\<not>p dvd x"
  using unit_imp_no_irreducible_divisors[OF assms(1) prime_imp_irreducible[OF assms(2)]] .

lemma prime_factorization_0 [simp]: "prime_factorization 0 = {#}"
  by (simp add: multiset_eq_iff count_prime_factorization)

lemma prime_factorization_empty_iff:
  "prime_factorization x = {#} \<longleftrightarrow> x = 0 \<or> is_unit x"
proof
  assume *: "prime_factorization x = {#}"
  {
    assume x: "x \<noteq> 0" "\<not>is_unit x"
    {
      fix p assume p: "is_prime p"
      have "count (prime_factorization x) p = 0" by (simp add: *)
      also from p have "count (prime_factorization x) p = multiplicity p x"
        by (rule count_prime_factorization_prime)
      also from x p have "\<dots> = 0 \<longleftrightarrow> \<not>p dvd x" by (simp add: multiplicity_eq_zero_iff)
      finally have "\<not>p dvd x" .
    }
    with prime_divisor_exists[OF x] have False by blast
  }
  thus "x = 0 \<or> is_unit x" by blast
next
  assume "x = 0 \<or> is_unit x"
  thus "prime_factorization x = {#}"
  proof
    assume x: "is_unit x"
    {
      fix p assume p: "is_prime p"
      from p x have "multiplicity p x = 0"
        by (subst multiplicity_eq_zero_iff)
           (auto simp: multiplicity_eq_zero_iff dest: unit_imp_no_prime_divisors)
    }
    thus ?thesis by (simp add: multiset_eq_iff count_prime_factorization)
  qed simp_all
qed

lemma prime_factorization_unit:
  assumes "is_unit x"
  shows   "prime_factorization x = {#}"
proof (rule multiset_eqI)
  fix p :: 'a
  show "count (prime_factorization x) p = count {#} p"
  proof (cases "is_prime p")
    case True
    with assms have "multiplicity p x = 0"
      by (subst multiplicity_eq_zero_iff)
         (auto simp: multiplicity_eq_zero_iff dest: unit_imp_no_prime_divisors)
    with True show ?thesis by (simp add: count_prime_factorization_prime)
  qed (simp_all add: count_prime_factorization_nonprime)
qed

lemma prime_factorization_1 [simp]: "prime_factorization 1 = {#}"
  by (simp add: prime_factorization_unit)

lemma prime_factorization_times_prime:
  assumes "x \<noteq> 0" "is_prime p"
  shows   "prime_factorization (p * x) = {#p#} + prime_factorization x"
proof (rule multiset_eqI)
  fix q :: 'a
  consider "\<not>is_prime q" | "p = q" | "is_prime q" "p \<noteq> q" by blast
  thus "count (prime_factorization (p * x)) q = count ({#p#} + prime_factorization x) q"
  proof cases
    assume q: "is_prime q" "p \<noteq> q"
    with assms primes_dvd_imp_eq[of q p] have "\<not>q dvd p" by auto
    with q assms show ?thesis
      by (simp add: multiplicity_prime_times_other count_prime_factorization)
  qed (insert assms, auto simp: count_prime_factorization multiplicity_times_same)
qed

lemma msetprod_prime_factorization:
  assumes "x \<noteq> 0"
  shows   "msetprod (prime_factorization x) = normalize x"
  using assms
  by (induction x rule: prime_divisors_induct)
     (simp_all add: prime_factorization_unit prime_factorization_times_prime
                    is_unit_normalize normalize_mult)

lemma in_prime_factorization_iff:
  "p \<in># prime_factorization x \<longleftrightarrow> x \<noteq> 0 \<and> p dvd x \<and> is_prime p"
proof -
  have "p \<in># prime_factorization x \<longleftrightarrow> count (prime_factorization x) p > 0" by simp
  also have "\<dots> \<longleftrightarrow> x \<noteq> 0 \<and> p dvd x \<and> is_prime p"
   by (subst count_prime_factorization, cases "x = 0")
      (auto simp: multiplicity_eq_zero_iff multiplicity_gt_zero_iff)
  finally show ?thesis .
qed

lemma in_prime_factorization_imp_prime:
  "p \<in># prime_factorization x \<Longrightarrow> is_prime p"
  by (simp add: in_prime_factorization_iff)

lemma in_prime_factorization_imp_dvd:
  "p \<in># prime_factorization x \<Longrightarrow> p dvd x"
  by (simp add: in_prime_factorization_iff)

lemma multiplicity_self:
  assumes "p \<noteq> 0" "\<not>is_unit p"
  shows   "multiplicity p p = 1"
proof -
  from assms have "multiplicity p p = Max {n. p ^ n dvd p}"
    by (simp add: multiplicity_eq_Max)
  also from assms have "p ^ n dvd p \<longleftrightarrow> n \<le> 1" for n
    using dvd_power_iff[of p n 1] by auto
  hence "{n. p ^ n dvd p} = {..1}" by auto
  also have "\<dots> = {0,1}" by auto
  finally show ?thesis by simp
qed

lemma prime_factorization_prime:
  assumes "is_prime p"
  shows   "prime_factorization p = {#p#}"
proof (rule multiset_eqI)
  fix q :: 'a
  consider "\<not>is_prime q" | "q = p" | "is_prime q" "q \<noteq> p" by blast
  thus "count (prime_factorization p) q = count {#p#} q"
    by cases (insert assms, auto dest: primes_dvd_imp_eq
                simp: count_prime_factorization multiplicity_self multiplicity_eq_zero_iff)
qed

lemma prime_factorization_msetprod_primes:
  assumes "\<And>p. p \<in># A \<Longrightarrow> is_prime p"
  shows   "prime_factorization (msetprod A) = A"
  using assms
proof (induction A)
  case (add A p)
  from add.prems[of 0] have "0 \<notin># A" by auto
  hence "msetprod A \<noteq> 0" by auto
  with add show ?case
    by (simp_all add: mult_ac prime_factorization_times_prime Multiset.union_commute)
qed simp_all

lemma multiplicity_times_unit_left:
  assumes "is_unit c"
  shows   "multiplicity (c * p) x = multiplicity p x"
proof -
  from assms have "{n. (c * p) ^ n dvd x} = {n. p ^ n dvd x}"
    by (subst mult.commute) (simp add: mult_unit_dvd_iff power_mult_distrib is_unit_power_iff)
  thus ?thesis by (simp add: multiplicity_def)
qed

lemma multiplicity_times_unit_right:
  assumes "is_unit c"
  shows   "multiplicity p (c * x) = multiplicity p x"
proof -
  from assms have "{n. p ^ n dvd c * x} = {n. p ^ n dvd x}"
    by (subst mult.commute) (simp add: dvd_mult_unit_iff)
  thus ?thesis by (simp add: multiplicity_def)
qed

lemma multiplicity_normalize_left [simp]: "multiplicity (normalize p) x = multiplicity p x"
proof (cases "p = 0")
  case [simp]: False
  have "normalize p = (1 div unit_factor p) * p"
    by (simp add: unit_div_commute is_unit_unit_factor)
  also have "multiplicity \<dots> x = multiplicity p x"
    by (rule multiplicity_times_unit_left) (simp add: is_unit_unit_factor)
  finally show ?thesis .
qed simp_all

lemma multiplicity_normalize_right [simp]: "multiplicity p (normalize x) = multiplicity p x"
proof (cases "x = 0")
  case [simp]: False
  have "normalize x = (1 div unit_factor x) * x"
    by (simp add: unit_div_commute is_unit_unit_factor)
  also have "multiplicity p \<dots> = multiplicity p x"
    by (rule multiplicity_times_unit_right) (simp add: is_unit_unit_factor)
  finally show ?thesis .
qed simp_all

lemma prime_factorization_cong:
  "normalize x = normalize y \<Longrightarrow> prime_factorization x = prime_factorization y"
  by (simp add: multiset_eq_iff count_prime_factorization
                multiplicity_normalize_right [of _ x, symmetric]
                multiplicity_normalize_right [of _ y, symmetric]
           del:  multiplicity_normalize_right)

lemma prime_factorization_unique:
  assumes "x \<noteq> 0" "y \<noteq> 0"
  shows   "prime_factorization x = prime_factorization y \<longleftrightarrow> normalize x = normalize y"
proof
  assume "prime_factorization x = prime_factorization y"
  hence "msetprod (prime_factorization x) = msetprod (prime_factorization y)" by simp
  with assms show "normalize x = normalize y" by (simp add: msetprod_prime_factorization)
qed (rule prime_factorization_cong)

lemma prime_factorization_mult:
  assumes "x \<noteq> 0" "y \<noteq> 0"
  shows   "prime_factorization (x * y) = prime_factorization x + prime_factorization y"
proof -
  have "prime_factorization (msetprod (prime_factorization (x * y))) =
          prime_factorization (msetprod (prime_factorization x + prime_factorization y))"
    by (simp add: msetprod_prime_factorization assms normalize_mult)
  also have "prime_factorization (msetprod (prime_factorization (x * y))) =
               prime_factorization (x * y)"
    by (rule prime_factorization_msetprod_primes) (simp_all add: in_prime_factorization_imp_prime)
  also have "prime_factorization (msetprod (prime_factorization x + prime_factorization y)) =
               prime_factorization x + prime_factorization y"
    by (rule prime_factorization_msetprod_primes) (auto simp: in_prime_factorization_imp_prime)
  finally show ?thesis .
qed

lemma prime_factorization_prime_power:
  "is_prime p \<Longrightarrow> prime_factorization (p ^ n) = replicate_mset n p"
  by (induction n)
     (simp_all add: prime_factorization_mult prime_factorization_prime Multiset.union_commute)

lemma prime_decomposition: "unit_factor x * msetprod (prime_factorization x) = x"
  by (cases "x = 0") (simp_all add: msetprod_prime_factorization)

lemma prime_factorization_subset_iff_dvd:
  assumes [simp]: "x \<noteq> 0" "y \<noteq> 0"
  shows   "prime_factorization x \<subseteq># prime_factorization y \<longleftrightarrow> x dvd y"
proof -
  have "x dvd y \<longleftrightarrow> msetprod (prime_factorization x) dvd msetprod (prime_factorization y)"
    by (simp add: msetprod_prime_factorization)
  also have "\<dots> \<longleftrightarrow> prime_factorization x \<subseteq># prime_factorization y"
    by (auto intro!: msetprod_primes_dvd_imp_subset msetprod_subset_imp_dvd
                     in_prime_factorization_imp_prime)
  finally show ?thesis ..
qed

lemma prime_factorization_divide:
  assumes "b dvd a"
  shows   "prime_factorization (a div b) = prime_factorization a - prime_factorization b"
proof (cases "a = 0")
  case [simp]: False
  from assms have [simp]: "b \<noteq> 0" by auto
  have "prime_factorization ((a div b) * b) = prime_factorization (a div b) + prime_factorization b"
    by (intro prime_factorization_mult) (insert assms, auto elim!: dvdE)
  with assms show ?thesis by simp
qed simp_all

lemma zero_not_in_prime_factorization [simp]: "0 \<notin># prime_factorization x"
  by (auto dest: in_prime_factorization_imp_prime)


definition "gcd_factorial a b = (if a = 0 then normalize b
     else if b = 0 then normalize a
     else msetprod (prime_factorization a #\<inter> prime_factorization b))"

definition "lcm_factorial a b = (if a = 0 \<or> b = 0 then 0
     else msetprod (prime_factorization a #\<union> prime_factorization b))"

definition "Gcd_factorial A =
  (if A \<subseteq> {0} then 0 else msetprod (Inf (prime_factorization ` (A - {0}))))"

definition "Lcm_factorial A =
  (if A = {} then 1
   else if 0 \<notin> A \<and> subset_mset.bdd_above (prime_factorization ` (A - {0})) then
     msetprod (Sup (prime_factorization ` A))
   else
     0)"

lemma prime_factorization_gcd_factorial:
  assumes [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "prime_factorization (gcd_factorial a b) = prime_factorization a #\<inter> prime_factorization b"
proof -
  have "prime_factorization (gcd_factorial a b) =
          prime_factorization (msetprod (prime_factorization a #\<inter> prime_factorization b))"
    by (simp add: gcd_factorial_def)
  also have "\<dots> = prime_factorization a #\<inter> prime_factorization b"
    by (subst prime_factorization_msetprod_primes) (auto simp add: in_prime_factorization_imp_prime)
  finally show ?thesis .
qed

lemma prime_factorization_lcm_factorial:
  assumes [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "prime_factorization (lcm_factorial a b) = prime_factorization a #\<union> prime_factorization b"
proof -
  have "prime_factorization (lcm_factorial a b) =
          prime_factorization (msetprod (prime_factorization a #\<union> prime_factorization b))"
    by (simp add: lcm_factorial_def)
  also have "\<dots> = prime_factorization a #\<union> prime_factorization b"
    by (subst prime_factorization_msetprod_primes) (auto simp add: in_prime_factorization_imp_prime)
  finally show ?thesis .
qed

lemma prime_factorization_Gcd_factorial:
  assumes "\<not>A \<subseteq> {0}"
  shows   "prime_factorization (Gcd_factorial A) = Inf (prime_factorization ` (A - {0}))"
proof -
  from assms obtain x where x: "x \<in> A - {0}" by auto
  hence "Inf (prime_factorization ` (A - {0})) \<subseteq># prime_factorization x"
    by (intro subset_mset.cInf_lower) simp_all
  hence "\<forall>y. y \<in># Inf (prime_factorization ` (A - {0})) \<longrightarrow> y \<in># prime_factorization x"
    by (auto dest: mset_subset_eqD)
  with in_prime_factorization_imp_prime[of _ x]
    have "\<forall>p. p \<in># Inf (prime_factorization ` (A - {0})) \<longrightarrow> is_prime p" by blast
  with assms show ?thesis
    by (simp add: Gcd_factorial_def prime_factorization_msetprod_primes)
qed

lemma prime_factorization_Lcm_factorial:
  assumes "0 \<notin> A" "subset_mset.bdd_above (prime_factorization ` A)"
  shows   "prime_factorization (Lcm_factorial A) = Sup (prime_factorization ` A)"
proof (cases "A = {}")
  case True
  hence "prime_factorization ` A = {}" by auto
  also have "Sup \<dots> = {#}" by (simp add: Sup_multiset_empty)
  finally show ?thesis by (simp add: Lcm_factorial_def)
next
  case False
  have "\<forall>y. y \<in># Sup (prime_factorization ` A) \<longrightarrow> is_prime y"
    by (auto simp: in_Sup_multiset_iff assms in_prime_factorization_imp_prime)
  with assms False show ?thesis
    by (simp add: Lcm_factorial_def prime_factorization_msetprod_primes)
qed

lemma gcd_factorial_commute: "gcd_factorial a b = gcd_factorial b a"
  by (simp add: gcd_factorial_def multiset_inter_commute)

lemma gcd_factorial_dvd1: "gcd_factorial a b dvd a"
proof (cases "a = 0 \<or> b = 0")
  case False
  hence "gcd_factorial a b \<noteq> 0" by (auto simp: gcd_factorial_def)
  with False show ?thesis
    by (subst prime_factorization_subset_iff_dvd [symmetric])
       (auto simp: prime_factorization_gcd_factorial)
qed (auto simp: gcd_factorial_def)

lemma gcd_factorial_dvd2: "gcd_factorial a b dvd b"
  by (subst gcd_factorial_commute) (rule gcd_factorial_dvd1)

lemma normalize_gcd_factorial: "normalize (gcd_factorial a b) = gcd_factorial a b"
proof -
  have "normalize (msetprod (prime_factorization a #\<inter> prime_factorization b)) =
          msetprod (prime_factorization a #\<inter> prime_factorization b)"
    by (intro normalize_msetprod_primes) (auto simp: in_prime_factorization_imp_prime)
  thus ?thesis by (simp add: gcd_factorial_def)
qed

lemma gcd_factorial_greatest: "c dvd gcd_factorial a b" if "c dvd a" "c dvd b" for a b c
proof (cases "a = 0 \<or> b = 0")
  case False
  with that have [simp]: "c \<noteq> 0" by auto
  let ?p = "prime_factorization"
  from that False have "?p c \<subseteq># ?p a" "?p c \<subseteq># ?p b"
    by (simp_all add: prime_factorization_subset_iff_dvd)
  hence "prime_factorization c \<subseteq>#
           prime_factorization (msetprod (prime_factorization a #\<inter> prime_factorization b))"
    using False by (subst prime_factorization_msetprod_primes)
                   (auto simp: in_prime_factorization_imp_prime)
  with False show ?thesis
    by (auto simp: gcd_factorial_def prime_factorization_subset_iff_dvd [symmetric])
qed (auto simp: gcd_factorial_def that)

lemma lcm_factorial_gcd_factorial:
  "lcm_factorial a b = normalize (a * b) div gcd_factorial a b" for a b
proof (cases "a = 0 \<or> b = 0")
  case False
  let ?p = "prime_factorization"
  from False have "msetprod (?p (a * b)) div gcd_factorial a b =
                     msetprod (?p a + ?p b - ?p a #\<inter> ?p b)"
    by (subst msetprod_diff) (auto simp: lcm_factorial_def gcd_factorial_def
                                prime_factorization_mult subset_mset.le_infI1)
  also from False have "msetprod (?p (a * b)) = normalize (a * b)"
    by (intro msetprod_prime_factorization) simp_all
  also from False have "msetprod (?p a + ?p b - ?p a #\<inter> ?p b) = lcm_factorial a b"
    by (simp add: union_diff_inter_eq_sup lcm_factorial_def)
  finally show ?thesis ..
qed (auto simp: lcm_factorial_def)

lemma normalize_Gcd_factorial:
  "normalize (Gcd_factorial A) = Gcd_factorial A"
proof (cases "A \<subseteq> {0}")
  case False
  then obtain x where "x \<in> A" "x \<noteq> 0" by blast
  hence "Inf (prime_factorization ` (A - {0})) \<subseteq># prime_factorization x"
    by (intro subset_mset.cInf_lower) auto
  hence "is_prime p" if "p \<in># Inf (prime_factorization ` (A - {0}))" for p
    using that by (auto dest: mset_subset_eqD intro: in_prime_factorization_imp_prime)
  with False show ?thesis
    by (auto simp add: Gcd_factorial_def normalize_msetprod_primes)
qed (simp_all add: Gcd_factorial_def)

lemma Gcd_factorial_eq_0_iff:
  "Gcd_factorial A = 0 \<longleftrightarrow> A \<subseteq> {0}"
  by (auto simp: Gcd_factorial_def in_Inf_multiset_iff split: if_splits)

lemma Gcd_factorial_dvd:
  assumes "x \<in> A"
  shows   "Gcd_factorial A dvd x"
proof (cases "x = 0")
  case False
  with assms have "prime_factorization (Gcd_factorial A) = Inf (prime_factorization ` (A - {0}))"
    by (intro prime_factorization_Gcd_factorial) auto
  also from False assms have "\<dots> \<subseteq># prime_factorization x"
    by (intro subset_mset.cInf_lower) auto
  finally show ?thesis
    by (subst (asm) prime_factorization_subset_iff_dvd)
       (insert assms False, auto simp: Gcd_factorial_eq_0_iff)
qed simp_all

lemma Gcd_factorial_greatest:
  assumes "\<And>y. y \<in> A \<Longrightarrow> x dvd y"
  shows   "x dvd Gcd_factorial A"
proof (cases "A \<subseteq> {0}")
  case False
  from False obtain y where "y \<in> A" "y \<noteq> 0" by auto
  with assms[of y] have nz: "x \<noteq> 0" by auto
  from nz assms have "prime_factorization x \<subseteq># prime_factorization y" if "y \<in> A - {0}" for y
    using that by (subst prime_factorization_subset_iff_dvd) auto
  with False have "prime_factorization x \<subseteq># Inf (prime_factorization ` (A - {0}))"
    by (intro subset_mset.cInf_greatest) auto
  also from False have "\<dots> = prime_factorization (Gcd_factorial A)"
    by (rule prime_factorization_Gcd_factorial [symmetric])
  finally show ?thesis
    by (subst (asm) prime_factorization_subset_iff_dvd)
       (insert nz False, auto simp: Gcd_factorial_eq_0_iff)
qed (simp_all add: Gcd_factorial_def)


lemma normalize_Lcm_factorial:
  "normalize (Lcm_factorial A) = Lcm_factorial A"
proof (cases "subset_mset.bdd_above (prime_factorization ` A)")
  case True
  hence "normalize (msetprod (Sup (prime_factorization ` A))) =
           msetprod (Sup (prime_factorization ` A))"
    by (intro normalize_msetprod_primes)
       (auto simp: in_Sup_multiset_iff in_prime_factorization_imp_prime)
  with True show ?thesis by (simp add: Lcm_factorial_def)
qed (auto simp: Lcm_factorial_def)

lemma Lcm_factorial_eq_0_iff:
  "Lcm_factorial A = 0 \<longleftrightarrow> 0 \<in> A \<or> \<not>subset_mset.bdd_above (prime_factorization ` A)"
  by (auto simp: Lcm_factorial_def in_Sup_multiset_iff)

lemma dvd_Lcm_factorial:
  assumes "x \<in> A"
  shows   "x dvd Lcm_factorial A"
proof (cases "0 \<notin> A \<and> subset_mset.bdd_above (prime_factorization ` A)")
  case True
  with assms have [simp]: "0 \<notin> A" "x \<noteq> 0" "A \<noteq> {}" by auto
  from assms True have "prime_factorization x \<subseteq># Sup (prime_factorization ` A)"
    by (intro subset_mset.cSup_upper) auto
  also have "\<dots> = prime_factorization (Lcm_factorial A)"
    by (rule prime_factorization_Lcm_factorial [symmetric]) (insert True, simp_all)
  finally show ?thesis
    by (subst (asm) prime_factorization_subset_iff_dvd)
       (insert True, auto simp: Lcm_factorial_eq_0_iff)
qed (insert assms, auto simp: Lcm_factorial_def)

lemma Lcm_factorial_least:
  assumes "\<And>y. y \<in> A \<Longrightarrow> y dvd x"
  shows   "Lcm_factorial A dvd x"
proof -
  consider "A = {}" | "0 \<in> A" | "x = 0" | "A \<noteq> {}" "0 \<notin> A" "x \<noteq> 0" by blast
  thus ?thesis
  proof cases
    assume *: "A \<noteq> {}" "0 \<notin> A" "x \<noteq> 0"
    hence nz: "x \<noteq> 0" if "x \<in> A" for x using that by auto
    from * have bdd: "subset_mset.bdd_above (prime_factorization ` A)"
      by (intro subset_mset.bdd_aboveI[of _ "prime_factorization x"])
         (auto simp: prime_factorization_subset_iff_dvd nz dest: assms)
    have "prime_factorization (Lcm_factorial A) = Sup (prime_factorization ` A)"
      by (rule prime_factorization_Lcm_factorial) fact+
    also from * have "\<dots> \<subseteq># prime_factorization x"
      by (intro subset_mset.cSup_least)
         (auto simp: prime_factorization_subset_iff_dvd nz dest: assms)
    finally show ?thesis
      by (subst (asm) prime_factorization_subset_iff_dvd)
         (insert * bdd, auto simp: Lcm_factorial_eq_0_iff)
  qed (auto simp: Lcm_factorial_def dest: assms)
qed

lemmas gcd_lcm_factorial =
  gcd_factorial_dvd1 gcd_factorial_dvd2 gcd_factorial_greatest
  normalize_gcd_factorial lcm_factorial_gcd_factorial
  normalize_Gcd_factorial Gcd_factorial_dvd Gcd_factorial_greatest
  normalize_Lcm_factorial dvd_Lcm_factorial Lcm_factorial_least

end

lemma (in normalization_semidom) factorial_semiring_altI_aux:
  assumes finite_divisors: "\<And>x::'a. x \<noteq> 0 \<Longrightarrow> finite {y. y dvd x \<and> normalize y = y}"
  assumes irreducible_imp_prime: "\<And>x::'a. irreducible x \<Longrightarrow> is_prime_elem x"
  assumes "(x::'a) \<noteq> 0"
  shows   "\<exists>A. (\<forall>x. x \<in># A \<longrightarrow> is_prime_elem x) \<and> msetprod A = normalize x"
using \<open>x \<noteq> 0\<close>
proof (induction "card {b. b dvd x \<and> normalize b = b}" arbitrary: x rule: less_induct)
  case (less a)
  let ?fctrs = "\<lambda>a. {b. b dvd a \<and> normalize b = b}"
  show ?case
  proof (cases "is_unit a")
    case True
    thus ?thesis by (intro exI[of _ "{#}"]) (auto simp: is_unit_normalize)
  next
    case False
    show ?thesis
    proof (cases "\<exists>b. b dvd a \<and> \<not>is_unit b \<and> \<not>a dvd b")
      case False
      with \<open>\<not>is_unit a\<close> less.prems have "irreducible a" by (auto simp: irreducible_altdef)
      hence "is_prime_elem a" by (rule irreducible_imp_prime)
      thus ?thesis by (intro exI[of _ "{#normalize a#}"]) auto
    next
      case True
      then guess b by (elim exE conjE) note b = this

      from b have "?fctrs b \<subseteq> ?fctrs a" by (auto intro: dvd_trans)
      moreover from b have "normalize a \<notin> ?fctrs b" "normalize a \<in> ?fctrs a" by simp_all
      hence "?fctrs b \<noteq> ?fctrs a" by blast
      ultimately have "?fctrs b \<subset> ?fctrs a" by (subst subset_not_subset_eq) blast
      with finite_divisors[OF \<open>a \<noteq> 0\<close>] have "card (?fctrs b) < card (?fctrs a)"
        by (rule psubset_card_mono)
      moreover from \<open>a \<noteq> 0\<close> b have "b \<noteq> 0" by auto
      ultimately have "\<exists>A. (\<forall>x. x \<in># A \<longrightarrow> is_prime_elem x) \<and> msetprod A = normalize b"
        by (intro less) auto
      then guess A .. note A = this

      define c where "c = a div b"
      from b have c: "a = b * c" by (simp add: c_def)
      from less.prems c have "c \<noteq> 0" by auto
      from b c have "?fctrs c \<subseteq> ?fctrs a" by (auto intro: dvd_trans)
      moreover have "normalize a \<notin> ?fctrs c"
      proof safe
        assume "normalize a dvd c"
        hence "b * c dvd 1 * c" by (simp add: c)
        hence "b dvd 1" by (subst (asm) dvd_times_right_cancel_iff) fact+
        with b show False by simp
      qed
      with \<open>normalize a \<in> ?fctrs a\<close> have "?fctrs a \<noteq> ?fctrs c" by blast
      ultimately have "?fctrs c \<subset> ?fctrs a" by (subst subset_not_subset_eq) blast
      with finite_divisors[OF \<open>a \<noteq> 0\<close>] have "card (?fctrs c) < card (?fctrs a)"
        by (rule psubset_card_mono)
      with \<open>c \<noteq> 0\<close> have "\<exists>A. (\<forall>x. x \<in># A \<longrightarrow> is_prime_elem x) \<and> msetprod A = normalize c"
        by (intro less) auto
      then guess B .. note B = this

      from A B show ?thesis by (intro exI[of _ "A + B"]) (auto simp: c normalize_mult)
    qed
  qed
qed 

lemma factorial_semiring_altI:
  assumes finite_divisors: "\<And>x::'a. x \<noteq> 0 \<Longrightarrow> finite {y. y dvd x \<and> normalize y = y}"
  assumes irreducible_imp_prime: "\<And>x::'a. irreducible x \<Longrightarrow> is_prime_elem x"
  shows   "OFCLASS('a :: normalization_semidom, factorial_semiring_class)"
  by intro_classes (rule factorial_semiring_altI_aux[OF assms])


class factorial_semiring_gcd = factorial_semiring + gcd + Gcd +
  assumes gcd_eq_gcd_factorial: "gcd a b = gcd_factorial a b"
  and     lcm_eq_lcm_factorial: "lcm a b = lcm_factorial a b"
  and     Gcd_eq_Gcd_factorial: "Gcd A = Gcd_factorial A"
  and     Lcm_eq_Lcm_factorial: "Lcm A = Lcm_factorial A"
begin

lemma prime_factorization_gcd:
  assumes [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "prime_factorization (gcd a b) = prime_factorization a #\<inter> prime_factorization b"
  by (simp add: gcd_eq_gcd_factorial prime_factorization_gcd_factorial)

lemma prime_factorization_lcm:
  assumes [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "prime_factorization (lcm a b) = prime_factorization a #\<union> prime_factorization b"
  by (simp add: lcm_eq_lcm_factorial prime_factorization_lcm_factorial)

lemma prime_factorization_Gcd:
  assumes "Gcd A \<noteq> 0"
  shows   "prime_factorization (Gcd A) = Inf (prime_factorization ` (A - {0}))"
  using assms
  by (simp add: prime_factorization_Gcd_factorial Gcd_eq_Gcd_factorial Gcd_factorial_eq_0_iff)

lemma prime_factorization_Lcm:
  assumes "Lcm A \<noteq> 0"
  shows   "prime_factorization (Lcm A) = Sup (prime_factorization ` A)"
  using assms
  by (simp add: prime_factorization_Lcm_factorial Lcm_eq_Lcm_factorial Lcm_factorial_eq_0_iff)

subclass semiring_gcd
  by (standard, unfold gcd_eq_gcd_factorial lcm_eq_lcm_factorial)
     (rule gcd_lcm_factorial; assumption)+

subclass semiring_Gcd
  by (standard, unfold Gcd_eq_Gcd_factorial Lcm_eq_Lcm_factorial)
     (rule gcd_lcm_factorial; assumption)+

end


class factorial_ring_gcd = factorial_semiring_gcd + idom
begin

subclass ring_gcd ..

subclass idom_divide ..

end


lemma is_prime_elem_nat: "is_prime_elem (n::nat) \<longleftrightarrow> prime n"
proof
  assume *: "is_prime_elem n"
  show "prime n" unfolding prime_def
  proof safe
    from * have "n \<noteq> 0" "n \<noteq> 1" by (intro notI, simp del: One_nat_def)+
    thus "n > 1" by (cases n) simp_all
  next
    fix m assume m: "m dvd n" "m \<noteq> n"
    from * \<open>m dvd n\<close> have "n dvd m \<or> is_unit m"
      by (intro irreducibleD' prime_imp_irreducible)
    with m show "m = 1" by (auto dest: dvd_antisym)
  qed
qed (auto simp: is_prime_elem_def prime_gt_0_nat)

lemma is_prime_nat: "is_prime (n::nat) \<longleftrightarrow> prime n"
  by (simp add: is_prime_def is_prime_elem_nat)

lemma is_prime_elem_int: "is_prime_elem (n::int) \<longleftrightarrow> prime (nat (abs n))"
proof (subst is_prime_elem_nat [symmetric], rule iffI)
  assume "is_prime_elem n"
  thus "is_prime_elem (nat (abs n))" by (auto simp: is_prime_elem_def nat_dvd_iff)
next
  assume "is_prime_elem (nat (abs n))"
  thus "is_prime_elem n"
    by (auto simp: dvd_int_unfold_dvd_nat is_prime_elem_def abs_mult nat_mult_distrib)
qed

lemma is_prime_int: "is_prime (n::int) \<longleftrightarrow> prime n \<and> n \<ge> 0"
  by (simp add: is_prime_def is_prime_elem_int)

end

