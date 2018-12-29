(*  Author:     L C Paulson, University of Cambridge
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
    Author:     Brian Huffman, Portland State University
*)

section \<open>Elementary Topology\<close>

theory Elementary_Topology
imports
  "HOL-Library.Indicator_Function"
  "HOL-Library.Countable_Set"
  "HOL-Library.FuncSet"
  "HOL-Library.Set_Idioms"
  "HOL-Library.Infinite_Set"
  Product_Vector
begin

(* FIXME: move elsewhere *)

lemma approachable_lt_le: "(\<exists>(d::real) > 0. \<forall>x. f x < d \<longrightarrow> P x) \<longleftrightarrow> (\<exists>d>0. \<forall>x. f x \<le> d \<longrightarrow> P x)"
  apply auto
  apply (rule_tac x="d/2" in exI)
  apply auto
  done

lemma approachable_lt_le2:  \<comment> \<open>like the above, but pushes aside an extra formula\<close>
    "(\<exists>(d::real) > 0. \<forall>x. Q x \<longrightarrow> f x < d \<longrightarrow> P x) \<longleftrightarrow> (\<exists>d>0. \<forall>x. f x \<le> d \<longrightarrow> Q x \<longrightarrow> P x)"
  apply auto
  apply (rule_tac x="d/2" in exI, auto)
  done

lemma triangle_lemma:
  fixes x y z :: real
  assumes x: "0 \<le> x"
    and y: "0 \<le> y"
    and z: "0 \<le> z"
    and xy: "x\<^sup>2 \<le> y\<^sup>2 + z\<^sup>2"
  shows "x \<le> y + z"
proof -
  have "y\<^sup>2 + z\<^sup>2 \<le> y\<^sup>2 + 2 * y * z + z\<^sup>2"
    using z y by simp
  with xy have th: "x\<^sup>2 \<le> (y + z)\<^sup>2"
    by (simp add: power2_eq_square field_simps)
  from y z have yz: "y + z \<ge> 0"
    by arith
  from power2_le_imp_le[OF th yz] show ?thesis .
qed

definition (in monoid_add) support_on :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'b set"
  where "support_on s f = {x\<in>s. f x \<noteq> 0}"

lemma in_support_on: "x \<in> support_on s f \<longleftrightarrow> x \<in> s \<and> f x \<noteq> 0"
  by (simp add: support_on_def)

lemma support_on_simps[simp]:
  "support_on {} f = {}"
  "support_on (insert x s) f =
    (if f x = 0 then support_on s f else insert x (support_on s f))"
  "support_on (s \<union> t) f = support_on s f \<union> support_on t f"
  "support_on (s \<inter> t) f = support_on s f \<inter> support_on t f"
  "support_on (s - t) f = support_on s f - support_on t f"
  "support_on (f ` s) g = f ` (support_on s (g \<circ> f))"
  unfolding support_on_def by auto

lemma support_on_cong:
  "(\<And>x. x \<in> s \<Longrightarrow> f x = 0 \<longleftrightarrow> g x = 0) \<Longrightarrow> support_on s f = support_on s g"
  by (auto simp: support_on_def)

lemma support_on_if: "a \<noteq> 0 \<Longrightarrow> support_on A (\<lambda>x. if P x then a else 0) = {x\<in>A. P x}"
  by (auto simp: support_on_def)

lemma support_on_if_subset: "support_on A (\<lambda>x. if P x then a else 0) \<subseteq> {x \<in> A. P x}"
  by (auto simp: support_on_def)

lemma finite_support[intro]: "finite S \<Longrightarrow> finite (support_on S f)"
  unfolding support_on_def by auto

(* TODO: is supp_sum really needed? TODO: Generalize to Finite_Set.fold *)
definition (in comm_monoid_add) supp_sum :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'a"
  where "supp_sum f S = (\<Sum>x\<in>support_on S f. f x)"

lemma supp_sum_empty[simp]: "supp_sum f {} = 0"
  unfolding supp_sum_def by auto

lemma supp_sum_insert[simp]:
  "finite (support_on S f) \<Longrightarrow>
    supp_sum f (insert x S) = (if x \<in> S then supp_sum f S else f x + supp_sum f S)"
  by (simp add: supp_sum_def in_support_on insert_absorb)

lemma supp_sum_divide_distrib: "supp_sum f A / (r::'a::field) = supp_sum (\<lambda>n. f n / r) A"
  by (cases "r = 0")
     (auto simp: supp_sum_def sum_divide_distrib intro!: sum.cong support_on_cong)

(*END OF SUPPORT, ETC.*)

lemma image_affinity_interval:
  fixes c :: "'a::ordered_real_vector"
  shows "((\<lambda>x. m *\<^sub>R x + c) ` {a..b}) = 
           (if {a..b}={} then {}
            else if 0 \<le> m then {m *\<^sub>R a + c .. m  *\<^sub>R b + c}
            else {m *\<^sub>R b + c .. m *\<^sub>R a + c})"
         (is "?lhs = ?rhs")
proof (cases "m=0")
  case True
  then show ?thesis
    by force
next
  case False
  show ?thesis
  proof
    show "?lhs \<subseteq> ?rhs"
      by (auto simp: scaleR_left_mono scaleR_left_mono_neg)
    show "?rhs \<subseteq> ?lhs"
    proof (clarsimp, intro conjI impI subsetI)
      show "\<lbrakk>0 \<le> m; a \<le> b; x \<in> {m *\<^sub>R a + c..m *\<^sub>R b + c}\<rbrakk>
            \<Longrightarrow> x \<in> (\<lambda>x. m *\<^sub>R x + c) ` {a..b}" for x
        apply (rule_tac x="inverse m *\<^sub>R (x-c)" in rev_image_eqI)
        using False apply (auto simp: le_diff_eq pos_le_divideRI)
        using diff_le_eq pos_le_divideR_eq by force
      show "\<lbrakk>\<not> 0 \<le> m; a \<le> b;  x \<in> {m *\<^sub>R b + c..m *\<^sub>R a + c}\<rbrakk>
            \<Longrightarrow> x \<in> (\<lambda>x. m *\<^sub>R x + c) ` {a..b}" for x
        apply (rule_tac x="inverse m *\<^sub>R (x-c)" in rev_image_eqI)
        apply (auto simp: diff_le_eq neg_le_divideR_eq)
        using diff_eq_diff_less_eq linordered_field_class.sign_simps(11) minus_diff_eq not_less scaleR_le_cancel_left_neg by fastforce
    qed
  qed
qed

lemma countable_PiE:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> countable (F i)) \<Longrightarrow> countable (Pi\<^sub>E I F)"
  by (induct I arbitrary: F rule: finite_induct) (auto simp: PiE_insert_eq)

lemma open_sums:
  fixes T :: "('b::real_normed_vector) set"
  assumes "open S \<or> open T"
  shows "open (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
  using assms
proof
  assume S: "open S"
  show ?thesis
  proof (clarsimp simp: open_dist)
    fix x y
    assume "x \<in> S" "y \<in> T"
    with S obtain e where "e > 0" and e: "\<And>x'. dist x' x < e \<Longrightarrow> x' \<in> S"
      by (auto simp: open_dist)
    then have "\<And>z. dist z (x + y) < e \<Longrightarrow> \<exists>x\<in>S. \<exists>y\<in>T. z = x + y"
      by (metis \<open>y \<in> T\<close> diff_add_cancel dist_add_cancel2)
    then show "\<exists>e>0. \<forall>z. dist z (x + y) < e \<longrightarrow> (\<exists>x\<in>S. \<exists>y\<in>T. z = x + y)"
      using \<open>0 < e\<close> \<open>x \<in> S\<close> by blast
  qed
next
  assume T: "open T"
  show ?thesis
  proof (clarsimp simp: open_dist)
    fix x y
    assume "x \<in> S" "y \<in> T"
    with T obtain e where "e > 0" and e: "\<And>x'. dist x' y < e \<Longrightarrow> x' \<in> T"
      by (auto simp: open_dist)
    then have "\<And>z. dist z (x + y) < e \<Longrightarrow> \<exists>x\<in>S. \<exists>y\<in>T. z = x + y"
      by (metis \<open>x \<in> S\<close> add_diff_cancel_left' add_diff_eq diff_diff_add dist_norm)
    then show "\<exists>e>0. \<forall>z. dist z (x + y) < e \<longrightarrow> (\<exists>x\<in>S. \<exists>y\<in>T. z = x + y)"
      using \<open>0 < e\<close> \<open>y \<in> T\<close> by blast
  qed
qed


subsection \<open>Topological Basis\<close>

context topological_space
begin

definition%important "topological_basis B \<longleftrightarrow>
  (\<forall>b\<in>B. open b) \<and> (\<forall>x. open x \<longrightarrow> (\<exists>B'. B' \<subseteq> B \<and> \<Union>B' = x))"

lemma topological_basis:
  "topological_basis B \<longleftrightarrow> (\<forall>x. open x \<longleftrightarrow> (\<exists>B'. B' \<subseteq> B \<and> \<Union>B' = x))"
  unfolding topological_basis_def
  apply safe
     apply fastforce
    apply fastforce
   apply (erule_tac x=x in allE, simp)
   apply (rule_tac x="{x}" in exI, auto)
  done

lemma topological_basis_iff:
  assumes "\<And>B'. B' \<in> B \<Longrightarrow> open B'"
  shows "topological_basis B \<longleftrightarrow> (\<forall>O'. open O' \<longrightarrow> (\<forall>x\<in>O'. \<exists>B'\<in>B. x \<in> B' \<and> B' \<subseteq> O'))"
    (is "_ \<longleftrightarrow> ?rhs")
proof safe
  fix O' and x::'a
  assume H: "topological_basis B" "open O'" "x \<in> O'"
  then have "(\<exists>B'\<subseteq>B. \<Union>B' = O')" by (simp add: topological_basis_def)
  then obtain B' where "B' \<subseteq> B" "O' = \<Union>B'" by auto
  then show "\<exists>B'\<in>B. x \<in> B' \<and> B' \<subseteq> O'" using H by auto
next
  assume H: ?rhs
  show "topological_basis B"
    using assms unfolding topological_basis_def
  proof safe
    fix O' :: "'a set"
    assume "open O'"
    with H obtain f where "\<forall>x\<in>O'. f x \<in> B \<and> x \<in> f x \<and> f x \<subseteq> O'"
      by (force intro: bchoice simp: Bex_def)
    then show "\<exists>B'\<subseteq>B. \<Union>B' = O'"
      by (auto intro: exI[where x="{f x |x. x \<in> O'}"])
  qed
qed

lemma topological_basisI:
  assumes "\<And>B'. B' \<in> B \<Longrightarrow> open B'"
    and "\<And>O' x. open O' \<Longrightarrow> x \<in> O' \<Longrightarrow> \<exists>B'\<in>B. x \<in> B' \<and> B' \<subseteq> O'"
  shows "topological_basis B"
  using assms by (subst topological_basis_iff) auto

lemma topological_basisE:
  fixes O'
  assumes "topological_basis B"
    and "open O'"
    and "x \<in> O'"
  obtains B' where "B' \<in> B" "x \<in> B'" "B' \<subseteq> O'"
proof atomize_elim
  from assms have "\<And>B'. B'\<in>B \<Longrightarrow> open B'"
    by (simp add: topological_basis_def)
  with topological_basis_iff assms
  show  "\<exists>B'. B' \<in> B \<and> x \<in> B' \<and> B' \<subseteq> O'"
    using assms by (simp add: Bex_def)
qed

lemma topological_basis_open:
  assumes "topological_basis B"
    and "X \<in> B"
  shows "open X"
  using assms by (simp add: topological_basis_def)

lemma topological_basis_imp_subbasis:
  assumes B: "topological_basis B"
  shows "open = generate_topology B"
proof (intro ext iffI)
  fix S :: "'a set"
  assume "open S"
  with B obtain B' where "B' \<subseteq> B" "S = \<Union>B'"
    unfolding topological_basis_def by blast
  then show "generate_topology B S"
    by (auto intro: generate_topology.intros dest: topological_basis_open)
next
  fix S :: "'a set"
  assume "generate_topology B S"
  then show "open S"
    by induct (auto dest: topological_basis_open[OF B])
qed

lemma basis_dense:
  fixes B :: "'a set set"
    and f :: "'a set \<Rightarrow> 'a"
  assumes "topological_basis B"
    and choosefrom_basis: "\<And>B'. B' \<noteq> {} \<Longrightarrow> f B' \<in> B'"
  shows "\<forall>X. open X \<longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>B' \<in> B. f B' \<in> X)"
proof (intro allI impI)
  fix X :: "'a set"
  assume "open X" and "X \<noteq> {}"
  from topological_basisE[OF \<open>topological_basis B\<close> \<open>open X\<close> choosefrom_basis[OF \<open>X \<noteq> {}\<close>]]
  obtain B' where "B' \<in> B" "f X \<in> B'" "B' \<subseteq> X" .
  then show "\<exists>B'\<in>B. f B' \<in> X"
    by (auto intro!: choosefrom_basis)
qed

end

lemma topological_basis_prod:
  assumes A: "topological_basis A"
    and B: "topological_basis B"
  shows "topological_basis ((\<lambda>(a, b). a \<times> b) ` (A \<times> B))"
  unfolding topological_basis_def
proof (safe, simp_all del: ex_simps add: subset_image_iff ex_simps(1)[symmetric])
  fix S :: "('a \<times> 'b) set"
  assume "open S"
  then show "\<exists>X\<subseteq>A \<times> B. (\<Union>(a,b)\<in>X. a \<times> b) = S"
  proof (safe intro!: exI[of _ "{x\<in>A \<times> B. fst x \<times> snd x \<subseteq> S}"])
    fix x y
    assume "(x, y) \<in> S"
    from open_prod_elim[OF \<open>open S\<close> this]
    obtain a b where a: "open a""x \<in> a" and b: "open b" "y \<in> b" and "a \<times> b \<subseteq> S"
      by (metis mem_Sigma_iff)
    moreover
    from A a obtain A0 where "A0 \<in> A" "x \<in> A0" "A0 \<subseteq> a"
      by (rule topological_basisE)
    moreover
    from B b obtain B0 where "B0 \<in> B" "y \<in> B0" "B0 \<subseteq> b"
      by (rule topological_basisE)
    ultimately show "(x, y) \<in> (\<Union>(a, b)\<in>{X \<in> A \<times> B. fst X \<times> snd X \<subseteq> S}. a \<times> b)"
      by (intro UN_I[of "(A0, B0)"]) auto
  qed auto
qed (metis A B topological_basis_open open_Times)


subsection \<open>Countable Basis\<close>

locale%important countable_basis =
  fixes B :: "'a::topological_space set set"
  assumes is_basis: "topological_basis B"
    and countable_basis: "countable B"
begin

lemma open_countable_basis_ex:
  assumes "open X"
  shows "\<exists>B' \<subseteq> B. X = \<Union>B'"
  using assms countable_basis is_basis
  unfolding topological_basis_def by blast

lemma open_countable_basisE:
  assumes "open X"
  obtains B' where "B' \<subseteq> B" "X = \<Union>B'"
  using assms open_countable_basis_ex
  by atomize_elim simp

lemma countable_dense_exists:
  "\<exists>D::'a set. countable D \<and> (\<forall>X. open X \<longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>d \<in> D. d \<in> X))"
proof -
  let ?f = "(\<lambda>B'. SOME x. x \<in> B')"
  have "countable (?f ` B)" using countable_basis by simp
  with basis_dense[OF is_basis, of ?f] show ?thesis
    by (intro exI[where x="?f ` B"]) (metis (mono_tags) all_not_in_conv imageI someI)
qed

lemma countable_dense_setE:
  obtains D :: "'a set"
  where "countable D" "\<And>X. open X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>d \<in> D. d \<in> X"
  using countable_dense_exists by blast

end

lemma (in first_countable_topology) first_countable_basisE:
  fixes x :: 'a
  obtains \<A> where "countable \<A>" "\<And>A. A \<in> \<A> \<Longrightarrow> x \<in> A" "\<And>A. A \<in> \<A> \<Longrightarrow> open A"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> (\<exists>A\<in>\<A>. A \<subseteq> S)"
proof -
  obtain \<A> where \<A>: "(\<forall>i::nat. x \<in> \<A> i \<and> open (\<A> i))" "(\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. \<A> i \<subseteq> S))"
    using first_countable_basis[of x] by metis
  show thesis
  proof 
    show "countable (range \<A>)"
      by simp
  qed (use \<A> in auto)
qed

lemma (in first_countable_topology) first_countable_basis_Int_stableE:
  obtains \<A> where "countable \<A>" "\<And>A. A \<in> \<A> \<Longrightarrow> x \<in> A" "\<And>A. A \<in> \<A> \<Longrightarrow> open A"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> (\<exists>A\<in>\<A>. A \<subseteq> S)"
    "\<And>A B. A \<in> \<A> \<Longrightarrow> B \<in> \<A> \<Longrightarrow> A \<inter> B \<in> \<A>"
proof atomize_elim
  obtain \<B> where \<B>:
    "countable \<B>"
    "\<And>B. B \<in> \<B> \<Longrightarrow> x \<in> B"
    "\<And>B. B \<in> \<B> \<Longrightarrow> open B"
    "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists>B\<in>\<B>. B \<subseteq> S"
    by (rule first_countable_basisE) blast
  define \<A> where [abs_def]:
    "\<A> = (\<lambda>N. \<Inter>((\<lambda>n. from_nat_into \<B> n) ` N)) ` (Collect finite::nat set set)"
  then show "\<exists>\<A>. countable \<A> \<and> (\<forall>A. A \<in> \<A> \<longrightarrow> x \<in> A) \<and> (\<forall>A. A \<in> \<A> \<longrightarrow> open A) \<and>
        (\<forall>S. open S \<longrightarrow> x \<in> S \<longrightarrow> (\<exists>A\<in>\<A>. A \<subseteq> S)) \<and> (\<forall>A B. A \<in> \<A> \<longrightarrow> B \<in> \<A> \<longrightarrow> A \<inter> B \<in> \<A>)"
  proof (safe intro!: exI[where x=\<A>])
    show "countable \<A>"
      unfolding \<A>_def by (intro countable_image countable_Collect_finite)
    fix A
    assume "A \<in> \<A>"
    then show "x \<in> A" "open A"
      using \<B>(4)[OF open_UNIV] by (auto simp: \<A>_def intro: \<B> from_nat_into)
  next
    let ?int = "\<lambda>N. \<Inter>(from_nat_into \<B> ` N)"
    fix A B
    assume "A \<in> \<A>" "B \<in> \<A>"
    then obtain N M where "A = ?int N" "B = ?int M" "finite (N \<union> M)"
      by (auto simp: \<A>_def)
    then show "A \<inter> B \<in> \<A>"
      by (auto simp: \<A>_def intro!: image_eqI[where x="N \<union> M"])
  next
    fix S
    assume "open S" "x \<in> S"
    then obtain a where a: "a\<in>\<B>" "a \<subseteq> S" using \<B> by blast
    then show "\<exists>a\<in>\<A>. a \<subseteq> S" using a \<B>
      by (intro bexI[where x=a]) (auto simp: \<A>_def intro: image_eqI[where x="{to_nat_on \<B> a}"])
  qed
qed

lemma (in topological_space) first_countableI:
  assumes "countable \<A>"
    and 1: "\<And>A. A \<in> \<A> \<Longrightarrow> x \<in> A" "\<And>A. A \<in> \<A> \<Longrightarrow> open A"
    and 2: "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists>A\<in>\<A>. A \<subseteq> S"
  shows "\<exists>\<A>::nat \<Rightarrow> 'a set. (\<forall>i. x \<in> \<A> i \<and> open (\<A> i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. \<A> i \<subseteq> S))"
proof (safe intro!: exI[of _ "from_nat_into \<A>"])
  fix i
  have "\<A> \<noteq> {}" using 2[of UNIV] by auto
  show "x \<in> from_nat_into \<A> i" "open (from_nat_into \<A> i)"
    using range_from_nat_into_subset[OF \<open>\<A> \<noteq> {}\<close>] 1 by auto
next
  fix S
  assume "open S" "x\<in>S" from 2[OF this]
  show "\<exists>i. from_nat_into \<A> i \<subseteq> S"
    using subset_range_from_nat_into[OF \<open>countable \<A>\<close>] by auto
qed

instance prod :: (first_countable_topology, first_countable_topology) first_countable_topology
proof
  fix x :: "'a \<times> 'b"
  obtain \<A> where \<A>:
      "countable \<A>"
      "\<And>a. a \<in> \<A> \<Longrightarrow> fst x \<in> a"
      "\<And>a. a \<in> \<A> \<Longrightarrow> open a"
      "\<And>S. open S \<Longrightarrow> fst x \<in> S \<Longrightarrow> \<exists>a\<in>\<A>. a \<subseteq> S"
    by (rule first_countable_basisE[of "fst x"]) blast
  obtain B where B:
      "countable B"
      "\<And>a. a \<in> B \<Longrightarrow> snd x \<in> a"
      "\<And>a. a \<in> B \<Longrightarrow> open a"
      "\<And>S. open S \<Longrightarrow> snd x \<in> S \<Longrightarrow> \<exists>a\<in>B. a \<subseteq> S"
    by (rule first_countable_basisE[of "snd x"]) blast
  show "\<exists>\<A>::nat \<Rightarrow> ('a \<times> 'b) set.
    (\<forall>i. x \<in> \<A> i \<and> open (\<A> i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. \<A> i \<subseteq> S))"
  proof (rule first_countableI[of "(\<lambda>(a, b). a \<times> b) ` (\<A> \<times> B)"], safe)
    fix a b
    assume x: "a \<in> \<A>" "b \<in> B"
    show "x \<in> a \<times> b" 
      by (simp add: \<A>(2) B(2) mem_Times_iff x)
    show "open (a \<times> b)"
      by (simp add: \<A>(3) B(3) open_Times x)
  next
    fix S
    assume "open S" "x \<in> S"
    then obtain a' b' where a'b': "open a'" "open b'" "x \<in> a' \<times> b'" "a' \<times> b' \<subseteq> S"
      by (rule open_prod_elim)
    moreover
    from a'b' \<A>(4)[of a'] B(4)[of b']
    obtain a b where "a \<in> \<A>" "a \<subseteq> a'" "b \<in> B" "b \<subseteq> b'"
      by auto
    ultimately
    show "\<exists>a\<in>(\<lambda>(a, b). a \<times> b) ` (\<A> \<times> B). a \<subseteq> S"
      by (auto intro!: bexI[of _ "a \<times> b"] bexI[of _ a] bexI[of _ b])
  qed (simp add: \<A> B)
qed

class second_countable_topology = topological_space +
  assumes ex_countable_subbasis:
    "\<exists>B::'a::topological_space set set. countable B \<and> open = generate_topology B"
begin

lemma ex_countable_basis: "\<exists>B::'a set set. countable B \<and> topological_basis B"
proof -
  from ex_countable_subbasis obtain B where B: "countable B" "open = generate_topology B"
    by blast
  let ?B = "Inter ` {b. finite b \<and> b \<subseteq> B }"

  show ?thesis
  proof (intro exI conjI)
    show "countable ?B"
      by (intro countable_image countable_Collect_finite_subset B)
    {
      fix S
      assume "open S"
      then have "\<exists>B'\<subseteq>{b. finite b \<and> b \<subseteq> B}. (\<Union>b\<in>B'. \<Inter>b) = S"
        unfolding B
      proof induct
        case UNIV
        show ?case by (intro exI[of _ "{{}}"]) simp
      next
        case (Int a b)
        then obtain x y where x: "a = \<Union>(Inter ` x)" "\<And>i. i \<in> x \<Longrightarrow> finite i \<and> i \<subseteq> B"
          and y: "b = \<Union>(Inter ` y)" "\<And>i. i \<in> y \<Longrightarrow> finite i \<and> i \<subseteq> B"
          by blast
        show ?case
          unfolding x y Int_UN_distrib2
          by (intro exI[of _ "{i \<union> j| i j.  i \<in> x \<and> j \<in> y}"]) (auto dest: x(2) y(2))
      next
        case (UN K)
        then have "\<forall>k\<in>K. \<exists>B'\<subseteq>{b. finite b \<and> b \<subseteq> B}. \<Union> (Inter ` B') = k" by auto
        then obtain k where
            "\<forall>ka\<in>K. k ka \<subseteq> {b. finite b \<and> b \<subseteq> B} \<and> \<Union>(Inter ` (k ka)) = ka"
          unfolding bchoice_iff ..
        then show "\<exists>B'\<subseteq>{b. finite b \<and> b \<subseteq> B}. \<Union> (Inter ` B') = \<Union>K"
          by (intro exI[of _ "\<Union>(k ` K)"]) auto
      next
        case (Basis S)
        then show ?case
          by (intro exI[of _ "{{S}}"]) auto
      qed
      then have "(\<exists>B'\<subseteq>Inter ` {b. finite b \<and> b \<subseteq> B}. \<Union>B' = S)"
        unfolding subset_image_iff by blast }
    then show "topological_basis ?B"
      unfolding topological_space_class.topological_basis_def
      by (safe intro!: topological_space_class.open_Inter)
         (simp_all add: B generate_topology.Basis subset_eq)
  qed
qed

end

sublocale second_countable_topology <
  countable_basis "SOME B. countable B \<and> topological_basis B"
  using someI_ex[OF ex_countable_basis]
  by unfold_locales safe

instance prod :: (second_countable_topology, second_countable_topology) second_countable_topology
proof
  obtain A :: "'a set set" where "countable A" "topological_basis A"
    using ex_countable_basis by auto
  moreover
  obtain B :: "'b set set" where "countable B" "topological_basis B"
    using ex_countable_basis by auto
  ultimately show "\<exists>B::('a \<times> 'b) set set. countable B \<and> open = generate_topology B"
    by (auto intro!: exI[of _ "(\<lambda>(a, b). a \<times> b) ` (A \<times> B)"] topological_basis_prod
      topological_basis_imp_subbasis)
qed

instance second_countable_topology \<subseteq> first_countable_topology
proof
  fix x :: 'a
  define B :: "'a set set" where "B = (SOME B. countable B \<and> topological_basis B)"
  then have B: "countable B" "topological_basis B"
    using countable_basis is_basis
    by (auto simp: countable_basis is_basis)
  then show "\<exists>A::nat \<Rightarrow> 'a set.
    (\<forall>i. x \<in> A i \<and> open (A i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. A i \<subseteq> S))"
    by (intro first_countableI[of "{b\<in>B. x \<in> b}"])
       (fastforce simp: topological_space_class.topological_basis_def)+
qed

instance nat :: second_countable_topology
proof
  show "\<exists>B::nat set set. countable B \<and> open = generate_topology B"
    by (intro exI[of _ "range lessThan \<union> range greaterThan"]) (auto simp: open_nat_def)
qed

lemma countable_separating_set_linorder1:
  shows "\<exists>B::('a::{linorder_topology, second_countable_topology} set). countable B \<and> (\<forall>x y. x < y \<longrightarrow> (\<exists>b \<in> B. x < b \<and> b \<le> y))"
proof -
  obtain A::"'a set set" where "countable A" "topological_basis A" using ex_countable_basis by auto
  define B1 where "B1 = {(LEAST x. x \<in> U)| U. U \<in> A}"
  then have "countable B1" using \<open>countable A\<close> by (simp add: Setcompr_eq_image)
  define B2 where "B2 = {(SOME x. x \<in> U)| U. U \<in> A}"
  then have "countable B2" using \<open>countable A\<close> by (simp add: Setcompr_eq_image)
  have "\<exists>b \<in> B1 \<union> B2. x < b \<and> b \<le> y" if "x < y" for x y
  proof (cases)
    assume "\<exists>z. x < z \<and> z < y"
    then obtain z where z: "x < z \<and> z < y" by auto
    define U where "U = {x<..<y}"
    then have "open U" by simp
    moreover have "z \<in> U" using z U_def by simp
    ultimately obtain V where "V \<in> A" "z \<in> V" "V \<subseteq> U" using topological_basisE[OF \<open>topological_basis A\<close>] by auto
    define w where "w = (SOME x. x \<in> V)"
    then have "w \<in> V" using \<open>z \<in> V\<close> by (metis someI2)
    then have "x < w \<and> w \<le> y" using \<open>w \<in> V\<close> \<open>V \<subseteq> U\<close> U_def by fastforce
    moreover have "w \<in> B1 \<union> B2" using w_def B2_def \<open>V \<in> A\<close> by auto
    ultimately show ?thesis by auto
  next
    assume "\<not>(\<exists>z. x < z \<and> z < y)"
    then have *: "\<And>z. z > x \<Longrightarrow> z \<ge> y" by auto
    define U where "U = {x<..}"
    then have "open U" by simp
    moreover have "y \<in> U" using \<open>x < y\<close> U_def by simp
    ultimately obtain "V" where "V \<in> A" "y \<in> V" "V \<subseteq> U" using topological_basisE[OF \<open>topological_basis A\<close>] by auto
    have "U = {y..}" unfolding U_def using * \<open>x < y\<close> by auto
    then have "V \<subseteq> {y..}" using \<open>V \<subseteq> U\<close> by simp
    then have "(LEAST w. w \<in> V) = y" using \<open>y \<in> V\<close> by (meson Least_equality atLeast_iff subsetCE)
    then have "y \<in> B1 \<union> B2" using \<open>V \<in> A\<close> B1_def by auto
    moreover have "x < y \<and> y \<le> y" using \<open>x < y\<close> by simp
    ultimately show ?thesis by auto
  qed
  moreover have "countable (B1 \<union> B2)" using \<open>countable B1\<close> \<open>countable B2\<close> by simp
  ultimately show ?thesis by auto
qed

lemma countable_separating_set_linorder2:
  shows "\<exists>B::('a::{linorder_topology, second_countable_topology} set). countable B \<and> (\<forall>x y. x < y \<longrightarrow> (\<exists>b \<in> B. x \<le> b \<and> b < y))"
proof -
  obtain A::"'a set set" where "countable A" "topological_basis A" using ex_countable_basis by auto
  define B1 where "B1 = {(GREATEST x. x \<in> U) | U. U \<in> A}"
  then have "countable B1" using \<open>countable A\<close> by (simp add: Setcompr_eq_image)
  define B2 where "B2 = {(SOME x. x \<in> U)| U. U \<in> A}"
  then have "countable B2" using \<open>countable A\<close> by (simp add: Setcompr_eq_image)
  have "\<exists>b \<in> B1 \<union> B2. x \<le> b \<and> b < y" if "x < y" for x y
  proof (cases)
    assume "\<exists>z. x < z \<and> z < y"
    then obtain z where z: "x < z \<and> z < y" by auto
    define U where "U = {x<..<y}"
    then have "open U" by simp
    moreover have "z \<in> U" using z U_def by simp
    ultimately obtain "V" where "V \<in> A" "z \<in> V" "V \<subseteq> U" using topological_basisE[OF \<open>topological_basis A\<close>] by auto
    define w where "w = (SOME x. x \<in> V)"
    then have "w \<in> V" using \<open>z \<in> V\<close> by (metis someI2)
    then have "x \<le> w \<and> w < y" using \<open>w \<in> V\<close> \<open>V \<subseteq> U\<close> U_def by fastforce
    moreover have "w \<in> B1 \<union> B2" using w_def B2_def \<open>V \<in> A\<close> by auto
    ultimately show ?thesis by auto
  next
    assume "\<not>(\<exists>z. x < z \<and> z < y)"
    then have *: "\<And>z. z < y \<Longrightarrow> z \<le> x" using leI by blast
    define U where "U = {..<y}"
    then have "open U" by simp
    moreover have "x \<in> U" using \<open>x < y\<close> U_def by simp
    ultimately obtain "V" where "V \<in> A" "x \<in> V" "V \<subseteq> U" using topological_basisE[OF \<open>topological_basis A\<close>] by auto
    have "U = {..x}" unfolding U_def using * \<open>x < y\<close> by auto
    then have "V \<subseteq> {..x}" using \<open>V \<subseteq> U\<close> by simp
    then have "(GREATEST x. x \<in> V) = x" using \<open>x \<in> V\<close> by (meson Greatest_equality atMost_iff subsetCE)
    then have "x \<in> B1 \<union> B2" using \<open>V \<in> A\<close> B1_def by auto
    moreover have "x \<le> x \<and> x < y" using \<open>x < y\<close> by simp
    ultimately show ?thesis by auto
  qed
  moreover have "countable (B1 \<union> B2)" using \<open>countable B1\<close> \<open>countable B2\<close> by simp
  ultimately show ?thesis by auto
qed

lemma countable_separating_set_dense_linorder:
  shows "\<exists>B::('a::{linorder_topology, dense_linorder, second_countable_topology} set). countable B \<and> (\<forall>x y. x < y \<longrightarrow> (\<exists>b \<in> B. x < b \<and> b < y))"
proof -
  obtain B::"'a set" where B: "countable B" "\<And>x y. x < y \<Longrightarrow> (\<exists>b \<in> B. x < b \<and> b \<le> y)"
    using countable_separating_set_linorder1 by auto
  have "\<exists>b \<in> B. x < b \<and> b < y" if "x < y" for x y
  proof -
    obtain z where "x < z" "z < y" using \<open>x < y\<close> dense by blast
    then obtain b where "b \<in> B" "x < b \<and> b \<le> z" using B(2) by auto
    then have "x < b \<and> b < y" using \<open>z < y\<close> by auto
    then show ?thesis using \<open>b \<in> B\<close> by auto
  qed
  then show ?thesis using B(1) by auto
qed

subsection%important \<open>Polish spaces\<close>

text \<open>Textbooks define Polish spaces as completely metrizable.
  We assume the topology to be complete for a given metric.\<close>

class polish_space = complete_space + second_countable_topology

subsection \<open>General notion of a topology as a value\<close>

definition%important "istopology L \<longleftrightarrow>
  L {} \<and> (\<forall>S T. L S \<longrightarrow> L T \<longrightarrow> L (S \<inter> T)) \<and> (\<forall>K. Ball K L \<longrightarrow> L (\<Union>K))"

typedef%important 'a topology = "{L::('a set) \<Rightarrow> bool. istopology L}"
  morphisms "openin" "topology"
  unfolding istopology_def by blast

lemma istopology_openin[intro]: "istopology(openin U)"
  using openin[of U] by blast

lemma topology_inverse': "istopology U \<Longrightarrow> openin (topology U) = U"
  using topology_inverse[unfolded mem_Collect_eq] .

lemma topology_inverse_iff: "istopology U \<longleftrightarrow> openin (topology U) = U"
  using topology_inverse[of U] istopology_openin[of "topology U"] by auto

lemma topology_eq: "T1 = T2 \<longleftrightarrow> (\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S)"
proof
  assume "T1 = T2"
  then show "\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S" by simp
next
  assume H: "\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S"
  then have "openin T1 = openin T2" by (simp add: fun_eq_iff)
  then have "topology (openin T1) = topology (openin T2)" by simp
  then show "T1 = T2" unfolding openin_inverse .
qed


text\<open>The "universe": the union of all sets in the topology.\<close>
definition "topspace T = \<Union>{S. openin T S}"

subsubsection \<open>Main properties of open sets\<close>

proposition openin_clauses:
  fixes U :: "'a topology"
  shows
    "openin U {}"
    "\<And>S T. openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S\<inter>T)"
    "\<And>K. (\<forall>S \<in> K. openin U S) \<Longrightarrow> openin U (\<Union>K)"
  using openin[of U] unfolding istopology_def mem_Collect_eq by fast+

lemma openin_subset[intro]: "openin U S \<Longrightarrow> S \<subseteq> topspace U"
  unfolding topspace_def by blast

lemma openin_empty[simp]: "openin U {}"
  by (rule openin_clauses)

lemma openin_Int[intro]: "openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S \<inter> T)"
  by (rule openin_clauses)

lemma openin_Union[intro]: "(\<And>S. S \<in> K \<Longrightarrow> openin U S) \<Longrightarrow> openin U (\<Union>K)"
  using openin_clauses by blast

lemma openin_Un[intro]: "openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S \<union> T)"
  using openin_Union[of "{S,T}" U] by auto

lemma openin_topspace[intro, simp]: "openin U (topspace U)"
  by (force simp: openin_Union topspace_def)

lemma openin_subopen: "openin U S \<longleftrightarrow> (\<forall>x \<in> S. \<exists>T. openin U T \<and> x \<in> T \<and> T \<subseteq> S)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs by auto
next
  assume H: ?rhs
  let ?t = "\<Union>{T. openin U T \<and> T \<subseteq> S}"
  have "openin U ?t" by (force simp: openin_Union)
  also have "?t = S" using H by auto
  finally show "openin U S" .
qed

lemma openin_INT [intro]:
  assumes "finite I"
          "\<And>i. i \<in> I \<Longrightarrow> openin T (U i)"
  shows "openin T ((\<Inter>i \<in> I. U i) \<inter> topspace T)"
using assms by (induct, auto simp: inf_sup_aci(2) openin_Int)

lemma openin_INT2 [intro]:
  assumes "finite I" "I \<noteq> {}"
          "\<And>i. i \<in> I \<Longrightarrow> openin T (U i)"
  shows "openin T (\<Inter>i \<in> I. U i)"
proof -
  have "(\<Inter>i \<in> I. U i) \<subseteq> topspace T"
    using \<open>I \<noteq> {}\<close> openin_subset[OF assms(3)] by auto
  then show ?thesis
    using openin_INT[of _ _ U, OF assms(1) assms(3)] by (simp add: inf.absorb2 inf_commute)
qed

lemma openin_Inter [intro]:
  assumes "finite \<F>" "\<F> \<noteq> {}" "\<And>X. X \<in> \<F> \<Longrightarrow> openin T X" shows "openin T (\<Inter>\<F>)"
  by (metis (full_types) assms openin_INT2 image_ident)

lemma openin_Int_Inter:
  assumes "finite \<F>" "openin T U" "\<And>X. X \<in> \<F> \<Longrightarrow> openin T X" shows "openin T (U \<inter> \<Inter>\<F>)"
  using openin_Inter [of "insert U \<F>"] assms by auto


subsubsection \<open>Closed sets\<close>

definition%important "closedin U S \<longleftrightarrow> S \<subseteq> topspace U \<and> openin U (topspace U - S)"

lemma closedin_subset: "closedin U S \<Longrightarrow> S \<subseteq> topspace U"
  by (metis closedin_def)

lemma closedin_empty[simp]: "closedin U {}"
  by (simp add: closedin_def)

lemma closedin_topspace[intro, simp]: "closedin U (topspace U)"
  by (simp add: closedin_def)

lemma closedin_Un[intro]: "closedin U S \<Longrightarrow> closedin U T \<Longrightarrow> closedin U (S \<union> T)"
  by (auto simp: Diff_Un closedin_def)

lemma Diff_Inter[intro]: "A - \<Inter>S = \<Union>{A - s|s. s\<in>S}"
  by auto

lemma closedin_Union:
  assumes "finite S" "\<And>T. T \<in> S \<Longrightarrow> closedin U T"
    shows "closedin U (\<Union>S)"
  using assms by induction auto

lemma closedin_Inter[intro]:
  assumes Ke: "K \<noteq> {}"
    and Kc: "\<And>S. S \<in>K \<Longrightarrow> closedin U S"
  shows "closedin U (\<Inter>K)"
  using Ke Kc unfolding closedin_def Diff_Inter by auto

lemma closedin_INT[intro]:
  assumes "A \<noteq> {}" "\<And>x. x \<in> A \<Longrightarrow> closedin U (B x)"
  shows "closedin U (\<Inter>x\<in>A. B x)"
  apply (rule closedin_Inter)
  using assms
  apply auto
  done

lemma closedin_Int[intro]: "closedin U S \<Longrightarrow> closedin U T \<Longrightarrow> closedin U (S \<inter> T)"
  using closedin_Inter[of "{S,T}" U] by auto

lemma openin_closedin_eq: "openin U S \<longleftrightarrow> S \<subseteq> topspace U \<and> closedin U (topspace U - S)"
  apply (auto simp: closedin_def Diff_Diff_Int inf_absorb2)
  apply (metis openin_subset subset_eq)
  done

lemma openin_closedin: "S \<subseteq> topspace U \<Longrightarrow> (openin U S \<longleftrightarrow> closedin U (topspace U - S))"
  by (simp add: openin_closedin_eq)

lemma openin_diff[intro]:
  assumes oS: "openin U S"
    and cT: "closedin U T"
  shows "openin U (S - T)"
proof -
  have "S - T = S \<inter> (topspace U - T)" using openin_subset[of U S]  oS cT
    by (auto simp: topspace_def openin_subset)
  then show ?thesis using oS cT
    by (auto simp: closedin_def)
qed

lemma closedin_diff[intro]:
  assumes oS: "closedin U S"
    and cT: "openin U T"
  shows "closedin U (S - T)"
proof -
  have "S - T = S \<inter> (topspace U - T)"
    using closedin_subset[of U S] oS cT by (auto simp: topspace_def)
  then show ?thesis
    using oS cT by (auto simp: openin_closedin_eq)
qed


subsection\<open>The discrete topology\<close>

definition discrete_topology where "discrete_topology U \<equiv> topology (\<lambda>S. S \<subseteq> U)"

lemma openin_discrete_topology [simp]: "openin (discrete_topology U) S \<longleftrightarrow> S \<subseteq> U"
proof -
  have "istopology (\<lambda>S. S \<subseteq> U)"
    by (auto simp: istopology_def)
  then show ?thesis
    by (simp add: discrete_topology_def topology_inverse')
qed

lemma topspace_discrete_topology [simp]: "topspace(discrete_topology U) = U"
  by (meson openin_discrete_topology openin_subset openin_topspace order_refl subset_antisym)

lemma closedin_discrete_topology [simp]: "closedin (discrete_topology U) S \<longleftrightarrow> S \<subseteq> U"
  by (simp add: closedin_def)

lemma discrete_topology_unique:
   "discrete_topology U = X \<longleftrightarrow> topspace X = U \<and> (\<forall>x \<in> U. openin X {x})" (is "?lhs = ?rhs")
proof
  assume R: ?rhs
  then have "openin X S" if "S \<subseteq> U" for S
    using openin_subopen subsetD that by fastforce
  moreover have "x \<in> topspace X" if "openin X S" and "x \<in> S" for x S
    using openin_subset that by blast
  ultimately
  show ?lhs
    using R by (auto simp: topology_eq)
qed auto

lemma discrete_topology_unique_alt:
  "discrete_topology U = X \<longleftrightarrow> topspace X \<subseteq> U \<and> (\<forall>x \<in> U. openin X {x})"
  using openin_subset
  by (auto simp: discrete_topology_unique)

lemma subtopology_eq_discrete_topology_empty:
   "X = discrete_topology {} \<longleftrightarrow> topspace X = {}"
  using discrete_topology_unique [of "{}" X] by auto

lemma subtopology_eq_discrete_topology_sing:
   "X = discrete_topology {a} \<longleftrightarrow> topspace X = {a}"
  by (metis discrete_topology_unique openin_topspace singletonD)


subsection \<open>Subspace topology\<close>

definition%important "subtopology U V = topology (\<lambda>T. \<exists>S. T = S \<inter> V \<and> openin U S)"

lemma istopology_subtopology: "istopology (\<lambda>T. \<exists>S. T = S \<inter> V \<and> openin U S)"
  (is "istopology ?L")
proof -
  have "?L {}" by blast
  {
    fix A B
    assume A: "?L A" and B: "?L B"
    from A B obtain Sa and Sb where Sa: "openin U Sa" "A = Sa \<inter> V" and Sb: "openin U Sb" "B = Sb \<inter> V"
      by blast
    have "A \<inter> B = (Sa \<inter> Sb) \<inter> V" "openin U (Sa \<inter> Sb)"
      using Sa Sb by blast+
    then have "?L (A \<inter> B)" by blast
  }
  moreover
  {
    fix K
    assume K: "K \<subseteq> Collect ?L"
    have th0: "Collect ?L = (\<lambda>S. S \<inter> V) ` Collect (openin U)"
      by blast
    from K[unfolded th0 subset_image_iff]
    obtain Sk where Sk: "Sk \<subseteq> Collect (openin U)" "K = (\<lambda>S. S \<inter> V) ` Sk"
      by blast
    have "\<Union>K = (\<Union>Sk) \<inter> V"
      using Sk by auto
    moreover have "openin U (\<Union>Sk)"
      using Sk by (auto simp: subset_eq)
    ultimately have "?L (\<Union>K)" by blast
  }
  ultimately show ?thesis
    unfolding subset_eq mem_Collect_eq istopology_def by auto
qed

lemma openin_subtopology: "openin (subtopology U V) S \<longleftrightarrow> (\<exists>T. openin U T \<and> S = T \<inter> V)"
  unfolding subtopology_def topology_inverse'[OF istopology_subtopology]
  by auto

lemma openin_subtopology_Int:
   "openin X S \<Longrightarrow> openin (subtopology X T) (S \<inter> T)"
  using openin_subtopology by auto

lemma openin_subtopology_Int2:
   "openin X T \<Longrightarrow> openin (subtopology X S) (S \<inter> T)"
  using openin_subtopology by auto

lemma openin_subtopology_diff_closed:
   "\<lbrakk>S \<subseteq> topspace X; closedin X T\<rbrakk> \<Longrightarrow> openin (subtopology X S) (S - T)"
  unfolding closedin_def openin_subtopology
  by (rule_tac x="topspace X - T" in exI) auto

lemma openin_relative_to: "(openin X relative_to S) = openin (subtopology X S)"
  by (force simp: relative_to_def openin_subtopology)

lemma topspace_subtopology: "topspace (subtopology U V) = topspace U \<inter> V"
  by (auto simp: topspace_def openin_subtopology)

lemma closedin_subtopology: "closedin (subtopology U V) S \<longleftrightarrow> (\<exists>T. closedin U T \<and> S = T \<inter> V)"
  unfolding closedin_def topspace_subtopology
  by (auto simp: openin_subtopology)

lemma openin_subtopology_refl: "openin (subtopology U V) V \<longleftrightarrow> V \<subseteq> topspace U"
  unfolding openin_subtopology
  by auto (metis IntD1 in_mono openin_subset)

lemma subtopology_subtopology:
   "subtopology (subtopology X S) T = subtopology X (S \<inter> T)"
proof -
  have eq: "\<And>T'. (\<exists>S'. T' = S' \<inter> T \<and> (\<exists>T. openin X T \<and> S' = T \<inter> S)) = (\<exists>Sa. T' = Sa \<inter> (S \<inter> T) \<and> openin X Sa)"
    by (metis inf_assoc)
  have "subtopology (subtopology X S) T = topology (\<lambda>Ta. \<exists>Sa. Ta = Sa \<inter> T \<and> openin (subtopology X S) Sa)"
    by (simp add: subtopology_def)
  also have "\<dots> = subtopology X (S \<inter> T)"
    by (simp add: openin_subtopology eq) (simp add: subtopology_def)
  finally show ?thesis .
qed

lemma openin_subtopology_alt:
     "openin (subtopology X U) S \<longleftrightarrow> S \<in> (\<lambda>T. U \<inter> T) ` Collect (openin X)"
  by (simp add: image_iff inf_commute openin_subtopology)

lemma closedin_subtopology_alt:
     "closedin (subtopology X U) S \<longleftrightarrow> S \<in> (\<lambda>T. U \<inter> T) ` Collect (closedin X)"
  by (simp add: image_iff inf_commute closedin_subtopology)

lemma subtopology_superset:
  assumes UV: "topspace U \<subseteq> V"
  shows "subtopology U V = U"
proof -
  {
    fix S
    {
      fix T
      assume T: "openin U T" "S = T \<inter> V"
      from T openin_subset[OF T(1)] UV have eq: "S = T"
        by blast
      have "openin U S"
        unfolding eq using T by blast
    }
    moreover
    {
      assume S: "openin U S"
      then have "\<exists>T. openin U T \<and> S = T \<inter> V"
        using openin_subset[OF S] UV by auto
    }
    ultimately have "(\<exists>T. openin U T \<and> S = T \<inter> V) \<longleftrightarrow> openin U S"
      by blast
  }
  then show ?thesis
    unfolding topology_eq openin_subtopology by blast
qed

lemma subtopology_topspace[simp]: "subtopology U (topspace U) = U"
  by (simp add: subtopology_superset)

lemma subtopology_UNIV[simp]: "subtopology U UNIV = U"
  by (simp add: subtopology_superset)

lemma openin_subtopology_empty:
   "openin (subtopology U {}) S \<longleftrightarrow> S = {}"
by (metis Int_empty_right openin_empty openin_subtopology)

lemma closedin_subtopology_empty:
   "closedin (subtopology U {}) S \<longleftrightarrow> S = {}"
by (metis Int_empty_right closedin_empty closedin_subtopology)

lemma closedin_subtopology_refl [simp]:
   "closedin (subtopology U X) X \<longleftrightarrow> X \<subseteq> topspace U"
by (metis closedin_def closedin_topspace inf.absorb_iff2 le_inf_iff topspace_subtopology)

lemma closedin_topspace_empty: "topspace T = {} \<Longrightarrow> (closedin T S \<longleftrightarrow> S = {})"
  by (simp add: closedin_def)

lemma openin_imp_subset:
   "openin (subtopology U S) T \<Longrightarrow> T \<subseteq> S"
by (metis Int_iff openin_subtopology subsetI)

lemma closedin_imp_subset:
   "closedin (subtopology U S) T \<Longrightarrow> T \<subseteq> S"
by (simp add: closedin_def topspace_subtopology)

lemma openin_open_subtopology:
     "openin X S \<Longrightarrow> openin (subtopology X S) T \<longleftrightarrow> openin X T \<and> T \<subseteq> S"
  by (metis inf.orderE openin_Int openin_imp_subset openin_subtopology)

lemma closedin_closed_subtopology:
     "closedin X S \<Longrightarrow> (closedin (subtopology X S) T \<longleftrightarrow> closedin X T \<and> T \<subseteq> S)"
  by (metis closedin_Int closedin_imp_subset closedin_subtopology inf.orderE)

lemma openin_subtopology_Un:
    "\<lbrakk>openin (subtopology X T) S; openin (subtopology X U) S\<rbrakk>
     \<Longrightarrow> openin (subtopology X (T \<union> U)) S"
by (simp add: openin_subtopology) blast

lemma closedin_subtopology_Un:
    "\<lbrakk>closedin (subtopology X T) S; closedin (subtopology X U) S\<rbrakk>
     \<Longrightarrow> closedin (subtopology X (T \<union> U)) S"
by (simp add: closedin_subtopology) blast


subsection \<open>The standard Euclidean topology\<close>

definition%important euclidean :: "'a::topological_space topology"
  where "euclidean = topology open"

lemma open_openin: "open S \<longleftrightarrow> openin euclidean S"
  unfolding euclidean_def
  apply (rule cong[where x=S and y=S])
  apply (rule topology_inverse[symmetric])
  apply (auto simp: istopology_def)
  done

declare open_openin [symmetric, simp]

lemma topspace_euclidean [simp]: "topspace euclidean = UNIV"
  by (force simp: topspace_def)

lemma topspace_euclidean_subtopology[simp]: "topspace (subtopology euclidean S) = S"
  by (simp add: topspace_subtopology)

lemma closed_closedin: "closed S \<longleftrightarrow> closedin euclidean S"
  by (simp add: closed_def closedin_def Compl_eq_Diff_UNIV)

declare closed_closedin [symmetric, simp]

lemma open_subopen: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>T. open T \<and> x \<in> T \<and> T \<subseteq> S)"
  using openI by auto

lemma openin_subtopology_self [simp]: "openin (subtopology euclidean S) S"
  by (metis openin_topspace topspace_euclidean_subtopology)

subsubsection\<open>The most basic facts about the usual topology and metric on R\<close>

abbreviation euclideanreal :: "real topology"
  where "euclideanreal \<equiv> topology open"

lemma real_openin [simp]: "openin euclideanreal S = open S"
  by (simp add: euclidean_def open_openin)

lemma topspace_euclideanreal [simp]: "topspace euclideanreal = UNIV"
  using openin_subset open_UNIV real_openin by blast

lemma topspace_euclideanreal_subtopology [simp]:
   "topspace (subtopology euclideanreal S) = S"
  by (simp add: topspace_subtopology)

lemma real_closedin [simp]: "closedin euclideanreal S = closed S"
  by (simp add: closed_closedin euclidean_def)

subsection \<open>Basic "localization" results are handy for connectedness.\<close>

lemma openin_open: "openin (subtopology euclidean U) S \<longleftrightarrow> (\<exists>T. open T \<and> (S = U \<inter> T))"
  by (auto simp: openin_subtopology)

lemma openin_Int_open:
   "\<lbrakk>openin (subtopology euclidean U) S; open T\<rbrakk>
        \<Longrightarrow> openin (subtopology euclidean U) (S \<inter> T)"
by (metis open_Int Int_assoc openin_open)

lemma openin_open_Int[intro]: "open S \<Longrightarrow> openin (subtopology euclidean U) (U \<inter> S)"
  by (auto simp: openin_open)

lemma open_openin_trans[trans]:
  "open S \<Longrightarrow> open T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> openin (subtopology euclidean S) T"
  by (metis Int_absorb1  openin_open_Int)

lemma open_subset: "S \<subseteq> T \<Longrightarrow> open S \<Longrightarrow> openin (subtopology euclidean T) S"
  by (auto simp: openin_open)

lemma closedin_closed: "closedin (subtopology euclidean U) S \<longleftrightarrow> (\<exists>T. closed T \<and> S = U \<inter> T)"
  by (simp add: closedin_subtopology Int_ac)

lemma closedin_closed_Int: "closed S \<Longrightarrow> closedin (subtopology euclidean U) (U \<inter> S)"
  by (metis closedin_closed)

lemma closed_subset: "S \<subseteq> T \<Longrightarrow> closed S \<Longrightarrow> closedin (subtopology euclidean T) S"
  by (auto simp: closedin_closed)

lemma closedin_closed_subset:
 "\<lbrakk>closedin (subtopology euclidean U) V; T \<subseteq> U; S = V \<inter> T\<rbrakk>
             \<Longrightarrow> closedin (subtopology euclidean T) S"
  by (metis (no_types, lifting) Int_assoc Int_commute closedin_closed inf.orderE)

lemma finite_imp_closedin:
  fixes S :: "'a::t1_space set"
  shows "\<lbrakk>finite S; S \<subseteq> T\<rbrakk> \<Longrightarrow> closedin (subtopology euclidean T) S"
    by (simp add: finite_imp_closed closed_subset)

lemma closedin_singleton [simp]:
  fixes a :: "'a::t1_space"
  shows "closedin (subtopology euclidean U) {a} \<longleftrightarrow> a \<in> U"
using closedin_subset  by (force intro: closed_subset)

lemma openin_euclidean_subtopology_iff:
  fixes S U :: "'a::metric_space set"
  shows "openin (subtopology euclidean U) S \<longleftrightarrow>
    S \<subseteq> U \<and> (\<forall>x\<in>S. \<exists>e>0. \<forall>x'\<in>U. dist x' x < e \<longrightarrow> x'\<in> S)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding openin_open open_dist by blast
next
  define T where "T = {x. \<exists>a\<in>S. \<exists>d>0. (\<forall>y\<in>U. dist y a < d \<longrightarrow> y \<in> S) \<and> dist x a < d}"
  have 1: "\<forall>x\<in>T. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> T"
    unfolding T_def
    apply clarsimp
    apply (rule_tac x="d - dist x a" in exI)
    apply (clarsimp simp add: less_diff_eq)
    by (metis dist_commute dist_triangle_lt)
  assume ?rhs then have 2: "S = U \<inter> T"
    unfolding T_def
    by auto (metis dist_self)
  from 1 2 show ?lhs
    unfolding openin_open open_dist by fast
qed

lemma connected_openin:
      "connected S \<longleftrightarrow>
       \<not>(\<exists>E1 E2. openin (subtopology euclidean S) E1 \<and>
                 openin (subtopology euclidean S) E2 \<and>
                 S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"
  apply (simp add: connected_def openin_open disjoint_iff_not_equal, safe)
  apply (simp_all, blast+)  (* SLOW *)
  done

lemma connected_openin_eq:
      "connected S \<longleftrightarrow>
       \<not>(\<exists>E1 E2. openin (subtopology euclidean S) E1 \<and>
                 openin (subtopology euclidean S) E2 \<and>
                 E1 \<union> E2 = S \<and> E1 \<inter> E2 = {} \<and>
                 E1 \<noteq> {} \<and> E2 \<noteq> {})"
  apply (simp add: connected_openin, safe, blast)
  by (metis Int_lower1 Un_subset_iff openin_open subset_antisym)

lemma connected_closedin:
      "connected S \<longleftrightarrow>
       (\<nexists>E1 E2.
        closedin (subtopology euclidean S) E1 \<and>
        closedin (subtopology euclidean S) E2 \<and>
        S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"
       (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs 
    by (auto simp add: connected_closed closedin_closed)
next
  assume R: ?rhs
  then show ?lhs 
  proof (clarsimp simp add: connected_closed closedin_closed)
    fix A B 
    assume s_sub: "S \<subseteq> A \<union> B" "B \<inter> S \<noteq> {}"
      and disj: "A \<inter> B \<inter> S = {}"
      and cl: "closed A" "closed B"
    have "S \<inter> (A \<union> B) = S"
      using s_sub(1) by auto
    have "S - A = B \<inter> S"
      using Diff_subset_conv Un_Diff_Int disj s_sub(1) by auto
    then have "S \<inter> A = {}"
      by (metis Diff_Diff_Int Diff_disjoint Un_Diff_Int R cl closedin_closed_Int inf_commute order_refl s_sub(2))
    then show "A \<inter> S = {}"
      by blast
  qed
qed

lemma connected_closedin_eq:
      "connected S \<longleftrightarrow>
           \<not>(\<exists>E1 E2.
                 closedin (subtopology euclidean S) E1 \<and>
                 closedin (subtopology euclidean S) E2 \<and>
                 E1 \<union> E2 = S \<and> E1 \<inter> E2 = {} \<and>
                 E1 \<noteq> {} \<and> E2 \<noteq> {})"
  apply (simp add: connected_closedin, safe, blast)
  by (metis Int_lower1 Un_subset_iff closedin_closed subset_antisym)

text \<open>These "transitivity" results are handy too\<close>

lemma openin_trans[trans]:
  "openin (subtopology euclidean T) S \<Longrightarrow> openin (subtopology euclidean U) T \<Longrightarrow>
    openin (subtopology euclidean U) S"
  unfolding open_openin openin_open by blast

lemma openin_open_trans: "openin (subtopology euclidean T) S \<Longrightarrow> open T \<Longrightarrow> open S"
  by (auto simp: openin_open intro: openin_trans)

lemma closedin_trans[trans]:
  "closedin (subtopology euclidean T) S \<Longrightarrow> closedin (subtopology euclidean U) T \<Longrightarrow>
    closedin (subtopology euclidean U) S"
  by (auto simp: closedin_closed closed_Inter Int_assoc)

lemma closedin_closed_trans: "closedin (subtopology euclidean T) S \<Longrightarrow> closed T \<Longrightarrow> closed S"
  by (auto simp: closedin_closed intro: closedin_trans)

lemma openin_subtopology_Int_subset:
   "\<lbrakk>openin (subtopology euclidean u) (u \<inter> S); v \<subseteq> u\<rbrakk> \<Longrightarrow> openin (subtopology euclidean v) (v \<inter> S)"
  by (auto simp: openin_subtopology)

lemma openin_open_eq: "open s \<Longrightarrow> (openin (subtopology euclidean s) t \<longleftrightarrow> open t \<and> t \<subseteq> s)"
  using open_subset openin_open_trans openin_subset by fastforce


subsection \<open>Open and closed balls\<close>

definition%important ball :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set"
  where "ball x e = {y. dist x y < e}"

definition%important cball :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set"
  where "cball x e = {y. dist x y \<le> e}"

definition%important sphere :: "'a::metric_space \<Rightarrow> real \<Rightarrow> 'a set"
  where "sphere x e = {y. dist x y = e}"

lemma mem_ball [simp]: "y \<in> ball x e \<longleftrightarrow> dist x y < e"
  by (simp add: ball_def)

lemma mem_cball [simp]: "y \<in> cball x e \<longleftrightarrow> dist x y \<le> e"
  by (simp add: cball_def)

lemma mem_sphere [simp]: "y \<in> sphere x e \<longleftrightarrow> dist x y = e"
  by (simp add: sphere_def)

lemma ball_trivial [simp]: "ball x 0 = {}"
  by (simp add: ball_def)

lemma cball_trivial [simp]: "cball x 0 = {x}"
  by (simp add: cball_def)

lemma sphere_trivial [simp]: "sphere x 0 = {x}"
  by (simp add: sphere_def)

lemma mem_ball_0 [simp]: "x \<in> ball 0 e \<longleftrightarrow> norm x < e"
  for x :: "'a::real_normed_vector"
  by (simp add: dist_norm)

lemma mem_cball_0 [simp]: "x \<in> cball 0 e \<longleftrightarrow> norm x \<le> e"
  for x :: "'a::real_normed_vector"
  by (simp add: dist_norm)

lemma disjoint_ballI: "dist x y \<ge> r+s \<Longrightarrow> ball x r \<inter> ball y s = {}"
  using dist_triangle_less_add not_le by fastforce

lemma disjoint_cballI: "dist x y > r + s \<Longrightarrow> cball x r \<inter> cball y s = {}"
  by (metis add_mono disjoint_iff_not_equal dist_triangle2 dual_order.trans leD mem_cball)

lemma mem_sphere_0 [simp]: "x \<in> sphere 0 e \<longleftrightarrow> norm x = e"
  for x :: "'a::real_normed_vector"
  by (simp add: dist_norm)

lemma sphere_empty [simp]: "r < 0 \<Longrightarrow> sphere a r = {}"
  for a :: "'a::metric_space"
  by auto

lemma centre_in_ball [simp]: "x \<in> ball x e \<longleftrightarrow> 0 < e"
  by simp

lemma centre_in_cball [simp]: "x \<in> cball x e \<longleftrightarrow> 0 \<le> e"
  by simp

lemma ball_subset_cball [simp, intro]: "ball x e \<subseteq> cball x e"
  by (simp add: subset_eq)

lemma mem_ball_imp_mem_cball: "x \<in> ball y e \<Longrightarrow> x \<in> cball y e"
  by (auto simp: mem_ball mem_cball)

lemma sphere_cball [simp,intro]: "sphere z r \<subseteq> cball z r"
  by force

lemma cball_diff_sphere: "cball a r - sphere a r = ball a r"
  by auto

lemma subset_ball[intro]: "d \<le> e \<Longrightarrow> ball x d \<subseteq> ball x e"
  by (simp add: subset_eq)

lemma subset_cball[intro]: "d \<le> e \<Longrightarrow> cball x d \<subseteq> cball x e"
  by (simp add: subset_eq)

lemma mem_ball_leI: "x \<in> ball y e \<Longrightarrow> e \<le> f \<Longrightarrow> x \<in> ball y f"
  by (auto simp: mem_ball mem_cball)

lemma mem_cball_leI: "x \<in> cball y e \<Longrightarrow> e \<le> f \<Longrightarrow> x \<in> cball y f"
  by (auto simp: mem_ball mem_cball)

lemma cball_trans: "y \<in> cball z b \<Longrightarrow> x \<in> cball y a \<Longrightarrow> x \<in> cball z (b + a)"
  unfolding mem_cball
proof -
  have "dist z x \<le> dist z y + dist y x"
    by (rule dist_triangle)
  also assume "dist z y \<le> b"
  also assume "dist y x \<le> a"
  finally show "dist z x \<le> b + a" by arith
qed

lemma ball_max_Un: "ball a (max r s) = ball a r \<union> ball a s"
  by (simp add: set_eq_iff) arith

lemma ball_min_Int: "ball a (min r s) = ball a r \<inter> ball a s"
  by (simp add: set_eq_iff)

lemma cball_max_Un: "cball a (max r s) = cball a r \<union> cball a s"
  by (simp add: set_eq_iff) arith

lemma cball_min_Int: "cball a (min r s) = cball a r \<inter> cball a s"
  by (simp add: set_eq_iff)

lemma cball_diff_eq_sphere: "cball a r - ball a r =  sphere a r"
  by (auto simp: cball_def ball_def dist_commute)

lemma image_add_ball [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "(+) b ` ball a r = ball (a+b) r"
apply (intro equalityI subsetI)
apply (force simp: dist_norm)
apply (rule_tac x="x-b" in image_eqI)
apply (auto simp: dist_norm algebra_simps)
done

lemma image_add_cball [simp]:
  fixes a :: "'a::real_normed_vector"
  shows "(+) b ` cball a r = cball (a+b) r"
apply (intro equalityI subsetI)
apply (force simp: dist_norm)
apply (rule_tac x="x-b" in image_eqI)
apply (auto simp: dist_norm algebra_simps)
done

lemma open_ball [intro, simp]: "open (ball x e)"
proof -
  have "open (dist x -` {..<e})"
    by (intro open_vimage open_lessThan continuous_intros)
  also have "dist x -` {..<e} = ball x e"
    by auto
  finally show ?thesis .
qed

lemma open_contains_ball: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. ball x e \<subseteq> S)"
  by (simp add: open_dist subset_eq mem_ball Ball_def dist_commute)

lemma openI [intro?]: "(\<And>x. x\<in>S \<Longrightarrow> \<exists>e>0. ball x e \<subseteq> S) \<Longrightarrow> open S"
  by (auto simp: open_contains_ball)

lemma openE[elim?]:
  assumes "open S" "x\<in>S"
  obtains e where "e>0" "ball x e \<subseteq> S"
  using assms unfolding open_contains_ball by auto

lemma open_contains_ball_eq: "open S \<Longrightarrow> x\<in>S \<longleftrightarrow> (\<exists>e>0. ball x e \<subseteq> S)"
  by (metis open_contains_ball subset_eq centre_in_ball)

lemma openin_contains_ball:
    "openin (subtopology euclidean t) s \<longleftrightarrow>
     s \<subseteq> t \<and> (\<forall>x \<in> s. \<exists>e. 0 < e \<and> ball x e \<inter> t \<subseteq> s)"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (simp add: openin_open)
    apply (metis Int_commute Int_mono inf.cobounded2 open_contains_ball order_refl subsetCE)
    done
next
  assume ?rhs
  then show ?lhs
    apply (simp add: openin_euclidean_subtopology_iff)
    by (metis (no_types) Int_iff dist_commute inf.absorb_iff2 mem_ball)
qed

lemma openin_contains_cball:
   "openin (subtopology euclidean t) s \<longleftrightarrow>
        s \<subseteq> t \<and>
        (\<forall>x \<in> s. \<exists>e. 0 < e \<and> cball x e \<inter> t \<subseteq> s)"
apply (simp add: openin_contains_ball)
apply (rule iffI)
apply (auto dest!: bspec)
apply (rule_tac x="e/2" in exI, force+)
done

lemma ball_eq_empty[simp]: "ball x e = {} \<longleftrightarrow> e \<le> 0"
  unfolding mem_ball set_eq_iff
  apply (simp add: not_less)
  apply (metis zero_le_dist order_trans dist_self)
  done

lemma ball_empty: "e \<le> 0 \<Longrightarrow> ball x e = {}" by simp

lemma closed_cball [iff]: "closed (cball x e)"
proof -
  have "closed (dist x -` {..e})"
    by (intro closed_vimage closed_atMost continuous_intros)
  also have "dist x -` {..e} = cball x e"
    by auto
  finally show ?thesis .
qed

lemma open_contains_cball: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0.  cball x e \<subseteq> S)"
proof -
  {
    fix x and e::real
    assume "x\<in>S" "e>0" "ball x e \<subseteq> S"
    then have "\<exists>d>0. cball x d \<subseteq> S" unfolding subset_eq by (rule_tac x="e/2" in exI, auto)
  }
  moreover
  {
    fix x and e::real
    assume "x\<in>S" "e>0" "cball x e \<subseteq> S"
    then have "\<exists>d>0. ball x d \<subseteq> S"
      unfolding subset_eq
      apply (rule_tac x="e/2" in exI, auto)
      done
  }
  ultimately show ?thesis
    unfolding open_contains_ball by auto
qed

lemma open_contains_cball_eq: "open S \<Longrightarrow> (\<forall>x. x \<in> S \<longleftrightarrow> (\<exists>e>0. cball x e \<subseteq> S))"
  by (metis open_contains_cball subset_eq order_less_imp_le centre_in_cball)

lemma eventually_nhds_ball: "d > 0 \<Longrightarrow> eventually (\<lambda>x. x \<in> ball z d) (nhds z)"
  by (rule eventually_nhds_in_open) simp_all

lemma eventually_at_ball: "d > 0 \<Longrightarrow> eventually (\<lambda>t. t \<in> ball z d \<and> t \<in> A) (at z within A)"
  unfolding eventually_at by (intro exI[of _ d]) (simp_all add: dist_commute)

lemma eventually_at_ball': "d > 0 \<Longrightarrow> eventually (\<lambda>t. t \<in> ball z d \<and> t \<noteq> z \<and> t \<in> A) (at z within A)"
  unfolding eventually_at by (intro exI[of _ d]) (simp_all add: dist_commute)

lemma at_within_ball: "e > 0 \<Longrightarrow> dist x y < e \<Longrightarrow> at y within ball x e = at y"
  by (subst at_within_open) auto

lemma atLeastAtMost_eq_cball:
  fixes a b::real
  shows "{a .. b} = cball ((a + b)/2) ((b - a)/2)"
  by (auto simp: dist_real_def field_simps mem_cball)

lemma greaterThanLessThan_eq_ball:
  fixes a b::real
  shows "{a <..< b} = ball ((a + b)/2) ((b - a)/2)"
  by (auto simp: dist_real_def field_simps mem_ball)


subsection \<open>Limit points\<close>

definition%important (in topological_space) islimpt:: "'a \<Rightarrow> 'a set \<Rightarrow> bool"  (infixr "islimpt" 60)
  where "x islimpt S \<longleftrightarrow> (\<forall>T. x\<in>T \<longrightarrow> open T \<longrightarrow> (\<exists>y\<in>S. y\<in>T \<and> y\<noteq>x))"

lemma islimptI:
  assumes "\<And>T. x \<in> T \<Longrightarrow> open T \<Longrightarrow> \<exists>y\<in>S. y \<in> T \<and> y \<noteq> x"
  shows "x islimpt S"
  using assms unfolding islimpt_def by auto

lemma islimptE:
  assumes "x islimpt S" and "x \<in> T" and "open T"
  obtains y where "y \<in> S" and "y \<in> T" and "y \<noteq> x"
  using assms unfolding islimpt_def by auto

lemma islimpt_iff_eventually: "x islimpt S \<longleftrightarrow> \<not> eventually (\<lambda>y. y \<notin> S) (at x)"
  unfolding islimpt_def eventually_at_topological by auto

lemma islimpt_subset: "x islimpt S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> x islimpt T"
  unfolding islimpt_def by fast

lemma islimpt_approachable:
  fixes x :: "'a::metric_space"
  shows "x islimpt S \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e)"
  unfolding islimpt_iff_eventually eventually_at by fast

lemma islimpt_approachable_le: "x islimpt S \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in> S. x' \<noteq> x \<and> dist x' x \<le> e)"
  for x :: "'a::metric_space"
  unfolding islimpt_approachable
  using approachable_lt_le [where f="\<lambda>y. dist y x" and P="\<lambda>y. y \<notin> S \<or> y = x",
    THEN arg_cong [where f=Not]]
  by (simp add: Bex_def conj_commute conj_left_commute)

lemma islimpt_UNIV_iff: "x islimpt UNIV \<longleftrightarrow> \<not> open {x}"
  unfolding islimpt_def by (safe, fast, case_tac "T = {x}", fast, fast)

lemma islimpt_punctured: "x islimpt S = x islimpt (S-{x})"
  unfolding islimpt_def by blast

text \<open>A perfect space has no isolated points.\<close>

lemma islimpt_UNIV [simp, intro]: "x islimpt UNIV"
  for x :: "'a::perfect_space"
  unfolding islimpt_UNIV_iff by (rule not_open_singleton)

lemma perfect_choose_dist: "0 < r \<Longrightarrow> \<exists>a. a \<noteq> x \<and> dist a x < r"
  for x :: "'a::{perfect_space,metric_space}"
  using islimpt_UNIV [of x] by (simp add: islimpt_approachable)

lemma closed_limpt: "closed S \<longleftrightarrow> (\<forall>x. x islimpt S \<longrightarrow> x \<in> S)"
  unfolding closed_def
  apply (subst open_subopen)
  apply (simp add: islimpt_def subset_eq)
  apply (metis ComplE ComplI)
  done

lemma islimpt_EMPTY[simp]: "\<not> x islimpt {}"
  by (auto simp: islimpt_def)

lemma finite_ball_include:
  fixes a :: "'a::metric_space"
  assumes "finite S" 
  shows "\<exists>e>0. S \<subseteq> ball a e"
  using assms
proof induction
  case (insert x S)
  then obtain e0 where "e0>0" and e0:"S \<subseteq> ball a e0" by auto
  define e where "e = max e0 (2 * dist a x)"
  have "e>0" unfolding e_def using \<open>e0>0\<close> by auto
  moreover have "insert x S \<subseteq> ball a e"
    using e0 \<open>e>0\<close> unfolding e_def by auto
  ultimately show ?case by auto
qed (auto intro: zero_less_one)

lemma finite_set_avoid:
  fixes a :: "'a::metric_space"
  assumes "finite S"
  shows "\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<longrightarrow> d \<le> dist a x"
  using assms
proof induction
  case (insert x S)
  then obtain d where "d > 0" and d: "\<forall>x\<in>S. x \<noteq> a \<longrightarrow> d \<le> dist a x"
    by blast
  show ?case
  proof (cases "x = a")
    case True
    with \<open>d > 0 \<close>d show ?thesis by auto
  next
    case False
    let ?d = "min d (dist a x)"
    from False \<open>d > 0\<close> have dp: "?d > 0"
      by auto
    from d have d': "\<forall>x\<in>S. x \<noteq> a \<longrightarrow> ?d \<le> dist a x"
      by auto
    with dp False show ?thesis
      by (metis insert_iff le_less min_less_iff_conj not_less)
  qed
qed (auto intro: zero_less_one)

lemma islimpt_Un: "x islimpt (S \<union> T) \<longleftrightarrow> x islimpt S \<or> x islimpt T"
  by (simp add: islimpt_iff_eventually eventually_conj_iff)

lemma discrete_imp_closed:
  fixes S :: "'a::metric_space set"
  assumes e: "0 < e"
    and d: "\<forall>x \<in> S. \<forall>y \<in> S. dist y x < e \<longrightarrow> y = x"
  shows "closed S"
proof -
  have False if C: "\<And>e. e>0 \<Longrightarrow> \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e" for x
  proof -
    from e have e2: "e/2 > 0" by arith
    from C[rule_format, OF e2] obtain y where y: "y \<in> S" "y \<noteq> x" "dist y x < e/2"
      by blast
    let ?m = "min (e/2) (dist x y) "
    from e2 y(2) have mp: "?m > 0"
      by simp
    from C[OF mp] obtain z where z: "z \<in> S" "z \<noteq> x" "dist z x < ?m"
      by blast
    from z y have "dist z y < e"
      by (intro dist_triangle_lt [where z=x]) simp
    from d[rule_format, OF y(1) z(1) this] y z show ?thesis
      by (auto simp: dist_commute)
  qed
  then show ?thesis
    by (metis islimpt_approachable closed_limpt [where 'a='a])
qed

lemma closed_of_nat_image: "closed (of_nat ` A :: 'a::real_normed_algebra_1 set)"
  by (rule discrete_imp_closed[of 1]) (auto simp: dist_of_nat)

lemma closed_of_int_image: "closed (of_int ` A :: 'a::real_normed_algebra_1 set)"
  by (rule discrete_imp_closed[of 1]) (auto simp: dist_of_int)

lemma closed_Nats [simp]: "closed (\<nat> :: 'a :: real_normed_algebra_1 set)"
  unfolding Nats_def by (rule closed_of_nat_image)

lemma closed_Ints [simp]: "closed (\<int> :: 'a :: real_normed_algebra_1 set)"
  unfolding Ints_def by (rule closed_of_int_image)

lemma closed_subset_Ints:
  fixes A :: "'a :: real_normed_algebra_1 set"
  assumes "A \<subseteq> \<int>"
  shows   "closed A"
proof (intro discrete_imp_closed[OF zero_less_one] ballI impI, goal_cases)
  case (1 x y)
  with assms have "x \<in> \<int>" and "y \<in> \<int>" by auto
  with \<open>dist y x < 1\<close> show "y = x"
    by (auto elim!: Ints_cases simp: dist_of_int)
qed


subsection \<open>Interior of a Set\<close>

definition%important "interior S = \<Union>{T. open T \<and> T \<subseteq> S}"

lemma interiorI [intro?]:
  assumes "open T" and "x \<in> T" and "T \<subseteq> S"
  shows "x \<in> interior S"
  using assms unfolding interior_def by fast

lemma interiorE [elim?]:
  assumes "x \<in> interior S"
  obtains T where "open T" and "x \<in> T" and "T \<subseteq> S"
  using assms unfolding interior_def by fast

lemma open_interior [simp, intro]: "open (interior S)"
  by (simp add: interior_def open_Union)

lemma interior_subset: "interior S \<subseteq> S"
  by (auto simp: interior_def)

lemma interior_maximal: "T \<subseteq> S \<Longrightarrow> open T \<Longrightarrow> T \<subseteq> interior S"
  by (auto simp: interior_def)

lemma interior_open: "open S \<Longrightarrow> interior S = S"
  by (intro equalityI interior_subset interior_maximal subset_refl)

lemma interior_eq: "interior S = S \<longleftrightarrow> open S"
  by (metis open_interior interior_open)

lemma open_subset_interior: "open S \<Longrightarrow> S \<subseteq> interior T \<longleftrightarrow> S \<subseteq> T"
  by (metis interior_maximal interior_subset subset_trans)

lemma interior_empty [simp]: "interior {} = {}"
  using open_empty by (rule interior_open)

lemma interior_UNIV [simp]: "interior UNIV = UNIV"
  using open_UNIV by (rule interior_open)

lemma interior_interior [simp]: "interior (interior S) = interior S"
  using open_interior by (rule interior_open)

lemma interior_mono: "S \<subseteq> T \<Longrightarrow> interior S \<subseteq> interior T"
  by (auto simp: interior_def)

lemma interior_unique:
  assumes "T \<subseteq> S" and "open T"
  assumes "\<And>T'. T' \<subseteq> S \<Longrightarrow> open T' \<Longrightarrow> T' \<subseteq> T"
  shows "interior S = T"
  by (intro equalityI assms interior_subset open_interior interior_maximal)

lemma interior_singleton [simp]: "interior {a} = {}"
  for a :: "'a::perfect_space"
  apply (rule interior_unique, simp_all)
  using not_open_singleton subset_singletonD
  apply fastforce
  done

lemma interior_Int [simp]: "interior (S \<inter> T) = interior S \<inter> interior T"
  by (intro equalityI Int_mono Int_greatest interior_mono Int_lower1
    Int_lower2 interior_maximal interior_subset open_Int open_interior)

lemma mem_interior: "x \<in> interior S \<longleftrightarrow> (\<exists>e>0. ball x e \<subseteq> S)"
  using open_contains_ball_eq [where S="interior S"]
  by (simp add: open_subset_interior)

lemma eventually_nhds_in_nhd: "x \<in> interior s \<Longrightarrow> eventually (\<lambda>y. y \<in> s) (nhds x)"
  using interior_subset[of s] by (subst eventually_nhds) blast

lemma interior_limit_point [intro]:
  fixes x :: "'a::perfect_space"
  assumes x: "x \<in> interior S"
  shows "x islimpt S"
  using x islimpt_UNIV [of x]
  unfolding interior_def islimpt_def
  apply (clarsimp, rename_tac T T')
  apply (drule_tac x="T \<inter> T'" in spec)
  apply (auto simp: open_Int)
  done

lemma interior_closed_Un_empty_interior:
  assumes cS: "closed S"
    and iT: "interior T = {}"
  shows "interior (S \<union> T) = interior S"
proof
  show "interior S \<subseteq> interior (S \<union> T)"
    by (rule interior_mono) (rule Un_upper1)
  show "interior (S \<union> T) \<subseteq> interior S"
  proof
    fix x
    assume "x \<in> interior (S \<union> T)"
    then obtain R where "open R" "x \<in> R" "R \<subseteq> S \<union> T" ..
    show "x \<in> interior S"
    proof (rule ccontr)
      assume "x \<notin> interior S"
      with \<open>x \<in> R\<close> \<open>open R\<close> obtain y where "y \<in> R - S"
        unfolding interior_def by fast
      from \<open>open R\<close> \<open>closed S\<close> have "open (R - S)"
        by (rule open_Diff)
      from \<open>R \<subseteq> S \<union> T\<close> have "R - S \<subseteq> T"
        by fast
      from \<open>y \<in> R - S\<close> \<open>open (R - S)\<close> \<open>R - S \<subseteq> T\<close> \<open>interior T = {}\<close> show False
        unfolding interior_def by fast
    qed
  qed
qed

lemma interior_Times: "interior (A \<times> B) = interior A \<times> interior B"
proof (rule interior_unique)
  show "interior A \<times> interior B \<subseteq> A \<times> B"
    by (intro Sigma_mono interior_subset)
  show "open (interior A \<times> interior B)"
    by (intro open_Times open_interior)
  fix T
  assume "T \<subseteq> A \<times> B" and "open T"
  then show "T \<subseteq> interior A \<times> interior B"
  proof safe
    fix x y
    assume "(x, y) \<in> T"
    then obtain C D where "open C" "open D" "C \<times> D \<subseteq> T" "x \<in> C" "y \<in> D"
      using \<open>open T\<close> unfolding open_prod_def by fast
    then have "open C" "open D" "C \<subseteq> A" "D \<subseteq> B" "x \<in> C" "y \<in> D"
      using \<open>T \<subseteq> A \<times> B\<close> by auto
    then show "x \<in> interior A" and "y \<in> interior B"
      by (auto intro: interiorI)
  qed
qed

lemma interior_Ici:
  fixes x :: "'a :: {dense_linorder,linorder_topology}"
  assumes "b < x"
  shows "interior {x ..} = {x <..}"
proof (rule interior_unique)
  fix T
  assume "T \<subseteq> {x ..}" "open T"
  moreover have "x \<notin> T"
  proof
    assume "x \<in> T"
    obtain y where "y < x" "{y <.. x} \<subseteq> T"
      using open_left[OF \<open>open T\<close> \<open>x \<in> T\<close> \<open>b < x\<close>] by auto
    with dense[OF \<open>y < x\<close>] obtain z where "z \<in> T" "z < x"
      by (auto simp: subset_eq Ball_def)
    with \<open>T \<subseteq> {x ..}\<close> show False by auto
  qed
  ultimately show "T \<subseteq> {x <..}"
    by (auto simp: subset_eq less_le)
qed auto

lemma interior_Iic:
  fixes x :: "'a ::{dense_linorder,linorder_topology}"
  assumes "x < b"
  shows "interior {.. x} = {..< x}"
proof (rule interior_unique)
  fix T
  assume "T \<subseteq> {.. x}" "open T"
  moreover have "x \<notin> T"
  proof
    assume "x \<in> T"
    obtain y where "x < y" "{x ..< y} \<subseteq> T"
      using open_right[OF \<open>open T\<close> \<open>x \<in> T\<close> \<open>x < b\<close>] by auto
    with dense[OF \<open>x < y\<close>] obtain z where "z \<in> T" "x < z"
      by (auto simp: subset_eq Ball_def less_le)
    with \<open>T \<subseteq> {.. x}\<close> show False by auto
  qed
  ultimately show "T \<subseteq> {..< x}"
    by (auto simp: subset_eq less_le)
qed auto


subsection \<open>Closure of a Set\<close>

definition%important "closure S = S \<union> {x | x. x islimpt S}"

lemma interior_closure: "interior S = - (closure (- S))"
  by (auto simp: interior_def closure_def islimpt_def)

lemma closure_interior: "closure S = - interior (- S)"
  by (simp add: interior_closure)

lemma closed_closure[simp, intro]: "closed (closure S)"
  by (simp add: closure_interior closed_Compl)

lemma closure_subset: "S \<subseteq> closure S"
  by (simp add: closure_def)

lemma closure_hull: "closure S = closed hull S"
  by (auto simp: hull_def closure_interior interior_def)

lemma closure_eq: "closure S = S \<longleftrightarrow> closed S"
  unfolding closure_hull using closed_Inter by (rule hull_eq)

lemma closure_closed [simp]: "closed S \<Longrightarrow> closure S = S"
  by (simp only: closure_eq)

lemma closure_closure [simp]: "closure (closure S) = closure S"
  unfolding closure_hull by (rule hull_hull)

lemma closure_mono: "S \<subseteq> T \<Longrightarrow> closure S \<subseteq> closure T"
  unfolding closure_hull by (rule hull_mono)

lemma closure_minimal: "S \<subseteq> T \<Longrightarrow> closed T \<Longrightarrow> closure S \<subseteq> T"
  unfolding closure_hull by (rule hull_minimal)

lemma closure_unique:
  assumes "S \<subseteq> T"
    and "closed T"
    and "\<And>T'. S \<subseteq> T' \<Longrightarrow> closed T' \<Longrightarrow> T \<subseteq> T'"
  shows "closure S = T"
  using assms unfolding closure_hull by (rule hull_unique)

lemma closure_empty [simp]: "closure {} = {}"
  using closed_empty by (rule closure_closed)

lemma closure_UNIV [simp]: "closure UNIV = UNIV"
  using closed_UNIV by (rule closure_closed)

lemma closure_Un [simp]: "closure (S \<union> T) = closure S \<union> closure T"
  by (simp add: closure_interior)

lemma closure_eq_empty [iff]: "closure S = {} \<longleftrightarrow> S = {}"
  using closure_empty closure_subset[of S] by blast

lemma closure_subset_eq: "closure S \<subseteq> S \<longleftrightarrow> closed S"
  using closure_eq[of S] closure_subset[of S] by simp

lemma open_Int_closure_eq_empty: "open S \<Longrightarrow> (S \<inter> closure T) = {} \<longleftrightarrow> S \<inter> T = {}"
  using open_subset_interior[of S "- T"]
  using interior_subset[of "- T"]
  by (auto simp: closure_interior)

lemma open_Int_closure_subset: "open S \<Longrightarrow> S \<inter> closure T \<subseteq> closure (S \<inter> T)"
proof
  fix x
  assume *: "open S" "x \<in> S \<inter> closure T"
  have "x islimpt (S \<inter> T)" if **: "x islimpt T"
  proof (rule islimptI)
    fix A
    assume "x \<in> A" "open A"
    with * have "x \<in> A \<inter> S" "open (A \<inter> S)"
      by (simp_all add: open_Int)
    with ** obtain y where "y \<in> T" "y \<in> A \<inter> S" "y \<noteq> x"
      by (rule islimptE)
    then have "y \<in> S \<inter> T" "y \<in> A \<and> y \<noteq> x"
      by simp_all
    then show "\<exists>y\<in>(S \<inter> T). y \<in> A \<and> y \<noteq> x" ..
  qed
  with * show "x \<in> closure (S \<inter> T)"
    unfolding closure_def by blast
qed

lemma closure_complement: "closure (- S) = - interior S"
  by (simp add: closure_interior)

lemma interior_complement: "interior (- S) = - closure S"
  by (simp add: closure_interior)

lemma interior_diff: "interior(S - T) = interior S - closure T"
  by (simp add: Diff_eq interior_complement)

lemma closure_Times: "closure (A \<times> B) = closure A \<times> closure B"
proof (rule closure_unique)
  show "A \<times> B \<subseteq> closure A \<times> closure B"
    by (intro Sigma_mono closure_subset)
  show "closed (closure A \<times> closure B)"
    by (intro closed_Times closed_closure)
  fix T
  assume "A \<times> B \<subseteq> T" and "closed T"
  then show "closure A \<times> closure B \<subseteq> T"
    apply (simp add: closed_def open_prod_def, clarify)
    apply (rule ccontr)
    apply (drule_tac x="(a, b)" in bspec, simp, clarify, rename_tac C D)
    apply (simp add: closure_interior interior_def)
    apply (drule_tac x=C in spec)
    apply (drule_tac x=D in spec, auto)
    done
qed

lemma closure_openin_Int_closure:
  assumes ope: "openin (subtopology euclidean U) S" and "T \<subseteq> U"
  shows "closure(S \<inter> closure T) = closure(S \<inter> T)"
proof
  obtain V where "open V" and S: "S = U \<inter> V"
    using ope using openin_open by metis
  show "closure (S \<inter> closure T) \<subseteq> closure (S \<inter> T)"
    proof (clarsimp simp: S)
      fix x
      assume  "x \<in> closure (U \<inter> V \<inter> closure T)"
      then have "V \<inter> closure T \<subseteq> A \<Longrightarrow> x \<in> closure A" for A
          by (metis closure_mono subsetD inf.coboundedI2 inf_assoc)
      then have "x \<in> closure (T \<inter> V)"
         by (metis \<open>open V\<close> closure_closure inf_commute open_Int_closure_subset)
      then show "x \<in> closure (U \<inter> V \<inter> T)"
        by (metis \<open>T \<subseteq> U\<close> inf.absorb_iff2 inf_assoc inf_commute)
    qed
next
  show "closure (S \<inter> T) \<subseteq> closure (S \<inter> closure T)"
    by (meson Int_mono closure_mono closure_subset order_refl)
qed

lemma islimpt_in_closure: "(x islimpt S) = (x\<in>closure(S-{x}))"
  unfolding closure_def using islimpt_punctured by blast

lemma connected_imp_connected_closure: "connected S \<Longrightarrow> connected (closure S)"
  by (rule connectedI) (meson closure_subset open_Int open_Int_closure_eq_empty subset_trans connectedD)

lemma limpt_of_limpts: "x islimpt {y. y islimpt S} \<Longrightarrow> x islimpt S"
  for x :: "'a::metric_space"
  apply (clarsimp simp add: islimpt_approachable)
  apply (drule_tac x="e/2" in spec)
  apply (auto simp: simp del: less_divide_eq_numeral1)
  apply (drule_tac x="dist x' x" in spec)
  apply (auto simp: zero_less_dist_iff simp del: less_divide_eq_numeral1)
  apply (erule rev_bexI)
  apply (metis dist_commute dist_triangle_half_r less_trans less_irrefl)
  done

lemma closed_limpts:  "closed {x::'a::metric_space. x islimpt S}"
  using closed_limpt limpt_of_limpts by blast

lemma limpt_of_closure: "x islimpt closure S \<longleftrightarrow> x islimpt S"
  for x :: "'a::metric_space"
  by (auto simp: closure_def islimpt_Un dest: limpt_of_limpts)

lemma closedin_limpt:
  "closedin (subtopology euclidean T) S \<longleftrightarrow> S \<subseteq> T \<and> (\<forall>x. x islimpt S \<and> x \<in> T \<longrightarrow> x \<in> S)"
  apply (simp add: closedin_closed, safe)
   apply (simp add: closed_limpt islimpt_subset)
  apply (rule_tac x="closure S" in exI, simp)
  apply (force simp: closure_def)
  done

lemma closedin_closed_eq: "closed S \<Longrightarrow> closedin (subtopology euclidean S) T \<longleftrightarrow> closed T \<and> T \<subseteq> S"
  by (meson closedin_limpt closed_subset closedin_closed_trans)

lemma connected_closed_set:
   "closed S
    \<Longrightarrow> connected S \<longleftrightarrow> (\<nexists>A B. closed A \<and> closed B \<and> A \<noteq> {} \<and> B \<noteq> {} \<and> A \<union> B = S \<and> A \<inter> B = {})"
  unfolding connected_closedin_eq closedin_closed_eq connected_closedin_eq by blast

text \<open>If a connnected set is written as the union of two nonempty closed sets, then these sets
have to intersect.\<close>

lemma connected_as_closed_union:
  assumes "connected C" "C = A \<union> B" "closed A" "closed B" "A \<noteq> {}" "B \<noteq> {}"
  shows "A \<inter> B \<noteq> {}"
by (metis assms closed_Un connected_closed_set)

lemma closedin_subset_trans:
  "closedin (subtopology euclidean U) S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> T \<subseteq> U \<Longrightarrow>
    closedin (subtopology euclidean T) S"
  by (meson closedin_limpt subset_iff)

lemma openin_subset_trans:
  "openin (subtopology euclidean U) S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> T \<subseteq> U \<Longrightarrow>
    openin (subtopology euclidean T) S"
  by (auto simp: openin_open)

lemma openin_Times:
  "openin (subtopology euclidean S) S' \<Longrightarrow> openin (subtopology euclidean T) T' \<Longrightarrow>
    openin (subtopology euclidean (S \<times> T)) (S' \<times> T')"
  unfolding openin_open using open_Times by blast

lemma Times_in_interior_subtopology:
  fixes U :: "('a::metric_space \<times> 'b::metric_space) set"
  assumes "(x, y) \<in> U" "openin (subtopology euclidean (S \<times> T)) U"
  obtains V W where "openin (subtopology euclidean S) V" "x \<in> V"
                    "openin (subtopology euclidean T) W" "y \<in> W" "(V \<times> W) \<subseteq> U"
proof -
  from assms obtain e where "e > 0" and "U \<subseteq> S \<times> T"
    and e: "\<And>x' y'. \<lbrakk>x'\<in>S; y'\<in>T; dist (x', y') (x, y) < e\<rbrakk> \<Longrightarrow> (x', y') \<in> U"
    by (force simp: openin_euclidean_subtopology_iff)
  with assms have "x \<in> S" "y \<in> T"
    by auto
  show ?thesis
  proof
    show "openin (subtopology euclidean S) (ball x (e/2) \<inter> S)"
      by (simp add: Int_commute openin_open_Int)
    show "x \<in> ball x (e / 2) \<inter> S"
      by (simp add: \<open>0 < e\<close> \<open>x \<in> S\<close>)
    show "openin (subtopology euclidean T) (ball y (e/2) \<inter> T)"
      by (simp add: Int_commute openin_open_Int)
    show "y \<in> ball y (e / 2) \<inter> T"
      by (simp add: \<open>0 < e\<close> \<open>y \<in> T\<close>)
    show "(ball x (e / 2) \<inter> S) \<times> (ball y (e / 2) \<inter> T) \<subseteq> U"
      by clarify (simp add: e dist_Pair_Pair \<open>0 < e\<close> dist_commute sqrt_sum_squares_half_less)
  qed
qed

lemma openin_Times_eq:
  fixes S :: "'a::metric_space set" and T :: "'b::metric_space set"
  shows
    "openin (subtopology euclidean (S \<times> T)) (S' \<times> T') \<longleftrightarrow>
      S' = {} \<or> T' = {} \<or> openin (subtopology euclidean S) S' \<and> openin (subtopology euclidean T) T'"
    (is "?lhs = ?rhs")
proof (cases "S' = {} \<or> T' = {}")
  case True
  then show ?thesis by auto
next
  case False
  then obtain x y where "x \<in> S'" "y \<in> T'"
    by blast
  show ?thesis
  proof
    assume ?lhs
    have "openin (subtopology euclidean S) S'"
      apply (subst openin_subopen, clarify)
      apply (rule Times_in_interior_subtopology [OF _ \<open>?lhs\<close>])
      using \<open>y \<in> T'\<close>
       apply auto
      done
    moreover have "openin (subtopology euclidean T) T'"
      apply (subst openin_subopen, clarify)
      apply (rule Times_in_interior_subtopology [OF _ \<open>?lhs\<close>])
      using \<open>x \<in> S'\<close>
       apply auto
      done
    ultimately show ?rhs
      by simp
  next
    assume ?rhs
    with False show ?lhs
      by (simp add: openin_Times)
  qed
qed

lemma closedin_Times:
  "closedin (subtopology euclidean S) S' \<Longrightarrow> closedin (subtopology euclidean T) T' \<Longrightarrow>
    closedin (subtopology euclidean (S \<times> T)) (S' \<times> T')"
  unfolding closedin_closed using closed_Times by blast

lemma bdd_below_closure:
  fixes A :: "real set"
  assumes "bdd_below A"
  shows "bdd_below (closure A)"
proof -
  from assms obtain m where "\<And>x. x \<in> A \<Longrightarrow> m \<le> x"
    by (auto simp: bdd_below_def)
  then have "A \<subseteq> {m..}" by auto
  then have "closure A \<subseteq> {m..}"
    using closed_real_atLeast by (rule closure_minimal)
  then show ?thesis
    by (auto simp: bdd_below_def)
qed


subsection \<open>Frontier (also known as boundary)\<close>

definition%important "frontier S = closure S - interior S"

lemma frontier_closed [iff]: "closed (frontier S)"
  by (simp add: frontier_def closed_Diff)

lemma frontier_closures: "frontier S = closure S \<inter> closure (- S)"
  by (auto simp: frontier_def interior_closure)

lemma frontier_Int: "frontier(S \<inter> T) = closure(S \<inter> T) \<inter> (frontier S \<union> frontier T)"
proof -
  have "closure (S \<inter> T) \<subseteq> closure S" "closure (S \<inter> T) \<subseteq> closure T"
    by (simp_all add: closure_mono)
  then show ?thesis
    by (auto simp: frontier_closures)
qed

lemma frontier_Int_subset: "frontier(S \<inter> T) \<subseteq> frontier S \<union> frontier T"
  by (auto simp: frontier_Int)

lemma frontier_Int_closed:
  assumes "closed S" "closed T"
  shows "frontier(S \<inter> T) = (frontier S \<inter> T) \<union> (S \<inter> frontier T)"
proof -
  have "closure (S \<inter> T) = T \<inter> S"
    using assms by (simp add: Int_commute closed_Int)
  moreover have "T \<inter> (closure S \<inter> closure (- S)) = frontier S \<inter> T"
    by (simp add: Int_commute frontier_closures)
  ultimately show ?thesis
    by (simp add: Int_Un_distrib Int_assoc Int_left_commute assms frontier_closures)
qed

lemma frontier_straddle:
  fixes a :: "'a::metric_space"
  shows "a \<in> frontier S \<longleftrightarrow> (\<forall>e>0. (\<exists>x\<in>S. dist a x < e) \<and> (\<exists>x. x \<notin> S \<and> dist a x < e))"
  unfolding frontier_def closure_interior
  by (auto simp: mem_interior subset_eq ball_def)

lemma frontier_subset_closed: "closed S \<Longrightarrow> frontier S \<subseteq> S"
  by (metis frontier_def closure_closed Diff_subset)

lemma frontier_empty [simp]: "frontier {} = {}"
  by (simp add: frontier_def)

lemma frontier_subset_eq: "frontier S \<subseteq> S \<longleftrightarrow> closed S"
proof -
  {
    assume "frontier S \<subseteq> S"
    then have "closure S \<subseteq> S"
      using interior_subset unfolding frontier_def by auto
    then have "closed S"
      using closure_subset_eq by auto
  }
  then show ?thesis using frontier_subset_closed[of S] ..
qed

lemma frontier_complement [simp]: "frontier (- S) = frontier S"
  by (auto simp: frontier_def closure_complement interior_complement)

lemma frontier_Un_subset: "frontier(S \<union> T) \<subseteq> frontier S \<union> frontier T"
  by (metis compl_sup frontier_Int_subset frontier_complement)

lemma frontier_disjoint_eq: "frontier S \<inter> S = {} \<longleftrightarrow> open S"
  using frontier_complement frontier_subset_eq[of "- S"]
  unfolding open_closed by auto

lemma frontier_UNIV [simp]: "frontier UNIV = {}"
  using frontier_complement frontier_empty by fastforce

lemma frontier_interiors: "frontier s = - interior(s) - interior(-s)"
  by (simp add: Int_commute frontier_def interior_closure)

lemma frontier_interior_subset: "frontier(interior S) \<subseteq> frontier S"
  by (simp add: Diff_mono frontier_interiors interior_mono interior_subset)

lemma connected_Int_frontier:
     "\<lbrakk>connected s; s \<inter> t \<noteq> {}; s - t \<noteq> {}\<rbrakk> \<Longrightarrow> (s \<inter> frontier t \<noteq> {})"
  apply (simp add: frontier_interiors connected_openin, safe)
  apply (drule_tac x="s \<inter> interior t" in spec, safe)
   apply (drule_tac [2] x="s \<inter> interior (-t)" in spec)
   apply (auto simp: disjoint_eq_subset_Compl dest: interior_subset [THEN subsetD])
  done

lemma closure_Un_frontier: "closure S = S \<union> frontier S"
proof -
  have "S \<union> interior S = S"
    using interior_subset by auto
  then show ?thesis
    using closure_subset by (auto simp: frontier_def)
qed


subsection%unimportant \<open>Filters and the ``eventually true'' quantifier\<close>

definition indirection :: "'a::real_normed_vector \<Rightarrow> 'a \<Rightarrow> 'a filter"  (infixr "indirection" 70)
  where "a indirection v = at a within {b. \<exists>c\<ge>0. b - a = scaleR c v}"

text \<open>Identify Trivial limits, where we can't approach arbitrarily closely.\<close>

lemma trivial_limit_within: "trivial_limit (at a within S) \<longleftrightarrow> \<not> a islimpt S"
proof
  assume "trivial_limit (at a within S)"
  then show "\<not> a islimpt S"
    unfolding trivial_limit_def
    unfolding eventually_at_topological
    unfolding islimpt_def
    apply (clarsimp simp add: set_eq_iff)
    apply (rename_tac T, rule_tac x=T in exI)
    apply (clarsimp, drule_tac x=y in bspec, simp_all)
    done
next
  assume "\<not> a islimpt S"
  then show "trivial_limit (at a within S)"
    unfolding trivial_limit_def eventually_at_topological islimpt_def
    by metis
qed

lemma trivial_limit_at_iff: "trivial_limit (at a) \<longleftrightarrow> \<not> a islimpt UNIV"
  using trivial_limit_within [of a UNIV] by simp

lemma trivial_limit_at: "\<not> trivial_limit (at a)"
  for a :: "'a::perfect_space"
  by (rule at_neq_bot)

lemma trivial_limit_at_infinity:
  "\<not> trivial_limit (at_infinity :: ('a::{real_normed_vector,perfect_space}) filter)"
  unfolding trivial_limit_def eventually_at_infinity
  apply clarsimp
  apply (subgoal_tac "\<exists>x::'a. x \<noteq> 0", clarify)
   apply (rule_tac x="scaleR (b / norm x) x" in exI, simp)
  apply (cut_tac islimpt_UNIV [of "0::'a", unfolded islimpt_def])
  apply (drule_tac x=UNIV in spec, simp)
  done

lemma not_trivial_limit_within: "\<not> trivial_limit (at x within S) = (x \<in> closure (S - {x}))"
  using islimpt_in_closure by (metis trivial_limit_within)

lemma not_in_closure_trivial_limitI:
  "x \<notin> closure s \<Longrightarrow> trivial_limit (at x within s)"
  using not_trivial_limit_within[of x s]
  by safe (metis Diff_empty Diff_insert0 closure_subset contra_subsetD)

lemma filterlim_at_within_closure_implies_filterlim: "filterlim f l (at x within s)"
  if "x \<in> closure s \<Longrightarrow> filterlim f l (at x within s)"
  by (metis bot.extremum filterlim_filtercomap filterlim_mono not_in_closure_trivial_limitI that)

lemma at_within_eq_bot_iff: "at c within A = bot \<longleftrightarrow> c \<notin> closure (A - {c})"
  using not_trivial_limit_within[of c A] by blast

text \<open>Some property holds "sufficiently close" to the limit point.\<close>

lemma trivial_limit_eventually: "trivial_limit net \<Longrightarrow> eventually P net"
  by simp

lemma trivial_limit_eq: "trivial_limit net \<longleftrightarrow> (\<forall>P. eventually P net)"
  by (simp add: filter_eq_iff)


subsection \<open>Limits\<close>

proposition Lim: "(f \<longlongrightarrow> l) net \<longleftrightarrow> trivial_limit net \<or> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) net)"
  by (auto simp: tendsto_iff trivial_limit_eq)

text \<open>Show that they yield usual definitions in the various cases.\<close>

proposition Lim_within_le: "(f \<longlongrightarrow> l)(at a within S) \<longleftrightarrow>
    (\<forall>e>0. \<exists>d>0. \<forall>x\<in>S. 0 < dist x a \<and> dist x a \<le> d \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at_le)

proposition Lim_within: "(f \<longlongrightarrow> l) (at a within S) \<longleftrightarrow>
    (\<forall>e >0. \<exists>d>0. \<forall>x \<in> S. 0 < dist x a \<and> dist x a  < d \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at)

corollary Lim_withinI [intro?]:
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>d>0. \<forall>x \<in> S. 0 < dist x a \<and> dist x a < d \<longrightarrow> dist (f x) l \<le> e"
  shows "(f \<longlongrightarrow> l) (at a within S)"
  apply (simp add: Lim_within, clarify)
  apply (rule ex_forward [OF assms [OF half_gt_zero]], auto)
  done

proposition Lim_at: "(f \<longlongrightarrow> l) (at a) \<longleftrightarrow>
    (\<forall>e >0. \<exists>d>0. \<forall>x. 0 < dist x a \<and> dist x a < d  \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at)

proposition Lim_at_infinity: "(f \<longlongrightarrow> l) at_infinity \<longleftrightarrow> (\<forall>e>0. \<exists>b. \<forall>x. norm x \<ge> b \<longrightarrow> dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at_infinity)

corollary Lim_at_infinityI [intro?]:
  assumes "\<And>e. e > 0 \<Longrightarrow> \<exists>B. \<forall>x. norm x \<ge> B \<longrightarrow> dist (f x) l \<le> e"
  shows "(f \<longlongrightarrow> l) at_infinity"
  apply (simp add: Lim_at_infinity, clarify)
  apply (rule ex_forward [OF assms [OF half_gt_zero]], auto)
  done

lemma Lim_eventually: "eventually (\<lambda>x. f x = l) net \<Longrightarrow> (f \<longlongrightarrow> l) net"
  by (rule topological_tendstoI) (auto elim: eventually_mono)

lemma Lim_transform_within_set:
  fixes a :: "'a::metric_space" and l :: "'b::metric_space"
  shows "\<lbrakk>(f \<longlongrightarrow> l) (at a within S); eventually (\<lambda>x. x \<in> S \<longleftrightarrow> x \<in> T) (at a)\<rbrakk>
         \<Longrightarrow> (f \<longlongrightarrow> l) (at a within T)"
apply (clarsimp simp: eventually_at Lim_within)
apply (drule_tac x=e in spec, clarify)
apply (rename_tac k)
apply (rule_tac x="min d k" in exI, simp)
done

lemma Lim_transform_within_set_eq:
  fixes a l :: "'a::real_normed_vector"
  shows "eventually (\<lambda>x. x \<in> s \<longleftrightarrow> x \<in> t) (at a)
         \<Longrightarrow> ((f \<longlongrightarrow> l) (at a within s) \<longleftrightarrow> (f \<longlongrightarrow> l) (at a within t))"
  by (force intro: Lim_transform_within_set elim: eventually_mono)

lemma Lim_transform_within_openin:
  fixes a :: "'a::metric_space"
  assumes f: "(f \<longlongrightarrow> l) (at a within T)"
    and "openin (subtopology euclidean T) S" "a \<in> S"
    and eq: "\<And>x. \<lbrakk>x \<in> S; x \<noteq> a\<rbrakk> \<Longrightarrow> f x = g x"
  shows "(g \<longlongrightarrow> l) (at a within T)"
proof -
  obtain \<epsilon> where "0 < \<epsilon>" and \<epsilon>: "ball a \<epsilon> \<inter> T \<subseteq> S"
    using assms by (force simp: openin_contains_ball)
  then have "a \<in> ball a \<epsilon>"
    by simp
  show ?thesis
    by (rule Lim_transform_within [OF f \<open>0 < \<epsilon>\<close> eq]) (use \<epsilon> in \<open>auto simp: dist_commute subset_iff\<close>)
qed

lemma continuous_transform_within_openin:
  fixes a :: "'a::metric_space"
  assumes "continuous (at a within T) f"
    and "openin (subtopology euclidean T) S" "a \<in> S"
    and eq: "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "continuous (at a within T) g"
  using assms by (simp add: Lim_transform_within_openin continuous_within)

text \<open>The expected monotonicity property.\<close>

lemma Lim_Un:
  assumes "(f \<longlongrightarrow> l) (at x within S)" "(f \<longlongrightarrow> l) (at x within T)"
  shows "(f \<longlongrightarrow> l) (at x within (S \<union> T))"
  using assms unfolding at_within_union by (rule filterlim_sup)

lemma Lim_Un_univ:
  "(f \<longlongrightarrow> l) (at x within S) \<Longrightarrow> (f \<longlongrightarrow> l) (at x within T) \<Longrightarrow>
    S \<union> T = UNIV \<Longrightarrow> (f \<longlongrightarrow> l) (at x)"
  by (metis Lim_Un)

text \<open>Interrelations between restricted and unrestricted limits.\<close>

lemma Lim_at_imp_Lim_at_within: "(f \<longlongrightarrow> l) (at x) \<Longrightarrow> (f \<longlongrightarrow> l) (at x within S)"
  by (metis order_refl filterlim_mono subset_UNIV at_le)

lemma eventually_within_interior:
  assumes "x \<in> interior S"
  shows "eventually P (at x within S) \<longleftrightarrow> eventually P (at x)"
  (is "?lhs = ?rhs")
proof
  from assms obtain T where T: "open T" "x \<in> T" "T \<subseteq> S" ..
  {
    assume ?lhs
    then obtain A where "open A" and "x \<in> A" and "\<forall>y\<in>A. y \<noteq> x \<longrightarrow> y \<in> S \<longrightarrow> P y"
      by (auto simp: eventually_at_topological)
    with T have "open (A \<inter> T)" and "x \<in> A \<inter> T" and "\<forall>y \<in> A \<inter> T. y \<noteq> x \<longrightarrow> P y"
      by auto
    then show ?rhs
      by (auto simp: eventually_at_topological)
  next
    assume ?rhs
    then show ?lhs
      by (auto elim: eventually_mono simp: eventually_at_filter)
  }
qed

lemma at_within_interior: "x \<in> interior S \<Longrightarrow> at x within S = at x"
  unfolding filter_eq_iff by (intro allI eventually_within_interior)

lemma Lim_within_LIMSEQ:
  fixes a :: "'a::first_countable_topology"
  assumes "\<forall>S. (\<forall>n. S n \<noteq> a \<and> S n \<in> T) \<and> S \<longlonglongrightarrow> a \<longrightarrow> (\<lambda>n. X (S n)) \<longlonglongrightarrow> L"
  shows "(X \<longlongrightarrow> L) (at a within T)"
  using assms unfolding tendsto_def [where l=L]
  by (simp add: sequentially_imp_eventually_within)

lemma Lim_right_bound:
  fixes f :: "'a :: {linorder_topology, conditionally_complete_linorder, no_top} \<Rightarrow>
    'b::{linorder_topology, conditionally_complete_linorder}"
  assumes mono: "\<And>a b. a \<in> I \<Longrightarrow> b \<in> I \<Longrightarrow> x < a \<Longrightarrow> a \<le> b \<Longrightarrow> f a \<le> f b"
    and bnd: "\<And>a. a \<in> I \<Longrightarrow> x < a \<Longrightarrow> K \<le> f a"
  shows "(f \<longlongrightarrow> Inf (f ` ({x<..} \<inter> I))) (at x within ({x<..} \<inter> I))"
proof (cases "{x<..} \<inter> I = {}")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof (rule order_tendstoI)
    fix a
    assume a: "a < Inf (f ` ({x<..} \<inter> I))"
    {
      fix y
      assume "y \<in> {x<..} \<inter> I"
      with False bnd have "Inf (f ` ({x<..} \<inter> I)) \<le> f y"
        by (auto intro!: cInf_lower bdd_belowI2)
      with a have "a < f y"
        by (blast intro: less_le_trans)
    }
    then show "eventually (\<lambda>x. a < f x) (at x within ({x<..} \<inter> I))"
      by (auto simp: eventually_at_filter intro: exI[of _ 1] zero_less_one)
  next
    fix a
    assume "Inf (f ` ({x<..} \<inter> I)) < a"
    from cInf_lessD[OF _ this] False obtain y where y: "x < y" "y \<in> I" "f y < a"
      by auto
    then have "eventually (\<lambda>x. x \<in> I \<longrightarrow> f x < a) (at_right x)"
      unfolding eventually_at_right[OF \<open>x < y\<close>] by (metis less_imp_le le_less_trans mono)
    then show "eventually (\<lambda>x. f x < a) (at x within ({x<..} \<inter> I))"
      unfolding eventually_at_filter by eventually_elim simp
  qed
qed

text \<open>Another limit point characterization.\<close>

lemma limpt_sequential_inj:
  fixes x :: "'a::metric_space"
  shows "x islimpt S \<longleftrightarrow>
         (\<exists>f. (\<forall>n::nat. f n \<in> S - {x}) \<and> inj f \<and> (f \<longlongrightarrow> x) sequentially)"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have "\<forall>e>0. \<exists>x'\<in>S. x' \<noteq> x \<and> dist x' x < e"
    by (force simp: islimpt_approachable)
  then obtain y where y: "\<And>e. e>0 \<Longrightarrow> y e \<in> S \<and> y e \<noteq> x \<and> dist (y e) x < e"
    by metis
  define f where "f \<equiv> rec_nat (y 1) (\<lambda>n fn. y (min (inverse(2 ^ (Suc n))) (dist fn x)))"
  have [simp]: "f 0 = y 1"
               "f(Suc n) = y (min (inverse(2 ^ (Suc n))) (dist (f n) x))" for n
    by (simp_all add: f_def)
  have f: "f n \<in> S \<and> (f n \<noteq> x) \<and> dist (f n) x < inverse(2 ^ n)" for n
  proof (induction n)
    case 0 show ?case
      by (simp add: y)
  next
    case (Suc n) then show ?case
      apply (auto simp: y)
      by (metis half_gt_zero_iff inverse_positive_iff_positive less_divide_eq_numeral1(1) min_less_iff_conj y zero_less_dist_iff zero_less_numeral zero_less_power)
  qed
  show ?rhs
  proof (rule_tac x=f in exI, intro conjI allI)
    show "\<And>n. f n \<in> S - {x}"
      using f by blast
    have "dist (f n) x < dist (f m) x" if "m < n" for m n
    using that
    proof (induction n)
      case 0 then show ?case by simp
    next
      case (Suc n)
      then consider "m < n" | "m = n" using less_Suc_eq by blast
      then show ?case
      proof cases
        assume "m < n"
        have "dist (f(Suc n)) x = dist (y (min (inverse(2 ^ (Suc n))) (dist (f n) x))) x"
          by simp
        also have "\<dots> < dist (f n) x"
          by (metis dist_pos_lt f min.strict_order_iff min_less_iff_conj y)
        also have "\<dots> < dist (f m) x"
          using Suc.IH \<open>m < n\<close> by blast
        finally show ?thesis .
      next
        assume "m = n" then show ?case
          by simp (metis dist_pos_lt f half_gt_zero_iff inverse_positive_iff_positive min_less_iff_conj y zero_less_numeral zero_less_power)
      qed
    qed
    then show "inj f"
      by (metis less_irrefl linorder_injI)
    show "f \<longlonglongrightarrow> x"
      apply (rule tendstoI)
      apply (rule_tac c="nat (ceiling(1/e))" in eventually_sequentiallyI)
      apply (rule less_trans [OF f [THEN conjunct2, THEN conjunct2]])
      apply (simp add: field_simps)
      by (meson le_less_trans mult_less_cancel_left not_le of_nat_less_two_power)
  qed
next
  assume ?rhs
  then show ?lhs
    by (fastforce simp add: islimpt_approachable lim_sequentially)
qed

(*could prove directly from islimpt_sequential_inj, but only for metric spaces*)
lemma islimpt_sequential:
  fixes x :: "'a::first_countable_topology"
  shows "x islimpt S \<longleftrightarrow> (\<exists>f. (\<forall>n::nat. f n \<in> S - {x}) \<and> (f \<longlongrightarrow> x) sequentially)"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  from countable_basis_at_decseq[of x] obtain A where A:
      "\<And>i. open (A i)"
      "\<And>i. x \<in> A i"
      "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
    by blast
  define f where "f n = (SOME y. y \<in> S \<and> y \<in> A n \<and> x \<noteq> y)" for n
  {
    fix n
    from \<open>?lhs\<close> have "\<exists>y. y \<in> S \<and> y \<in> A n \<and> x \<noteq> y"
      unfolding islimpt_def using A(1,2)[of n] by auto
    then have "f n \<in> S \<and> f n \<in> A n \<and> x \<noteq> f n"
      unfolding f_def by (rule someI_ex)
    then have "f n \<in> S" "f n \<in> A n" "x \<noteq> f n" by auto
  }
  then have "\<forall>n. f n \<in> S - {x}" by auto
  moreover have "(\<lambda>n. f n) \<longlonglongrightarrow> x"
  proof (rule topological_tendstoI)
    fix S
    assume "open S" "x \<in> S"
    from A(3)[OF this] \<open>\<And>n. f n \<in> A n\<close>
    show "eventually (\<lambda>x. f x \<in> S) sequentially"
      by (auto elim!: eventually_mono)
  qed
  ultimately show ?rhs by fast
next
  assume ?rhs
  then obtain f :: "nat \<Rightarrow> 'a" where f: "\<And>n. f n \<in> S - {x}" and lim: "f \<longlonglongrightarrow> x"
    by auto
  show ?lhs
    unfolding islimpt_def
  proof safe
    fix T
    assume "open T" "x \<in> T"
    from lim[THEN topological_tendstoD, OF this] f
    show "\<exists>y\<in>S. y \<in> T \<and> y \<noteq> x"
      unfolding eventually_sequentially by auto
  qed
qed

lemma Lim_null:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "(f \<longlongrightarrow> l) net \<longleftrightarrow> ((\<lambda>x. f(x) - l) \<longlongrightarrow> 0) net"
  by (simp add: Lim dist_norm)

lemma Lim_null_comparison:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "eventually (\<lambda>x. norm (f x) \<le> g x) net" "(g \<longlongrightarrow> 0) net"
  shows "(f \<longlongrightarrow> 0) net"
  using assms(2)
proof (rule metric_tendsto_imp_tendsto)
  show "eventually (\<lambda>x. dist (f x) 0 \<le> dist (g x) 0) net"
    using assms(1) by (rule eventually_mono) (simp add: dist_norm)
qed

lemma Lim_transform_bound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
    and g :: "'a \<Rightarrow> 'c::real_normed_vector"
  assumes "eventually (\<lambda>n. norm (f n) \<le> norm (g n)) net"
    and "(g \<longlongrightarrow> 0) net"
  shows "(f \<longlongrightarrow> 0) net"
  using assms(1) tendsto_norm_zero [OF assms(2)]
  by (rule Lim_null_comparison)

lemma lim_null_mult_right_bounded:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes f: "(f \<longlongrightarrow> 0) F" and g: "eventually (\<lambda>x. norm(g x) \<le> B) F"
    shows "((\<lambda>z. f z * g z) \<longlongrightarrow> 0) F"
proof -
  have *: "((\<lambda>x. norm (f x) * B) \<longlongrightarrow> 0) F"
    by (simp add: f tendsto_mult_left_zero tendsto_norm_zero)
  have "((\<lambda>x. norm (f x) * norm (g x)) \<longlongrightarrow> 0) F"
    apply (rule Lim_null_comparison [OF _ *])
    apply (simp add: eventually_mono [OF g] mult_left_mono)
    done
  then show ?thesis
    by (subst tendsto_norm_zero_iff [symmetric]) (simp add: norm_mult)
qed

lemma lim_null_mult_left_bounded:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes g: "eventually (\<lambda>x. norm(g x) \<le> B) F" and f: "(f \<longlongrightarrow> 0) F"
    shows "((\<lambda>z. g z * f z) \<longlongrightarrow> 0) F"
proof -
  have *: "((\<lambda>x. B * norm (f x)) \<longlongrightarrow> 0) F"
    by (simp add: f tendsto_mult_right_zero tendsto_norm_zero)
  have "((\<lambda>x. norm (g x) * norm (f x)) \<longlongrightarrow> 0) F"
    apply (rule Lim_null_comparison [OF _ *])
    apply (simp add: eventually_mono [OF g] mult_right_mono)
    done
  then show ?thesis
    by (subst tendsto_norm_zero_iff [symmetric]) (simp add: norm_mult)
qed

lemma lim_null_scaleR_bounded:
  assumes f: "(f \<longlongrightarrow> 0) net" and gB: "eventually (\<lambda>a. f a = 0 \<or> norm(g a) \<le> B) net"
    shows "((\<lambda>n. f n *\<^sub>R g n) \<longlongrightarrow> 0) net"
proof
  fix \<epsilon>::real
  assume "0 < \<epsilon>"
  then have B: "0 < \<epsilon> / (abs B + 1)" by simp
  have *: "\<bar>f x\<bar> * norm (g x) < \<epsilon>" if f: "\<bar>f x\<bar> * (\<bar>B\<bar> + 1) < \<epsilon>" and g: "norm (g x) \<le> B" for x
  proof -
    have "\<bar>f x\<bar> * norm (g x) \<le> \<bar>f x\<bar> * B"
      by (simp add: mult_left_mono g)
    also have "\<dots> \<le> \<bar>f x\<bar> * (\<bar>B\<bar> + 1)"
      by (simp add: mult_left_mono)
    also have "\<dots> < \<epsilon>"
      by (rule f)
    finally show ?thesis .
  qed
  show "\<forall>\<^sub>F x in net. dist (f x *\<^sub>R g x) 0 < \<epsilon>"
    apply (rule eventually_mono [OF eventually_conj [OF tendstoD [OF f B] gB] ])
    apply (auto simp: \<open>0 < \<epsilon>\<close> divide_simps * split: if_split_asm)
    done
qed

text\<open>Deducing things about the limit from the elements.\<close>

lemma Lim_in_closed_set:
  assumes "closed S"
    and "eventually (\<lambda>x. f(x) \<in> S) net"
    and "\<not> trivial_limit net" "(f \<longlongrightarrow> l) net"
  shows "l \<in> S"
proof (rule ccontr)
  assume "l \<notin> S"
  with \<open>closed S\<close> have "open (- S)" "l \<in> - S"
    by (simp_all add: open_Compl)
  with assms(4) have "eventually (\<lambda>x. f x \<in> - S) net"
    by (rule topological_tendstoD)
  with assms(2) have "eventually (\<lambda>x. False) net"
    by (rule eventually_elim2) simp
  with assms(3) show "False"
    by (simp add: eventually_False)
qed

text\<open>Need to prove closed(cball(x,e)) before deducing this as a corollary.\<close>

lemma Lim_dist_ubound:
  assumes "\<not>(trivial_limit net)"
    and "(f \<longlongrightarrow> l) net"
    and "eventually (\<lambda>x. dist a (f x) \<le> e) net"
  shows "dist a l \<le> e"
  using assms by (fast intro: tendsto_le tendsto_intros)

lemma Lim_norm_ubound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "\<not>(trivial_limit net)" "(f \<longlongrightarrow> l) net" "eventually (\<lambda>x. norm(f x) \<le> e) net"
  shows "norm(l) \<le> e"
  using assms by (fast intro: tendsto_le tendsto_intros)

lemma Lim_norm_lbound:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "\<not> trivial_limit net"
    and "(f \<longlongrightarrow> l) net"
    and "eventually (\<lambda>x. e \<le> norm (f x)) net"
  shows "e \<le> norm l"
  using assms by (fast intro: tendsto_le tendsto_intros)

text\<open>Limit under bilinear function\<close>

lemma Lim_bilinear:
  assumes "(f \<longlongrightarrow> l) net"
    and "(g \<longlongrightarrow> m) net"
    and "bounded_bilinear h"
  shows "((\<lambda>x. h (f x) (g x)) \<longlongrightarrow> (h l m)) net"
  using \<open>bounded_bilinear h\<close> \<open>(f \<longlongrightarrow> l) net\<close> \<open>(g \<longlongrightarrow> m) net\<close>
  by (rule bounded_bilinear.tendsto)

text\<open>These are special for limits out of the same vector space.\<close>

lemma Lim_within_id: "(id \<longlongrightarrow> a) (at a within s)"
  unfolding id_def by (rule tendsto_ident_at)

lemma Lim_at_id: "(id \<longlongrightarrow> a) (at a)"
  unfolding id_def by (rule tendsto_ident_at)

lemma Lim_at_zero:
  fixes a :: "'a::real_normed_vector"
    and l :: "'b::topological_space"
  shows "(f \<longlongrightarrow> l) (at a) \<longleftrightarrow> ((\<lambda>x. f(a + x)) \<longlongrightarrow> l) (at 0)"
  using LIM_offset_zero LIM_offset_zero_cancel ..

text\<open>It's also sometimes useful to extract the limit point from the filter.\<close>

abbreviation netlimit :: "'a::t2_space filter \<Rightarrow> 'a"
  where "netlimit F \<equiv> Lim F (\<lambda>x. x)"

lemma netlimit_within: "\<not> trivial_limit (at a within S) \<Longrightarrow> netlimit (at a within S) = a"
  by (rule tendsto_Lim) (auto intro: tendsto_intros)

lemma netlimit_at [simp]:
  fixes a :: "'a::{perfect_space,t2_space}"
  shows "netlimit (at a) = a"
  using netlimit_within [of a UNIV] by simp

lemma lim_within_interior:
  "x \<in> interior S \<Longrightarrow> (f \<longlongrightarrow> l) (at x within S) \<longleftrightarrow> (f \<longlongrightarrow> l) (at x)"
  by (metis at_within_interior)

lemma netlimit_within_interior:
  fixes x :: "'a::{t2_space,perfect_space}"
  assumes "x \<in> interior S"
  shows "netlimit (at x within S) = x"
  using assms by (metis at_within_interior netlimit_at)

lemma netlimit_at_vector:
  fixes a :: "'a::real_normed_vector"
  shows "netlimit (at a) = a"
proof (cases "\<exists>x. x \<noteq> a")
  case True then obtain x where x: "x \<noteq> a" ..
  have "\<not> trivial_limit (at a)"
    unfolding trivial_limit_def eventually_at dist_norm
    apply clarsimp
    apply (rule_tac x="a + scaleR (d / 2) (sgn (x - a))" in exI)
    apply (simp add: norm_sgn sgn_zero_iff x)
    done
  then show ?thesis
    by (rule netlimit_within [of a UNIV])
qed simp


text\<open>Useful lemmas on closure and set of possible sequential limits.\<close>

lemma closure_sequential:
  fixes l :: "'a::first_countable_topology"
  shows "l \<in> closure S \<longleftrightarrow> (\<exists>x. (\<forall>n. x n \<in> S) \<and> (x \<longlongrightarrow> l) sequentially)"
  (is "?lhs = ?rhs")
proof
  assume "?lhs"
  moreover
  {
    assume "l \<in> S"
    then have "?rhs" using tendsto_const[of l sequentially] by auto
  }
  moreover
  {
    assume "l islimpt S"
    then have "?rhs" unfolding islimpt_sequential by auto
  }
  ultimately show "?rhs"
    unfolding closure_def by auto
next
  assume "?rhs"
  then show "?lhs" unfolding closure_def islimpt_sequential by auto
qed

lemma closed_sequential_limits:
  fixes S :: "'a::first_countable_topology set"
  shows "closed S \<longleftrightarrow> (\<forall>x l. (\<forall>n. x n \<in> S) \<and> (x \<longlongrightarrow> l) sequentially \<longrightarrow> l \<in> S)"
by (metis closure_sequential closure_subset_eq subset_iff)

lemma closure_approachable:
  fixes S :: "'a::metric_space set"
  shows "x \<in> closure S \<longleftrightarrow> (\<forall>e>0. \<exists>y\<in>S. dist y x < e)"
  apply (auto simp: closure_def islimpt_approachable)
  apply (metis dist_self)
  done

lemma closure_approachable_le:
  fixes S :: "'a::metric_space set"
  shows "x \<in> closure S \<longleftrightarrow> (\<forall>e>0. \<exists>y\<in>S. dist y x \<le> e)"
  unfolding closure_approachable
  using dense by force

lemma closure_approachableD:
  assumes "x \<in> closure S" "e>0"
  shows "\<exists>y\<in>S. dist x y < e"
  using assms unfolding closure_approachable by (auto simp: dist_commute)

lemma closed_approachable:
  fixes S :: "'a::metric_space set"
  shows "closed S \<Longrightarrow> (\<forall>e>0. \<exists>y\<in>S. dist y x < e) \<longleftrightarrow> x \<in> S"
  by (metis closure_closed closure_approachable)

lemma closure_contains_Inf:
  fixes S :: "real set"
  assumes "S \<noteq> {}" "bdd_below S"
  shows "Inf S \<in> closure S"
proof -
  have *: "\<forall>x\<in>S. Inf S \<le> x"
    using cInf_lower[of _ S] assms by metis
  {
    fix e :: real
    assume "e > 0"
    then have "Inf S < Inf S + e" by simp
    with assms obtain x where "x \<in> S" "x < Inf S + e"
      by (subst (asm) cInf_less_iff) auto
    with * have "\<exists>x\<in>S. dist x (Inf S) < e"
      by (intro bexI[of _ x]) (auto simp: dist_real_def)
  }
  then show ?thesis unfolding closure_approachable by auto
qed

lemma closure_Int_ballI:
  fixes S :: "'a :: metric_space set"
  assumes "\<And>U. \<lbrakk>openin (subtopology euclidean S) U; U \<noteq> {}\<rbrakk> \<Longrightarrow> T \<inter> U \<noteq> {}"
 shows "S \<subseteq> closure T"
proof (clarsimp simp: closure_approachable dist_commute)
  fix x and e::real
  assume "x \<in> S" "0 < e"
  with assms [of "S \<inter> ball x e"] show "\<exists>y\<in>T. dist x y < e"
    by force
qed

lemma closed_contains_Inf:
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> bdd_below S \<Longrightarrow> closed S \<Longrightarrow> Inf S \<in> S"
  by (metis closure_contains_Inf closure_closed)

lemma closed_subset_contains_Inf:
  fixes A C :: "real set"
  shows "closed C \<Longrightarrow> A \<subseteq> C \<Longrightarrow> A \<noteq> {} \<Longrightarrow> bdd_below A \<Longrightarrow> Inf A \<in> C"
  by (metis closure_contains_Inf closure_minimal subset_eq)

lemma atLeastAtMost_subset_contains_Inf:
  fixes A :: "real set" and a b :: real
  shows "A \<noteq> {} \<Longrightarrow> a \<le> b \<Longrightarrow> A \<subseteq> {a..b} \<Longrightarrow> Inf A \<in> {a..b}"
  by (rule closed_subset_contains_Inf)
     (auto intro: closed_real_atLeastAtMost intro!: bdd_belowI[of A a])

lemma not_trivial_limit_within_ball:
  "\<not> trivial_limit (at x within S) \<longleftrightarrow> (\<forall>e>0. S \<inter> ball x e - {x} \<noteq> {})"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs
  proof -
    {
      fix e :: real
      assume "e > 0"
      then obtain y where "y \<in> S - {x}" and "dist y x < e"
        using \<open>?lhs\<close> not_trivial_limit_within[of x S] closure_approachable[of x "S - {x}"]
        by auto
      then have "y \<in> S \<inter> ball x e - {x}"
        unfolding ball_def by (simp add: dist_commute)
      then have "S \<inter> ball x e - {x} \<noteq> {}" by blast
    }
    then show ?thesis by auto
  qed
  show ?lhs if ?rhs
  proof -
    {
      fix e :: real
      assume "e > 0"
      then obtain y where "y \<in> S \<inter> ball x e - {x}"
        using \<open>?rhs\<close> by blast
      then have "y \<in> S - {x}" and "dist y x < e"
        unfolding ball_def by (simp_all add: dist_commute)
      then have "\<exists>y \<in> S - {x}. dist y x < e"
        by auto
    }
    then show ?thesis
      using not_trivial_limit_within[of x S] closure_approachable[of x "S - {x}"]
      by auto
  qed
qed

lemma tendsto_If_within_closures:
  assumes f: "x \<in> s \<union> (closure s \<inter> closure t) \<Longrightarrow>
      (f \<longlongrightarrow> l x) (at x within s \<union> (closure s \<inter> closure t))"
  assumes g: "x \<in> t \<union> (closure s \<inter> closure t) \<Longrightarrow>
      (g \<longlongrightarrow> l x) (at x within t \<union> (closure s \<inter> closure t))"
  assumes "x \<in> s \<union> t"
  shows "((\<lambda>x. if x \<in> s then f x else g x) \<longlongrightarrow> l x) (at x within s \<union> t)"
proof -
  have *: "(s \<union> t) \<inter> {x. x \<in> s} = s" "(s \<union> t) \<inter> {x. x \<notin> s} = t - s"
    by auto
  have "(f \<longlongrightarrow> l x) (at x within s)"
    by (rule filterlim_at_within_closure_implies_filterlim)
       (use \<open>x \<in> _\<close> in \<open>auto simp: inf_commute closure_def intro: tendsto_within_subset[OF f]\<close>)
  moreover
  have "(g \<longlongrightarrow> l x) (at x within t - s)"
    by (rule filterlim_at_within_closure_implies_filterlim)
      (use \<open>x \<in> _\<close> in
        \<open>auto intro!: tendsto_within_subset[OF g] simp: closure_def intro: islimpt_subset\<close>)
  ultimately show ?thesis
    by (intro filterlim_at_within_If) (simp_all only: *)
qed


subsection \<open>Boundedness\<close>

  (* FIXME: This has to be unified with BSEQ!! *)
definition%important (in metric_space) bounded :: "'a set \<Rightarrow> bool"
  where "bounded S \<longleftrightarrow> (\<exists>x e. \<forall>y\<in>S. dist x y \<le> e)"

lemma bounded_subset_cball: "bounded S \<longleftrightarrow> (\<exists>e x. S \<subseteq> cball x e \<and> 0 \<le> e)"
  unfolding bounded_def subset_eq  by auto (meson order_trans zero_le_dist)

lemma bounded_any_center: "bounded S \<longleftrightarrow> (\<exists>e. \<forall>y\<in>S. dist a y \<le> e)"
  unfolding bounded_def
  by auto (metis add.commute add_le_cancel_right dist_commute dist_triangle_le)

lemma bounded_iff: "bounded S \<longleftrightarrow> (\<exists>a. \<forall>x\<in>S. norm x \<le> a)"
  unfolding bounded_any_center [where a=0]
  by (simp add: dist_norm)

lemma bdd_above_norm: "bdd_above (norm ` X) \<longleftrightarrow> bounded X"
  by (simp add: bounded_iff bdd_above_def)

lemma bounded_norm_comp: "bounded ((\<lambda>x. norm (f x)) ` S) = bounded (f ` S)"
  by (simp add: bounded_iff)

lemma boundedI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> norm x \<le> B"
  shows "bounded S"
  using assms bounded_iff by blast

lemma bounded_empty [simp]: "bounded {}"
  by (simp add: bounded_def)

lemma bounded_subset: "bounded T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> bounded S"
  by (metis bounded_def subset_eq)

lemma bounded_interior[intro]: "bounded S \<Longrightarrow> bounded(interior S)"
  by (metis bounded_subset interior_subset)

lemma bounded_closure[intro]:
  assumes "bounded S"
  shows "bounded (closure S)"
proof -
  from assms obtain x and a where a: "\<forall>y\<in>S. dist x y \<le> a"
    unfolding bounded_def by auto
  {
    fix y
    assume "y \<in> closure S"
    then obtain f where f: "\<forall>n. f n \<in> S"  "(f \<longlongrightarrow> y) sequentially"
      unfolding closure_sequential by auto
    have "\<forall>n. f n \<in> S \<longrightarrow> dist x (f n) \<le> a" using a by simp
    then have "eventually (\<lambda>n. dist x (f n) \<le> a) sequentially"
      by (simp add: f(1))
    have "dist x y \<le> a"
      apply (rule Lim_dist_ubound [of sequentially f])
      apply (rule trivial_limit_sequentially)
      apply (rule f(2))
      apply fact
      done
  }
  then show ?thesis
    unfolding bounded_def by auto
qed

lemma bounded_closure_image: "bounded (f ` closure S) \<Longrightarrow> bounded (f ` S)"
  by (simp add: bounded_subset closure_subset image_mono)

lemma bounded_cball[simp,intro]: "bounded (cball x e)"
  apply (simp add: bounded_def)
  apply (rule_tac x=x in exI)
  apply (rule_tac x=e in exI, auto)
  done

lemma bounded_ball[simp,intro]: "bounded (ball x e)"
  by (metis ball_subset_cball bounded_cball bounded_subset)

lemma bounded_Un[simp]: "bounded (S \<union> T) \<longleftrightarrow> bounded S \<and> bounded T"
  by (auto simp: bounded_def) (metis Un_iff bounded_any_center le_max_iff_disj)

lemma bounded_Union[intro]: "finite F \<Longrightarrow> \<forall>S\<in>F. bounded S \<Longrightarrow> bounded (\<Union>F)"
  by (induct rule: finite_induct[of F]) auto

lemma bounded_UN [intro]: "finite A \<Longrightarrow> \<forall>x\<in>A. bounded (B x) \<Longrightarrow> bounded (\<Union>x\<in>A. B x)"
  by (induct set: finite) auto

lemma bounded_insert [simp]: "bounded (insert x S) \<longleftrightarrow> bounded S"
proof -
  have "\<forall>y\<in>{x}. dist x y \<le> 0"
    by simp
  then have "bounded {x}"
    unfolding bounded_def by fast
  then show ?thesis
    by (metis insert_is_Un bounded_Un)
qed

lemma bounded_subset_ballI: "S \<subseteq> ball x r \<Longrightarrow> bounded S"
  by (meson bounded_ball bounded_subset)

lemma bounded_subset_ballD:
  assumes "bounded S" shows "\<exists>r. 0 < r \<and> S \<subseteq> ball x r"
proof -
  obtain e::real and y where "S \<subseteq> cball y e"  "0 \<le> e"
    using assms by (auto simp: bounded_subset_cball)
  then show ?thesis
    apply (rule_tac x="dist x y + e + 1" in exI)
    apply (simp add: add.commute add_pos_nonneg)
    apply (erule subset_trans)
    apply (clarsimp simp add: cball_def)
    by (metis add_le_cancel_right add_strict_increasing dist_commute dist_triangle_le zero_less_one)
qed

lemma finite_imp_bounded [intro]: "finite S \<Longrightarrow> bounded S"
  by (induct set: finite) simp_all

lemma bounded_pos: "bounded S \<longleftrightarrow> (\<exists>b>0. \<forall>x\<in> S. norm x \<le> b)"
  apply (simp add: bounded_iff)
  apply (subgoal_tac "\<And>x (y::real). 0 < 1 + \<bar>y\<bar> \<and> (x \<le> y \<longrightarrow> x \<le> 1 + \<bar>y\<bar>)")
  apply metis
  apply arith
  done

lemma bounded_pos_less: "bounded S \<longleftrightarrow> (\<exists>b>0. \<forall>x\<in> S. norm x < b)"
  apply (simp add: bounded_pos)
  apply (safe; rule_tac x="b+1" in exI; force)
  done

lemma Bseq_eq_bounded:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "Bseq f \<longleftrightarrow> bounded (range f)"
  unfolding Bseq_def bounded_pos by auto

lemma bounded_Int[intro]: "bounded S \<or> bounded T \<Longrightarrow> bounded (S \<inter> T)"
  by (metis Int_lower1 Int_lower2 bounded_subset)

lemma bounded_diff[intro]: "bounded S \<Longrightarrow> bounded (S - T)"
  by (metis Diff_subset bounded_subset)

lemma not_bounded_UNIV[simp]:
  "\<not> bounded (UNIV :: 'a::{real_normed_vector, perfect_space} set)"
proof (auto simp: bounded_pos not_le)
  obtain x :: 'a where "x \<noteq> 0"
    using perfect_choose_dist [OF zero_less_one] by fast
  fix b :: real
  assume b: "b >0"
  have b1: "b +1 \<ge> 0"
    using b by simp
  with \<open>x \<noteq> 0\<close> have "b < norm (scaleR (b + 1) (sgn x))"
    by (simp add: norm_sgn)
  then show "\<exists>x::'a. b < norm x" ..
qed

corollary cobounded_imp_unbounded:
    fixes S :: "'a::{real_normed_vector, perfect_space} set"
    shows "bounded (- S) \<Longrightarrow> \<not> bounded S"
  using bounded_Un [of S "-S"]  by (simp add: sup_compl_top)

lemma bounded_dist_comp:
  assumes "bounded (f ` S)" "bounded (g ` S)"
  shows "bounded ((\<lambda>x. dist (f x) (g x)) ` S)"
proof -
  from assms obtain M1 M2 where *: "dist (f x) undefined \<le> M1" "dist undefined (g x) \<le> M2" if "x \<in> S" for x
    by (auto simp: bounded_any_center[of _ undefined] dist_commute)
  have "dist (f x) (g x) \<le> M1 + M2" if "x \<in> S" for x
    using *[OF that]
    by (rule order_trans[OF dist_triangle add_mono])
  then show ?thesis
    by (auto intro!: boundedI)
qed

lemma bounded_linear_image:
  assumes "bounded S"
    and "bounded_linear f"
  shows "bounded (f ` S)"
proof -
  from assms(1) obtain b where "b > 0" and b: "\<forall>x\<in>S. norm x \<le> b"
    unfolding bounded_pos by auto
  from assms(2) obtain B where B: "B > 0" "\<forall>x. norm (f x) \<le> B * norm x"
    using bounded_linear.pos_bounded by (auto simp: ac_simps)
  show ?thesis
    unfolding bounded_pos
  proof (intro exI, safe)
    show "norm (f x) \<le> B * b" if "x \<in> S" for x
      by (meson B b less_imp_le mult_left_mono order_trans that)
  qed (use \<open>b > 0\<close> \<open>B > 0\<close> in auto)
qed

lemma bounded_scaling:
  fixes S :: "'a::real_normed_vector set"
  shows "bounded S \<Longrightarrow> bounded ((\<lambda>x. c *\<^sub>R x) ` S)"
  apply (rule bounded_linear_image, assumption)
  apply (rule bounded_linear_scaleR_right)
  done

lemma bounded_scaleR_comp:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes "bounded (f ` S)"
  shows "bounded ((\<lambda>x. r *\<^sub>R f x) ` S)"
  using bounded_scaling[of "f ` S" r] assms
  by (auto simp: image_image)

lemma bounded_translation:
  fixes S :: "'a::real_normed_vector set"
  assumes "bounded S"
  shows "bounded ((\<lambda>x. a + x) ` S)"
proof -
  from assms obtain b where b: "b > 0" "\<forall>x\<in>S. norm x \<le> b"
    unfolding bounded_pos by auto
  {
    fix x
    assume "x \<in> S"
    then have "norm (a + x) \<le> b + norm a"
      using norm_triangle_ineq[of a x] b by auto
  }
  then show ?thesis
    unfolding bounded_pos
    using norm_ge_zero[of a] b(1) and add_strict_increasing[of b 0 "norm a"]
    by (auto intro!: exI[of _ "b + norm a"])
qed

lemma bounded_translation_minus:
  fixes S :: "'a::real_normed_vector set"
  shows "bounded S \<Longrightarrow> bounded ((\<lambda>x. x - a) ` S)"
using bounded_translation [of S "-a"] by simp

lemma bounded_uminus [simp]:
  fixes X :: "'a::real_normed_vector set"
  shows "bounded (uminus ` X) \<longleftrightarrow> bounded X"
by (auto simp: bounded_def dist_norm; rule_tac x="-x" in exI; force simp: add.commute norm_minus_commute)

lemma uminus_bounded_comp [simp]:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  shows "bounded ((\<lambda>x. - f x) ` S) \<longleftrightarrow> bounded (f ` S)"
  using bounded_uminus[of "f ` S"]
  by (auto simp: image_image)

lemma bounded_plus_comp:
  fixes f g::"'a \<Rightarrow> 'b::real_normed_vector"
  assumes "bounded (f ` S)"
  assumes "bounded (g ` S)"
  shows "bounded ((\<lambda>x. f x + g x) ` S)"
proof -
  {
    fix B C
    assume "\<And>x. x\<in>S \<Longrightarrow> norm (f x) \<le> B" "\<And>x. x\<in>S \<Longrightarrow> norm (g x) \<le> C"
    then have "\<And>x. x \<in> S \<Longrightarrow> norm (f x + g x) \<le> B + C"
      by (auto intro!: norm_triangle_le add_mono)
  } then show ?thesis
    using assms by (fastforce simp: bounded_iff)
qed

lemma bounded_plus:
  fixes S ::"'a::real_normed_vector set"
  assumes "bounded S" "bounded T"
  shows "bounded ((\<lambda>(x,y). x + y) ` (S \<times> T))"
  using bounded_plus_comp [of fst "S \<times> T" snd] assms
  by (auto simp: split_def split: if_split_asm)

lemma bounded_minus_comp:
  "bounded (f ` S) \<Longrightarrow> bounded (g ` S) \<Longrightarrow> bounded ((\<lambda>x. f x - g x) ` S)"
  for f g::"'a \<Rightarrow> 'b::real_normed_vector"
  using bounded_plus_comp[of "f" S "\<lambda>x. - g x"]
  by auto

lemma bounded_minus:
  fixes S ::"'a::real_normed_vector set"
  assumes "bounded S" "bounded T"
  shows "bounded ((\<lambda>(x,y). x - y) ` (S \<times> T))"
  using bounded_minus_comp [of fst "S \<times> T" snd] assms
  by (auto simp: split_def split: if_split_asm)


subsection \<open>Compactness\<close>

subsubsection \<open>Bolzano-Weierstrass property\<close>

proposition Heine_Borel_imp_Bolzano_Weierstrass:
  assumes "compact s"
    and "infinite t"
    and "t \<subseteq> s"
  shows "\<exists>x \<in> s. x islimpt t"
proof (rule ccontr)
  assume "\<not> (\<exists>x \<in> s. x islimpt t)"
  then obtain f where f: "\<forall>x\<in>s. x \<in> f x \<and> open (f x) \<and> (\<forall>y\<in>t. y \<in> f x \<longrightarrow> y = x)"
    unfolding islimpt_def
    using bchoice[of s "\<lambda> x T. x \<in> T \<and> open T \<and> (\<forall>y\<in>t. y \<in> T \<longrightarrow> y = x)"]
    by auto
  obtain g where g: "g \<subseteq> {t. \<exists>x. x \<in> s \<and> t = f x}" "finite g" "s \<subseteq> \<Union>g"
    using assms(1)[unfolded compact_eq_Heine_Borel, THEN spec[where x="{t. \<exists>x. x\<in>s \<and> t = f x}"]]
    using f by auto
  from g(1,3) have g':"\<forall>x\<in>g. \<exists>xa \<in> s. x = f xa"
    by auto
  {
    fix x y
    assume "x \<in> t" "y \<in> t" "f x = f y"
    then have "x \<in> f x"  "y \<in> f x \<longrightarrow> y = x"
      using f[THEN bspec[where x=x]] and \<open>t \<subseteq> s\<close> by auto
    then have "x = y"
      using \<open>f x = f y\<close> and f[THEN bspec[where x=y]] and \<open>y \<in> t\<close> and \<open>t \<subseteq> s\<close>
      by auto
  }
  then have "inj_on f t"
    unfolding inj_on_def by simp
  then have "infinite (f ` t)"
    using assms(2) using finite_imageD by auto
  moreover
  {
    fix x
    assume "x \<in> t" "f x \<notin> g"
    from g(3) assms(3) \<open>x \<in> t\<close> obtain h where "h \<in> g" and "x \<in> h"
      by auto
    then obtain y where "y \<in> s" "h = f y"
      using g'[THEN bspec[where x=h]] by auto
    then have "y = x"
      using f[THEN bspec[where x=y]] and \<open>x\<in>t\<close> and \<open>x\<in>h\<close>[unfolded \<open>h = f y\<close>]
      by auto
    then have False
      using \<open>f x \<notin> g\<close> \<open>h \<in> g\<close> unfolding \<open>h = f y\<close>
      by auto
  }
  then have "f ` t \<subseteq> g" by auto
  ultimately show False
    using g(2) using finite_subset by auto
qed

lemma acc_point_range_imp_convergent_subsequence:
  fixes l :: "'a :: first_countable_topology"
  assumes l: "\<forall>U. l\<in>U \<longrightarrow> open U \<longrightarrow> infinite (U \<inter> range f)"
  shows "\<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
proof -
  from countable_basis_at_decseq[of l]
  obtain A where A:
      "\<And>i. open (A i)"
      "\<And>i. l \<in> A i"
      "\<And>S. open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
    by blast
  define s where "s n i = (SOME j. i < j \<and> f j \<in> A (Suc n))" for n i
  {
    fix n i
    have "infinite (A (Suc n) \<inter> range f - f`{.. i})"
      using l A by auto
    then have "\<exists>x. x \<in> A (Suc n) \<inter> range f - f`{.. i}"
      unfolding ex_in_conv by (intro notI) simp
    then have "\<exists>j. f j \<in> A (Suc n) \<and> j \<notin> {.. i}"
      by auto
    then have "\<exists>a. i < a \<and> f a \<in> A (Suc n)"
      by (auto simp: not_le)
    then have "i < s n i" "f (s n i) \<in> A (Suc n)"
      unfolding s_def by (auto intro: someI2_ex)
  }
  note s = this
  define r where "r = rec_nat (s 0 0) s"
  have "strict_mono r"
    by (auto simp: r_def s strict_mono_Suc_iff)
  moreover
  have "(\<lambda>n. f (r n)) \<longlonglongrightarrow> l"
  proof (rule topological_tendstoI)
    fix S
    assume "open S" "l \<in> S"
    with A(3) have "eventually (\<lambda>i. A i \<subseteq> S) sequentially"
      by auto
    moreover
    {
      fix i
      assume "Suc 0 \<le> i"
      then have "f (r i) \<in> A i"
        by (cases i) (simp_all add: r_def s)
    }
    then have "eventually (\<lambda>i. f (r i) \<in> A i) sequentially"
      by (auto simp: eventually_sequentially)
    ultimately show "eventually (\<lambda>i. f (r i) \<in> S) sequentially"
      by eventually_elim auto
  qed
  ultimately show "\<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
    by (auto simp: convergent_def comp_def)
qed

lemma sequence_infinite_lemma:
  fixes f :: "nat \<Rightarrow> 'a::t1_space"
  assumes "\<forall>n. f n \<noteq> l"
    and "(f \<longlongrightarrow> l) sequentially"
  shows "infinite (range f)"
proof
  assume "finite (range f)"
  then have "closed (range f)"
    by (rule finite_imp_closed)
  then have "open (- range f)"
    by (rule open_Compl)
  from assms(1) have "l \<in> - range f"
    by auto
  from assms(2) have "eventually (\<lambda>n. f n \<in> - range f) sequentially"
    using \<open>open (- range f)\<close> \<open>l \<in> - range f\<close>
    by (rule topological_tendstoD)
  then show False
    unfolding eventually_sequentially
    by auto
qed

lemma closure_insert:
  fixes x :: "'a::t1_space"
  shows "closure (insert x s) = insert x (closure s)"
  apply (rule closure_unique)
  apply (rule insert_mono [OF closure_subset])
  apply (rule closed_insert [OF closed_closure])
  apply (simp add: closure_minimal)
  done

lemma islimpt_insert:
  fixes x :: "'a::t1_space"
  shows "x islimpt (insert a s) \<longleftrightarrow> x islimpt s"
proof
  assume *: "x islimpt (insert a s)"
  show "x islimpt s"
  proof (rule islimptI)
    fix t
    assume t: "x \<in> t" "open t"
    show "\<exists>y\<in>s. y \<in> t \<and> y \<noteq> x"
    proof (cases "x = a")
      case True
      obtain y where "y \<in> insert a s" "y \<in> t" "y \<noteq> x"
        using * t by (rule islimptE)
      with \<open>x = a\<close> show ?thesis by auto
    next
      case False
      with t have t': "x \<in> t - {a}" "open (t - {a})"
        by (simp_all add: open_Diff)
      obtain y where "y \<in> insert a s" "y \<in> t - {a}" "y \<noteq> x"
        using * t' by (rule islimptE)
      then show ?thesis by auto
    qed
  qed
next
  assume "x islimpt s"
  then show "x islimpt (insert a s)"
    by (rule islimpt_subset) auto
qed

lemma islimpt_finite:
  fixes x :: "'a::t1_space"
  shows "finite s \<Longrightarrow> \<not> x islimpt s"
  by (induct set: finite) (simp_all add: islimpt_insert)

lemma islimpt_Un_finite:
  fixes x :: "'a::t1_space"
  shows "finite s \<Longrightarrow> x islimpt (s \<union> t) \<longleftrightarrow> x islimpt t"
  by (simp add: islimpt_Un islimpt_finite)

lemma islimpt_eq_acc_point:
  fixes l :: "'a :: t1_space"
  shows "l islimpt S \<longleftrightarrow> (\<forall>U. l\<in>U \<longrightarrow> open U \<longrightarrow> infinite (U \<inter> S))"
proof (safe intro!: islimptI)
  fix U
  assume "l islimpt S" "l \<in> U" "open U" "finite (U \<inter> S)"
  then have "l islimpt S" "l \<in> (U - (U \<inter> S - {l}))" "open (U - (U \<inter> S - {l}))"
    by (auto intro: finite_imp_closed)
  then show False
    by (rule islimptE) auto
next
  fix T
  assume *: "\<forall>U. l\<in>U \<longrightarrow> open U \<longrightarrow> infinite (U \<inter> S)" "l \<in> T" "open T"
  then have "infinite (T \<inter> S - {l})"
    by auto
  then have "\<exists>x. x \<in> (T \<inter> S - {l})"
    unfolding ex_in_conv by (intro notI) simp
  then show "\<exists>y\<in>S. y \<in> T \<and> y \<noteq> l"
    by auto
qed

corollary infinite_openin:
  fixes S :: "'a :: t1_space set"
  shows "\<lbrakk>openin (subtopology euclidean U) S; x \<in> S; x islimpt U\<rbrakk> \<Longrightarrow> infinite S"
  by (clarsimp simp add: openin_open islimpt_eq_acc_point inf_commute)

lemma islimpt_range_imp_convergent_subsequence:
  fixes l :: "'a :: {t1_space, first_countable_topology}"
  assumes l: "l islimpt (range f)"
  shows "\<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
  using l unfolding islimpt_eq_acc_point
  by (rule acc_point_range_imp_convergent_subsequence)

lemma islimpt_eq_infinite_ball: "x islimpt S \<longleftrightarrow> (\<forall>e>0. infinite(S \<inter> ball x e))"
  apply (simp add: islimpt_eq_acc_point, safe)
   apply (metis Int_commute open_ball centre_in_ball)
  by (metis open_contains_ball Int_mono finite_subset inf_commute subset_refl)

lemma islimpt_eq_infinite_cball: "x islimpt S \<longleftrightarrow> (\<forall>e>0. infinite(S \<inter> cball x e))"
  apply (simp add: islimpt_eq_infinite_ball, safe)
   apply (meson Int_mono ball_subset_cball finite_subset order_refl)
  by (metis open_ball centre_in_ball finite_Int inf.absorb_iff2 inf_assoc open_contains_cball_eq)

lemma sequence_unique_limpt:
  fixes f :: "nat \<Rightarrow> 'a::t2_space"
  assumes "(f \<longlongrightarrow> l) sequentially"
    and "l' islimpt (range f)"
  shows "l' = l"
proof (rule ccontr)
  assume "l' \<noteq> l"
  obtain s t where "open s" "open t" "l' \<in> s" "l \<in> t" "s \<inter> t = {}"
    using hausdorff [OF \<open>l' \<noteq> l\<close>] by auto
  have "eventually (\<lambda>n. f n \<in> t) sequentially"
    using assms(1) \<open>open t\<close> \<open>l \<in> t\<close> by (rule topological_tendstoD)
  then obtain N where "\<forall>n\<ge>N. f n \<in> t"
    unfolding eventually_sequentially by auto

  have "UNIV = {..<N} \<union> {N..}"
    by auto
  then have "l' islimpt (f ` ({..<N} \<union> {N..}))"
    using assms(2) by simp
  then have "l' islimpt (f ` {..<N} \<union> f ` {N..})"
    by (simp add: image_Un)
  then have "l' islimpt (f ` {N..})"
    by (simp add: islimpt_Un_finite)
  then obtain y where "y \<in> f ` {N..}" "y \<in> s" "y \<noteq> l'"
    using \<open>l' \<in> s\<close> \<open>open s\<close> by (rule islimptE)
  then obtain n where "N \<le> n" "f n \<in> s" "f n \<noteq> l'"
    by auto
  with \<open>\<forall>n\<ge>N. f n \<in> t\<close> have "f n \<in> s \<inter> t"
    by simp
  with \<open>s \<inter> t = {}\<close> show False
    by simp
qed

lemma Bolzano_Weierstrass_imp_closed:
  fixes s :: "'a::{first_countable_topology,t2_space} set"
  assumes "\<forall>t. infinite t \<and> t \<subseteq> s --> (\<exists>x \<in> s. x islimpt t)"
  shows "closed s"
proof -
  {
    fix x l
    assume as: "\<forall>n::nat. x n \<in> s" "(x \<longlongrightarrow> l) sequentially"
    then have "l \<in> s"
    proof (cases "\<forall>n. x n \<noteq> l")
      case False
      then show "l\<in>s" using as(1) by auto
    next
      case True note cas = this
      with as(2) have "infinite (range x)"
        using sequence_infinite_lemma[of x l] by auto
      then obtain l' where "l'\<in>s" "l' islimpt (range x)"
        using assms[THEN spec[where x="range x"]] as(1) by auto
      then show "l\<in>s" using sequence_unique_limpt[of x l l']
        using as cas by auto
    qed
  }
  then show ?thesis
    unfolding closed_sequential_limits by fast
qed

lemma compact_imp_bounded:
  assumes "compact U"
  shows "bounded U"
proof -
  have "compact U" "\<forall>x\<in>U. open (ball x 1)" "U \<subseteq> (\<Union>x\<in>U. ball x 1)"
    using assms by auto
  then obtain D where D: "D \<subseteq> U" "finite D" "U \<subseteq> (\<Union>x\<in>D. ball x 1)"
    by (metis compactE_image)
  from \<open>finite D\<close> have "bounded (\<Union>x\<in>D. ball x 1)"
    by (simp add: bounded_UN)
  then show "bounded U" using \<open>U \<subseteq> (\<Union>x\<in>D. ball x 1)\<close>
    by (rule bounded_subset)
qed

text\<open>In particular, some common special cases.\<close>

lemma compact_Un [intro]:
  assumes "compact s"
    and "compact t"
  shows " compact (s \<union> t)"
proof (rule compactI)
  fix f
  assume *: "Ball f open" "s \<union> t \<subseteq> \<Union>f"
  from * \<open>compact s\<close> obtain s' where "s' \<subseteq> f \<and> finite s' \<and> s \<subseteq> \<Union>s'"
    unfolding compact_eq_Heine_Borel by (auto elim!: allE[of _ f])
  moreover
  from * \<open>compact t\<close> obtain t' where "t' \<subseteq> f \<and> finite t' \<and> t \<subseteq> \<Union>t'"
    unfolding compact_eq_Heine_Borel by (auto elim!: allE[of _ f])
  ultimately show "\<exists>f'\<subseteq>f. finite f' \<and> s \<union> t \<subseteq> \<Union>f'"
    by (auto intro!: exI[of _ "s' \<union> t'"])
qed

lemma compact_Union [intro]: "finite S \<Longrightarrow> (\<And>T. T \<in> S \<Longrightarrow> compact T) \<Longrightarrow> compact (\<Union>S)"
  by (induct set: finite) auto

lemma compact_UN [intro]:
  "finite A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> compact (B x)) \<Longrightarrow> compact (\<Union>x\<in>A. B x)"
  by (rule compact_Union) auto

lemma closed_Int_compact [intro]:
  assumes "closed s"
    and "compact t"
  shows "compact (s \<inter> t)"
  using compact_Int_closed [of t s] assms
  by (simp add: Int_commute)

lemma compact_Int [intro]:
  fixes s t :: "'a :: t2_space set"
  assumes "compact s"
    and "compact t"
  shows "compact (s \<inter> t)"
  using assms by (intro compact_Int_closed compact_imp_closed)

lemma compact_sing [simp]: "compact {a}"
  unfolding compact_eq_Heine_Borel by auto

lemma compact_insert [simp]:
  assumes "compact s"
  shows "compact (insert x s)"
proof -
  have "compact ({x} \<union> s)"
    using compact_sing assms by (rule compact_Un)
  then show ?thesis by simp
qed

lemma finite_imp_compact: "finite s \<Longrightarrow> compact s"
  by (induct set: finite) simp_all

lemma open_delete:
  fixes s :: "'a::t1_space set"
  shows "open s \<Longrightarrow> open (s - {x})"
  by (simp add: open_Diff)

lemma openin_delete:
  fixes a :: "'a :: t1_space"
  shows "openin (subtopology euclidean u) s
         \<Longrightarrow> openin (subtopology euclidean u) (s - {a})"
by (metis Int_Diff open_delete openin_open)

text\<open>Compactness expressed with filters\<close>

lemma closure_iff_nhds_not_empty:
  "x \<in> closure X \<longleftrightarrow> (\<forall>A. \<forall>S\<subseteq>A. open S \<longrightarrow> x \<in> S \<longrightarrow> X \<inter> A \<noteq> {})"
proof safe
  assume x: "x \<in> closure X"
  fix S A
  assume "open S" "x \<in> S" "X \<inter> A = {}" "S \<subseteq> A"
  then have "x \<notin> closure (-S)"
    by (auto simp: closure_complement subset_eq[symmetric] intro: interiorI)
  with x have "x \<in> closure X - closure (-S)"
    by auto
  also have "\<dots> \<subseteq> closure (X \<inter> S)"
    using \<open>open S\<close> open_Int_closure_subset[of S X] by (simp add: closed_Compl ac_simps)
  finally have "X \<inter> S \<noteq> {}" by auto
  then show False using \<open>X \<inter> A = {}\<close> \<open>S \<subseteq> A\<close> by auto
next
  assume "\<forall>A S. S \<subseteq> A \<longrightarrow> open S \<longrightarrow> x \<in> S \<longrightarrow> X \<inter> A \<noteq> {}"
  from this[THEN spec, of "- X", THEN spec, of "- closure X"]
  show "x \<in> closure X"
    by (simp add: closure_subset open_Compl)
qed

corollary closure_Int_ball_not_empty:
  assumes "S \<subseteq> closure T" "x \<in> S" "r > 0"
  shows "T \<inter> ball x r \<noteq> {}"
  using assms centre_in_ball closure_iff_nhds_not_empty by blast

lemma compact_filter:
  "compact U \<longleftrightarrow> (\<forall>F. F \<noteq> bot \<longrightarrow> eventually (\<lambda>x. x \<in> U) F \<longrightarrow> (\<exists>x\<in>U. inf (nhds x) F \<noteq> bot))"
proof (intro allI iffI impI compact_fip[THEN iffD2] notI)
  fix F
  assume "compact U"
  assume F: "F \<noteq> bot" "eventually (\<lambda>x. x \<in> U) F"
  then have "U \<noteq> {}"
    by (auto simp: eventually_False)

  define Z where "Z = closure ` {A. eventually (\<lambda>x. x \<in> A) F}"
  then have "\<forall>z\<in>Z. closed z"
    by auto
  moreover
  have ev_Z: "\<And>z. z \<in> Z \<Longrightarrow> eventually (\<lambda>x. x \<in> z) F"
    unfolding Z_def by (auto elim: eventually_mono intro: set_mp[OF closure_subset])
  have "(\<forall>B \<subseteq> Z. finite B \<longrightarrow> U \<inter> \<Inter>B \<noteq> {})"
  proof (intro allI impI)
    fix B assume "finite B" "B \<subseteq> Z"
    with \<open>finite B\<close> ev_Z F(2) have "eventually (\<lambda>x. x \<in> U \<inter> (\<Inter>B)) F"
      by (auto simp: eventually_ball_finite_distrib eventually_conj_iff)
    with F show "U \<inter> \<Inter>B \<noteq> {}"
      by (intro notI) (simp add: eventually_False)
  qed
  ultimately have "U \<inter> \<Inter>Z \<noteq> {}"
    using \<open>compact U\<close> unfolding compact_fip by blast
  then obtain x where "x \<in> U" and x: "\<And>z. z \<in> Z \<Longrightarrow> x \<in> z"
    by auto

  have "\<And>P. eventually P (inf (nhds x) F) \<Longrightarrow> P \<noteq> bot"
    unfolding eventually_inf eventually_nhds
  proof safe
    fix P Q R S
    assume "eventually R F" "open S" "x \<in> S"
    with open_Int_closure_eq_empty[of S "{x. R x}"] x[of "closure {x. R x}"]
    have "S \<inter> {x. R x} \<noteq> {}" by (auto simp: Z_def)
    moreover assume "Ball S Q" "\<forall>x. Q x \<and> R x \<longrightarrow> bot x"
    ultimately show False by (auto simp: set_eq_iff)
  qed
  with \<open>x \<in> U\<close> show "\<exists>x\<in>U. inf (nhds x) F \<noteq> bot"
    by (metis eventually_bot)
next
  fix A
  assume A: "\<forall>a\<in>A. closed a" "\<forall>B\<subseteq>A. finite B \<longrightarrow> U \<inter> \<Inter>B \<noteq> {}" "U \<inter> \<Inter>A = {}"
  define F where "F = (INF a\<in>insert U A. principal a)"
  have "F \<noteq> bot"
    unfolding F_def
  proof (rule INF_filter_not_bot)
    fix X
    assume X: "X \<subseteq> insert U A" "finite X"
    with A(2)[THEN spec, of "X - {U}"] have "U \<inter> \<Inter>(X - {U}) \<noteq> {}"
      by auto
    with X show "(INF a\<in>X. principal a) \<noteq> bot"
      by (auto simp: INF_principal_finite principal_eq_bot_iff)
  qed
  moreover
  have "F \<le> principal U"
    unfolding F_def by auto
  then have "eventually (\<lambda>x. x \<in> U) F"
    by (auto simp: le_filter_def eventually_principal)
  moreover
  assume "\<forall>F. F \<noteq> bot \<longrightarrow> eventually (\<lambda>x. x \<in> U) F \<longrightarrow> (\<exists>x\<in>U. inf (nhds x) F \<noteq> bot)"
  ultimately obtain x where "x \<in> U" and x: "inf (nhds x) F \<noteq> bot"
    by auto

  { fix V assume "V \<in> A"
    then have "F \<le> principal V"
      unfolding F_def by (intro INF_lower2[of V]) auto
    then have V: "eventually (\<lambda>x. x \<in> V) F"
      by (auto simp: le_filter_def eventually_principal)
    have "x \<in> closure V"
      unfolding closure_iff_nhds_not_empty
    proof (intro impI allI)
      fix S A
      assume "open S" "x \<in> S" "S \<subseteq> A"
      then have "eventually (\<lambda>x. x \<in> A) (nhds x)"
        by (auto simp: eventually_nhds)
      with V have "eventually (\<lambda>x. x \<in> V \<inter> A) (inf (nhds x) F)"
        by (auto simp: eventually_inf)
      with x show "V \<inter> A \<noteq> {}"
        by (auto simp del: Int_iff simp add: trivial_limit_def)
    qed
    then have "x \<in> V"
      using \<open>V \<in> A\<close> A(1) by simp
  }
  with \<open>x\<in>U\<close> have "x \<in> U \<inter> \<Inter>A" by auto
  with \<open>U \<inter> \<Inter>A = {}\<close> show False by auto
qed

definition%important "countably_compact U \<longleftrightarrow>
    (\<forall>A. countable A \<longrightarrow> (\<forall>a\<in>A. open a) \<longrightarrow> U \<subseteq> \<Union>A \<longrightarrow> (\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T))"

lemma countably_compactE:
  assumes "countably_compact s" and "\<forall>t\<in>C. open t" and "s \<subseteq> \<Union>C" "countable C"
  obtains C' where "C' \<subseteq> C" and "finite C'" and "s \<subseteq> \<Union>C'"
  using assms unfolding countably_compact_def by metis

lemma countably_compactI:
  assumes "\<And>C. \<forall>t\<in>C. open t \<Longrightarrow> s \<subseteq> \<Union>C \<Longrightarrow> countable C \<Longrightarrow> (\<exists>C'\<subseteq>C. finite C' \<and> s \<subseteq> \<Union>C')"
  shows "countably_compact s"
  using assms unfolding countably_compact_def by metis

lemma compact_imp_countably_compact: "compact U \<Longrightarrow> countably_compact U"
  by (auto simp: compact_eq_Heine_Borel countably_compact_def)

lemma countably_compact_imp_compact:
  assumes "countably_compact U"
    and ccover: "countable B" "\<forall>b\<in>B. open b"
    and basis: "\<And>T x. open T \<Longrightarrow> x \<in> T \<Longrightarrow> x \<in> U \<Longrightarrow> \<exists>b\<in>B. x \<in> b \<and> b \<inter> U \<subseteq> T"
  shows "compact U"
  using \<open>countably_compact U\<close>
  unfolding compact_eq_Heine_Borel countably_compact_def
proof safe
  fix A
  assume A: "\<forall>a\<in>A. open a" "U \<subseteq> \<Union>A"
  assume *: "\<forall>A. countable A \<longrightarrow> (\<forall>a\<in>A. open a) \<longrightarrow> U \<subseteq> \<Union>A \<longrightarrow> (\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T)"
  moreover define C where "C = {b\<in>B. \<exists>a\<in>A. b \<inter> U \<subseteq> a}"
  ultimately have "countable C" "\<forall>a\<in>C. open a"
    unfolding C_def using ccover by auto
  moreover
  have "\<Union>A \<inter> U \<subseteq> \<Union>C"
  proof safe
    fix x a
    assume "x \<in> U" "x \<in> a" "a \<in> A"
    with basis[of a x] A obtain b where "b \<in> B" "x \<in> b" "b \<inter> U \<subseteq> a"
      by blast
    with \<open>a \<in> A\<close> show "x \<in> \<Union>C"
      unfolding C_def by auto
  qed
  then have "U \<subseteq> \<Union>C" using \<open>U \<subseteq> \<Union>A\<close> by auto
  ultimately obtain T where T: "T\<subseteq>C" "finite T" "U \<subseteq> \<Union>T"
    using * by metis
  then have "\<forall>t\<in>T. \<exists>a\<in>A. t \<inter> U \<subseteq> a"
    by (auto simp: C_def)
  then obtain f where "\<forall>t\<in>T. f t \<in> A \<and> t \<inter> U \<subseteq> f t"
    unfolding bchoice_iff Bex_def ..
  with T show "\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T"
    unfolding C_def by (intro exI[of _ "f`T"]) fastforce
qed

proposition countably_compact_imp_compact_second_countable:
  "countably_compact U \<Longrightarrow> compact (U :: 'a :: second_countable_topology set)"
proof (rule countably_compact_imp_compact)
  fix T and x :: 'a
  assume "open T" "x \<in> T"
  from topological_basisE[OF is_basis this] obtain b where
    "b \<in> (SOME B. countable B \<and> topological_basis B)" "x \<in> b" "b \<subseteq> T" .
  then show "\<exists>b\<in>SOME B. countable B \<and> topological_basis B. x \<in> b \<and> b \<inter> U \<subseteq> T"
    by blast
qed (insert countable_basis topological_basis_open[OF is_basis], auto)

lemma countably_compact_eq_compact:
  "countably_compact U \<longleftrightarrow> compact (U :: 'a :: second_countable_topology set)"
  using countably_compact_imp_compact_second_countable compact_imp_countably_compact by blast

subsubsection\<open>Sequential compactness\<close>

definition%important seq_compact :: "'a::topological_space set \<Rightarrow> bool"
  where "seq_compact S \<longleftrightarrow>
    (\<forall>f. (\<forall>n. f n \<in> S) \<longrightarrow> (\<exists>l\<in>S. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially))"

lemma seq_compactI:
  assumes "\<And>f. \<forall>n. f n \<in> S \<Longrightarrow> \<exists>l\<in>S. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
  shows "seq_compact S"
  unfolding seq_compact_def using assms by fast

lemma seq_compactE:
  assumes "seq_compact S" "\<forall>n. f n \<in> S"
  obtains l r where "l \<in> S" "strict_mono (r :: nat \<Rightarrow> nat)" "((f \<circ> r) \<longlongrightarrow> l) sequentially"
  using assms unfolding seq_compact_def by fast

lemma closed_sequentially: (* TODO: move upwards *)
  assumes "closed s" and "\<forall>n. f n \<in> s" and "f \<longlonglongrightarrow> l"
  shows "l \<in> s"
proof (rule ccontr)
  assume "l \<notin> s"
  with \<open>closed s\<close> and \<open>f \<longlonglongrightarrow> l\<close> have "eventually (\<lambda>n. f n \<in> - s) sequentially"
    by (fast intro: topological_tendstoD)
  with \<open>\<forall>n. f n \<in> s\<close> show "False"
    by simp
qed

lemma seq_compact_Int_closed:
  assumes "seq_compact s" and "closed t"
  shows "seq_compact (s \<inter> t)"
proof (rule seq_compactI)
  fix f assume "\<forall>n::nat. f n \<in> s \<inter> t"
  hence "\<forall>n. f n \<in> s" and "\<forall>n. f n \<in> t"
    by simp_all
  from \<open>seq_compact s\<close> and \<open>\<forall>n. f n \<in> s\<close>
  obtain l r where "l \<in> s" and r: "strict_mono r" and l: "(f \<circ> r) \<longlonglongrightarrow> l"
    by (rule seq_compactE)
  from \<open>\<forall>n. f n \<in> t\<close> have "\<forall>n. (f \<circ> r) n \<in> t"
    by simp
  from \<open>closed t\<close> and this and l have "l \<in> t"
    by (rule closed_sequentially)
  with \<open>l \<in> s\<close> and r and l show "\<exists>l\<in>s \<inter> t. \<exists>r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
    by fast
qed

lemma seq_compact_closed_subset:
  assumes "closed s" and "s \<subseteq> t" and "seq_compact t"
  shows "seq_compact s"
  using assms seq_compact_Int_closed [of t s] by (simp add: Int_absorb1)

lemma seq_compact_imp_countably_compact:
  fixes U :: "'a :: first_countable_topology set"
  assumes "seq_compact U"
  shows "countably_compact U"
proof (safe intro!: countably_compactI)
  fix A
  assume A: "\<forall>a\<in>A. open a" "U \<subseteq> \<Union>A" "countable A"
  have subseq: "\<And>X. range X \<subseteq> U \<Longrightarrow> \<exists>r x. x \<in> U \<and> strict_mono (r :: nat \<Rightarrow> nat) \<and> (X \<circ> r) \<longlonglongrightarrow> x"
    using \<open>seq_compact U\<close> by (fastforce simp: seq_compact_def subset_eq)
  show "\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T"
  proof cases
    assume "finite A"
    with A show ?thesis by auto
  next
    assume "infinite A"
    then have "A \<noteq> {}" by auto
    show ?thesis
    proof (rule ccontr)
      assume "\<not> (\<exists>T\<subseteq>A. finite T \<and> U \<subseteq> \<Union>T)"
      then have "\<forall>T. \<exists>x. T \<subseteq> A \<and> finite T \<longrightarrow> (x \<in> U - \<Union>T)"
        by auto
      then obtain X' where T: "\<And>T. T \<subseteq> A \<Longrightarrow> finite T \<Longrightarrow> X' T \<in> U - \<Union>T"
        by metis
      define X where "X n = X' (from_nat_into A ` {.. n})" for n
      have X: "\<And>n. X n \<in> U - (\<Union>i\<le>n. from_nat_into A i)"
        using \<open>A \<noteq> {}\<close> unfolding X_def by (intro T) (auto intro: from_nat_into)
      then have "range X \<subseteq> U"
        by auto
      with subseq[of X] obtain r x where "x \<in> U" and r: "strict_mono r" "(X \<circ> r) \<longlonglongrightarrow> x"
        by auto
      from \<open>x\<in>U\<close> \<open>U \<subseteq> \<Union>A\<close> from_nat_into_surj[OF \<open>countable A\<close>]
      obtain n where "x \<in> from_nat_into A n" by auto
      with r(2) A(1) from_nat_into[OF \<open>A \<noteq> {}\<close>, of n]
      have "eventually (\<lambda>i. X (r i) \<in> from_nat_into A n) sequentially"
        unfolding tendsto_def by (auto simp: comp_def)
      then obtain N where "\<And>i. N \<le> i \<Longrightarrow> X (r i) \<in> from_nat_into A n"
        by (auto simp: eventually_sequentially)
      moreover from X have "\<And>i. n \<le> r i \<Longrightarrow> X (r i) \<notin> from_nat_into A n"
        by auto
      moreover from \<open>strict_mono r\<close>[THEN seq_suble, of "max n N"] have "\<exists>i. n \<le> r i \<and> N \<le> i"
        by (auto intro!: exI[of _ "max n N"])
      ultimately show False
        by auto
    qed
  qed
qed

lemma compact_imp_seq_compact:
  fixes U :: "'a :: first_countable_topology set"
  assumes "compact U"
  shows "seq_compact U"
  unfolding seq_compact_def
proof safe
  fix X :: "nat \<Rightarrow> 'a"
  assume "\<forall>n. X n \<in> U"
  then have "eventually (\<lambda>x. x \<in> U) (filtermap X sequentially)"
    by (auto simp: eventually_filtermap)
  moreover
  have "filtermap X sequentially \<noteq> bot"
    by (simp add: trivial_limit_def eventually_filtermap)
  ultimately
  obtain x where "x \<in> U" and x: "inf (nhds x) (filtermap X sequentially) \<noteq> bot" (is "?F \<noteq> _")
    using \<open>compact U\<close> by (auto simp: compact_filter)

  from countable_basis_at_decseq[of x]
  obtain A where A:
      "\<And>i. open (A i)"
      "\<And>i. x \<in> A i"
      "\<And>S. open S \<Longrightarrow> x \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
    by blast
  define s where "s n i = (SOME j. i < j \<and> X j \<in> A (Suc n))" for n i
  {
    fix n i
    have "\<exists>a. i < a \<and> X a \<in> A (Suc n)"
    proof (rule ccontr)
      assume "\<not> (\<exists>a>i. X a \<in> A (Suc n))"
      then have "\<And>a. Suc i \<le> a \<Longrightarrow> X a \<notin> A (Suc n)"
        by auto
      then have "eventually (\<lambda>x. x \<notin> A (Suc n)) (filtermap X sequentially)"
        by (auto simp: eventually_filtermap eventually_sequentially)
      moreover have "eventually (\<lambda>x. x \<in> A (Suc n)) (nhds x)"
        using A(1,2)[of "Suc n"] by (auto simp: eventually_nhds)
      ultimately have "eventually (\<lambda>x. False) ?F"
        by (auto simp: eventually_inf)
      with x show False
        by (simp add: eventually_False)
    qed
    then have "i < s n i" "X (s n i) \<in> A (Suc n)"
      unfolding s_def by (auto intro: someI2_ex)
  }
  note s = this
  define r where "r = rec_nat (s 0 0) s"
  have "strict_mono r"
    by (auto simp: r_def s strict_mono_Suc_iff)
  moreover
  have "(\<lambda>n. X (r n)) \<longlonglongrightarrow> x"
  proof (rule topological_tendstoI)
    fix S
    assume "open S" "x \<in> S"
    with A(3) have "eventually (\<lambda>i. A i \<subseteq> S) sequentially"
      by auto
    moreover
    {
      fix i
      assume "Suc 0 \<le> i"
      then have "X (r i) \<in> A i"
        by (cases i) (simp_all add: r_def s)
    }
    then have "eventually (\<lambda>i. X (r i) \<in> A i) sequentially"
      by (auto simp: eventually_sequentially)
    ultimately show "eventually (\<lambda>i. X (r i) \<in> S) sequentially"
      by eventually_elim auto
  qed
  ultimately show "\<exists>x \<in> U. \<exists>r. strict_mono r \<and> (X \<circ> r) \<longlonglongrightarrow> x"
    using \<open>x \<in> U\<close> by (auto simp: convergent_def comp_def)
qed

lemma countably_compact_imp_acc_point:
  assumes "countably_compact s"
    and "countable t"
    and "infinite t"
    and "t \<subseteq> s"
  shows "\<exists>x\<in>s. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> t)"
proof (rule ccontr)
  define C where "C = (\<lambda>F. interior (F \<union> (- t))) ` {F. finite F \<and> F \<subseteq> t }"
  note \<open>countably_compact s\<close>
  moreover have "\<forall>t\<in>C. open t"
    by (auto simp: C_def)
  moreover
  assume "\<not> (\<exists>x\<in>s. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> t))"
  then have s: "\<And>x. x \<in> s \<Longrightarrow> \<exists>U. x\<in>U \<and> open U \<and> finite (U \<inter> t)" by metis
  have "s \<subseteq> \<Union>C"
    using \<open>t \<subseteq> s\<close>
    unfolding C_def
    apply (safe dest!: s)
    apply (rule_tac a="U \<inter> t" in UN_I)
    apply (auto intro!: interiorI simp add: finite_subset)
    done
  moreover
  from \<open>countable t\<close> have "countable C"
    unfolding C_def by (auto intro: countable_Collect_finite_subset)
  ultimately
  obtain D where "D \<subseteq> C" "finite D" "s \<subseteq> \<Union>D"
    by (rule countably_compactE)
  then obtain E where E: "E \<subseteq> {F. finite F \<and> F \<subseteq> t }" "finite E"
    and s: "s \<subseteq> (\<Union>F\<in>E. interior (F \<union> (- t)))"
    by (metis (lifting) finite_subset_image C_def)
  from s \<open>t \<subseteq> s\<close> have "t \<subseteq> \<Union>E"
    using interior_subset by blast
  moreover have "finite (\<Union>E)"
    using E by auto
  ultimately show False using \<open>infinite t\<close>
    by (auto simp: finite_subset)
qed

lemma countable_acc_point_imp_seq_compact:
  fixes s :: "'a::first_countable_topology set"
  assumes "\<forall>t. infinite t \<and> countable t \<and> t \<subseteq> s \<longrightarrow>
    (\<exists>x\<in>s. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> t))"
  shows "seq_compact s"
proof -
  {
    fix f :: "nat \<Rightarrow> 'a"
    assume f: "\<forall>n. f n \<in> s"
    have "\<exists>l\<in>s. \<exists>r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    proof (cases "finite (range f)")
      case True
      obtain l where "infinite {n. f n = f l}"
        using pigeonhole_infinite[OF _ True] by auto
      then obtain r :: "nat \<Rightarrow> nat" where "strict_mono  r" and fr: "\<forall>n. f (r n) = f l"
        using infinite_enumerate by blast
      then have "strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> f l"
        by (simp add: fr o_def)
      with f show "\<exists>l\<in>s. \<exists>r. strict_mono  r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
        by auto
    next
      case False
      with f assms have "\<exists>x\<in>s. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> range f)"
        by auto
      then obtain l where "l \<in> s" "\<forall>U. l\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> range f)" ..
      from this(2) have "\<exists>r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
        using acc_point_range_imp_convergent_subsequence[of l f] by auto
      with \<open>l \<in> s\<close> show "\<exists>l\<in>s. \<exists>r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially" ..
    qed
  }
  then show ?thesis
    unfolding seq_compact_def by auto
qed

lemma seq_compact_eq_countably_compact:
  fixes U :: "'a :: first_countable_topology set"
  shows "seq_compact U \<longleftrightarrow> countably_compact U"
  using
    countable_acc_point_imp_seq_compact
    countably_compact_imp_acc_point
    seq_compact_imp_countably_compact
  by metis

lemma seq_compact_eq_acc_point:
  fixes s :: "'a :: first_countable_topology set"
  shows "seq_compact s \<longleftrightarrow>
    (\<forall>t. infinite t \<and> countable t \<and> t \<subseteq> s --> (\<exists>x\<in>s. \<forall>U. x\<in>U \<and> open U \<longrightarrow> infinite (U \<inter> t)))"
  using
    countable_acc_point_imp_seq_compact[of s]
    countably_compact_imp_acc_point[of s]
    seq_compact_imp_countably_compact[of s]
  by metis

lemma seq_compact_eq_compact:
  fixes U :: "'a :: second_countable_topology set"
  shows "seq_compact U \<longleftrightarrow> compact U"
  using seq_compact_eq_countably_compact countably_compact_eq_compact by blast

proposition Bolzano_Weierstrass_imp_seq_compact:
  fixes s :: "'a::{t1_space, first_countable_topology} set"
  shows "\<forall>t. infinite t \<and> t \<subseteq> s \<longrightarrow> (\<exists>x \<in> s. x islimpt t) \<Longrightarrow> seq_compact s"
  by (rule countable_acc_point_imp_seq_compact) (metis islimpt_eq_acc_point)


subsubsection\<open>Totally bounded\<close>

lemma cauchy_def: "Cauchy s \<longleftrightarrow> (\<forall>e>0. \<exists>N. \<forall>m n. m \<ge> N \<and> n \<ge> N \<longrightarrow> dist (s m) (s n) < e)"
  unfolding Cauchy_def by metis

proposition seq_compact_imp_totally_bounded:
  assumes "seq_compact s"
  shows "\<forall>e>0. \<exists>k. finite k \<and> k \<subseteq> s \<and> s \<subseteq> (\<Union>x\<in>k. ball x e)"
proof -
  { fix e::real assume "e > 0" assume *: "\<And>k. finite k \<Longrightarrow> k \<subseteq> s \<Longrightarrow> \<not> s \<subseteq> (\<Union>x\<in>k. ball x e)"
    let ?Q = "\<lambda>x n r. r \<in> s \<and> (\<forall>m < (n::nat). \<not> (dist (x m) r < e))"
    have "\<exists>x. \<forall>n::nat. ?Q x n (x n)"
    proof (rule dependent_wellorder_choice)
      fix n x assume "\<And>y. y < n \<Longrightarrow> ?Q x y (x y)"
      then have "\<not> s \<subseteq> (\<Union>x\<in>x ` {0..<n}. ball x e)"
        using *[of "x ` {0 ..< n}"] by (auto simp: subset_eq)
      then obtain z where z:"z\<in>s" "z \<notin> (\<Union>x\<in>x ` {0..<n}. ball x e)"
        unfolding subset_eq by auto
      show "\<exists>r. ?Q x n r"
        using z by auto
    qed simp
    then obtain x where "\<forall>n::nat. x n \<in> s" and x:"\<And>n m. m < n \<Longrightarrow> \<not> (dist (x m) (x n) < e)"
      by blast
    then obtain l r where "l \<in> s" and r:"strict_mono  r" and "((x \<circ> r) \<longlongrightarrow> l) sequentially"
      using assms by (metis seq_compact_def)
    from this(3) have "Cauchy (x \<circ> r)"
      using LIMSEQ_imp_Cauchy by auto
    then obtain N::nat where "\<And>m n. N \<le> m \<Longrightarrow> N \<le> n \<Longrightarrow> dist ((x \<circ> r) m) ((x \<circ> r) n) < e"
      unfolding cauchy_def using \<open>e > 0\<close> by blast
    then have False
      using x[of "r N" "r (N+1)"] r by (auto simp: strict_mono_def) }
  then show ?thesis
    by metis
qed

subsubsection\<open>Heine-Borel theorem\<close>

proposition seq_compact_imp_Heine_Borel:
  fixes s :: "'a :: metric_space set"
  assumes "seq_compact s"
  shows "compact s"
proof -
  from seq_compact_imp_totally_bounded[OF \<open>seq_compact s\<close>]
  obtain f where f: "\<forall>e>0. finite (f e) \<and> f e \<subseteq> s \<and> s \<subseteq> (\<Union>x\<in>f e. ball x e)"
    unfolding choice_iff' ..
  define K where "K = (\<lambda>(x, r). ball x r) ` ((\<Union>e \<in> \<rat> \<inter> {0 <..}. f e) \<times> \<rat>)"
  have "countably_compact s"
    using \<open>seq_compact s\<close> by (rule seq_compact_imp_countably_compact)
  then show "compact s"
  proof (rule countably_compact_imp_compact)
    show "countable K"
      unfolding K_def using f
      by (auto intro: countable_finite countable_subset countable_rat
               intro!: countable_image countable_SIGMA countable_UN)
    show "\<forall>b\<in>K. open b" by (auto simp: K_def)
  next
    fix T x
    assume T: "open T" "x \<in> T" and x: "x \<in> s"
    from openE[OF T] obtain e where "0 < e" "ball x e \<subseteq> T"
      by auto
    then have "0 < e / 2" "ball x (e / 2) \<subseteq> T"
      by auto
    from Rats_dense_in_real[OF \<open>0 < e / 2\<close>] obtain r where "r \<in> \<rat>" "0 < r" "r < e / 2"
      by auto
    from f[rule_format, of r] \<open>0 < r\<close> \<open>x \<in> s\<close> obtain k where "k \<in> f r" "x \<in> ball k r"
      by auto
    from \<open>r \<in> \<rat>\<close> \<open>0 < r\<close> \<open>k \<in> f r\<close> have "ball k r \<in> K"
      by (auto simp: K_def)
    then show "\<exists>b\<in>K. x \<in> b \<and> b \<inter> s \<subseteq> T"
    proof (rule bexI[rotated], safe)
      fix y
      assume "y \<in> ball k r"
      with \<open>r < e / 2\<close> \<open>x \<in> ball k r\<close> have "dist x y < e"
        by (intro dist_triangle_half_r [of k _ e]) (auto simp: dist_commute)
      with \<open>ball x e \<subseteq> T\<close> show "y \<in> T"
        by auto
    next
      show "x \<in> ball k r" by fact
    qed
  qed
qed

proposition compact_eq_seq_compact_metric:
  "compact (s :: 'a::metric_space set) \<longleftrightarrow> seq_compact s"
  using compact_imp_seq_compact seq_compact_imp_Heine_Borel by blast

proposition compact_def: \<comment> \<open>this is the definition of compactness in HOL Light\<close>
  "compact (S :: 'a::metric_space set) \<longleftrightarrow>
   (\<forall>f. (\<forall>n. f n \<in> S) \<longrightarrow> (\<exists>l\<in>S. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l))"
  unfolding compact_eq_seq_compact_metric seq_compact_def by auto

subsubsection \<open>Complete the chain of compactness variants\<close>

proposition compact_eq_Bolzano_Weierstrass:
  fixes s :: "'a::metric_space set"
  shows "compact s \<longleftrightarrow> (\<forall>t. infinite t \<and> t \<subseteq> s --> (\<exists>x \<in> s. x islimpt t))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using Heine_Borel_imp_Bolzano_Weierstrass[of s] by auto
next
  assume ?rhs
  then show ?lhs
    unfolding compact_eq_seq_compact_metric by (rule Bolzano_Weierstrass_imp_seq_compact)
qed

proposition Bolzano_Weierstrass_imp_bounded:
  "\<forall>t. infinite t \<and> t \<subseteq> s \<longrightarrow> (\<exists>x \<in> s. x islimpt t) \<Longrightarrow> bounded s"
  using compact_imp_bounded unfolding compact_eq_Bolzano_Weierstrass .


subsection \<open>Metric spaces with the Heine-Borel property\<close>

text \<open>
  A metric space (or topological vector space) is said to have the
  Heine-Borel property if every closed and bounded subset is compact.
\<close>

class heine_borel = metric_space +
  assumes bounded_imp_convergent_subsequence:
    "bounded (range f) \<Longrightarrow> \<exists>l r. strict_mono (r::nat\<Rightarrow>nat) \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"

proposition bounded_closed_imp_seq_compact:
  fixes s::"'a::heine_borel set"
  assumes "bounded s"
    and "closed s"
  shows "seq_compact s"
proof (unfold seq_compact_def, clarify)
  fix f :: "nat \<Rightarrow> 'a"
  assume f: "\<forall>n. f n \<in> s"
  with \<open>bounded s\<close> have "bounded (range f)"
    by (auto intro: bounded_subset)
  obtain l r where r: "strict_mono (r :: nat \<Rightarrow> nat)" and l: "((f \<circ> r) \<longlongrightarrow> l) sequentially"
    using bounded_imp_convergent_subsequence [OF \<open>bounded (range f)\<close>] by auto
  from f have fr: "\<forall>n. (f \<circ> r) n \<in> s"
    by simp
  have "l \<in> s" using \<open>closed s\<close> fr l
    by (rule closed_sequentially)
  show "\<exists>l\<in>s. \<exists>r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    using \<open>l \<in> s\<close> r l by blast
qed

lemma compact_eq_bounded_closed:
  fixes s :: "'a::heine_borel set"
  shows "compact s \<longleftrightarrow> bounded s \<and> closed s"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using compact_imp_closed compact_imp_bounded
    by blast
next
  assume ?rhs
  then show ?lhs
    using bounded_closed_imp_seq_compact[of s]
    unfolding compact_eq_seq_compact_metric
    by auto
qed

lemma compact_Inter:
  fixes \<F> :: "'a :: heine_borel set set"
  assumes com: "\<And>S. S \<in> \<F> \<Longrightarrow> compact S" and "\<F> \<noteq> {}"
  shows "compact(\<Inter> \<F>)"
  using assms
  by (meson Inf_lower all_not_in_conv bounded_subset closed_Inter compact_eq_bounded_closed)

lemma compact_closure [simp]:
  fixes S :: "'a::heine_borel set"
  shows "compact(closure S) \<longleftrightarrow> bounded S"
by (meson bounded_closure bounded_subset closed_closure closure_subset compact_eq_bounded_closed)

lemma not_compact_UNIV[simp]:
  fixes s :: "'a::{real_normed_vector,perfect_space,heine_borel} set"
  shows "\<not> compact (UNIV::'a set)"
    by (simp add: compact_eq_bounded_closed)

text\<open>Representing sets as the union of a chain of compact sets.\<close>
lemma closed_Union_compact_subsets:
  fixes S :: "'a::{heine_borel,real_normed_vector} set"
  assumes "closed S"
  obtains F where "\<And>n. compact(F n)" "\<And>n. F n \<subseteq> S" "\<And>n. F n \<subseteq> F(Suc n)"
                  "(\<Union>n. F n) = S" "\<And>K. \<lbrakk>compact K; K \<subseteq> S\<rbrakk> \<Longrightarrow> \<exists>N. \<forall>n \<ge> N. K \<subseteq> F n"
proof
  show "compact (S \<inter> cball 0 (of_nat n))" for n
    using assms compact_eq_bounded_closed by auto
next
  show "(\<Union>n. S \<inter> cball 0 (real n)) = S"
    by (auto simp: real_arch_simple)
next
  fix K :: "'a set"
  assume "compact K" "K \<subseteq> S"
  then obtain N where "K \<subseteq> cball 0 N"
    by (meson bounded_pos mem_cball_0 compact_imp_bounded subsetI)
  then show "\<exists>N. \<forall>n\<ge>N. K \<subseteq> S \<inter> cball 0 (real n)"
    by (metis of_nat_le_iff Int_subset_iff \<open>K \<subseteq> S\<close> real_arch_simple subset_cball subset_trans)
qed auto

instance%important real :: heine_borel
proof%unimportant
  fix f :: "nat \<Rightarrow> real"
  assume f: "bounded (range f)"
  obtain r :: "nat \<Rightarrow> nat" where r: "strict_mono r" "monoseq (f \<circ> r)"
    unfolding comp_def by (metis seq_monosub)
  then have "Bseq (f \<circ> r)"
    unfolding Bseq_eq_bounded using f by (force intro: bounded_subset)
  with r show "\<exists>l r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
    using Bseq_monoseq_convergent[of "f \<circ> r"] by (auto simp: convergent_def)
qed

lemma compact_lemma_general:
  fixes f :: "nat \<Rightarrow> 'a"
  fixes proj::"'a \<Rightarrow> 'b \<Rightarrow> 'c::heine_borel" (infixl "proj" 60)
  fixes unproj:: "('b \<Rightarrow> 'c) \<Rightarrow> 'a"
  assumes finite_basis: "finite basis"
  assumes bounded_proj: "\<And>k. k \<in> basis \<Longrightarrow> bounded ((\<lambda>x. x proj k) ` range f)"
  assumes proj_unproj: "\<And>e k. k \<in> basis \<Longrightarrow> (unproj e) proj k = e k"
  assumes unproj_proj: "\<And>x. unproj (\<lambda>k. x proj k) = x"
  shows "\<forall>d\<subseteq>basis. \<exists>l::'a. \<exists> r::nat\<Rightarrow>nat.
    strict_mono r \<and> (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) proj i) (l proj i) < e) sequentially)"
proof safe
  fix d :: "'b set"
  assume d: "d \<subseteq> basis"
  with finite_basis have "finite d"
    by (blast intro: finite_subset)
  from this d show "\<exists>l::'a. \<exists>r::nat\<Rightarrow>nat. strict_mono r \<and>
    (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) proj i) (l proj i) < e) sequentially)"
  proof (induct d)
    case empty
    then show ?case
      unfolding strict_mono_def by auto
  next
    case (insert k d)
    have k[intro]: "k \<in> basis"
      using insert by auto
    have s': "bounded ((\<lambda>x. x proj k) ` range f)"
      using k
      by (rule bounded_proj)
    obtain l1::"'a" and r1 where r1: "strict_mono r1"
      and lr1: "\<forall>e > 0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 n) proj i) (l1 proj i) < e) sequentially"
      using insert(3) using insert(4) by auto
    have f': "\<forall>n. f (r1 n) proj k \<in> (\<lambda>x. x proj k) ` range f"
      by simp
    have "bounded (range (\<lambda>i. f (r1 i) proj k))"
      by (metis (lifting) bounded_subset f' image_subsetI s')
    then obtain l2 r2 where r2:"strict_mono r2" and lr2:"((\<lambda>i. f (r1 (r2 i)) proj k) \<longlongrightarrow> l2) sequentially"
      using bounded_imp_convergent_subsequence[of "\<lambda>i. f (r1 i) proj k"]
      by (auto simp: o_def)
    define r where "r = r1 \<circ> r2"
    have r:"strict_mono r"
      using r1 and r2 unfolding r_def o_def strict_mono_def by auto
    moreover
    define l where "l = unproj (\<lambda>i. if i = k then l2 else l1 proj i)"
    {
      fix e::real
      assume "e > 0"
      from lr1 \<open>e > 0\<close> have N1: "eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 n) proj i) (l1 proj i) < e) sequentially"
        by blast
      from lr2 \<open>e > 0\<close> have N2:"eventually (\<lambda>n. dist (f (r1 (r2 n)) proj k) l2 < e) sequentially"
        by (rule tendstoD)
      from r2 N1 have N1': "eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r1 (r2 n)) proj i) (l1 proj i) < e) sequentially"
        by (rule eventually_subseq)
      have "eventually (\<lambda>n. \<forall>i\<in>(insert k d). dist (f (r n) proj i) (l proj i) < e) sequentially"
        using N1' N2
        by eventually_elim (insert insert.prems, auto simp: l_def r_def o_def proj_unproj)
    }
    ultimately show ?case by auto
  qed
qed

lemma bounded_fst: "bounded s \<Longrightarrow> bounded (fst ` s)"
  unfolding bounded_def
  by (metis (erased, hide_lams) dist_fst_le image_iff order_trans)

lemma bounded_snd: "bounded s \<Longrightarrow> bounded (snd ` s)"
  unfolding bounded_def
  by (metis (no_types, hide_lams) dist_snd_le image_iff order.trans)

instance%important prod :: (heine_borel, heine_borel) heine_borel
proof%unimportant
  fix f :: "nat \<Rightarrow> 'a \<times> 'b"
  assume f: "bounded (range f)"
  then have "bounded (fst ` range f)"
    by (rule bounded_fst)
  then have s1: "bounded (range (fst \<circ> f))"
    by (simp add: image_comp)
  obtain l1 r1 where r1: "strict_mono r1" and l1: "(\<lambda>n. fst (f (r1 n))) \<longlonglongrightarrow> l1"
    using bounded_imp_convergent_subsequence [OF s1] unfolding o_def by fast
  from f have s2: "bounded (range (snd \<circ> f \<circ> r1))"
    by (auto simp: image_comp intro: bounded_snd bounded_subset)
  obtain l2 r2 where r2: "strict_mono r2" and l2: "((\<lambda>n. snd (f (r1 (r2 n)))) \<longlongrightarrow> l2) sequentially"
    using bounded_imp_convergent_subsequence [OF s2]
    unfolding o_def by fast
  have l1': "((\<lambda>n. fst (f (r1 (r2 n)))) \<longlongrightarrow> l1) sequentially"
    using LIMSEQ_subseq_LIMSEQ [OF l1 r2] unfolding o_def .
  have l: "((f \<circ> (r1 \<circ> r2)) \<longlongrightarrow> (l1, l2)) sequentially"
    using tendsto_Pair [OF l1' l2] unfolding o_def by simp
  have r: "strict_mono (r1 \<circ> r2)"
    using r1 r2 unfolding strict_mono_def by simp
  show "\<exists>l r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    using l r by fast
qed

subsubsection \<open>Completeness\<close>

proposition (in metric_space) completeI:
  assumes "\<And>f. \<forall>n. f n \<in> s \<Longrightarrow> Cauchy f \<Longrightarrow> \<exists>l\<in>s. f \<longlonglongrightarrow> l"
  shows "complete s"
  using assms unfolding complete_def by fast

proposition (in metric_space) completeE:
  assumes "complete s" and "\<forall>n. f n \<in> s" and "Cauchy f"
  obtains l where "l \<in> s" and "f \<longlonglongrightarrow> l"
  using assms unfolding complete_def by fast

(* TODO: generalize to uniform spaces *)
lemma compact_imp_complete:
  fixes s :: "'a::metric_space set"
  assumes "compact s"
  shows "complete s"
proof -
  {
    fix f
    assume as: "(\<forall>n::nat. f n \<in> s)" "Cauchy f"
    from as(1) obtain l r where lr: "l\<in>s" "strict_mono r" "(f \<circ> r) \<longlonglongrightarrow> l"
      using assms unfolding compact_def by blast

    note lr' = seq_suble [OF lr(2)]
    {
      fix e :: real
      assume "e > 0"
      from as(2) obtain N where N:"\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (f m) (f n) < e/2"
        unfolding cauchy_def
        using \<open>e > 0\<close>
        apply (erule_tac x="e/2" in allE, auto)
        done
      from lr(3)[unfolded lim_sequentially, THEN spec[where x="e/2"]]
      obtain M where M:"\<forall>n\<ge>M. dist ((f \<circ> r) n) l < e/2"
        using \<open>e > 0\<close> by auto
      {
        fix n :: nat
        assume n: "n \<ge> max N M"
        have "dist ((f \<circ> r) n) l < e/2"
          using n M by auto
        moreover have "r n \<ge> N"
          using lr'[of n] n by auto
        then have "dist (f n) ((f \<circ> r) n) < e / 2"
          using N and n by auto
        ultimately have "dist (f n) l < e"
          using dist_triangle_half_r[of "f (r n)" "f n" e l]
          by (auto simp: dist_commute)
      }
      then have "\<exists>N. \<forall>n\<ge>N. dist (f n) l < e" by blast
    }
    then have "\<exists>l\<in>s. (f \<longlongrightarrow> l) sequentially" using \<open>l\<in>s\<close>
      unfolding lim_sequentially by auto
  }
  then show ?thesis unfolding complete_def by auto
qed

proposition compact_eq_totally_bounded:
  "compact s \<longleftrightarrow> complete s \<and> (\<forall>e>0. \<exists>k. finite k \<and> s \<subseteq> (\<Union>x\<in>k. ball x e))"
    (is "_ \<longleftrightarrow> ?rhs")
proof
  assume assms: "?rhs"
  then obtain k where k: "\<And>e. 0 < e \<Longrightarrow> finite (k e)" "\<And>e. 0 < e \<Longrightarrow> s \<subseteq> (\<Union>x\<in>k e. ball x e)"
    by (auto simp: choice_iff')

  show "compact s"
  proof cases
    assume "s = {}"
    then show "compact s" by (simp add: compact_def)
  next
    assume "s \<noteq> {}"
    show ?thesis
      unfolding compact_def
    proof safe
      fix f :: "nat \<Rightarrow> 'a"
      assume f: "\<forall>n. f n \<in> s"

      define e where "e n = 1 / (2 * Suc n)" for n
      then have [simp]: "\<And>n. 0 < e n" by auto
      define B where "B n U = (SOME b. infinite {n. f n \<in> b} \<and> (\<exists>x. b \<subseteq> ball x (e n) \<inter> U))" for n U
      {
        fix n U
        assume "infinite {n. f n \<in> U}"
        then have "\<exists>b\<in>k (e n). infinite {i\<in>{n. f n \<in> U}. f i \<in> ball b (e n)}"
          using k f by (intro pigeonhole_infinite_rel) (auto simp: subset_eq)
        then obtain a where
          "a \<in> k (e n)"
          "infinite {i \<in> {n. f n \<in> U}. f i \<in> ball a (e n)}" ..
        then have "\<exists>b. infinite {i. f i \<in> b} \<and> (\<exists>x. b \<subseteq> ball x (e n) \<inter> U)"
          by (intro exI[of _ "ball a (e n) \<inter> U"] exI[of _ a]) (auto simp: ac_simps)
        from someI_ex[OF this]
        have "infinite {i. f i \<in> B n U}" "\<exists>x. B n U \<subseteq> ball x (e n) \<inter> U"
          unfolding B_def by auto
      }
      note B = this

      define F where "F = rec_nat (B 0 UNIV) B"
      {
        fix n
        have "infinite {i. f i \<in> F n}"
          by (induct n) (auto simp: F_def B)
      }
      then have F: "\<And>n. \<exists>x. F (Suc n) \<subseteq> ball x (e n) \<inter> F n"
        using B by (simp add: F_def)
      then have F_dec: "\<And>m n. m \<le> n \<Longrightarrow> F n \<subseteq> F m"
        using decseq_SucI[of F] by (auto simp: decseq_def)

      obtain sel where sel: "\<And>k i. i < sel k i" "\<And>k i. f (sel k i) \<in> F k"
      proof (atomize_elim, unfold all_conj_distrib[symmetric], intro choice allI)
        fix k i
        have "infinite ({n. f n \<in> F k} - {.. i})"
          using \<open>infinite {n. f n \<in> F k}\<close> by auto
        from infinite_imp_nonempty[OF this]
        show "\<exists>x>i. f x \<in> F k"
          by (simp add: set_eq_iff not_le conj_commute)
      qed

      define t where "t = rec_nat (sel 0 0) (\<lambda>n i. sel (Suc n) i)"
      have "strict_mono t"
        unfolding strict_mono_Suc_iff by (simp add: t_def sel)
      moreover have "\<forall>i. (f \<circ> t) i \<in> s"
        using f by auto
      moreover
      {
        fix n
        have "(f \<circ> t) n \<in> F n"
          by (cases n) (simp_all add: t_def sel)
      }
      note t = this

      have "Cauchy (f \<circ> t)"
      proof (safe intro!: metric_CauchyI exI elim!: nat_approx_posE)
        fix r :: real and N n m
        assume "1 / Suc N < r" "Suc N \<le> n" "Suc N \<le> m"
        then have "(f \<circ> t) n \<in> F (Suc N)" "(f \<circ> t) m \<in> F (Suc N)" "2 * e N < r"
          using F_dec t by (auto simp: e_def field_simps of_nat_Suc)
        with F[of N] obtain x where "dist x ((f \<circ> t) n) < e N" "dist x ((f \<circ> t) m) < e N"
          by (auto simp: subset_eq)
        with dist_triangle[of "(f \<circ> t) m" "(f \<circ> t) n" x] \<open>2 * e N < r\<close>
        show "dist ((f \<circ> t) m) ((f \<circ> t) n) < r"
          by (simp add: dist_commute)
      qed

      ultimately show "\<exists>l\<in>s. \<exists>r. strict_mono r \<and> (f \<circ> r) \<longlonglongrightarrow> l"
        using assms unfolding complete_def by blast
    qed
  qed
qed (metis compact_imp_complete compact_imp_seq_compact seq_compact_imp_totally_bounded)

lemma cauchy_imp_bounded:
  assumes "Cauchy s"
  shows "bounded (range s)"
proof -
  from assms obtain N :: nat where "\<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (s m) (s n) < 1"
    unfolding cauchy_def by force
  then have N:"\<forall>n. N \<le> n \<longrightarrow> dist (s N) (s n) < 1" by auto
  moreover
  have "bounded (s ` {0..N})"
    using finite_imp_bounded[of "s ` {1..N}"] by auto
  then obtain a where a:"\<forall>x\<in>s ` {0..N}. dist (s N) x \<le> a"
    unfolding bounded_any_center [where a="s N"] by auto
  ultimately show "?thesis"
    unfolding bounded_any_center [where a="s N"]
    apply (rule_tac x="max a 1" in exI, auto)
    apply (erule_tac x=y in allE)
    apply (erule_tac x=y in ballE, auto)
    done
qed

instance heine_borel < complete_space
proof
  fix f :: "nat \<Rightarrow> 'a" assume "Cauchy f"
  then have "bounded (range f)"
    by (rule cauchy_imp_bounded)
  then have "compact (closure (range f))"
    unfolding compact_eq_bounded_closed by auto
  then have "complete (closure (range f))"
    by (rule compact_imp_complete)
  moreover have "\<forall>n. f n \<in> closure (range f)"
    using closure_subset [of "range f"] by auto
  ultimately have "\<exists>l\<in>closure (range f). (f \<longlongrightarrow> l) sequentially"
    using \<open>Cauchy f\<close> unfolding complete_def by auto
  then show "convergent f"
    unfolding convergent_def by auto
qed

lemma complete_UNIV: "complete (UNIV :: ('a::complete_space) set)"
proof (rule completeI)
  fix f :: "nat \<Rightarrow> 'a" assume "Cauchy f"
  then have "convergent f" by (rule Cauchy_convergent)
  then show "\<exists>l\<in>UNIV. f \<longlonglongrightarrow> l" unfolding convergent_def by simp
qed

lemma complete_imp_closed:
  fixes S :: "'a::metric_space set"
  assumes "complete S"
  shows "closed S"
proof (unfold closed_sequential_limits, clarify)
  fix f x assume "\<forall>n. f n \<in> S" and "f \<longlonglongrightarrow> x"
  from \<open>f \<longlonglongrightarrow> x\<close> have "Cauchy f"
    by (rule LIMSEQ_imp_Cauchy)
  with \<open>complete S\<close> and \<open>\<forall>n. f n \<in> S\<close> obtain l where "l \<in> S" and "f \<longlonglongrightarrow> l"
    by (rule completeE)
  from \<open>f \<longlonglongrightarrow> x\<close> and \<open>f \<longlonglongrightarrow> l\<close> have "x = l"
    by (rule LIMSEQ_unique)
  with \<open>l \<in> S\<close> show "x \<in> S"
    by simp
qed

lemma complete_Int_closed:
  fixes S :: "'a::metric_space set"
  assumes "complete S" and "closed t"
  shows "complete (S \<inter> t)"
proof (rule completeI)
  fix f assume "\<forall>n. f n \<in> S \<inter> t" and "Cauchy f"
  then have "\<forall>n. f n \<in> S" and "\<forall>n. f n \<in> t"
    by simp_all
  from \<open>complete S\<close> obtain l where "l \<in> S" and "f \<longlonglongrightarrow> l"
    using \<open>\<forall>n. f n \<in> S\<close> and \<open>Cauchy f\<close> by (rule completeE)
  from \<open>closed t\<close> and \<open>\<forall>n. f n \<in> t\<close> and \<open>f \<longlonglongrightarrow> l\<close> have "l \<in> t"
    by (rule closed_sequentially)
  with \<open>l \<in> S\<close> and \<open>f \<longlonglongrightarrow> l\<close> show "\<exists>l\<in>S \<inter> t. f \<longlonglongrightarrow> l"
    by fast
qed

lemma complete_closed_subset:
  fixes S :: "'a::metric_space set"
  assumes "closed S" and "S \<subseteq> t" and "complete t"
  shows "complete S"
  using assms complete_Int_closed [of t S] by (simp add: Int_absorb1)

lemma complete_eq_closed:
  fixes S :: "('a::complete_space) set"
  shows "complete S \<longleftrightarrow> closed S"
proof
  assume "closed S" then show "complete S"
    using subset_UNIV complete_UNIV by (rule complete_closed_subset)
next
  assume "complete S" then show "closed S"
    by (rule complete_imp_closed)
qed

lemma convergent_eq_Cauchy:
  fixes S :: "nat \<Rightarrow> 'a::complete_space"
  shows "(\<exists>l. (S \<longlongrightarrow> l) sequentially) \<longleftrightarrow> Cauchy S"
  unfolding Cauchy_convergent_iff convergent_def ..

lemma convergent_imp_bounded:
  fixes S :: "nat \<Rightarrow> 'a::metric_space"
  shows "(S \<longlongrightarrow> l) sequentially \<Longrightarrow> bounded (range S)"
  by (intro cauchy_imp_bounded LIMSEQ_imp_Cauchy)

lemma frontier_subset_compact:
  fixes S :: "'a::heine_borel set"
  shows "compact S \<Longrightarrow> frontier S \<subseteq> S"
  using frontier_subset_closed compact_eq_bounded_closed
  by blast

subsection \<open>Continuity\<close>

text\<open>Derive the epsilon-delta forms, which we often use as "definitions"\<close>

proposition continuous_within_eps_delta:
  "continuous (at x within s) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. \<forall>x'\<in> s.  dist x' x < d --> dist (f x') (f x) < e)"
  unfolding continuous_within and Lim_within  by fastforce

corollary continuous_at_eps_delta:
  "continuous (at x) f \<longleftrightarrow> (\<forall>e > 0. \<exists>d > 0. \<forall>x'. dist x' x < d \<longrightarrow> dist (f x') (f x) < e)"
  using continuous_within_eps_delta [of x UNIV f] by simp

lemma continuous_at_right_real_increasing:
  fixes f :: "real \<Rightarrow> real"
  assumes nondecF: "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y"
  shows "continuous (at_right a) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. f (a + d) - f a < e)"
  apply (simp add: greaterThan_def dist_real_def continuous_within Lim_within_le)
  apply (intro all_cong ex_cong, safe)
  apply (erule_tac x="a + d" in allE, simp)
  apply (simp add: nondecF field_simps)
  apply (drule nondecF, simp)
  done

lemma continuous_at_left_real_increasing:
  assumes nondecF: "\<And> x y. x \<le> y \<Longrightarrow> f x \<le> ((f y) :: real)"
  shows "(continuous (at_left (a :: real)) f) = (\<forall>e > 0. \<exists>delta > 0. f a - f (a - delta) < e)"
  apply (simp add: lessThan_def dist_real_def continuous_within Lim_within_le)
  apply (intro all_cong ex_cong, safe)
  apply (erule_tac x="a - d" in allE, simp)
  apply (simp add: nondecF field_simps)
  apply (cut_tac x="a - d" and y=x in nondecF, simp_all)
  done

text\<open>Versions in terms of open balls.\<close>

lemma continuous_within_ball:
  "continuous (at x within s) f \<longleftrightarrow>
    (\<forall>e > 0. \<exists>d > 0. f ` (ball x d \<inter> s) \<subseteq> ball (f x) e)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  {
    fix e :: real
    assume "e > 0"
    then obtain d where d: "d>0" "\<forall>xa\<in>s. 0 < dist xa x \<and> dist xa x < d \<longrightarrow> dist (f xa) (f x) < e"
      using \<open>?lhs\<close>[unfolded continuous_within Lim_within] by auto
    {
      fix y
      assume "y \<in> f ` (ball x d \<inter> s)"
      then have "y \<in> ball (f x) e"
        using d(2)
        apply (auto simp: dist_commute)
        apply (erule_tac x=xa in ballE, auto)
        using \<open>e > 0\<close>
        apply auto
        done
    }
    then have "\<exists>d>0. f ` (ball x d \<inter> s) \<subseteq> ball (f x) e"
      using \<open>d > 0\<close>
      unfolding subset_eq ball_def by (auto simp: dist_commute)
  }
  then show ?rhs by auto
next
  assume ?rhs
  then show ?lhs
    unfolding continuous_within Lim_within ball_def subset_eq
    apply (auto simp: dist_commute)
    apply (erule_tac x=e in allE, auto)
    done
qed

lemma continuous_at_ball:
  "continuous (at x) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. f ` (ball x d) \<subseteq> ball (f x) e)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding continuous_at Lim_at subset_eq Ball_def Bex_def image_iff mem_ball
    apply auto
    apply (erule_tac x=e in allE, auto)
    apply (rule_tac x=d in exI, auto)
    apply (erule_tac x=xa in allE)
    apply (auto simp: dist_commute)
    done
next
  assume ?rhs
  then show ?lhs
    unfolding continuous_at Lim_at subset_eq Ball_def Bex_def image_iff mem_ball
    apply auto
    apply (erule_tac x=e in allE, auto)
    apply (rule_tac x=d in exI, auto)
    apply (erule_tac x="f xa" in allE)
    apply (auto simp: dist_commute)
    done
qed

text\<open>Define setwise continuity in terms of limits within the set.\<close>

lemma continuous_on_iff:
  "continuous_on s f \<longleftrightarrow>
    (\<forall>x\<in>s. \<forall>e>0. \<exists>d>0. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e)"
  unfolding continuous_on_def Lim_within
  by (metis dist_pos_lt dist_self)

lemma continuous_within_E:
  assumes "continuous (at x within s) f" "e>0"
  obtains d where "d>0"  "\<And>x'. \<lbrakk>x'\<in> s; dist x' x \<le> d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
  using assms apply (simp add: continuous_within_eps_delta)
  apply (drule spec [of _ e], clarify)
  apply (rule_tac d="d/2" in that, auto)
  done

lemma continuous_onI [intro?]:
  assumes "\<And>x e. \<lbrakk>e > 0; x \<in> s\<rbrakk> \<Longrightarrow> \<exists>d>0. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) \<le> e"
  shows "continuous_on s f"
apply (simp add: continuous_on_iff, clarify)
apply (rule ex_forward [OF assms [OF half_gt_zero]], auto)
done

text\<open>Some simple consequential lemmas.\<close>

lemma continuous_onE:
    assumes "continuous_on s f" "x\<in>s" "e>0"
    obtains d where "d>0"  "\<And>x'. \<lbrakk>x' \<in> s; dist x' x \<le> d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
  using assms
  apply (simp add: continuous_on_iff)
  apply (elim ballE allE)
  apply (auto intro: that [where d="d/2" for d])
  done

lemma uniformly_continuous_onE:
  assumes "uniformly_continuous_on s f" "0 < e"
  obtains d where "d>0" "\<And>x x'. \<lbrakk>x\<in>s; x'\<in>s; dist x' x < d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
using assms
by (auto simp: uniformly_continuous_on_def)

lemma continuous_at_imp_continuous_within:
  "continuous (at x) f \<Longrightarrow> continuous (at x within s) f"
  unfolding continuous_within continuous_at using Lim_at_imp_Lim_at_within by auto

lemma Lim_trivial_limit: "trivial_limit net \<Longrightarrow> (f \<longlongrightarrow> l) net"
  by simp

lemmas continuous_on = continuous_on_def \<comment> \<open>legacy theorem name\<close>

lemma continuous_within_subset:
  "continuous (at x within s) f \<Longrightarrow> t \<subseteq> s \<Longrightarrow> continuous (at x within t) f"
  unfolding continuous_within by(metis tendsto_within_subset)

lemma continuous_on_interior:
  "continuous_on s f \<Longrightarrow> x \<in> interior s \<Longrightarrow> continuous (at x) f"
  by (metis continuous_on_eq_continuous_at continuous_on_subset interiorE)

lemma continuous_on_eq:
  "\<lbrakk>continuous_on s f; \<And>x. x \<in> s \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> continuous_on s g"
  unfolding continuous_on_def tendsto_def eventually_at_topological
  by simp

text \<open>Characterization of various kinds of continuity in terms of sequences.\<close>

lemma continuous_within_sequentiallyI:
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::topological_space"
  assumes "\<And>u::nat \<Rightarrow> 'a. u \<longlonglongrightarrow> a \<Longrightarrow> (\<forall>n. u n \<in> s) \<Longrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> f a"
  shows "continuous (at a within s) f"
  using assms unfolding continuous_within tendsto_def[where l = "f a"]
  by (auto intro!: sequentially_imp_eventually_within)

lemma continuous_within_tendsto_compose:
  fixes f::"'a::t2_space \<Rightarrow> 'b::topological_space"
  assumes "continuous (at a within s) f"
          "eventually (\<lambda>n. x n \<in> s) F"
          "(x \<longlongrightarrow> a) F "
  shows "((\<lambda>n. f (x n)) \<longlongrightarrow> f a) F"
proof -
  have *: "filterlim x (inf (nhds a) (principal s)) F"
    using assms(2) assms(3) unfolding at_within_def filterlim_inf by (auto simp: filterlim_principal eventually_mono)
  show ?thesis
    by (auto simp: assms(1) continuous_within[symmetric] tendsto_at_within_iff_tendsto_nhds[symmetric] intro!: filterlim_compose[OF _ *])
qed

lemma continuous_within_tendsto_compose':
  fixes f::"'a::t2_space \<Rightarrow> 'b::topological_space"
  assumes "continuous (at a within s) f"
    "\<And>n. x n \<in> s"
    "(x \<longlongrightarrow> a) F "
  shows "((\<lambda>n. f (x n)) \<longlongrightarrow> f a) F"
  by (auto intro!: continuous_within_tendsto_compose[OF assms(1)] simp add: assms)

lemma continuous_within_sequentially:
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::topological_space"
  shows "continuous (at a within s) f \<longleftrightarrow>
    (\<forall>x. (\<forall>n::nat. x n \<in> s) \<and> (x \<longlongrightarrow> a) sequentially
         \<longrightarrow> ((f \<circ> x) \<longlongrightarrow> f a) sequentially)"
  using continuous_within_tendsto_compose'[of a s f _ sequentially]
    continuous_within_sequentiallyI[of a s f]
  by (auto simp: o_def)

lemma continuous_at_sequentiallyI:
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::topological_space"
  assumes "\<And>u. u \<longlonglongrightarrow> a \<Longrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> f a"
  shows "continuous (at a) f"
  using continuous_within_sequentiallyI[of a UNIV f] assms by auto

lemma continuous_at_sequentially:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::topological_space"
  shows "continuous (at a) f \<longleftrightarrow>
    (\<forall>x. (x \<longlongrightarrow> a) sequentially --> ((f \<circ> x) \<longlongrightarrow> f a) sequentially)"
  using continuous_within_sequentially[of a UNIV f] by simp

lemma continuous_on_sequentiallyI:
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::topological_space"
  assumes "\<And>u a. (\<forall>n. u n \<in> s) \<Longrightarrow> a \<in> s \<Longrightarrow> u \<longlonglongrightarrow> a \<Longrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> f a"
  shows "continuous_on s f"
  using assms unfolding continuous_on_eq_continuous_within
  using continuous_within_sequentiallyI[of _ s f] by auto

lemma continuous_on_sequentially:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::topological_space"
  shows "continuous_on s f \<longleftrightarrow>
    (\<forall>x. \<forall>a \<in> s. (\<forall>n. x(n) \<in> s) \<and> (x \<longlongrightarrow> a) sequentially
      --> ((f \<circ> x) \<longlongrightarrow> f a) sequentially)"
    (is "?lhs = ?rhs")
proof
  assume ?rhs
  then show ?lhs
    using continuous_within_sequentially[of _ s f]
    unfolding continuous_on_eq_continuous_within
    by auto
next
  assume ?lhs
  then show ?rhs
    unfolding continuous_on_eq_continuous_within
    using continuous_within_sequentially[of _ s f]
    by auto
qed

lemma uniformly_continuous_on_sequentially:
  "uniformly_continuous_on s f \<longleftrightarrow> (\<forall>x y. (\<forall>n. x n \<in> s) \<and> (\<forall>n. y n \<in> s) \<and>
    (\<lambda>n. dist (x n) (y n)) \<longlonglongrightarrow> 0 \<longrightarrow> (\<lambda>n. dist (f(x n)) (f(y n))) \<longlonglongrightarrow> 0)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  {
    fix x y
    assume x: "\<forall>n. x n \<in> s"
      and y: "\<forall>n. y n \<in> s"
      and xy: "((\<lambda>n. dist (x n) (y n)) \<longlongrightarrow> 0) sequentially"
    {
      fix e :: real
      assume "e > 0"
      then obtain d where "d > 0" and d: "\<forall>x\<in>s. \<forall>x'\<in>s. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
        using \<open>?lhs\<close>[unfolded uniformly_continuous_on_def, THEN spec[where x=e]] by auto
      obtain N where N: "\<forall>n\<ge>N. dist (x n) (y n) < d"
        using xy[unfolded lim_sequentially dist_norm] and \<open>d>0\<close> by auto
      {
        fix n
        assume "n\<ge>N"
        then have "dist (f (x n)) (f (y n)) < e"
          using N[THEN spec[where x=n]]
          using d[THEN bspec[where x="x n"], THEN bspec[where x="y n"]]
          using x and y
          by (simp add: dist_commute)
      }
      then have "\<exists>N. \<forall>n\<ge>N. dist (f (x n)) (f (y n)) < e"
        by auto
    }
    then have "((\<lambda>n. dist (f(x n)) (f(y n))) \<longlongrightarrow> 0) sequentially"
      unfolding lim_sequentially and dist_real_def by auto
  }
  then show ?rhs by auto
next
  assume ?rhs
  {
    assume "\<not> ?lhs"
    then obtain e where "e > 0" "\<forall>d>0. \<exists>x\<in>s. \<exists>x'\<in>s. dist x' x < d \<and> \<not> dist (f x') (f x) < e"
      unfolding uniformly_continuous_on_def by auto
    then obtain fa where fa:
      "\<forall>x. 0 < x \<longrightarrow> fst (fa x) \<in> s \<and> snd (fa x) \<in> s \<and> dist (fst (fa x)) (snd (fa x)) < x \<and> \<not> dist (f (fst (fa x))) (f (snd (fa x))) < e"
      using choice[of "\<lambda>d x. d>0 \<longrightarrow> fst x \<in> s \<and> snd x \<in> s \<and> dist (snd x) (fst x) < d \<and> \<not> dist (f (snd x)) (f (fst x)) < e"]
      unfolding Bex_def
      by (auto simp: dist_commute)
    define x where "x n = fst (fa (inverse (real n + 1)))" for n
    define y where "y n = snd (fa (inverse (real n + 1)))" for n
    have xyn: "\<forall>n. x n \<in> s \<and> y n \<in> s"
      and xy0: "\<forall>n. dist (x n) (y n) < inverse (real n + 1)"
      and fxy:"\<forall>n. \<not> dist (f (x n)) (f (y n)) < e"
      unfolding x_def and y_def using fa
      by auto
    {
      fix e :: real
      assume "e > 0"
      then obtain N :: nat where "N \<noteq> 0" and N: "0 < inverse (real N) \<and> inverse (real N) < e"
        unfolding real_arch_inverse[of e] by auto
      {
        fix n :: nat
        assume "n \<ge> N"
        then have "inverse (real n + 1) < inverse (real N)"
          using of_nat_0_le_iff and \<open>N\<noteq>0\<close> by auto
        also have "\<dots> < e" using N by auto
        finally have "inverse (real n + 1) < e" by auto
        then have "dist (x n) (y n) < e"
          using xy0[THEN spec[where x=n]] by auto
      }
      then have "\<exists>N. \<forall>n\<ge>N. dist (x n) (y n) < e" by auto
    }
    then have "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (f (x n)) (f (y n)) < e"
      using \<open>?rhs\<close>[THEN spec[where x=x], THEN spec[where x=y]] and xyn
      unfolding lim_sequentially dist_real_def by auto
    then have False using fxy and \<open>e>0\<close> by auto
  }
  then show ?lhs
    unfolding uniformly_continuous_on_def by blast
qed

lemma continuous_closed_imp_Cauchy_continuous:
  fixes S :: "('a::complete_space) set"
  shows "\<lbrakk>continuous_on S f; closed S; Cauchy \<sigma>; \<And>n. (\<sigma> n) \<in> S\<rbrakk> \<Longrightarrow> Cauchy(f \<circ> \<sigma>)"
  apply (simp add: complete_eq_closed [symmetric] continuous_on_sequentially)
  by (meson LIMSEQ_imp_Cauchy complete_def)

text\<open>The usual transformation theorems.\<close>

lemma continuous_transform_within:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::topological_space"
  assumes "continuous (at x within s) f"
    and "0 < d"
    and "x \<in> s"
    and "\<And>x'. \<lbrakk>x' \<in> s; dist x' x < d\<rbrakk> \<Longrightarrow> f x' = g x'"
  shows "continuous (at x within s) g"
  using assms
  unfolding continuous_within
  by (force intro: Lim_transform_within)


subsubsection%unimportant \<open>Structural rules for uniform continuity\<close>

lemma uniformly_continuous_on_dist[continuous_intros]:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "uniformly_continuous_on s f"
    and "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. dist (f x) (g x))"
proof -
  {
    fix a b c d :: 'b
    have "\<bar>dist a b - dist c d\<bar> \<le> dist a c + dist b d"
      using dist_triangle2 [of a b c] dist_triangle2 [of b c d]
      using dist_triangle3 [of c d a] dist_triangle [of a d b]
      by arith
  } note le = this
  {
    fix x y
    assume f: "(\<lambda>n. dist (f (x n)) (f (y n))) \<longlonglongrightarrow> 0"
    assume g: "(\<lambda>n. dist (g (x n)) (g (y n))) \<longlonglongrightarrow> 0"
    have "(\<lambda>n. \<bar>dist (f (x n)) (g (x n)) - dist (f (y n)) (g (y n))\<bar>) \<longlonglongrightarrow> 0"
      by (rule Lim_transform_bound [OF _ tendsto_add_zero [OF f g]],
        simp add: le)
  }
  then show ?thesis
    using assms unfolding uniformly_continuous_on_sequentially
    unfolding dist_real_def by simp
qed

lemma uniformly_continuous_on_norm[continuous_intros]:
  fixes f :: "'a :: metric_space \<Rightarrow> 'b :: real_normed_vector"
  assumes "uniformly_continuous_on s f"
  shows "uniformly_continuous_on s (\<lambda>x. norm (f x))"
  unfolding norm_conv_dist using assms
  by (intro uniformly_continuous_on_dist uniformly_continuous_on_const)

lemma (in bounded_linear) uniformly_continuous_on[continuous_intros]:
  fixes g :: "_::metric_space \<Rightarrow> _"
  assumes "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f (g x))"
  using assms unfolding uniformly_continuous_on_sequentially
  unfolding dist_norm tendsto_norm_zero_iff diff[symmetric]
  by (auto intro: tendsto_zero)

lemma uniformly_continuous_on_cmul[continuous_intros]:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_on s f"
  shows "uniformly_continuous_on s (\<lambda>x. c *\<^sub>R f(x))"
  using bounded_linear_scaleR_right assms
  by (rule bounded_linear.uniformly_continuous_on)

lemma dist_minus:
  fixes x y :: "'a::real_normed_vector"
  shows "dist (- x) (- y) = dist x y"
  unfolding dist_norm minus_diff_minus norm_minus_cancel ..

lemma uniformly_continuous_on_minus[continuous_intros]:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "uniformly_continuous_on s f \<Longrightarrow> uniformly_continuous_on s (\<lambda>x. - f x)"
  unfolding uniformly_continuous_on_def dist_minus .

lemma uniformly_continuous_on_add[continuous_intros]:
  fixes f g :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_on s f"
    and "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f x + g x)"
  using assms
  unfolding uniformly_continuous_on_sequentially
  unfolding dist_norm tendsto_norm_zero_iff add_diff_add
  by (auto intro: tendsto_add_zero)

lemma uniformly_continuous_on_diff[continuous_intros]:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  assumes "uniformly_continuous_on s f"
    and "uniformly_continuous_on s g"
  shows "uniformly_continuous_on s (\<lambda>x. f x - g x)"
  using assms uniformly_continuous_on_add [of s f "- g"]
    by (simp add: fun_Compl_def uniformly_continuous_on_minus)

text \<open>Continuity in terms of open preimages.\<close>

lemma continuous_at_open:
  "continuous (at x) f \<longleftrightarrow> (\<forall>t. open t \<and> f x \<in> t --> (\<exists>s. open s \<and> x \<in> s \<and> (\<forall>x' \<in> s. (f x') \<in> t)))"
  unfolding continuous_within_topological [of x UNIV f]
  unfolding imp_conjL
  by (intro all_cong imp_cong ex_cong conj_cong refl) auto

lemma continuous_imp_tendsto:
  assumes "continuous (at x0) f"
    and "x \<longlonglongrightarrow> x0"
  shows "(f \<circ> x) \<longlonglongrightarrow> (f x0)"
proof (rule topological_tendstoI)
  fix S
  assume "open S" "f x0 \<in> S"
  then obtain T where T_def: "open T" "x0 \<in> T" "\<forall>x\<in>T. f x \<in> S"
     using assms continuous_at_open by metis
  then have "eventually (\<lambda>n. x n \<in> T) sequentially"
    using assms T_def by (auto simp: tendsto_def)
  then show "eventually (\<lambda>n. (f \<circ> x) n \<in> S) sequentially"
    using T_def by (auto elim!: eventually_mono)
qed

lemma continuous_on_open:
  "continuous_on S f \<longleftrightarrow>
    (\<forall>T. openin (subtopology euclidean (f ` S)) T \<longrightarrow>
      openin (subtopology euclidean S) (S \<inter> f -` T))"
  unfolding continuous_on_open_invariant openin_open Int_def vimage_def Int_commute
  by (simp add: imp_ex imageI conj_commute eq_commute cong: conj_cong)

lemma continuous_on_open_gen:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "f ` S \<subseteq> T"
    shows "continuous_on S f \<longleftrightarrow>
             (\<forall>U. openin (subtopology euclidean T) U
                  \<longrightarrow> openin (subtopology euclidean S) (S \<inter> f -` U))"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (clarsimp simp: openin_euclidean_subtopology_iff continuous_on_iff)
    by (metis assms image_subset_iff)
next
  have ope: "openin (subtopology euclidean T) (ball y e \<inter> T)" for y e
    by (simp add: Int_commute openin_open_Int)
  assume R [rule_format]: ?rhs
  show ?lhs
  proof (clarsimp simp add: continuous_on_iff)
    fix x and e::real
    assume "x \<in> S" and "0 < e"
    then have x: "x \<in> S \<inter> (f -` ball (f x) e \<inter> f -` T)"
      using assms by auto
    show "\<exists>d>0. \<forall>x'\<in>S. dist x' x < d \<longrightarrow> dist (f x') (f x) < e"
      using R [of "ball (f x) e \<inter> T"] x
      by (fastforce simp add: ope openin_euclidean_subtopology_iff [of S] dist_commute)
  qed
qed

lemma continuous_openin_preimage:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  shows
   "\<lbrakk>continuous_on S f; f ` S \<subseteq> T; openin (subtopology euclidean T) U\<rbrakk>
        \<Longrightarrow> openin (subtopology euclidean S) (S \<inter> f -` U)"
by (simp add: continuous_on_open_gen)

text \<open>Similarly in terms of closed sets.\<close>

lemma continuous_on_closed:
  "continuous_on S f \<longleftrightarrow>
    (\<forall>T. closedin (subtopology euclidean (f ` S)) T \<longrightarrow>
      closedin (subtopology euclidean S) (S \<inter> f -` T))"
  unfolding continuous_on_closed_invariant closedin_closed Int_def vimage_def Int_commute
  by (simp add: imp_ex imageI conj_commute eq_commute cong: conj_cong)

lemma continuous_on_closed_gen:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "f ` S \<subseteq> T"
    shows "continuous_on S f \<longleftrightarrow>
             (\<forall>U. closedin (subtopology euclidean T) U
                  \<longrightarrow> closedin (subtopology euclidean S) (S \<inter> f -` U))"
     (is "?lhs = ?rhs")
proof -
  have *: "U \<subseteq> T \<Longrightarrow> S \<inter> f -` (T - U) = S - (S \<inter> f -` U)" for U
    using assms by blast
  show ?thesis
  proof
    assume L: ?lhs
    show ?rhs
    proof clarify
      fix U
      assume "closedin (subtopology euclidean T) U"
      then show "closedin (subtopology euclidean S) (S \<inter> f -` U)"
        using L unfolding continuous_on_open_gen [OF assms]
        by (metis * closedin_def inf_le1 topspace_euclidean_subtopology)
    qed
  next
    assume R [rule_format]: ?rhs
    show ?lhs
      unfolding continuous_on_open_gen [OF assms]
      by (metis * R inf_le1 openin_closedin_eq topspace_euclidean_subtopology)
  qed
qed

lemma continuous_closedin_preimage_gen:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "continuous_on S f" "f ` S \<subseteq> T" "closedin (subtopology euclidean T) U"
    shows "closedin (subtopology euclidean S) (S \<inter> f -` U)"
using assms continuous_on_closed_gen by blast

lemma continuous_on_imp_closedin:
  assumes "continuous_on S f" "closedin (subtopology euclidean (f ` S)) T"
    shows "closedin (subtopology euclidean S) (S \<inter> f -` T)"
using assms continuous_on_closed by blast

subsection%unimportant \<open>Half-global and completely global cases\<close>

lemma continuous_openin_preimage_gen:
  assumes "continuous_on S f"  "open T"
  shows "openin (subtopology euclidean S) (S \<inter> f -` T)"
proof -
  have *: "(S \<inter> f -` T) = (S \<inter> f -` (T \<inter> f ` S))"
    by auto
  have "openin (subtopology euclidean (f ` S)) (T \<inter> f ` S)"
    using openin_open_Int[of T "f ` S", OF assms(2)] unfolding openin_open by auto
  then show ?thesis
    using assms(1)[unfolded continuous_on_open, THEN spec[where x="T \<inter> f ` S"]]
    using * by auto
qed

lemma continuous_closedin_preimage:
  assumes "continuous_on S f" and "closed T"
  shows "closedin (subtopology euclidean S) (S \<inter> f -` T)"
proof -
  have *: "(S \<inter> f -` T) = (S \<inter> f -` (T \<inter> f ` S))"
    by auto
  have "closedin (subtopology euclidean (f ` S)) (T \<inter> f ` S)"
    using closedin_closed_Int[of T "f ` S", OF assms(2)]
    by (simp add: Int_commute)
  then show ?thesis
    using assms(1)[unfolded continuous_on_closed, THEN spec[where x="T \<inter> f ` S"]]
    using * by auto
qed

lemma continuous_openin_preimage_eq:
   "continuous_on S f \<longleftrightarrow>
    (\<forall>T. open T \<longrightarrow> openin (subtopology euclidean S) (S \<inter> f -` T))"
apply safe
apply (simp add: continuous_openin_preimage_gen)
apply (fastforce simp add: continuous_on_open openin_open)
done

lemma continuous_closedin_preimage_eq:
   "continuous_on S f \<longleftrightarrow>
    (\<forall>T. closed T \<longrightarrow> closedin (subtopology euclidean S) (S \<inter> f -` T))"
apply safe
apply (simp add: continuous_closedin_preimage)
apply (fastforce simp add: continuous_on_closed closedin_closed)
done

lemma continuous_open_preimage:
  assumes contf: "continuous_on S f" and "open S" "open T"
  shows "open (S \<inter> f -` T)"
proof-
  obtain U where "open U" "(S \<inter> f -` T) = S \<inter> U"
    using continuous_openin_preimage_gen[OF contf \<open>open T\<close>]
    unfolding openin_open by auto
  then show ?thesis
    using open_Int[of S U, OF \<open>open S\<close>] by auto
qed

lemma continuous_closed_preimage:
  assumes contf: "continuous_on S f" and "closed S" "closed T"
  shows "closed (S \<inter> f -` T)"
proof-
  obtain U where "closed U" "(S \<inter> f -` T) = S \<inter> U"
    using continuous_closedin_preimage[OF contf \<open>closed T\<close>]
    unfolding closedin_closed by auto
  then show ?thesis using closed_Int[of S U, OF \<open>closed S\<close>] by auto
qed

lemma continuous_open_vimage: "open S \<Longrightarrow> (\<And>x. continuous (at x) f) \<Longrightarrow> open (f -` S)"
  by (metis continuous_on_eq_continuous_within open_vimage) 
 
lemma continuous_closed_vimage: "closed S \<Longrightarrow> (\<And>x. continuous (at x) f) \<Longrightarrow> closed (f -` S)"
  by (simp add: closed_vimage continuous_on_eq_continuous_within)

lemma interior_image_subset:
  assumes "inj f" "\<And>x. continuous (at x) f"
  shows "interior (f ` S) \<subseteq> f ` (interior S)"
proof
  fix x assume "x \<in> interior (f ` S)"
  then obtain T where as: "open T" "x \<in> T" "T \<subseteq> f ` S" ..
  then have "x \<in> f ` S" by auto
  then obtain y where y: "y \<in> S" "x = f y" by auto
  have "open (f -` T)"
    using assms \<open>open T\<close> by (simp add: continuous_at_imp_continuous_on open_vimage)
  moreover have "y \<in> vimage f T"
    using \<open>x = f y\<close> \<open>x \<in> T\<close> by simp
  moreover have "vimage f T \<subseteq> S"
    using \<open>T \<subseteq> image f S\<close> \<open>inj f\<close> unfolding inj_on_def subset_eq by auto
  ultimately have "y \<in> interior S" ..
  with \<open>x = f y\<close> show "x \<in> f ` interior S" ..
qed

subsection%unimportant \<open>Topological properties of linear functions\<close>

lemma linear_lim_0:
  assumes "bounded_linear f"
  shows "(f \<longlongrightarrow> 0) (at (0))"
proof -
  interpret f: bounded_linear f by fact
  have "(f \<longlongrightarrow> f 0) (at 0)"
    using tendsto_ident_at by (rule f.tendsto)
  then show ?thesis unfolding f.zero .
qed

lemma linear_continuous_at:
  assumes "bounded_linear f"
  shows "continuous (at a) f"
  unfolding continuous_at using assms
  apply (rule bounded_linear.tendsto)
  apply (rule tendsto_ident_at)
  done

lemma linear_continuous_within:
  "bounded_linear f \<Longrightarrow> continuous (at x within s) f"
  using continuous_at_imp_continuous_within[of x f s] using linear_continuous_at[of f] by auto

lemma linear_continuous_on:
  "bounded_linear f \<Longrightarrow> continuous_on s f"
  using continuous_at_imp_continuous_on[of s f] using linear_continuous_at[of f] by auto

end