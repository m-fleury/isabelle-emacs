(* Title:      HOL/Analysis/Cartesian_Euclidean_Space.thy
   Some material by Tim Makarios and L C Paulson
*)

section \<open>Instantiates the finite Cartesian product of Euclidean spaces as a Euclidean space\<close>

theory Cartesian_Euclidean_Space
imports Finite_Cartesian_Product Derivative
begin

lemma norm_le_componentwise:
   "(\<And>b. b \<in> Basis \<Longrightarrow> abs(x \<bullet> b) \<le> abs(y \<bullet> b)) \<Longrightarrow> norm x \<le> norm y"
  by (auto simp: norm_le euclidean_inner [of x x] euclidean_inner [of y y] abs_le_square_iff power2_eq_square intro!: sum_mono)

lemma norm_le_componentwise_cart:
  fixes x :: "real^'n"
  shows "(\<And>i. abs(x$i) \<le> abs(y$i)) \<Longrightarrow> norm x \<le> norm y"
  unfolding cart_eq_inner_axis
  by (rule norm_le_componentwise) (metis axis_index)
  
lemma subspace_special_hyperplane: "subspace {x. x $ k = 0}"
  by (simp add: subspace_def)

lemma sum_mult_product:
  "sum h {..<A * B :: nat} = (\<Sum>i\<in>{..<A}. \<Sum>j\<in>{..<B}. h (j + i * B))"
  unfolding sum_nat_group[of h B A, unfolded atLeast0LessThan, symmetric]
proof (rule sum.cong, simp, rule sum.reindex_cong)
  fix i
  show "inj_on (\<lambda>j. j + i * B) {..<B}" by (auto intro!: inj_onI)
  show "{i * B..<i * B + B} = (\<lambda>j. j + i * B) ` {..<B}"
  proof safe
    fix j assume "j \<in> {i * B..<i * B + B}"
    then show "j \<in> (\<lambda>j. j + i * B) ` {..<B}"
      by (auto intro!: image_eqI[of _ _ "j - i * B"])
  qed simp
qed simp

subsection\<open>Basic componentwise operations on vectors\<close>

instantiation vec :: (times, finite) times
begin

definition "( * ) \<equiv> (\<lambda> x y.  (\<chi> i. (x$i) * (y$i)))"
instance ..

end

instantiation vec :: (one, finite) one
begin

definition "1 \<equiv> (\<chi> i. 1)"
instance ..

end

instantiation vec :: (ord, finite) ord
begin

definition "x \<le> y \<longleftrightarrow> (\<forall>i. x$i \<le> y$i)"
definition "x < (y::'a^'b) \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
instance ..

end

text\<open>The ordering on one-dimensional vectors is linear.\<close>

class cart_one =
  assumes UNIV_one: "card (UNIV :: 'a set) = Suc 0"
begin

subclass finite
proof
  from UNIV_one show "finite (UNIV :: 'a set)"
    by (auto intro!: card_ge_0_finite)
qed

end

instance vec:: (order, finite) order
  by standard (auto simp: less_eq_vec_def less_vec_def vec_eq_iff
      intro: order.trans order.antisym order.strict_implies_order)

instance vec :: (linorder, cart_one) linorder
proof
  obtain a :: 'b where all: "\<And>P. (\<forall>i. P i) \<longleftrightarrow> P a"
  proof -
    have "card (UNIV :: 'b set) = Suc 0" by (rule UNIV_one)
    then obtain b :: 'b where "UNIV = {b}" by (auto iff: card_Suc_eq)
    then have "\<And>P. (\<forall>i\<in>UNIV. P i) \<longleftrightarrow> P b" by auto
    then show thesis by (auto intro: that)
  qed
  fix x y :: "'a^'b::cart_one"
  note [simp] = less_eq_vec_def less_vec_def all vec_eq_iff field_simps
  show "x \<le> y \<or> y \<le> x" by auto
qed

text\<open>Constant Vectors\<close>

definition "vec x = (\<chi> i. x)"

lemma interval_cbox_cart: "{a::real^'n..b} = cbox a b"
  by (auto simp add: less_eq_vec_def mem_box Basis_vec_def inner_axis)

text\<open>Also the scalar-vector multiplication.\<close>

definition vector_scalar_mult:: "'a::times \<Rightarrow> 'a ^ 'n \<Rightarrow> 'a ^ 'n" (infixl "*s" 70)
  where "c *s x = (\<chi> i. c * (x$i))"


subsection \<open>A naive proof procedure to lift really trivial arithmetic stuff from the basis of the vector space\<close>

lemma sum_cong_aux:
  "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> sum f A = sum g A"
  by (auto intro: sum.cong)

hide_fact (open) sum_cong_aux

method_setup vector = \<open>
let
  val ss1 =
    simpset_of (put_simpset HOL_basic_ss @{context}
      addsimps [@{thm sum.distrib} RS sym,
      @{thm sum_subtractf} RS sym, @{thm sum_distrib_left},
      @{thm sum_distrib_right}, @{thm sum_negf} RS sym])
  val ss2 =
    simpset_of (@{context} addsimps
             [@{thm plus_vec_def}, @{thm times_vec_def},
              @{thm minus_vec_def}, @{thm uminus_vec_def},
              @{thm one_vec_def}, @{thm zero_vec_def}, @{thm vec_def},
              @{thm scaleR_vec_def},
              @{thm vec_lambda_beta}, @{thm vector_scalar_mult_def}])
  fun vector_arith_tac ctxt ths =
    simp_tac (put_simpset ss1 ctxt)
    THEN' (fn i => resolve_tac ctxt @{thms Cartesian_Euclidean_Space.sum_cong_aux} i
         ORELSE resolve_tac ctxt @{thms sum.neutral} i
         ORELSE simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm vec_eq_iff}]) i)
    (* THEN' TRY o clarify_tac HOL_cs  THEN' (TRY o rtac @{thm iffI}) *)
    THEN' asm_full_simp_tac (put_simpset ss2 ctxt addsimps ths)
in
  Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD' (vector_arith_tac ctxt ths))
end
\<close> "lift trivial vector statements to real arith statements"

lemma vec_0[simp]: "vec 0 = 0" by vector
lemma vec_1[simp]: "vec 1 = 1" by vector

lemma vec_inj[simp]: "vec x = vec y \<longleftrightarrow> x = y" by vector

lemma vec_in_image_vec: "vec x \<in> (vec ` S) \<longleftrightarrow> x \<in> S" by auto

lemma vec_add: "vec(x + y) = vec x + vec y"  by vector
lemma vec_sub: "vec(x - y) = vec x - vec y" by vector
lemma vec_cmul: "vec(c * x) = c *s vec x " by vector
lemma vec_neg: "vec(- x) = - vec x " by vector

lemma vec_scaleR: "vec(c * x) = c *\<^sub>R vec x"
  by vector

lemma vec_sum:
  assumes "finite S"
  shows "vec(sum f S) = sum (vec \<circ> f) S"
  using assms
proof induct
  case empty
  then show ?case by simp
next
  case insert
  then show ?case by (auto simp add: vec_add)
qed

text\<open>Obvious "component-pushing".\<close>

lemma vec_component [simp]: "vec x $ i = x"
  by vector

lemma vector_mult_component [simp]: "(x * y)$i = x$i * y$i"
  by vector

lemma vector_smult_component [simp]: "(c *s y)$i = c * (y$i)"
  by vector

lemma cond_component: "(if b then x else y)$i = (if b then x$i else y$i)" by vector

lemmas vector_component =
  vec_component vector_add_component vector_mult_component
  vector_smult_component vector_minus_component vector_uminus_component
  vector_scaleR_component cond_component


subsection \<open>Some frequently useful arithmetic lemmas over vectors\<close>

instance vec :: (semigroup_mult, finite) semigroup_mult
  by standard (vector mult.assoc)

instance vec :: (monoid_mult, finite) monoid_mult
  by standard vector+

instance vec :: (ab_semigroup_mult, finite) ab_semigroup_mult
  by standard (vector mult.commute)

instance vec :: (comm_monoid_mult, finite) comm_monoid_mult
  by standard vector

instance vec :: (semiring, finite) semiring
  by standard (vector field_simps)+

instance vec :: (semiring_0, finite) semiring_0
  by standard (vector field_simps)+
instance vec :: (semiring_1, finite) semiring_1
  by standard vector
instance vec :: (comm_semiring, finite) comm_semiring
  by standard (vector field_simps)+

instance vec :: (comm_semiring_0, finite) comm_semiring_0 ..
instance vec :: (cancel_comm_monoid_add, finite) cancel_comm_monoid_add ..
instance vec :: (semiring_0_cancel, finite) semiring_0_cancel ..
instance vec :: (comm_semiring_0_cancel, finite) comm_semiring_0_cancel ..
instance vec :: (ring, finite) ring ..
instance vec :: (semiring_1_cancel, finite) semiring_1_cancel ..
instance vec :: (comm_semiring_1, finite) comm_semiring_1 ..

instance vec :: (ring_1, finite) ring_1 ..

instance vec :: (real_algebra, finite) real_algebra
  by standard (simp_all add: vec_eq_iff)

instance vec :: (real_algebra_1, finite) real_algebra_1 ..

lemma of_nat_index: "(of_nat n :: 'a::semiring_1 ^'n)$i = of_nat n"
proof (induct n)
  case 0
  then show ?case by vector
next
  case Suc
  then show ?case by vector
qed

lemma one_index [simp]: "(1 :: 'a :: one ^ 'n) $ i = 1"
  by vector

lemma neg_one_index [simp]: "(- 1 :: 'a :: {one, uminus} ^ 'n) $ i = - 1"
  by vector

instance vec :: (semiring_char_0, finite) semiring_char_0
proof
  fix m n :: nat
  show "inj (of_nat :: nat \<Rightarrow> 'a ^ 'b)"
    by (auto intro!: injI simp add: vec_eq_iff of_nat_index)
qed

instance vec :: (numeral, finite) numeral ..
instance vec :: (semiring_numeral, finite) semiring_numeral ..

lemma numeral_index [simp]: "numeral w $ i = numeral w"
  by (induct w) (simp_all only: numeral.simps vector_add_component one_index)

lemma neg_numeral_index [simp]: "- numeral w $ i = - numeral w"
  by (simp only: vector_uminus_component numeral_index)

instance vec :: (comm_ring_1, finite) comm_ring_1 ..
instance vec :: (ring_char_0, finite) ring_char_0 ..

lemma vector_smult_assoc: "a *s (b *s x) = ((a::'a::semigroup_mult) * b) *s x"
  by (vector mult.assoc)
lemma vector_sadd_rdistrib: "((a::'a::semiring) + b) *s x = a *s x + b *s x"
  by (vector field_simps)
lemma vector_add_ldistrib: "(c::'a::semiring) *s (x + y) = c *s x + c *s y"
  by (vector field_simps)
lemma vector_smult_lzero[simp]: "(0::'a::mult_zero) *s x = 0" by vector
lemma vector_smult_lid[simp]: "(1::'a::monoid_mult) *s x = x" by vector
lemma vector_ssub_ldistrib: "(c::'a::ring) *s (x - y) = c *s x - c *s y"
  by (vector field_simps)
lemma vector_smult_rneg: "(c::'a::ring) *s -x = -(c *s x)" by vector
lemma vector_smult_lneg: "- (c::'a::ring) *s x = -(c *s x)" by vector
lemma vector_sneg_minus1: "-x = (-1::'a::ring_1) *s x" by vector
lemma vector_smult_rzero[simp]: "c *s 0 = (0::'a::mult_zero ^ 'n)" by vector
lemma vector_sub_rdistrib: "((a::'a::ring) - b) *s x = a *s x - b *s x"
  by (vector field_simps)

lemma vec_eq[simp]: "(vec m = vec n) \<longleftrightarrow> (m = n)"
  by (simp add: vec_eq_iff)

lemma linear_vec [simp]: "linear vec"
  by (simp add: linearI vec_add vec_eq_iff)

lemma differentiable_vec:
  fixes S :: "'a::euclidean_space set"
  shows "vec differentiable_on S"
  by (simp add: linear_linear bounded_linear_imp_differentiable_on)

lemma continuous_vec [continuous_intros]:
  fixes x :: "'a::euclidean_space"
  shows "isCont vec x"
  apply (clarsimp simp add: continuous_def LIM_def dist_vec_def L2_set_def)
  apply (rule_tac x="r / sqrt (real CARD('b))" in exI)
  by (simp add: mult.commute pos_less_divide_eq real_sqrt_mult)

lemma box_vec_eq_empty [simp]:
  shows "cbox (vec a) (vec b) = {} \<longleftrightarrow> cbox a b = {}"
        "box (vec a) (vec b) = {} \<longleftrightarrow> box a b = {}"
  by (auto simp: Basis_vec_def mem_box box_eq_empty inner_axis)

lemma norm_eq_0_imp: "norm x = 0 ==> x = (0::real ^'n)" by (metis norm_eq_zero)

lemma norm_axis_1 [simp]: "norm (axis m (1::real)) = 1"
  by (simp add: inner_axis' norm_eq_1)

lemma vector_mul_eq_0[simp]: "(a *s x = 0) \<longleftrightarrow> a = (0::'a::idom) \<or> x = 0"
  by vector

lemma vector_mul_lcancel[simp]: "a *s x = a *s y \<longleftrightarrow> a = (0::real) \<or> x = y"
  by (metis eq_iff_diff_eq_0 vector_mul_eq_0 vector_ssub_ldistrib)

lemma vector_mul_rcancel[simp]: "a *s x = b *s x \<longleftrightarrow> (a::real) = b \<or> x = 0"
  by (metis eq_iff_diff_eq_0 vector_mul_eq_0 vector_sub_rdistrib)

lemma vector_mul_lcancel_imp: "a \<noteq> (0::real) ==>  a *s x = a *s y ==> (x = y)"
  by (metis vector_mul_lcancel)

lemma vector_mul_rcancel_imp: "x \<noteq> 0 \<Longrightarrow> (a::real) *s x = b *s x ==> a = b"
  by (metis vector_mul_rcancel)

lemma component_le_norm_cart: "\<bar>x$i\<bar> \<le> norm x"
  apply (simp add: norm_vec_def)
  apply (rule member_le_L2_set, simp_all)
  done

lemma norm_bound_component_le_cart: "norm x \<le> e ==> \<bar>x$i\<bar> \<le> e"
  by (metis component_le_norm_cart order_trans)

lemma norm_bound_component_lt_cart: "norm x < e ==> \<bar>x$i\<bar> < e"
  by (metis component_le_norm_cart le_less_trans)

lemma norm_le_l1_cart: "norm x \<le> sum(\<lambda>i. \<bar>x$i\<bar>) UNIV"
  by (simp add: norm_vec_def L2_set_le_sum)

lemma scalar_mult_eq_scaleR [simp]: "c *s x = c *\<^sub>R x"
  unfolding scaleR_vec_def vector_scalar_mult_def by simp

lemma dist_mul[simp]: "dist (c *s x) (c *s y) = \<bar>c\<bar> * dist x y"
  unfolding dist_norm scalar_mult_eq_scaleR
  unfolding scaleR_right_diff_distrib[symmetric] by simp

lemma sum_component [simp]:
  fixes f:: " 'a \<Rightarrow> ('b::comm_monoid_add) ^'n"
  shows "(sum f S)$i = sum (\<lambda>x. (f x)$i) S"
proof (cases "finite S")
  case True
  then show ?thesis by induct simp_all
next
  case False
  then show ?thesis by simp
qed

lemma sum_eq: "sum f S = (\<chi> i. sum (\<lambda>x. (f x)$i ) S)"
  by (simp add: vec_eq_iff)

lemma sum_cmul:
  fixes f:: "'c \<Rightarrow> ('a::semiring_1)^'n"
  shows "sum (\<lambda>x. c *s f x) S = c *s sum f S"
  by (simp add: vec_eq_iff sum_distrib_left)

lemma sum_norm_allsubsets_bound_cart:
  fixes f:: "'a \<Rightarrow> real ^'n"
  assumes fP: "finite P" and fPs: "\<And>Q. Q \<subseteq> P \<Longrightarrow> norm (sum f Q) \<le> e"
  shows "sum (\<lambda>x. norm (f x)) P \<le> 2 * real CARD('n) *  e"
  using sum_norm_allsubsets_bound[OF assms]
  by simp

subsection\<open>Closures and interiors of halfspaces\<close>

lemma interior_halfspace_le [simp]:
  assumes "a \<noteq> 0"
    shows "interior {x. a \<bullet> x \<le> b} = {x. a \<bullet> x < b}"
proof -
  have *: "a \<bullet> x < b" if x: "x \<in> S" and S: "S \<subseteq> {x. a \<bullet> x \<le> b}" and "open S" for S x
  proof -
    obtain e where "e>0" and e: "cball x e \<subseteq> S"
      using \<open>open S\<close> open_contains_cball x by blast
    then have "x + (e / norm a) *\<^sub>R a \<in> cball x e"
      by (simp add: dist_norm)
    then have "x + (e / norm a) *\<^sub>R a \<in> S"
      using e by blast
    then have "x + (e / norm a) *\<^sub>R a \<in> {x. a \<bullet> x \<le> b}"
      using S by blast
    moreover have "e * (a \<bullet> a) / norm a > 0"
      by (simp add: \<open>0 < e\<close> assms)
    ultimately show ?thesis
      by (simp add: algebra_simps)
  qed
  show ?thesis
    by (rule interior_unique) (auto simp: open_halfspace_lt *)
qed

lemma interior_halfspace_ge [simp]:
   "a \<noteq> 0 \<Longrightarrow> interior {x. a \<bullet> x \<ge> b} = {x. a \<bullet> x > b}"
using interior_halfspace_le [of "-a" "-b"] by simp

lemma interior_halfspace_component_le [simp]:
     "interior {x. x$k \<le> a} = {x :: (real^'n). x$k < a}" (is "?LE")
  and interior_halfspace_component_ge [simp]:
     "interior {x. x$k \<ge> a} = {x :: (real^'n). x$k > a}" (is "?GE")
proof -
  have "axis k (1::real) \<noteq> 0"
    by (simp add: axis_def vec_eq_iff)
  moreover have "axis k (1::real) \<bullet> x = x$k" for x
    by (simp add: cart_eq_inner_axis inner_commute)
  ultimately show ?LE ?GE
    using interior_halfspace_le [of "axis k (1::real)" a]
          interior_halfspace_ge [of "axis k (1::real)" a] by auto
qed

lemma closure_halfspace_lt [simp]:
  assumes "a \<noteq> 0"
    shows "closure {x. a \<bullet> x < b} = {x. a \<bullet> x \<le> b}"
proof -
  have [simp]: "-{x. a \<bullet> x < b} = {x. a \<bullet> x \<ge> b}"
    by (force simp:)
  then show ?thesis
    using interior_halfspace_ge [of a b] assms
    by (force simp: closure_interior)
qed

lemma closure_halfspace_gt [simp]:
   "a \<noteq> 0 \<Longrightarrow> closure {x. a \<bullet> x > b} = {x. a \<bullet> x \<ge> b}"
using closure_halfspace_lt [of "-a" "-b"] by simp

lemma closure_halfspace_component_lt [simp]:
     "closure {x. x$k < a} = {x :: (real^'n). x$k \<le> a}" (is "?LE")
  and closure_halfspace_component_gt [simp]:
     "closure {x. x$k > a} = {x :: (real^'n). x$k \<ge> a}" (is "?GE")
proof -
  have "axis k (1::real) \<noteq> 0"
    by (simp add: axis_def vec_eq_iff)
  moreover have "axis k (1::real) \<bullet> x = x$k" for x
    by (simp add: cart_eq_inner_axis inner_commute)
  ultimately show ?LE ?GE
    using closure_halfspace_lt [of "axis k (1::real)" a]
          closure_halfspace_gt [of "axis k (1::real)" a] by auto
qed

lemma interior_hyperplane [simp]:
  assumes "a \<noteq> 0"
    shows "interior {x. a \<bullet> x = b} = {}"
proof -
  have [simp]: "{x. a \<bullet> x = b} = {x. a \<bullet> x \<le> b} \<inter> {x. a \<bullet> x \<ge> b}"
    by (force simp:)
  then show ?thesis
    by (auto simp: assms)
qed

lemma frontier_halfspace_le:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x \<le> b} = {x. a \<bullet> x = b}"
proof (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False then show ?thesis
    by (force simp: frontier_def closed_halfspace_le)
qed

lemma frontier_halfspace_ge:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x \<ge> b} = {x. a \<bullet> x = b}"
proof (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False then show ?thesis
    by (force simp: frontier_def closed_halfspace_ge)
qed

lemma frontier_halfspace_lt:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x < b} = {x. a \<bullet> x = b}"
proof (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False then show ?thesis
    by (force simp: frontier_def interior_open open_halfspace_lt)
qed

lemma frontier_halfspace_gt:
  assumes "a \<noteq> 0 \<or> b \<noteq> 0"
    shows "frontier {x. a \<bullet> x > b} = {x. a \<bullet> x = b}"
proof (cases "a = 0")
  case True with assms show ?thesis by simp
next
  case False then show ?thesis
    by (force simp: frontier_def interior_open open_halfspace_gt)
qed

lemma interior_standard_hyperplane:
   "interior {x :: (real^'n). x$k = a} = {}"
proof -
  have "axis k (1::real) \<noteq> 0"
    by (simp add: axis_def vec_eq_iff)
  moreover have "axis k (1::real) \<bullet> x = x$k" for x
    by (simp add: cart_eq_inner_axis inner_commute)
  ultimately show ?thesis
    using interior_hyperplane [of "axis k (1::real)" a]
    by force
qed

subsection \<open>Matrix operations\<close>

text\<open>Matrix notation. NB: an MxN matrix is of type @{typ "'a^'n^'m"}, not @{typ "'a^'m^'n"}\<close>

definition map_matrix::"('a \<Rightarrow> 'b) \<Rightarrow> (('a, 'i::finite)vec, 'j::finite) vec \<Rightarrow> (('b, 'i)vec, 'j) vec" where
  "map_matrix f x = (\<chi> i j. f (x $ i $ j))"

lemma nth_map_matrix[simp]: "map_matrix f x $ i $ j = f (x $ i $ j)"
  by (simp add: map_matrix_def)

definition matrix_matrix_mult :: "('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'p^'n \<Rightarrow> 'a ^ 'p ^'m"
    (infixl "**" 70)
  where "m ** m' == (\<chi> i j. sum (\<lambda>k. ((m$i)$k) * ((m'$k)$j)) (UNIV :: 'n set)) ::'a ^ 'p ^'m"

definition matrix_vector_mult :: "('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'n \<Rightarrow> 'a ^ 'm"
    (infixl "*v" 70)
  where "m *v x \<equiv> (\<chi> i. sum (\<lambda>j. ((m$i)$j) * (x$j)) (UNIV ::'n set)) :: 'a^'m"

definition vector_matrix_mult :: "'a ^ 'm \<Rightarrow> ('a::semiring_1) ^'n^'m \<Rightarrow> 'a ^'n "
    (infixl "v*" 70)
  where "v v* m == (\<chi> j. sum (\<lambda>i. ((m$i)$j) * (v$i)) (UNIV :: 'm set)) :: 'a^'n"

definition "(mat::'a::zero => 'a ^'n^'n) k = (\<chi> i j. if i = j then k else 0)"
definition transpose where
  "(transpose::'a^'n^'m \<Rightarrow> 'a^'m^'n) A = (\<chi> i j. ((A$j)$i))"
definition "(row::'m => 'a ^'n^'m \<Rightarrow> 'a ^'n) i A = (\<chi> j. ((A$i)$j))"
definition "(column::'n =>'a^'n^'m =>'a^'m) j A = (\<chi> i. ((A$i)$j))"
definition "rows(A::'a^'n^'m) = { row i A | i. i \<in> (UNIV :: 'm set)}"
definition "columns(A::'a^'n^'m) = { column i A | i. i \<in> (UNIV :: 'n set)}"
   
lemma times0_left [simp]: "(0::'a::semiring_1^'n^'m) ** (A::'a ^'p^'n) = 0" 
  by (simp add: matrix_matrix_mult_def zero_vec_def)

lemma times0_right [simp]: "(A::'a::semiring_1^'n^'m) ** (0::'a ^'p^'n) = 0" 
  by (simp add: matrix_matrix_mult_def zero_vec_def)

lemma mat_0[simp]: "mat 0 = 0" by (vector mat_def)
lemma matrix_add_ldistrib: "(A ** (B + C)) = (A ** B) + (A ** C)"
  by (vector matrix_matrix_mult_def sum.distrib[symmetric] field_simps)

lemma matrix_mul_lid [simp]:
  fixes A :: "'a::semiring_1 ^ 'm ^ 'n"
  shows "mat 1 ** A = A"
  apply (simp add: matrix_matrix_mult_def mat_def)
  apply vector
  apply (auto simp only: if_distrib cond_application_beta sum.delta'[OF finite]
    mult_1_left mult_zero_left if_True UNIV_I)
  done

lemma matrix_mul_rid [simp]:
  fixes A :: "'a::semiring_1 ^ 'm ^ 'n"
  shows "A ** mat 1 = A"
  apply (simp add: matrix_matrix_mult_def mat_def)
  apply vector
  apply (auto simp only: if_distrib cond_application_beta sum.delta[OF finite]
    mult_1_right mult_zero_right if_True UNIV_I cong: if_cong)
  done

lemma matrix_mul_assoc: "A ** (B ** C) = (A ** B) ** C"
  apply (vector matrix_matrix_mult_def sum_distrib_left sum_distrib_right mult.assoc)
  apply (subst sum.swap)
  apply simp
  done

lemma matrix_vector_mul_assoc: "A *v (B *v x) = (A ** B) *v x"
  apply (vector matrix_matrix_mult_def matrix_vector_mult_def
    sum_distrib_left sum_distrib_right mult.assoc)
  apply (subst sum.swap)
  apply simp
  done

lemma scalar_matrix_assoc:
  fixes A :: "real^'m^'n"
  shows "k *\<^sub>R (A ** B) = (k *\<^sub>R A) ** B"
  by (simp add: matrix_matrix_mult_def sum_distrib_left mult_ac vec_eq_iff)

lemma matrix_scalar_ac:
  fixes A :: "real^'m^'n"
  shows "A ** (k *\<^sub>R B) = k *\<^sub>R A ** B"
  by (simp add: matrix_matrix_mult_def sum_distrib_left mult_ac vec_eq_iff)

lemma matrix_vector_mul_lid [simp]: "mat 1 *v x = (x::'a::semiring_1 ^ 'n)"
  apply (vector matrix_vector_mult_def mat_def)
  apply (simp add: if_distrib cond_application_beta sum.delta' cong del: if_weak_cong)
  done

lemma matrix_transpose_mul:
    "transpose(A ** B) = transpose B ** transpose (A::'a::comm_semiring_1^_^_)"
  by (simp add: matrix_matrix_mult_def transpose_def vec_eq_iff mult.commute)

lemma matrix_eq:
  fixes A B :: "'a::semiring_1 ^ 'n ^ 'm"
  shows "A = B \<longleftrightarrow>  (\<forall>x. A *v x = B *v x)" (is "?lhs \<longleftrightarrow> ?rhs")
  apply auto
  apply (subst vec_eq_iff)
  apply clarify
  apply (clarsimp simp add: matrix_vector_mult_def if_distrib cond_application_beta vec_eq_iff cong del: if_weak_cong)
  apply (erule_tac x="axis ia 1" in allE)
  apply (erule_tac x="i" in allE)
  apply (auto simp add: if_distrib cond_application_beta axis_def
    sum.delta[OF finite] cong del: if_weak_cong)
  done

lemma matrix_vector_mul_component: "((A::real^_^_) *v x)$k = (A$k) \<bullet> x"
  by (simp add: matrix_vector_mult_def inner_vec_def)

lemma dot_lmul_matrix: "((x::real ^_) v* A) \<bullet> y = x \<bullet> (A *v y)"
  apply (simp add: inner_vec_def matrix_vector_mult_def vector_matrix_mult_def sum_distrib_right sum_distrib_left ac_simps)
  apply (subst sum.swap)
  apply simp
  done

lemma transpose_mat [simp]: "transpose (mat n) = mat n"
  by (vector transpose_def mat_def)

lemma transpose_transpose [simp]: "transpose(transpose A) = A"
  by (vector transpose_def)

lemma row_transpose [simp]:
  fixes A:: "'a::semiring_1^_^_"
  shows "row i (transpose A) = column i A"
  by (simp add: row_def column_def transpose_def vec_eq_iff)

lemma column_transpose [simp]:
  fixes A:: "'a::semiring_1^_^_"
  shows "column i (transpose A) = row i A"
  by (simp add: row_def column_def transpose_def vec_eq_iff)

lemma rows_transpose [simp]: "rows(transpose (A::'a::semiring_1^_^_)) = columns A"
  by (auto simp add: rows_def columns_def row_transpose intro: set_eqI)

lemma columns_transpose [simp]: "columns(transpose (A::'a::semiring_1^_^_)) = rows A"
  by (metis transpose_transpose rows_transpose)

lemma transpose_scalar: "transpose (k *\<^sub>R A) = k *\<^sub>R transpose A"
  unfolding transpose_def
  by (simp add: vec_eq_iff)

lemma transpose_iff [iff]: "transpose A = transpose B \<longleftrightarrow> A = B"
  by (metis transpose_transpose)

lemma matrix_mult_transpose_dot_column:
  fixes A :: "real^'n^'n"
  shows "transpose A ** A = (\<chi> i j. (column i A) \<bullet> (column j A))"
  by (simp add: matrix_matrix_mult_def vec_eq_iff transpose_def column_def inner_vec_def)

lemma matrix_mult_transpose_dot_row:
  fixes A :: "real^'n^'n"
  shows "A ** transpose A = (\<chi> i j. (row i A) \<bullet> (row j A))"
  by (simp add: matrix_matrix_mult_def vec_eq_iff transpose_def row_def inner_vec_def)

text\<open>Two sometimes fruitful ways of looking at matrix-vector multiplication.\<close>

lemma matrix_mult_dot: "A *v x = (\<chi> i. A$i \<bullet> x)"
  by (simp add: matrix_vector_mult_def inner_vec_def)

lemma matrix_mult_sum:
  "(A::'a::comm_semiring_1^'n^'m) *v x = sum (\<lambda>i. (x$i) *s column i A) (UNIV:: 'n set)"
  by (simp add: matrix_vector_mult_def vec_eq_iff column_def mult.commute)

lemma vector_componentwise:
  "(x::'a::ring_1^'n) = (\<chi> j. \<Sum>i\<in>UNIV. (x$i) * (axis i 1 :: 'a^'n) $ j)"
  by (simp add: axis_def if_distrib sum.If_cases vec_eq_iff)

lemma basis_expansion: "sum (\<lambda>i. (x$i) *s axis i 1) UNIV = (x::('a::ring_1) ^'n)"
  by (auto simp add: axis_def vec_eq_iff if_distrib sum.If_cases cong del: if_weak_cong)

lemma linear_componentwise_expansion:
  fixes f:: "real ^'m \<Rightarrow> real ^ _"
  assumes lf: "linear f"
  shows "(f x)$j = sum (\<lambda>i. (x$i) * (f (axis i 1)$j)) (UNIV :: 'm set)" (is "?lhs = ?rhs")
proof -
  let ?M = "(UNIV :: 'm set)"
  let ?N = "(UNIV :: 'n set)"
  have "?rhs = (sum (\<lambda>i.(x$i) *\<^sub>R f (axis i 1) ) ?M)$j"
    unfolding sum_component by simp
  then show ?thesis
    unfolding linear_sum_mul[OF lf, symmetric]
    unfolding scalar_mult_eq_scaleR[symmetric]
    unfolding basis_expansion
    by simp
qed

subsection\<open>Inverse matrices  (not necessarily square)\<close>

definition
  "invertible(A::'a::semiring_1^'n^'m) \<longleftrightarrow> (\<exists>A'::'a^'m^'n. A ** A' = mat 1 \<and> A' ** A = mat 1)"

definition
  "matrix_inv(A:: 'a::semiring_1^'n^'m) =
    (SOME A'::'a^'m^'n. A ** A' = mat 1 \<and> A' ** A = mat 1)"

text\<open>Correspondence between matrices and linear operators.\<close>

definition matrix :: "('a::{plus,times, one, zero}^'m \<Rightarrow> 'a ^ 'n) \<Rightarrow> 'a^'m^'n"
  where "matrix f = (\<chi> i j. (f(axis j 1))$i)"

lemma matrix_id_mat_1: "matrix id = mat 1"
  by (simp add: mat_def matrix_def axis_def)

lemma matrix_scaleR: "(matrix (( *\<^sub>R) r)) = mat r"
  by (simp add: mat_def matrix_def axis_def if_distrib cong: if_cong)

lemma matrix_vector_mul_linear: "linear(\<lambda>x. A *v (x::real ^ _))"
  by (simp add: linear_iff matrix_vector_mult_def vec_eq_iff
      field_simps sum_distrib_left sum.distrib)

lemma
  fixes A :: "real^'n^'m"
  shows matrix_vector_mult_linear_continuous_at [continuous_intros]: "isCont (( *v) A) z"
    and matrix_vector_mult_linear_continuous_on [continuous_intros]: "continuous_on S (( *v) A)"
  by (simp_all add: linear_linear linear_continuous_at linear_continuous_on matrix_vector_mul_linear)

lemma matrix_vector_mult_add_distrib [algebra_simps]:
  "A *v (x + y) = A *v x + A *v y"
  by (vector matrix_vector_mult_def sum.distrib distrib_left)

lemma matrix_vector_mult_diff_distrib [algebra_simps]:
  fixes A :: "'a::ring_1^'n^'m"
  shows "A *v (x - y) = A *v x - A *v y"
  by (vector matrix_vector_mult_def sum_subtractf right_diff_distrib)

lemma matrix_vector_mult_scaleR[algebra_simps]:
  fixes A :: "real^'n^'m"
  shows "A *v (c *\<^sub>R x) = c *\<^sub>R (A *v x)"
  using linear_iff matrix_vector_mul_linear by blast

lemma matrix_vector_mult_0_right [simp]: "A *v 0 = 0"
  by (simp add: matrix_vector_mult_def vec_eq_iff)

lemma matrix_vector_mult_0 [simp]: "0 *v w = 0"
  by (simp add: matrix_vector_mult_def vec_eq_iff)

lemma matrix_vector_mult_add_rdistrib [algebra_simps]:
  "(A + B) *v x = (A *v x) + (B *v x)"
  by (vector matrix_vector_mult_def sum.distrib distrib_right)

lemma matrix_vector_mult_diff_rdistrib [algebra_simps]:
  fixes A :: "'a :: ring_1^'n^'m"
  shows "(A - B) *v x = (A *v x) - (B *v x)"
  by (vector matrix_vector_mult_def sum_subtractf left_diff_distrib)

lemma matrix_works:
  assumes lf: "linear f"
  shows "matrix f *v x = f (x::real ^ 'n)"
  apply (simp add: matrix_def matrix_vector_mult_def vec_eq_iff mult.commute)
  by (simp add: linear_componentwise_expansion lf)

lemma matrix_vector_mul: "linear f ==> f = (\<lambda>x. matrix f *v (x::real ^ 'n))"
  by (simp add: ext matrix_works)

declare matrix_vector_mul [symmetric, simp]

lemma matrix_of_matrix_vector_mul [simp]: "matrix(\<lambda>x. A *v (x :: real ^ 'n)) = A"
  by (simp add: matrix_eq matrix_vector_mul_linear matrix_works)

lemma matrix_compose:
  assumes lf: "linear (f::real^'n \<Rightarrow> real^'m)"
    and lg: "linear (g::real^'m \<Rightarrow> real^_)"
  shows "matrix (g \<circ> f) = matrix g ** matrix f"
  using lf lg linear_compose[OF lf lg] matrix_works[OF linear_compose[OF lf lg]]
  by (simp add: matrix_eq matrix_works matrix_vector_mul_assoc[symmetric] o_def)

lemma matrix_vector_column:
  "(A::'a::comm_semiring_1^'n^_) *v x = sum (\<lambda>i. (x$i) *s ((transpose A)$i)) (UNIV:: 'n set)"
  by (simp add: matrix_vector_mult_def transpose_def vec_eq_iff mult.commute)

lemma adjoint_matrix: "adjoint(\<lambda>x. (A::real^'n^'m) *v x) = (\<lambda>x. transpose A *v x)"
  apply (rule adjoint_unique)
  apply (simp add: transpose_def inner_vec_def matrix_vector_mult_def
    sum_distrib_right sum_distrib_left)
  apply (subst sum.swap)
  apply (auto simp add: ac_simps)
  done

lemma matrix_adjoint: assumes lf: "linear (f :: real^'n \<Rightarrow> real ^'m)"
  shows "matrix(adjoint f) = transpose(matrix f)"
  apply (subst matrix_vector_mul[OF lf])
  unfolding adjoint_matrix matrix_of_matrix_vector_mul
  apply rule
  done

lemma inj_matrix_vector_mult:
  fixes A::"'a::field^'n^'m"
  assumes "invertible A"
  shows "inj (( *v) A)"
  by (metis assms inj_on_inverseI invertible_def matrix_vector_mul_assoc matrix_vector_mul_lid)

lemma scalar_invertible:
  fixes A :: "real^'m^'n"
  assumes "k \<noteq> 0" and "invertible A"
  shows "invertible (k *\<^sub>R A)"
proof -
  obtain A' where "A ** A' = mat 1" and "A' ** A = mat 1"
    using assms unfolding invertible_def by auto
  with `k \<noteq> 0`
  have "(k *\<^sub>R A) ** ((1/k) *\<^sub>R A') = mat 1" "((1/k) *\<^sub>R A') ** (k *\<^sub>R A) = mat 1"
    by (simp_all add: assms matrix_scalar_ac)
  thus "invertible (k *\<^sub>R A)"
    unfolding invertible_def by auto
qed

lemma scalar_invertible_iff:
  fixes A :: "real^'m^'n"
  assumes "k \<noteq> 0" and "invertible A"
  shows "invertible (k *\<^sub>R A) \<longleftrightarrow> k \<noteq> 0 \<and> invertible A"
  by (simp add: assms scalar_invertible)

lemma vector_transpose_matrix [simp]: "x v* transpose A = A *v x"
  unfolding transpose_def vector_matrix_mult_def matrix_vector_mult_def
  by simp

lemma transpose_matrix_vector [simp]: "transpose A *v x = x v* A"
  unfolding transpose_def vector_matrix_mult_def matrix_vector_mult_def
  by simp

lemma vector_matrix_mul_rid:
  fixes v :: "('a::semiring_1)^'n"
  shows "v v* mat 1 = v"
  by (metis matrix_vector_mul_lid transpose_mat vector_transpose_matrix)

lemma scalar_vector_matrix_assoc:
  fixes k :: real and x :: "real^'n" and A :: "real^'m^'n"
  shows "(k *\<^sub>R x) v* A = k *\<^sub>R (x v* A)"
  by (metis matrix_vector_mult_scaleR transpose_matrix_vector)

lemma vector_scalar_matrix_ac:
  fixes k :: real and x :: "real^'n" and A :: "real^'m^'n"
  shows "x v* (k *\<^sub>R A) = k *\<^sub>R (x v* A)"
proof -
  have "x v* (k *\<^sub>R A) = (k *\<^sub>R x) v* A"
    unfolding vector_matrix_mult_def
    by (simp add: algebra_simps)
  with scalar_vector_matrix_assoc
  show "x v* (k *\<^sub>R A) = k *\<^sub>R (x v* A)"
    by auto
qed

lemma vector_matrix_left_distrib:
  fixes x y :: "real^'n" and A :: "real^'m^'n"
  shows "(x + y) v* A = x v* A + y v* A"
  unfolding vector_matrix_mult_def
  by (simp add: algebra_simps sum.distrib vec_eq_iff)


subsection\<open>Some bounds on components etc. relative to operator norm\<close>

lemma norm_column_le_onorm:
  fixes A :: "real^'n^'m"
  shows "norm(column i A) \<le> onorm(( *v) A)"
proof -
  have bl: "bounded_linear (( *v) A)"
    by (simp add: linear_linear matrix_vector_mul_linear)
  have "norm (\<chi> j. A $ j $ i) \<le> norm (A *v axis i 1)"
    by (simp add: matrix_mult_dot cart_eq_inner_axis)
  also have "\<dots> \<le> onorm (( *v) A)"
    using onorm [OF bl, of "axis i 1"] by auto
  finally have "norm (\<chi> j. A $ j $ i) \<le> onorm (( *v) A)" .
  then show ?thesis
    unfolding column_def .
qed

lemma matrix_component_le_onorm:
  fixes A :: "real^'n^'m"
  shows "\<bar>A $ i $ j\<bar> \<le> onorm(( *v) A)"
proof -
  have "\<bar>A $ i $ j\<bar> \<le> norm (\<chi> n. (A $ n $ j))"
    by (metis (full_types, lifting) component_le_norm_cart vec_lambda_beta)
  also have "\<dots> \<le> onorm (( *v) A)"
    by (metis (no_types) column_def norm_column_le_onorm)
  finally show ?thesis .
qed

lemma component_le_onorm:
  fixes f :: "real^'m \<Rightarrow> real^'n"
  shows "linear f \<Longrightarrow> \<bar>matrix f $ i $ j\<bar> \<le> onorm f"
  by (metis matrix_component_le_onorm matrix_vector_mul)

lemma onorm_le_matrix_component_sum:
  fixes A :: "real^'n^'m"
  shows "onorm(( *v) A) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)"
proof (rule onorm_le)
  fix x
  have "norm (A *v x) \<le> (\<Sum>i\<in>UNIV. \<bar>(A *v x) $ i\<bar>)"
    by (rule norm_le_l1_cart)
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> * norm x)"
  proof (rule sum_mono)
    fix i
    have "\<bar>(A *v x) $ i\<bar> \<le> \<bar>\<Sum>j\<in>UNIV. A $ i $ j * x $ j\<bar>"
      by (simp add: matrix_vector_mult_def)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j * x $ j\<bar>)"
      by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> * norm x)"
      by (rule sum_mono) (simp add: abs_mult component_le_norm_cart mult_left_mono)
    finally show "\<bar>(A *v x) $ i\<bar> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> * norm x)" .
  qed
  finally show "norm (A *v x) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>) * norm x"
    by (simp add: sum_distrib_right)
qed

lemma onorm_le_matrix_component:
  fixes A :: "real^'n^'m"
  assumes "\<And>i j. abs(A$i$j) \<le> B"
  shows "onorm(( *v) A) \<le> real (CARD('m)) * real (CARD('n)) * B"
proof (rule onorm_le)
  fix x :: "real^'n::_"
  have "norm (A *v x) \<le> (\<Sum>i\<in>UNIV. \<bar>(A *v x) $ i\<bar>)"
    by (rule norm_le_l1_cart)
  also have "\<dots> \<le> (\<Sum>i::'m \<in>UNIV. real (CARD('n)) * B * norm x)"
  proof (rule sum_mono)
    fix i
    have "\<bar>(A *v x) $ i\<bar> \<le> norm(A $ i) * norm x"
      by (simp add: matrix_mult_dot Cauchy_Schwarz_ineq2)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>) * norm x"
      by (simp add: mult_right_mono norm_le_l1_cart)
    also have "\<dots> \<le> real (CARD('n)) * B * norm x"
      by (simp add: assms sum_bounded_above mult_right_mono)
    finally show "\<bar>(A *v x) $ i\<bar> \<le> real (CARD('n)) * B * norm x" .
  qed
  also have "\<dots> \<le> CARD('m) * real (CARD('n)) * B * norm x"
    by simp
  finally show "norm (A *v x) \<le> CARD('m) * real (CARD('n)) * B * norm x" .
qed

subsection \<open>lambda skolemization on cartesian products\<close>

lemma lambda_skolem: "(\<forall>i. \<exists>x. P i x) \<longleftrightarrow>
   (\<exists>x::'a ^ 'n. \<forall>i. P i (x $ i))" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  let ?S = "(UNIV :: 'n set)"
  { assume H: "?rhs"
    then have ?lhs by auto }
  moreover
  { assume H: "?lhs"
    then obtain f where f:"\<forall>i. P i (f i)" unfolding choice_iff by metis
    let ?x = "(\<chi> i. (f i)) :: 'a ^ 'n"
    { fix i
      from f have "P i (f i)" by metis
      then have "P i (?x $ i)" by auto
    }
    hence "\<forall>i. P i (?x$i)" by metis
    hence ?rhs by metis }
  ultimately show ?thesis by metis
qed

lemma rational_approximation:
  assumes "e > 0"
  obtains r::real where "r \<in> \<rat>" "\<bar>r - x\<bar> < e"
  using Rats_dense_in_real [of "x - e/2" "x + e/2"] assms by auto

lemma matrix_rational_approximation:
  fixes A :: "real^'n^'m"
  assumes "e > 0"
  obtains B where "\<And>i j. B$i$j \<in> \<rat>" "onorm(\<lambda>x. (A - B) *v x) < e"
proof -
  have "\<forall>i j. \<exists>q \<in> \<rat>. \<bar>q - A $ i $ j\<bar> < e / (2 * CARD('m) * CARD('n))"
    using assms by (force intro: rational_approximation [of "e / (2 * CARD('m) * CARD('n))"])
  then obtain B where B: "\<And>i j. B$i$j \<in> \<rat>" and Bclo: "\<And>i j. \<bar>B$i$j - A $ i $ j\<bar> < e / (2 * CARD('m) * CARD('n))"
    by (auto simp: lambda_skolem Bex_def)
  show ?thesis
  proof
    have "onorm (( *v) (A - B)) \<le> real CARD('m) * real CARD('n) *
    (e / (2 * real CARD('m) * real CARD('n)))"
      apply (rule onorm_le_matrix_component)
      using Bclo by (simp add: abs_minus_commute less_imp_le)
    also have "\<dots> < e"
      using \<open>0 < e\<close> by (simp add: divide_simps)
    finally show "onorm (( *v) (A - B)) < e" .
  qed (use B in auto)
qed

lemma vector_sub_project_orthogonal_cart: "(b::real^'n) \<bullet> (x - ((b \<bullet> x) / (b \<bullet> b)) *s b) = 0"
  unfolding inner_simps scalar_mult_eq_scaleR by auto

lemma left_invertible_transpose:
  "(\<exists>(B). B ** transpose (A) = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B). A ** B = mat 1)"
  by (metis matrix_transpose_mul transpose_mat transpose_transpose)

lemma right_invertible_transpose:
  "(\<exists>(B). transpose (A) ** B = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B). B ** A = mat 1)"
  by (metis matrix_transpose_mul transpose_mat transpose_transpose)

lemma matrix_left_invertible_injective:
  fixes A :: "real^'n^'m"
  shows "(\<exists>B. B ** A = mat 1) \<longleftrightarrow> inj (( *v) A)"
proof safe
  fix B
  assume B: "B ** A = mat 1"
  show "inj (( *v) A)"
    unfolding inj_on_def
      by (metis B matrix_vector_mul_assoc matrix_vector_mul_lid)
next
  assume "inj (( *v) A)"
  with linear_injective_left_inverse[OF matrix_vector_mul_linear]
  obtain g where "linear g" and g: "g \<circ> ( *v) A = id"
    by blast
  have "matrix g ** A = mat 1"
    by (metis \<open>linear g\<close> g matrix_compose matrix_id_mat_1 matrix_of_matrix_vector_mul matrix_vector_mul_linear)
  then show "\<exists>B. B ** A = mat 1"
    by metis
qed

lemma matrix_left_invertible_ker:
  "(\<exists>B. (B::real ^'m^'n) ** (A::real^'n^'m) = mat 1) \<longleftrightarrow> (\<forall>x. A *v x = 0 \<longrightarrow> x = 0)"
  unfolding matrix_left_invertible_injective
  using linear_injective_0[OF matrix_vector_mul_linear, of A]
  by (simp add: inj_on_def)

lemma matrix_right_invertible_surjective:
  "(\<exists>B. (A::real^'n^'m) ** (B::real^'m^'n) = mat 1) \<longleftrightarrow> surj (\<lambda>x. A *v x)"
proof -
  { fix B :: "real ^'m^'n"
    assume AB: "A ** B = mat 1"
    { fix x :: "real ^ 'm"
      have "A *v (B *v x) = x"
        by (simp add: matrix_vector_mul_lid matrix_vector_mul_assoc AB) }
    hence "surj (( *v) A)" unfolding surj_def by metis }
  moreover
  { assume sf: "surj (( *v) A)"
    from linear_surjective_right_inverse[OF matrix_vector_mul_linear sf]
    obtain g:: "real ^'m \<Rightarrow> real ^'n" where g: "linear g" "( *v) A \<circ> g = id"
      by blast

    have "A ** (matrix g) = mat 1"
      unfolding matrix_eq  matrix_vector_mul_lid
        matrix_vector_mul_assoc[symmetric] matrix_works[OF g(1)]
      using g(2) unfolding o_def fun_eq_iff id_def
      .
    hence "\<exists>B. A ** (B::real^'m^'n) = mat 1" by blast
  }
  ultimately show ?thesis unfolding surj_def by blast
qed

lemma matrix_left_invertible_independent_columns:
  fixes A :: "real^'n^'m"
  shows "(\<exists>(B::real ^'m^'n). B ** A = mat 1) \<longleftrightarrow>
      (\<forall>c. sum (\<lambda>i. c i *s column i A) (UNIV :: 'n set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  let ?U = "UNIV :: 'n set"
  { assume k: "\<forall>x. A *v x = 0 \<longrightarrow> x = 0"
    { fix c i
      assume c: "sum (\<lambda>i. c i *s column i A) ?U = 0" and i: "i \<in> ?U"
      let ?x = "\<chi> i. c i"
      have th0:"A *v ?x = 0"
        using c
        unfolding matrix_mult_sum vec_eq_iff
        by auto
      from k[rule_format, OF th0] i
      have "c i = 0" by (vector vec_eq_iff)}
    hence ?rhs by blast }
  moreover
  { assume H: ?rhs
    { fix x assume x: "A *v x = 0"
      let ?c = "\<lambda>i. ((x$i ):: real)"
      from H[rule_format, of ?c, unfolded matrix_mult_sum[symmetric], OF x]
      have "x = 0" by vector }
  }
  ultimately show ?thesis unfolding matrix_left_invertible_ker by blast
qed

lemma matrix_right_invertible_independent_rows:
  fixes A :: "real^'n^'m"
  shows "(\<exists>(B::real^'m^'n). A ** B = mat 1) \<longleftrightarrow>
    (\<forall>c. sum (\<lambda>i. c i *s row i A) (UNIV :: 'm set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
  unfolding left_invertible_transpose[symmetric]
    matrix_left_invertible_independent_columns
  by (simp add: column_transpose)

lemma matrix_right_invertible_span_columns:
  "(\<exists>(B::real ^'n^'m). (A::real ^'m^'n) ** B = mat 1) \<longleftrightarrow>
    span (columns A) = UNIV" (is "?lhs = ?rhs")
proof -
  let ?U = "UNIV :: 'm set"
  have fU: "finite ?U" by simp
  have lhseq: "?lhs \<longleftrightarrow> (\<forall>y. \<exists>(x::real^'m). sum (\<lambda>i. (x$i) *s column i A) ?U = y)"
    unfolding matrix_right_invertible_surjective matrix_mult_sum surj_def
    apply (subst eq_commute)
    apply rule
    done
  have rhseq: "?rhs \<longleftrightarrow> (\<forall>x. x \<in> span (columns A))" by blast
  { assume h: ?lhs
    { fix x:: "real ^'n"
      from h[unfolded lhseq, rule_format, of x] obtain y :: "real ^'m"
        where y: "sum (\<lambda>i. (y$i) *s column i A) ?U = x" by blast
      have "x \<in> span (columns A)"
        unfolding y[symmetric]
        apply (rule span_sum)
        unfolding scalar_mult_eq_scaleR
        apply (rule span_mul)
        apply (rule span_superset)
        unfolding columns_def
        apply blast
        done
    }
    then have ?rhs unfolding rhseq by blast }
  moreover
  { assume h:?rhs
    let ?P = "\<lambda>(y::real ^'n). \<exists>(x::real^'m). sum (\<lambda>i. (x$i) *s column i A) ?U = y"
    { fix y
      have "?P y"
      proof (rule span_induct_alt[of ?P "columns A", folded scalar_mult_eq_scaleR])
        show "\<exists>x::real ^ 'm. sum (\<lambda>i. (x$i) *s column i A) ?U = 0"
          by (rule exI[where x=0], simp)
      next
        fix c y1 y2
        assume y1: "y1 \<in> columns A" and y2: "?P y2"
        from y1 obtain i where i: "i \<in> ?U" "y1 = column i A"
          unfolding columns_def by blast
        from y2 obtain x:: "real ^'m" where
          x: "sum (\<lambda>i. (x$i) *s column i A) ?U = y2" by blast
        let ?x = "(\<chi> j. if j = i then c + (x$i) else (x$j))::real^'m"
        show "?P (c*s y1 + y2)"
        proof (rule exI[where x= "?x"], vector, auto simp add: i x[symmetric] if_distrib distrib_left cond_application_beta cong del: if_weak_cong)
          fix j
          have th: "\<forall>xa \<in> ?U. (if xa = i then (c + (x$i)) * ((column xa A)$j)
              else (x$xa) * ((column xa A$j))) = (if xa = i then c * ((column i A)$j) else 0) + ((x$xa) * ((column xa A)$j))"
            using i(1) by (simp add: field_simps)
          have "sum (\<lambda>xa. if xa = i then (c + (x$i)) * ((column xa A)$j)
              else (x$xa) * ((column xa A$j))) ?U = sum (\<lambda>xa. (if xa = i then c * ((column i A)$j) else 0) + ((x$xa) * ((column xa A)$j))) ?U"
            apply (rule sum.cong[OF refl])
            using th apply blast
            done
          also have "\<dots> = sum (\<lambda>xa. if xa = i then c * ((column i A)$j) else 0) ?U + sum (\<lambda>xa. ((x$xa) * ((column xa A)$j))) ?U"
            by (simp add: sum.distrib)
          also have "\<dots> = c * ((column i A)$j) + sum (\<lambda>xa. ((x$xa) * ((column xa A)$j))) ?U"
            unfolding sum.delta[OF fU]
            using i(1) by simp
          finally show "sum (\<lambda>xa. if xa = i then (c + (x$i)) * ((column xa A)$j)
            else (x$xa) * ((column xa A$j))) ?U = c * ((column i A)$j) + sum (\<lambda>xa. ((x$xa) * ((column xa A)$j))) ?U" .
        qed
      next
        show "y \<in> span (columns A)"
          unfolding h by blast
      qed
    }
    then have ?lhs unfolding lhseq ..
  }
  ultimately show ?thesis by blast
qed

lemma matrix_left_invertible_span_rows:
  "(\<exists>(B::real^'m^'n). B ** (A::real^'n^'m) = mat 1) \<longleftrightarrow> span (rows A) = UNIV"
  unfolding right_invertible_transpose[symmetric]
  unfolding columns_transpose[symmetric]
  unfolding matrix_right_invertible_span_columns
  ..

text \<open>The same result in terms of square matrices.\<close>

lemma matrix_left_right_inverse:
  fixes A A' :: "real ^'n^'n"
  shows "A ** A' = mat 1 \<longleftrightarrow> A' ** A = mat 1"
proof -
  { fix A A' :: "real ^'n^'n"
    assume AA': "A ** A' = mat 1"
    have sA: "surj (( *v) A)"
      using AA' matrix_right_invertible_surjective by auto
    from linear_surjective_isomorphism[OF matrix_vector_mul_linear sA]
    obtain f' :: "real ^'n \<Rightarrow> real ^'n"
      where f': "linear f'" "\<forall>x. f' (A *v x) = x" "\<forall>x. A *v f' x = x" by blast
    have th: "matrix f' ** A = mat 1"
      by (simp add: matrix_eq matrix_works[OF f'(1)]
          matrix_vector_mul_assoc[symmetric] matrix_vector_mul_lid f'(2)[rule_format])
    hence "(matrix f' ** A) ** A' = mat 1 ** A'" by simp
    hence "matrix f' = A'"
      by (simp add: matrix_mul_assoc[symmetric] AA' matrix_mul_rid matrix_mul_lid)
    hence "matrix f' ** A = A' ** A" by simp
    hence "A' ** A = mat 1" by (simp add: th)
  }
  then show ?thesis by blast
qed

lemma invertible_mult:
  fixes A B :: "real^'n^'n"
  assumes "invertible A" and "invertible B"
  shows "invertible (A ** B)"
  by (metis (no_types, hide_lams) assms invertible_def matrix_left_right_inverse matrix_mul_assoc matrix_mul_lid)

lemma transpose_invertible:
  fixes A :: "real^'n^'n"
  assumes "invertible A"
  shows "invertible (transpose A)"
  by (meson assms invertible_def matrix_left_right_inverse right_invertible_transpose)

text \<open>Considering an n-element vector as an n-by-1 or 1-by-n matrix.\<close>

definition "rowvector v = (\<chi> i j. (v$j))"

definition "columnvector v = (\<chi> i j. (v$i))"

lemma transpose_columnvector: "transpose(columnvector v) = rowvector v"
  by (simp add: transpose_def rowvector_def columnvector_def vec_eq_iff)

lemma transpose_rowvector: "transpose(rowvector v) = columnvector v"
  by (simp add: transpose_def columnvector_def rowvector_def vec_eq_iff)

lemma dot_rowvector_columnvector: "columnvector (A *v v) = A ** columnvector v"
  by (vector columnvector_def matrix_matrix_mult_def matrix_vector_mult_def)

lemma dot_matrix_product:
  "(x::real^'n) \<bullet> y = (((rowvector x ::real^'n^1) ** (columnvector y :: real^1^'n))$1)$1"
  by (vector matrix_matrix_mult_def rowvector_def columnvector_def inner_vec_def)

lemma dot_matrix_vector_mul:
  fixes A B :: "real ^'n ^'n" and x y :: "real ^'n"
  shows "(A *v x) \<bullet> (B *v y) =
      (((rowvector x :: real^'n^1) ** ((transpose A ** B) ** (columnvector y :: real ^1^'n)))$1)$1"
  unfolding dot_matrix_product transpose_columnvector[symmetric]
    dot_rowvector_columnvector matrix_transpose_mul matrix_mul_assoc ..

lemma infnorm_cart:"infnorm (x::real^'n) = Sup {\<bar>x$i\<bar> |i. i\<in>UNIV}"
  by (simp add: infnorm_def inner_axis Basis_vec_def) (metis (lifting) inner_axis real_inner_1_right)

lemma component_le_infnorm_cart: "\<bar>x$i\<bar> \<le> infnorm (x::real^'n)"
  using Basis_le_infnorm[of "axis i 1" x]
  by (simp add: Basis_vec_def axis_eq_axis inner_axis)

lemma continuous_component[continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. f x $ i)"
  unfolding continuous_def by (rule tendsto_vec_nth)

lemma continuous_on_component[continuous_intros]: "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. f x $ i)"
  unfolding continuous_on_def by (fast intro: tendsto_vec_nth)

lemma continuous_on_vec_lambda[continuous_intros]:
  "(\<And>i. continuous_on S (f i)) \<Longrightarrow> continuous_on S (\<lambda>x. \<chi> i. f i x)"
  unfolding continuous_on_def by (auto intro: tendsto_vec_lambda)

lemma closed_positive_orthant: "closed {x::real^'n. \<forall>i. 0 \<le>x$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le continuous_on_const continuous_on_id continuous_on_component)

lemma bounded_component_cart: "bounded s \<Longrightarrow> bounded ((\<lambda>x. x $ i) ` s)"
  unfolding bounded_def
  apply clarify
  apply (rule_tac x="x $ i" in exI)
  apply (rule_tac x="e" in exI)
  apply clarify
  apply (rule order_trans [OF dist_vec_nth_le], simp)
  done

lemma compact_lemma_cart:
  fixes f :: "nat \<Rightarrow> 'a::heine_borel ^ 'n"
  assumes f: "bounded (range f)"
  shows "\<exists>l r. strict_mono r \<and>
        (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) $ i) (l $ i) < e) sequentially)"
    (is "?th d")
proof -
  have "\<forall>d' \<subseteq> d. ?th d'"
    by (rule compact_lemma_general[where unproj=vec_lambda])
      (auto intro!: f bounded_component_cart simp: vec_lambda_eta)
  then show "?th d" by simp
qed

instance vec :: (heine_borel, finite) heine_borel
proof
  fix f :: "nat \<Rightarrow> 'a ^ 'b"
  assume f: "bounded (range f)"
  then obtain l r where r: "strict_mono r"
      and l: "\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>UNIV. dist (f (r n) $ i) (l $ i) < e) sequentially"
    using compact_lemma_cart [OF f] by blast
  let ?d = "UNIV::'b set"
  { fix e::real assume "e>0"
    hence "0 < e / (real_of_nat (card ?d))"
      using zero_less_card_finite divide_pos_pos[of e, of "real_of_nat (card ?d)"] by auto
    with l have "eventually (\<lambda>n. \<forall>i. dist (f (r n) $ i) (l $ i) < e / (real_of_nat (card ?d))) sequentially"
      by simp
    moreover
    { fix n
      assume n: "\<forall>i. dist (f (r n) $ i) (l $ i) < e / (real_of_nat (card ?d))"
      have "dist (f (r n)) l \<le> (\<Sum>i\<in>?d. dist (f (r n) $ i) (l $ i))"
        unfolding dist_vec_def using zero_le_dist by (rule L2_set_le_sum)
      also have "\<dots> < (\<Sum>i\<in>?d. e / (real_of_nat (card ?d)))"
        by (rule sum_strict_mono) (simp_all add: n)
      finally have "dist (f (r n)) l < e" by simp
    }
    ultimately have "eventually (\<lambda>n. dist (f (r n)) l < e) sequentially"
      by (rule eventually_mono)
  }
  hence "((f \<circ> r) \<longlongrightarrow> l) sequentially" unfolding o_def tendsto_iff by simp
  with r show "\<exists>l r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially" by auto
qed

lemma interval_cart:
  fixes a :: "real^'n"
  shows "box a b = {x::real^'n. \<forall>i. a$i < x$i \<and> x$i < b$i}"
    and "cbox a b = {x::real^'n. \<forall>i. a$i \<le> x$i \<and> x$i \<le> b$i}"
  by (auto simp add: set_eq_iff less_vec_def less_eq_vec_def mem_box Basis_vec_def inner_axis)

lemma mem_box_cart:
  fixes a :: "real^'n"
  shows "x \<in> box a b \<longleftrightarrow> (\<forall>i. a$i < x$i \<and> x$i < b$i)"
    and "x \<in> cbox a b \<longleftrightarrow> (\<forall>i. a$i \<le> x$i \<and> x$i \<le> b$i)"
  using interval_cart[of a b] by (auto simp add: set_eq_iff less_vec_def less_eq_vec_def)

lemma interval_eq_empty_cart:
  fixes a :: "real^'n"
  shows "(box a b = {} \<longleftrightarrow> (\<exists>i. b$i \<le> a$i))" (is ?th1)
    and "(cbox a b = {} \<longleftrightarrow> (\<exists>i. b$i < a$i))" (is ?th2)
proof -
  { fix i x assume as:"b$i \<le> a$i" and x:"x\<in>box a b"
    hence "a $ i < x $ i \<and> x $ i < b $ i" unfolding mem_box_cart by auto
    hence "a$i < b$i" by auto
    hence False using as by auto }
  moreover
  { assume as:"\<forall>i. \<not> (b$i \<le> a$i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    { fix i
      have "a$i < b$i" using as[THEN spec[where x=i]] by auto
      hence "a$i < ((1/2) *\<^sub>R (a+b)) $ i" "((1/2) *\<^sub>R (a+b)) $ i < b$i"
        unfolding vector_smult_component and vector_add_component
        by auto }
    hence "box a b \<noteq> {}" using mem_box_cart(1)[of "?x" a b] by auto }
  ultimately show ?th1 by blast

  { fix i x assume as:"b$i < a$i" and x:"x\<in>cbox a b"
    hence "a $ i \<le> x $ i \<and> x $ i \<le> b $ i" unfolding mem_box_cart by auto
    hence "a$i \<le> b$i" by auto
    hence False using as by auto }
  moreover
  { assume as:"\<forall>i. \<not> (b$i < a$i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    { fix i
      have "a$i \<le> b$i" using as[THEN spec[where x=i]] by auto
      hence "a$i \<le> ((1/2) *\<^sub>R (a+b)) $ i" "((1/2) *\<^sub>R (a+b)) $ i \<le> b$i"
        unfolding vector_smult_component and vector_add_component
        by auto }
    hence "cbox a b \<noteq> {}" using mem_box_cart(2)[of "?x" a b] by auto  }
  ultimately show ?th2 by blast
qed

lemma interval_ne_empty_cart:
  fixes a :: "real^'n"
  shows "cbox a b \<noteq> {} \<longleftrightarrow> (\<forall>i. a$i \<le> b$i)"
    and "box a b \<noteq> {} \<longleftrightarrow> (\<forall>i. a$i < b$i)"
  unfolding interval_eq_empty_cart[of a b] by (auto simp add: not_less not_le)
    (* BH: Why doesn't just "auto" work here? *)

lemma subset_interval_imp_cart:
  fixes a :: "real^'n"
  shows "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> cbox c d \<subseteq> cbox a b"
    and "(\<forall>i. a$i < c$i \<and> d$i < b$i) \<Longrightarrow> cbox c d \<subseteq> box a b"
    and "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> box c d \<subseteq> cbox a b"
    and "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> box c d \<subseteq> box a b"
  unfolding subset_eq[unfolded Ball_def] unfolding mem_box_cart
  by (auto intro: order_trans less_le_trans le_less_trans less_imp_le) (* BH: Why doesn't just "auto" work here? *)

lemma interval_sing:
  fixes a :: "'a::linorder^'n"
  shows "{a .. a} = {a} \<and> {a<..<a} = {}"
  apply (auto simp add: set_eq_iff less_vec_def less_eq_vec_def vec_eq_iff)
  done

lemma subset_interval_cart:
  fixes a :: "real^'n"
  shows "cbox c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i. c$i \<le> d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th1)
    and "cbox c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i. c$i \<le> d$i) --> (\<forall>i. a$i < c$i \<and> d$i < b$i)" (is ?th2)
    and "box c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i. c$i < d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th3)
    and "box c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i. c$i < d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th4)
  using subset_box[of c d a b] by (simp_all add: Basis_vec_def inner_axis)

lemma disjoint_interval_cart:
  fixes a::"real^'n"
  shows "cbox a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i. (b$i < a$i \<or> d$i < c$i \<or> b$i < c$i \<or> d$i < a$i))" (is ?th1)
    and "cbox a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i. (b$i < a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th2)
    and "box a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i. (b$i \<le> a$i \<or> d$i < c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th3)
    and "box a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i. (b$i \<le> a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th4)
  using disjoint_interval[of a b c d] by (simp_all add: Basis_vec_def inner_axis)

lemma Int_interval_cart:
  fixes a :: "real^'n"
  shows "cbox a b \<inter> cbox c d =  {(\<chi> i. max (a$i) (c$i)) .. (\<chi> i. min (b$i) (d$i))}"
  unfolding Int_interval
  by (auto simp: mem_box less_eq_vec_def)
    (auto simp: Basis_vec_def inner_axis)

lemma closed_interval_left_cart:
  fixes b :: "real^'n"
  shows "closed {x::real^'n. \<forall>i. x$i \<le> b$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le continuous_on_const continuous_on_id continuous_on_component)

lemma closed_interval_right_cart:
  fixes a::"real^'n"
  shows "closed {x::real^'n. \<forall>i. a$i \<le> x$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le continuous_on_const continuous_on_id continuous_on_component)

lemma is_interval_cart:
  "is_interval (s::(real^'n) set) \<longleftrightarrow>
    (\<forall>a\<in>s. \<forall>b\<in>s. \<forall>x. (\<forall>i. ((a$i \<le> x$i \<and> x$i \<le> b$i) \<or> (b$i \<le> x$i \<and> x$i \<le> a$i))) \<longrightarrow> x \<in> s)"
  by (simp add: is_interval_def Ball_def Basis_vec_def inner_axis imp_ex)

lemma closed_halfspace_component_le_cart: "closed {x::real^'n. x$i \<le> a}"
  by (simp add: closed_Collect_le continuous_on_const continuous_on_id continuous_on_component)

lemma closed_halfspace_component_ge_cart: "closed {x::real^'n. x$i \<ge> a}"
  by (simp add: closed_Collect_le continuous_on_const continuous_on_id continuous_on_component)

lemma open_halfspace_component_lt_cart: "open {x::real^'n. x$i < a}"
  by (simp add: open_Collect_less continuous_on_const continuous_on_id continuous_on_component)

lemma open_halfspace_component_gt_cart: "open {x::real^'n. x$i  > a}"
  by (simp add: open_Collect_less continuous_on_const continuous_on_id continuous_on_component)

lemma Lim_component_le_cart:
  fixes f :: "'a \<Rightarrow> real^'n"
  assumes "(f \<longlongrightarrow> l) net" "\<not> (trivial_limit net)"  "eventually (\<lambda>x. f x $i \<le> b) net"
  shows "l$i \<le> b"
  by (rule tendsto_le[OF assms(2) tendsto_const tendsto_vec_nth, OF assms(1, 3)])

lemma Lim_component_ge_cart:
  fixes f :: "'a \<Rightarrow> real^'n"
  assumes "(f \<longlongrightarrow> l) net"  "\<not> (trivial_limit net)"  "eventually (\<lambda>x. b \<le> (f x)$i) net"
  shows "b \<le> l$i"
  by (rule tendsto_le[OF assms(2) tendsto_vec_nth tendsto_const, OF assms(1, 3)])

lemma Lim_component_eq_cart:
  fixes f :: "'a \<Rightarrow> real^'n"
  assumes net: "(f \<longlongrightarrow> l) net" "~(trivial_limit net)" and ev:"eventually (\<lambda>x. f(x)$i = b) net"
  shows "l$i = b"
  using ev[unfolded order_eq_iff eventually_conj_iff] and
    Lim_component_ge_cart[OF net, of b i] and
    Lim_component_le_cart[OF net, of i b] by auto

lemma connected_ivt_component_cart:
  fixes x :: "real^'n"
  shows "connected s \<Longrightarrow> x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> x$k \<le> a \<Longrightarrow> a \<le> y$k \<Longrightarrow> (\<exists>z\<in>s.  z$k = a)"
  using connected_ivt_hyperplane[of s x y "axis k 1" a]
  by (auto simp add: inner_axis inner_commute)

lemma subspace_substandard_cart: "subspace {x::real^_. (\<forall>i. P i \<longrightarrow> x$i = 0)}"
  unfolding subspace_def by auto

lemma closed_substandard_cart:
  "closed {x::'a::real_normed_vector ^ 'n. \<forall>i. P i \<longrightarrow> x$i = 0}"
proof -
  { fix i::'n
    have "closed {x::'a ^ 'n. P i \<longrightarrow> x$i = 0}"
      by (cases "P i") (simp_all add: closed_Collect_eq continuous_on_const continuous_on_id continuous_on_component) }
  thus ?thesis
    unfolding Collect_all_eq by (simp add: closed_INT)
qed

lemma dim_substandard_cart: "dim {x::real^'n. \<forall>i. i \<notin> d \<longrightarrow> x$i = 0} = card d"
  (is "dim ?A = _")
proof -
  let ?a = "\<lambda>x. axis x 1 :: real^'n"
  have *: "{x. \<forall>i\<in>Basis. i \<notin> ?a ` d \<longrightarrow> x \<bullet> i = 0} = ?A"
    by (auto simp: image_iff Basis_vec_def axis_eq_axis inner_axis)
  have "?a ` d \<subseteq> Basis"
    by (auto simp: Basis_vec_def)
  thus ?thesis
    using dim_substandard[of "?a ` d"] card_image[of ?a d]
    by (auto simp: axis_eq_axis inj_on_def *)
qed

lemma dim_subset_UNIV_cart:
  fixes S :: "(real^'n) set"
  shows "dim S \<le> CARD('n)"
  by (metis dim_subset_UNIV DIM_cart DIM_real mult.right_neutral)

lemma affinity_inverses:
  assumes m0: "m \<noteq> (0::'a::field)"
  shows "(\<lambda>x. m *s x + c) \<circ> (\<lambda>x. inverse(m) *s x + (-(inverse(m) *s c))) = id"
  "(\<lambda>x. inverse(m) *s x + (-(inverse(m) *s c))) \<circ> (\<lambda>x. m *s x + c) = id"
  using m0
  apply (auto simp add: fun_eq_iff vector_add_ldistrib diff_conv_add_uminus simp del: add_uminus_conv_diff)
  apply (simp_all add: vector_smult_lneg[symmetric] vector_smult_assoc vector_sneg_minus1 [symmetric])
  done

lemma vector_affinity_eq:
  assumes m0: "(m::'a::field) \<noteq> 0"
  shows "m *s x + c = y \<longleftrightarrow> x = inverse m *s y + -(inverse m *s c)"
proof
  assume h: "m *s x + c = y"
  hence "m *s x = y - c" by (simp add: field_simps)
  hence "inverse m *s (m *s x) = inverse m *s (y - c)" by simp
  then show "x = inverse m *s y + - (inverse m *s c)"
    using m0 by (simp add: vector_smult_assoc vector_ssub_ldistrib)
next
  assume h: "x = inverse m *s y + - (inverse m *s c)"
  show "m *s x + c = y" unfolding h
    using m0 by (simp add: vector_smult_assoc vector_ssub_ldistrib)
qed

lemma vector_eq_affinity:
    "(m::'a::field) \<noteq> 0 ==> (y = m *s x + c \<longleftrightarrow> inverse(m) *s y + -(inverse(m) *s c) = x)"
  using vector_affinity_eq[where m=m and x=x and y=y and c=c]
  by metis

lemma vector_cart:
  fixes f :: "real^'n \<Rightarrow> real"
  shows "(\<chi> i. f (axis i 1)) = (\<Sum>i\<in>Basis. f i *\<^sub>R i)"
  unfolding euclidean_eq_iff[where 'a="real^'n"]
  by simp (simp add: Basis_vec_def inner_axis)

lemma const_vector_cart:"((\<chi> i. d)::real^'n) = (\<Sum>i\<in>Basis. d *\<^sub>R i)"
  by (rule vector_cart)

subsection "Convex Euclidean Space"

lemma Cart_1:"(1::real^'n) = \<Sum>Basis"
  using const_vector_cart[of 1] by (simp add: one_vec_def)

declare vector_add_ldistrib[simp] vector_ssub_ldistrib[simp] vector_smult_assoc[simp] vector_smult_rneg[simp]
declare vector_sadd_rdistrib[simp] vector_sub_rdistrib[simp]

lemmas vector_component_simps = vector_minus_component vector_smult_component vector_add_component less_eq_vec_def vec_lambda_beta vector_uminus_component

lemma convex_box_cart:
  assumes "\<And>i. convex {x. P i x}"
  shows "convex {x. \<forall>i. P i (x$i)}"
  using assms unfolding convex_def by auto

lemma convex_positive_orthant_cart: "convex {x::real^'n. (\<forall>i. 0 \<le> x$i)}"
  by (rule convex_box_cart) (simp add: atLeast_def[symmetric])

lemma unit_interval_convex_hull_cart:
  "cbox (0::real^'n) 1 = convex hull {x. \<forall>i. (x$i = 0) \<or> (x$i = 1)}"
  unfolding Cart_1 unit_interval_convex_hull[where 'a="real^'n"] box_real[symmetric]
  by (rule arg_cong[where f="\<lambda>x. convex hull x"]) (simp add: Basis_vec_def inner_axis)

lemma cube_convex_hull_cart:
  assumes "0 < d"
  obtains s::"(real^'n) set"
    where "finite s" "cbox (x - (\<chi> i. d)) (x + (\<chi> i. d)) = convex hull s"
proof -
  from assms obtain s where "finite s"
    and "cbox (x - sum (( *\<^sub>R) d) Basis) (x + sum (( *\<^sub>R) d) Basis) = convex hull s"
    by (rule cube_convex_hull)
  with that[of s] show thesis
    by (simp add: const_vector_cart)
qed


subsection "Derivative"

definition "jacobian f net = matrix(frechet_derivative f net)"

lemma jacobian_works:
  "(f::(real^'a) \<Rightarrow> (real^'b)) differentiable net \<longleftrightarrow>
    (f has_derivative (\<lambda>h. (jacobian f net) *v h)) net" (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: frechet_derivative_works has_derivative_linear jacobian_def)
next
  assume ?rhs then show ?lhs
    by (rule differentiableI)
qed


subsection \<open>Component of the differential must be zero if it exists at a local
  maximum or minimum for that corresponding component\<close>

lemma differential_zero_maxmin_cart:
  fixes f::"real^'a \<Rightarrow> real^'b"
  assumes "0 < e" "((\<forall>y \<in> ball x e. (f y)$k \<le> (f x)$k) \<or> (\<forall>y\<in>ball x e. (f x)$k \<le> (f y)$k))"
    "f differentiable (at x)"
  shows "jacobian f (at x) $ k = 0"
  using differential_zero_maxmin_component[of "axis k 1" e x f] assms
    vector_cart[of "\<lambda>j. frechet_derivative f (at x) j $ k"]
  by (simp add: Basis_vec_def axis_eq_axis inner_axis jacobian_def matrix_def)

subsection \<open>Lemmas for working on @{typ "real^1"}\<close>

lemma forall_1[simp]: "(\<forall>i::1. P i) \<longleftrightarrow> P 1"
  by (metis (full_types) num1_eq_iff)

lemma ex_1[simp]: "(\<exists>x::1. P x) \<longleftrightarrow> P 1"
  by auto (metis (full_types) num1_eq_iff)

lemma exhaust_2:
  fixes x :: 2
  shows "x = 1 \<or> x = 2"
proof (induct x)
  case (of_int z)
  then have "0 \<le> z" and "z < 2" by simp_all
  then have "z = 0 | z = 1" by arith
  then show ?case by auto
qed

lemma forall_2: "(\<forall>i::2. P i) \<longleftrightarrow> P 1 \<and> P 2"
  by (metis exhaust_2)

lemma exhaust_3:
  fixes x :: 3
  shows "x = 1 \<or> x = 2 \<or> x = 3"
proof (induct x)
  case (of_int z)
  then have "0 \<le> z" and "z < 3" by simp_all
  then have "z = 0 \<or> z = 1 \<or> z = 2" by arith
  then show ?case by auto
qed

lemma forall_3: "(\<forall>i::3. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3"
  by (metis exhaust_3)

lemma UNIV_1 [simp]: "UNIV = {1::1}"
  by (auto simp add: num1_eq_iff)

lemma UNIV_2: "UNIV = {1::2, 2::2}"
  using exhaust_2 by auto

lemma UNIV_3: "UNIV = {1::3, 2::3, 3::3}"
  using exhaust_3 by auto

lemma sum_1: "sum f (UNIV::1 set) = f 1"
  unfolding UNIV_1 by simp

lemma sum_2: "sum f (UNIV::2 set) = f 1 + f 2"
  unfolding UNIV_2 by simp

lemma sum_3: "sum f (UNIV::3 set) = f 1 + f 2 + f 3"
  unfolding UNIV_3 by (simp add: ac_simps)

lemma num1_eqI:
  fixes a::num1 shows "a = b"
  by (metis (full_types) UNIV_1 UNIV_I empty_iff insert_iff)

lemma num1_eq1 [simp]:
  fixes a::num1 shows "a = 1"
  by (rule num1_eqI)

instantiation num1 :: cart_one
begin

instance
proof
  show "CARD(1) = Suc 0" by auto
qed

end

instantiation num1 :: linorder begin
definition "a < b \<longleftrightarrow> Rep_num1 a < Rep_num1 b"
definition "a \<le> b \<longleftrightarrow> Rep_num1 a \<le> Rep_num1 b"
instance
  by intro_classes (auto simp: less_eq_num1_def less_num1_def intro: num1_eqI)
end

instance num1 :: wellorder
  by intro_classes (auto simp: less_eq_num1_def less_num1_def)

subsection\<open>The collapse of the general concepts to dimension one\<close>

lemma vector_one: "(x::'a ^1) = (\<chi> i. (x$1))"
  by (simp add: vec_eq_iff)

lemma forall_one: "(\<forall>(x::'a ^1). P x) \<longleftrightarrow> (\<forall>x. P(\<chi> i. x))"
  apply auto
  apply (erule_tac x= "x$1" in allE)
  apply (simp only: vector_one[symmetric])
  done

lemma norm_vector_1: "norm (x :: _^1) = norm (x$1)"
  by (simp add: norm_vec_def)

lemma dist_vector_1:
  fixes x :: "'a::real_normed_vector^1"
  shows "dist x y = dist (x$1) (y$1)"
  by (simp add: dist_norm norm_vector_1)

lemma norm_real: "norm(x::real ^ 1) = \<bar>x$1\<bar>"
  by (simp add: norm_vector_1)

lemma dist_real: "dist(x::real ^ 1) y = \<bar>(x$1) - (y$1)\<bar>"
  by (auto simp add: norm_real dist_norm)

subsection\<open> Rank of a matrix\<close>

text\<open>Equivalence of row and column rank is taken from George Mackiw's paper, Mathematics Magazine 1995, p. 285.\<close>

lemma matrix_vector_mult_in_columnspace:
  fixes A :: "real^'n^'m"
  shows "(A *v x) \<in> span(columns A)"
  apply (simp add: matrix_vector_column columns_def transpose_def column_def)
  apply (intro span_sum span_mul)
  apply (force intro: span_superset)
  done

lemma orthogonal_nullspace_rowspace:
  fixes A :: "real^'n^'m"
  assumes 0: "A *v x = 0" and y: "y \<in> span(rows A)"
  shows "orthogonal x y"
proof (rule span_induct [OF y])
  show "subspace {a. orthogonal x a}"
    by (simp add: subspace_orthogonal_to_vector)
next
  fix v
  assume "v \<in> rows A"
  then obtain i where "v = row i A"
    by (auto simp: rows_def)
  with 0 show "orthogonal x v"
    unfolding orthogonal_def inner_vec_def matrix_vector_mult_def row_def
    by (simp add: mult.commute) (metis (no_types) vec_lambda_beta zero_index)
qed

lemma nullspace_inter_rowspace:
  fixes A :: "real^'n^'m"
  shows "A *v x = 0 \<and> x \<in> span(rows A) \<longleftrightarrow> x = 0"
  using orthogonal_nullspace_rowspace orthogonal_self by auto

lemma matrix_vector_mul_injective_on_rowspace:
  fixes A :: "real^'n^'m"
  shows "\<lbrakk>A *v x = A *v y; x \<in> span(rows A); y \<in> span(rows A)\<rbrakk> \<Longrightarrow> x = y"
  using nullspace_inter_rowspace [of A "x-y"]
  by (metis eq_iff_diff_eq_0 matrix_vector_mult_diff_distrib span_diff)

definition rank :: "real^'n^'m=>nat"
  where "rank A \<equiv> dim(columns A)"

lemma dim_rows_le_dim_columns:
  fixes A :: "real^'n^'m"
  shows "dim(rows A) \<le> dim(columns A)"
proof -
  have "dim (span (rows A)) \<le> dim (span (columns A))"
  proof -
    obtain B where "independent B" "span(rows A) \<subseteq> span B"
              and B: "B \<subseteq> span(rows A)""card B = dim (span(rows A))"
      using basis_exists [of "span(rows A)"] by blast
    with span_subspace have eq: "span B = span(rows A)"
      by auto
    then have inj: "inj_on (( *v) A) (span B)"
      using inj_on_def matrix_vector_mul_injective_on_rowspace by blast
    then have ind: "independent (( *v) A ` B)"
      by (rule independent_inj_on_image [OF \<open>independent B\<close> matrix_vector_mul_linear])
    then have "finite (( *v) A ` B) \<and> card (( *v) A ` B) \<le> dim (( *v) A ` B)"
      by (rule independent_bound_general)
    then show ?thesis
      by (metis (no_types, lifting) B ind inj eq card_image image_subset_iff independent_card_le_dim inj_on_subset matrix_vector_mult_in_columnspace)
  qed
  then show ?thesis
    by simp
qed

lemma rank_row:
  fixes A :: "real^'n^'m"
  shows "rank A = dim(rows A)"
  unfolding rank_def
  by (metis dim_rows_le_dim_columns columns_transpose dual_order.antisym rows_transpose)

lemma rank_transpose:
  fixes A :: "real^'n^'m"
  shows "rank(transpose A) = rank A"
  by (metis rank_def rank_row rows_transpose)

lemma matrix_vector_mult_basis:
  fixes A :: "real^'n^'m"
  shows "A *v (axis k 1) = column k A"
  by (simp add: cart_eq_inner_axis column_def matrix_mult_dot)

lemma columns_image_basis:
  fixes A :: "real^'n^'m"
  shows "columns A = ( *v) A ` (range (\<lambda>i. axis i 1))"
  by (force simp: columns_def matrix_vector_mult_basis [symmetric])

lemma rank_dim_range:
  fixes A :: "real^'n^'m"
  shows "rank A = dim(range (\<lambda>x. A *v x))"
  unfolding rank_def
proof (rule span_eq_dim)
  show "span (columns A) = span (range (( *v) A))"
    apply (auto simp: columns_image_basis span_linear_image matrix_vector_mul_linear)
    by (metis columns_image_basis matrix_vector_mul_linear matrix_vector_mult_in_columnspace span_linear_image)
qed

lemma rank_bound:
  fixes A :: "real^'n^'m"
  shows "rank A \<le> min CARD('m) (CARD('n))"
  by (metis (mono_tags, hide_lams) min.bounded_iff DIM_cart DIM_real dim_subset_UNIV mult.right_neutral rank_def rank_transpose)

lemma full_rank_injective:
  fixes A :: "real^'n^'m"
  shows "rank A = CARD('n) \<longleftrightarrow> inj (( *v) A)"
  by (simp add: matrix_left_invertible_injective [symmetric] matrix_left_invertible_span_rows rank_row dim_eq_full [symmetric])

lemma full_rank_surjective:
  fixes A :: "real^'n^'m"
  shows "rank A = CARD('m) \<longleftrightarrow> surj (( *v) A)"
  by (simp add: matrix_right_invertible_surjective [symmetric] left_invertible_transpose [symmetric]
                matrix_left_invertible_injective full_rank_injective [symmetric] rank_transpose)

lemma rank_I: "rank(mat 1::real^'n^'n) = CARD('n)"
  by (simp add: full_rank_injective inj_on_def)

lemma less_rank_noninjective:
  fixes A :: "real^'n^'m"
  shows "rank A < CARD('n) \<longleftrightarrow> \<not> inj (( *v) A)"
using less_le rank_bound by (auto simp: full_rank_injective [symmetric])

lemma matrix_nonfull_linear_equations_eq:
  fixes A :: "real^'n^'m"
  shows "(\<exists>x. (x \<noteq> 0) \<and> A *v x = 0) \<longleftrightarrow> ~(rank A = CARD('n))"
  by (meson matrix_left_invertible_injective full_rank_injective matrix_left_invertible_ker)

lemma rank_eq_0: "rank A = 0 \<longleftrightarrow> A = 0" and rank_0 [simp]: "rank 0 = 0"
  by (auto simp: rank_dim_range matrix_eq)


lemma rank_mul_le_right:
  fixes A :: "real^'n^'m" and B :: "real^'p^'n"
  shows "rank(A ** B) \<le> rank B"
proof -
  have "rank(A ** B) \<le> dim (( *v) A ` range (( *v) B))"
    by (auto simp: rank_dim_range image_comp o_def matrix_vector_mul_assoc)
  also have "\<dots> \<le> rank B"
    by (simp add: rank_dim_range matrix_vector_mul_linear dim_image_le)
  finally show ?thesis .
qed

lemma rank_mul_le_left:
  fixes A :: "real^'n^'m" and B :: "real^'p^'n"
  shows "rank(A ** B) \<le> rank A"
  by (metis matrix_transpose_mul rank_mul_le_right rank_transpose)

subsection\<open>Routine results connecting the types @{typ "real^1"} and @{typ real}\<close>

lemma vector_one_nth [simp]:
  fixes x :: "'a^1" shows "vec (x $ 1) = x"
  by (metis vec_def vector_one)

lemma vec_cbox_1_eq [simp]:
  shows "vec ` cbox u v = cbox (vec u) (vec v ::real^1)"
  by (force simp: Basis_vec_def cart_eq_inner_axis [symmetric] mem_box)

lemma vec_nth_cbox_1_eq [simp]:
  fixes u v :: "'a::euclidean_space^1"
  shows "(\<lambda>x. x $ 1) ` cbox u v = cbox (u$1) (v$1)"
    by (auto simp: Basis_vec_def cart_eq_inner_axis [symmetric] mem_box image_iff Bex_def inner_axis) (metis vec_component)

lemma vec_nth_1_iff_cbox [simp]:
  fixes a b :: "'a::euclidean_space"
  shows "(\<lambda>x::'a^1. x $ 1) ` S = cbox a b \<longleftrightarrow> S = cbox (vec a) (vec b)"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs show ?rhs
  proof (intro equalityI subsetI)
    fix x 
    assume "x \<in> S"
    then have "x $ 1 \<in> (\<lambda>v. v $ (1::1)) ` cbox (vec a) (vec b)"
      using L by auto
    then show "x \<in> cbox (vec a) (vec b)"
      by (metis (no_types, lifting) imageE vector_one_nth)
  next
    fix x :: "'a^1"
    assume "x \<in> cbox (vec a) (vec b)"
    then show "x \<in> S"
      by (metis (no_types, lifting) L imageE imageI vec_component vec_nth_cbox_1_eq vector_one_nth)
  qed
qed simp

lemma tendsto_at_within_vector_1:
  fixes S :: "'a :: metric_space set"
  assumes "(f \<longlongrightarrow> fx) (at x within S)"
  shows "((\<lambda>y::'a^1. \<chi> i. f (y $ 1)) \<longlongrightarrow> (vec fx::'a^1)) (at (vec x) within vec ` S)"
proof (rule topological_tendstoI)
  fix T :: "('a^1) set"
  assume "open T" "vec fx \<in> T"
  have "\<forall>\<^sub>F x in at x within S. f x \<in> (\<lambda>x. x $ 1) ` T"
    using \<open>open T\<close> \<open>vec fx \<in> T\<close> assms open_image_vec_nth tendsto_def by fastforce
  then show "\<forall>\<^sub>F x::'a^1 in at (vec x) within vec ` S. (\<chi> i. f (x $ 1)) \<in> T"
    unfolding eventually_at dist_norm [symmetric]
    by (rule ex_forward)
       (use \<open>open T\<close> in 
         \<open>fastforce simp: dist_norm dist_vec_def L2_set_def image_iff vector_one open_vec_def\<close>)
qed

lemma has_derivative_vector_1:
  assumes der_g: "(g has_derivative (\<lambda>x. x * g' a)) (at a within S)"
  shows "((\<lambda>x. vec (g (x $ 1))) has_derivative ( *\<^sub>R) (g' a))
         (at ((vec a)::real^1) within vec ` S)"
    using der_g
    apply (auto simp: Deriv.has_derivative_within bounded_linear_scaleR_right norm_vector_1)
    apply (drule tendsto_at_within_vector_1, vector)
    apply (auto simp: algebra_simps eventually_at tendsto_def)
    done


subsection\<open>Explicit vector construction from lists\<close>

definition "vector l = (\<chi> i. foldr (\<lambda>x f n. fun_upd (f (n+1)) n x) l (\<lambda>n x. 0) 1 i)"

lemma vector_1: "(vector[x]) $1 = x"
  unfolding vector_def by simp

lemma vector_2:
 "(vector[x,y]) $1 = x"
 "(vector[x,y] :: 'a^2)$2 = (y::'a::zero)"
  unfolding vector_def by simp_all

lemma vector_3:
 "(vector [x,y,z] ::('a::zero)^3)$1 = x"
 "(vector [x,y,z] ::('a::zero)^3)$2 = y"
 "(vector [x,y,z] ::('a::zero)^3)$3 = z"
  unfolding vector_def by simp_all

lemma forall_vector_1: "(\<forall>v::'a::zero^1. P v) \<longleftrightarrow> (\<forall>x. P(vector[x]))"
  by (metis vector_1 vector_one)

lemma forall_vector_2: "(\<forall>v::'a::zero^2. P v) \<longleftrightarrow> (\<forall>x y. P(vector[x, y]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (erule_tac x="v$2" in allE)
  apply (subgoal_tac "vector [v$1, v$2] = v")
  apply simp
  apply (vector vector_def)
  apply (simp add: forall_2)
  done

lemma forall_vector_3: "(\<forall>v::'a::zero^3. P v) \<longleftrightarrow> (\<forall>x y z. P(vector[x, y, z]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (erule_tac x="v$2" in allE)
  apply (erule_tac x="v$3" in allE)
  apply (subgoal_tac "vector [v$1, v$2, v$3] = v")
  apply simp
  apply (vector vector_def)
  apply (simp add: forall_3)
  done

lemma bounded_linear_component_cart[intro]: "bounded_linear (\<lambda>x::real^'n. x $ k)"
  apply (rule bounded_linearI[where K=1])
  using component_le_norm_cart[of _ k] unfolding real_norm_def by auto

lemma interval_split_cart:
  "{a..b::real^'n} \<inter> {x. x$k \<le> c} = {a .. (\<chi> i. if i = k then min (b$k) c else b$i)}"
  "cbox a b \<inter> {x. x$k \<ge> c} = {(\<chi> i. if i = k then max (a$k) c else a$i) .. b}"
  apply (rule_tac[!] set_eqI)
  unfolding Int_iff mem_box_cart mem_Collect_eq interval_cbox_cart
  unfolding vec_lambda_beta
  by auto

lemmas cartesian_euclidean_space_uniform_limit_intros[uniform_limit_intros] =
  bounded_linear.uniform_limit[OF blinfun.bounded_linear_right]
  bounded_linear.uniform_limit[OF bounded_linear_vec_nth]
  bounded_linear.uniform_limit[OF bounded_linear_component_cart]

end
