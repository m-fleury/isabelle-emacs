theory Laurent_Convergence
  imports "HOL-Computational_Algebra.Formal_Laurent_Series" "HOL-Library.Landau_Symbols"
          Residue_Theorem

begin

(* TODO: Move *)
text \<open>TODO: Better than @{thm deriv_compose_linear}?\<close>
lemma deriv_compose_linear':
  assumes "f field_differentiable at (c*z + a)"
  shows "deriv (\<lambda>w. f (c*w + a)) z = c * deriv f (c*z + a)"
  apply (subst deriv_chain[where f="\<lambda>w. c*w + a",unfolded comp_def])
  using assms by (auto intro:derivative_intros)

text \<open>TODO: Better than @{thm higher_deriv_compose_linear}?\<close>
lemma higher_deriv_compose_linear':
  fixes z::complex
  assumes f: "f holomorphic_on T" and S: "open S" and T: "open T" and z: "z \<in> S"
      and fg: "\<And>w. w \<in> S \<Longrightarrow> u*w + c \<in> T"
    shows "(deriv ^^ n) (\<lambda>w. f (u*w + c)) z = u^n * (deriv ^^ n) f (u*z + c)"
using z
proof (induction n arbitrary: z)
  case 0 then show ?case by simp
next
  case (Suc n z)
  have holo0: "f holomorphic_on (\<lambda>w. u * w+c) ` S"
    by (meson fg f holomorphic_on_subset image_subset_iff)
  have holo2: "(deriv ^^ n) f holomorphic_on (\<lambda>w. u * w+c) ` S"
    by (meson f fg holomorphic_higher_deriv holomorphic_on_subset image_subset_iff T)
  have holo3: "(\<lambda>z. u ^ n * (deriv ^^ n) f (u * z+c)) holomorphic_on S"
    by (intro holo2 holomorphic_on_compose [where g="(deriv ^^ n) f", unfolded o_def] holomorphic_intros)
  have "(\<lambda>w. u * w+c) holomorphic_on S" "f holomorphic_on (\<lambda>w. u * w+c) ` S"
    by (rule holo0 holomorphic_intros)+
  then have holo1: "(\<lambda>w. f (u * w+c)) holomorphic_on S"
    by (rule holomorphic_on_compose [where g=f, unfolded o_def])
  have "deriv ((deriv ^^ n) (\<lambda>w. f (u * w+c))) z = deriv (\<lambda>z. u^n * (deriv ^^ n) f (u*z+c)) z"
  proof (rule complex_derivative_transform_within_open [OF _ holo3 S Suc.prems])
    show "(deriv ^^ n) (\<lambda>w. f (u * w+c)) holomorphic_on S"
      by (rule holomorphic_higher_deriv [OF holo1 S])
  qed (simp add: Suc.IH)
  also have "\<dots> = u^n * deriv (\<lambda>z. (deriv ^^ n) f (u * z+c)) z"
  proof -
    have "(deriv ^^ n) f analytic_on T"
      by (simp add: analytic_on_open f holomorphic_higher_deriv T)
    then have "(\<lambda>w. (deriv ^^ n) f (u * w+c)) analytic_on S"
    proof -
      have "(deriv ^^ n) f \<circ> (\<lambda>w. u * w+c) holomorphic_on S"
        using holomorphic_on_compose[OF _ holo2] \<open>(\<lambda>w. u * w+c) holomorphic_on S\<close>
        by simp
      then show ?thesis
        by (simp add: S analytic_on_open o_def)
    qed
    then show ?thesis
      by (intro deriv_cmult analytic_on_imp_differentiable_at [OF _ Suc.prems])
  qed
  also have "\<dots> = u * u ^ n * deriv ((deriv ^^ n) f) (u * z+c)"
  proof -
    have "(deriv ^^ n) f field_differentiable at (u * z+c)"
      using Suc.prems T f fg holomorphic_higher_deriv holomorphic_on_imp_differentiable_at by blast
    then show ?thesis
      by (simp add: deriv_compose_linear')
  qed
  finally show ?case
    by simp
qed

lemma fps_to_fls_numeral [simp]: "fps_to_fls (numeral n) = numeral n"
  by (metis fps_to_fls_of_nat of_nat_numeral)

lemma fls_const_power: "fls_const (a ^ b) = fls_const a ^ b"
  by (induction b) (auto simp flip: fls_const_mult_const)

lemma fls_deriv_numeral [simp]: "fls_deriv (numeral n) = 0"
  by (metis fls_deriv_of_int of_int_numeral)

lemma fls_const_numeral [simp]: "fls_const (numeral n) = numeral n"
  by (metis fls_of_nat of_nat_numeral)

lemma fls_mult_of_int_nth [simp]:
  shows "fls_nth (numeral k * f) n = numeral k * fls_nth f n"
  and   "fls_nth (f * numeral k) n = fls_nth f n * numeral k"
  by (metis fls_const_numeral fls_mult_const_nth)+

lemma fls_nth_numeral' [simp]:
  "fls_nth (numeral n) 0 = numeral n" "k \<noteq> 0 \<Longrightarrow> fls_nth (numeral n) k = 0"
  by (subst fls_const_numeral [symmetric], subst fls_const_nth, simp)+

lemma fls_subdegree_prod:
  fixes F :: "'a \<Rightarrow> 'b :: field_char_0 fls"
  assumes "\<And>x. x \<in> I \<Longrightarrow> F x \<noteq> 0"
  shows   "fls_subdegree (\<Prod>x\<in>I. F x) = (\<Sum>x\<in>I. fls_subdegree (F x))"
  using assms by (induction I rule: infinite_finite_induct) auto

lemma fls_subdegree_prod':
  fixes F :: "'a \<Rightarrow> 'b :: field_char_0 fls"
  assumes "\<And>x. x \<in> I \<Longrightarrow> fls_subdegree (F x) \<noteq> 0"
  shows   "fls_subdegree (\<Prod>x\<in>I. F x) = (\<Sum>x\<in>I. fls_subdegree (F x))"
proof (intro fls_subdegree_prod)
  show "F x \<noteq> 0" if "x \<in> I" for x
    using assms[OF that] by auto
qed

instance fps :: (semiring_char_0) semiring_char_0
proof
  show "inj (of_nat :: nat \<Rightarrow> 'a fps)"
  proof
    fix m n :: nat
    assume "of_nat m = (of_nat n :: 'a fps)"
    hence "fps_nth (of_nat m) 0 = (fps_nth (of_nat n) 0 :: 'a)"
      by (simp only: )
    thus "m = n"
      by simp
  qed
qed

instance fls :: (semiring_char_0) semiring_char_0
proof
  show "inj (of_nat :: nat \<Rightarrow> 'a fls)"
    by (metis fls_regpart_of_nat injI of_nat_eq_iff)
qed

lemma fls_const_eq_0_iff [simp]: "fls_const c = 0 \<longleftrightarrow> c = 0"
  using fls_const_0 fls_const_nonzero by blast

lemma fls_subdegree_add_eq1:
  assumes "f \<noteq> 0" "fls_subdegree f < fls_subdegree g"
  shows   "fls_subdegree (f + g) = fls_subdegree f"
proof (intro antisym)
  from assms have *: "fls_nth (f + g) (fls_subdegree f) \<noteq> 0"
    by auto
  from * show "fls_subdegree (f + g) \<le> fls_subdegree f"
    by (rule fls_subdegree_leI)
  from * have "f + g \<noteq> 0"
    using fls_nonzeroI by blast
  thus "fls_subdegree f \<le> fls_subdegree (f + g)"
    using assms(2) fls_plus_subdegree by force
qed

lemma fls_subdegree_add_eq2:
  assumes "g \<noteq> 0" "fls_subdegree g < fls_subdegree f"
  shows   "fls_subdegree (f + g) = fls_subdegree g"
proof (intro antisym)
  from assms have *: "fls_nth (f + g) (fls_subdegree g) \<noteq> 0"
    by auto
  from * show "fls_subdegree (f + g) \<le> fls_subdegree g"
    by (rule fls_subdegree_leI)
  from * have "f + g \<noteq> 0"
    using fls_nonzeroI by blast
  thus "fls_subdegree g \<le> fls_subdegree (f + g)"
    using assms(2) fls_plus_subdegree by force
qed

lemma fls_subdegree_diff_eq1:
  assumes "f \<noteq> 0" "fls_subdegree f < fls_subdegree g"
  shows   "fls_subdegree (f - g) = fls_subdegree f"
  using fls_subdegree_add_eq1[of f "-g"] assms by simp

lemma fls_subdegree_diff_eq2:
  assumes "g \<noteq> 0" "fls_subdegree g < fls_subdegree f"
  shows   "fls_subdegree (f - g) = fls_subdegree g"
  using fls_subdegree_add_eq2[of "-g" f] assms by simp

lemma nat_minus_fls_subdegree_plus_const_eq:
  "nat (-fls_subdegree (F + fls_const c)) = nat (-fls_subdegree F)"
proof (cases "fls_subdegree F < 0")
  case True
  hence "fls_subdegree (F + fls_const c) = fls_subdegree F"
    by (intro fls_subdegree_add_eq1) auto
  thus ?thesis
    by simp
next
  case False
  thus ?thesis
    by (auto simp: fls_subdegree_ge0I)
qed

lemma at_to_0': "NO_MATCH 0 z \<Longrightarrow> at z = filtermap (\<lambda>x. x + z) (at 0)"
  for z :: "'a::real_normed_vector"
  by (rule at_to_0)

lemma nhds_to_0: "nhds (x :: 'a :: real_normed_vector) = filtermap ((+) x) (nhds 0)"
proof -
  have "(\<lambda>xa. xa - - x) = (+) x"
    by auto
  thus ?thesis
    using filtermap_nhds_shift[of "-x" 0] by simp
qed

lemma nhds_to_0': "NO_MATCH 0 x \<Longrightarrow> nhds (x :: 'a :: real_normed_vector) = filtermap ((+) x) (nhds 0)"
  by (rule nhds_to_0)


definition%important fls_conv_radius :: "complex fls \<Rightarrow> ereal" where
  "fls_conv_radius f = fps_conv_radius (fls_regpart f)"

definition%important eval_fls :: "complex fls \<Rightarrow> complex \<Rightarrow> complex" where
  "eval_fls F z = eval_fps (fls_base_factor_to_fps F) z * z powi fls_subdegree F"

definition\<^marker>\<open>tag important\<close>
  has_laurent_expansion :: "(complex \<Rightarrow> complex) \<Rightarrow> complex fls \<Rightarrow> bool"
  (infixl "has'_laurent'_expansion" 60)
  where "(f has_laurent_expansion F) \<longleftrightarrow>
            fls_conv_radius F > 0 \<and> eventually (\<lambda>z. eval_fls F z = f z) (at 0)"

lemma has_laurent_expansion_schematicI:
  "f has_laurent_expansion F \<Longrightarrow> F = G \<Longrightarrow> f has_laurent_expansion G"
  by simp

lemma has_laurent_expansion_cong:
  assumes "eventually (\<lambda>x. f x = g x) (at 0)" "F = G"
  shows   "(f has_laurent_expansion F) \<longleftrightarrow> (g has_laurent_expansion G)"
proof -
  have "eventually (\<lambda>z. eval_fls F z = g z) (at 0)"
    if "eventually (\<lambda>z. eval_fls F z = f z) (at 0)" "eventually (\<lambda>x. f x = g x) (at 0)" for f g
    using that by eventually_elim auto
  from this[of f g] this[of g f] show ?thesis
    using assms by (auto simp: eq_commute has_laurent_expansion_def)
qed

lemma has_laurent_expansion_cong':
  assumes "eventually (\<lambda>x. f x = g x) (at z)" "F = G" "z = z'"
  shows   "((\<lambda>x. f (z + x)) has_laurent_expansion F) \<longleftrightarrow> ((\<lambda>x. g (z' + x)) has_laurent_expansion G)"
  by (intro has_laurent_expansion_cong)
     (use assms in \<open>auto simp: at_to_0' eventually_filtermap add_ac\<close>)

lemma fls_conv_radius_altdef:
  "fls_conv_radius F = fps_conv_radius (fls_base_factor_to_fps F)"
proof -
  have "conv_radius (\<lambda>n. fls_nth F (int n)) = conv_radius (\<lambda>n. fls_nth F (int n + fls_subdegree F))"
  proof (cases "fls_subdegree F \<ge> 0")
    case True
    hence "conv_radius (\<lambda>n. fls_nth F (int n + fls_subdegree F)) =
           conv_radius (\<lambda>n. fls_nth F (int (n + nat (fls_subdegree F))))"
      by auto
    thus ?thesis
      by (subst (asm) conv_radius_shift) auto
  next
    case False
    hence "conv_radius (\<lambda>n. fls_nth F (int n)) =
           conv_radius (\<lambda>n. fls_nth F (fls_subdegree F + int (n + nat (-fls_subdegree F))))"
      by auto
    thus ?thesis
      by (subst (asm) conv_radius_shift) (auto simp: add_ac)
  qed
  thus ?thesis
    by (simp add: fls_conv_radius_def fps_conv_radius_def)
qed

lemma eval_fps_of_nat [simp]: "eval_fps (of_nat n) z = of_nat n"
  and eval_fps_of_int [simp]: "eval_fps (of_int m) z = of_int m"
  by (simp_all flip: fps_of_nat fps_of_int)

lemma fls_subdegree_numeral [simp]: "fls_subdegree (numeral n) = 0"
  by (metis fls_subdegree_of_nat of_nat_numeral)

lemma fls_regpart_numeral [simp]: "fls_regpart (numeral n) = numeral n"
  by (metis fls_regpart_of_nat of_nat_numeral)

lemma fps_conv_radius_of_nat [simp]: "fps_conv_radius (of_nat n) = \<infinity>"
  and fps_conv_radius_of_int [simp]: "fps_conv_radius (of_int m) = \<infinity>"
  by (simp_all flip: fps_of_nat fps_of_int)

lemma fps_conv_radius_fls_regpart: "fps_conv_radius (fls_regpart F) = fls_conv_radius F"
  by (simp add: fls_conv_radius_def)

lemma fls_conv_radius_0 [simp]: "fls_conv_radius 0 = \<infinity>"
  and fls_conv_radius_1 [simp]: "fls_conv_radius 1 = \<infinity>"
  and fls_conv_radius_const [simp]: "fls_conv_radius (fls_const c) = \<infinity>"
  and fls_conv_radius_numeral [simp]: "fls_conv_radius (numeral num) = \<infinity>"
  and fls_conv_radius_of_nat [simp]: "fls_conv_radius (of_nat n) = \<infinity>"
  and fls_conv_radius_of_int [simp]: "fls_conv_radius (of_int m) = \<infinity>"
  and fls_conv_radius_X [simp]: "fls_conv_radius fls_X = \<infinity>"
  and fls_conv_radius_X_inv [simp]: "fls_conv_radius fls_X_inv = \<infinity>"
  and fls_conv_radius_X_intpow [simp]: "fls_conv_radius (fls_X_intpow m) = \<infinity>"
  by (simp_all add: fls_conv_radius_def fls_X_intpow_regpart)

lemma fls_conv_radius_shift [simp]: "fls_conv_radius (fls_shift n F) = fls_conv_radius F"
  unfolding fls_conv_radius_altdef by (subst fls_base_factor_to_fps_shift) (rule refl)

lemma fls_conv_radius_fps_to_fls [simp]: "fls_conv_radius (fps_to_fls F) = fps_conv_radius F"
  by (simp add: fls_conv_radius_def)

lemma fls_conv_radius_deriv [simp]: "fls_conv_radius (fls_deriv F) \<ge> fls_conv_radius F"
proof -
  have "fls_conv_radius (fls_deriv F) = fps_conv_radius (fls_regpart (fls_deriv F))"
    by (simp add: fls_conv_radius_def)
  also have "fls_regpart (fls_deriv F) = fps_deriv (fls_regpart F)"
    by (intro fps_ext) (auto simp: add_ac)
  also have "fps_conv_radius \<dots> \<ge> fls_conv_radius F"
    by (simp add: fls_conv_radius_def fps_conv_radius_deriv)
  finally show ?thesis .
qed

lemma fls_conv_radius_uminus [simp]: "fls_conv_radius (-F) = fls_conv_radius F"
  by (simp add: fls_conv_radius_def)

lemma fls_conv_radius_add: "fls_conv_radius (F + G) \<ge> min (fls_conv_radius F) (fls_conv_radius G)"
  by (simp add: fls_conv_radius_def fps_conv_radius_add)

lemma fls_conv_radius_diff: "fls_conv_radius (F - G) \<ge> min (fls_conv_radius F) (fls_conv_radius G)"
  by (simp add: fls_conv_radius_def fps_conv_radius_diff)

lemma fls_conv_radius_mult: "fls_conv_radius (F * G) \<ge> min (fls_conv_radius F) (fls_conv_radius G)"
proof (cases "F = 0 \<or> G = 0")
  case False
  hence [simp]: "F \<noteq> 0" "G \<noteq> 0"
    by auto
  have "fls_conv_radius (F * G) = fps_conv_radius (fls_regpart (fls_shift (fls_subdegree F + fls_subdegree G) (F * G)))"
    by (simp add: fls_conv_radius_altdef)
  also have "fls_regpart (fls_shift (fls_subdegree F + fls_subdegree G) (F * G)) =
             fls_base_factor_to_fps F * fls_base_factor_to_fps G"
    by (simp add: fls_times_def)
  also have "fps_conv_radius \<dots> \<ge> min (fls_conv_radius F) (fls_conv_radius G)"
    unfolding fls_conv_radius_altdef by (rule fps_conv_radius_mult)
  finally show ?thesis .
qed auto

lemma fps_conv_radius_add_ge:
  "fps_conv_radius F \<ge> r \<Longrightarrow> fps_conv_radius G \<ge> r \<Longrightarrow> fps_conv_radius (F + G) \<ge> r"
  using fps_conv_radius_add[of F G] by (simp add: min_def split: if_splits)

lemma fps_conv_radius_diff_ge:
  "fps_conv_radius F \<ge> r \<Longrightarrow> fps_conv_radius G \<ge> r \<Longrightarrow> fps_conv_radius (F - G) \<ge> r"
  using fps_conv_radius_diff[of F G] by (simp add: min_def split: if_splits)

lemma fps_conv_radius_mult_ge:
  "fps_conv_radius F \<ge> r \<Longrightarrow> fps_conv_radius G \<ge> r \<Longrightarrow> fps_conv_radius (F * G) \<ge> r"
  using fps_conv_radius_mult[of F G] by (simp add: min_def split: if_splits)

lemma fls_conv_radius_add_ge:
  "fls_conv_radius F \<ge> r \<Longrightarrow> fls_conv_radius G \<ge> r \<Longrightarrow> fls_conv_radius (F + G) \<ge> r"
  using fls_conv_radius_add[of F G] by (simp add: min_def split: if_splits)

lemma fls_conv_radius_diff_ge:
  "fls_conv_radius F \<ge> r \<Longrightarrow> fls_conv_radius G \<ge> r \<Longrightarrow> fls_conv_radius (F - G) \<ge> r"
  using fls_conv_radius_diff[of F G] by (simp add: min_def split: if_splits)

lemma fls_conv_radius_mult_ge:
  "fls_conv_radius F \<ge> r \<Longrightarrow> fls_conv_radius G \<ge> r \<Longrightarrow> fls_conv_radius (F * G) \<ge> r"
  using fls_conv_radius_mult[of F G] by (simp add: min_def split: if_splits)

lemma fls_conv_radius_power: "fls_conv_radius (F ^ n) \<ge> fls_conv_radius F"
  by (induction n) (auto intro!: fls_conv_radius_mult_ge)

lemma eval_fls_0 [simp]: "eval_fls 0 z = 0"
  and eval_fls_1 [simp]: "eval_fls 1 z = 1"
  and eval_fls_const [simp]: "eval_fls (fls_const c) z = c"
  and eval_fls_numeral [simp]: "eval_fls (numeral num) z = numeral num"
  and eval_fls_of_nat [simp]: "eval_fls (of_nat n) z = of_nat n"
  and eval_fls_of_int [simp]: "eval_fls (of_int m) z = of_int m"
  and eval_fls_X [simp]: "eval_fls fls_X z = z"
  and eval_fls_X_intpow [simp]: "eval_fls (fls_X_intpow m) z = z powi m"
  by (simp_all add: eval_fls_def)

lemma eval_fls_at_0: "eval_fls F 0 = (if fls_subdegree F \<ge> 0 then fls_nth F 0 else 0)"
  by (cases "fls_subdegree F = 0")
     (simp_all add: eval_fls_def fls_regpart_def eval_fps_at_0)

lemma eval_fps_to_fls:
  assumes "norm z < fps_conv_radius F"
  shows   "eval_fls (fps_to_fls F) z = eval_fps F z"
proof (cases "F = 0")
  case [simp]: False
  have "eval_fps F z = eval_fps (unit_factor F * normalize F) z"
    by (metis unit_factor_mult_normalize)
  also have "\<dots> = eval_fps (unit_factor F * fps_X ^ subdegree F) z"
    by simp
  also have "\<dots> = eval_fps (unit_factor F) z * z ^ subdegree F"
    using assms by (subst eval_fps_mult) auto
  also have "\<dots> = eval_fls (fps_to_fls F) z"
    unfolding eval_fls_def fls_base_factor_to_fps_to_fls fls_subdegree_fls_to_fps
              power_int_of_nat ..
  finally show ?thesis ..
qed auto

lemma eval_fls_shift:
  assumes [simp]: "z \<noteq> 0"
  shows   "eval_fls (fls_shift n F) z = eval_fls F z * z powi -n"
proof (cases "F = 0")
  case [simp]: False
  show ?thesis
  unfolding eval_fls_def
  by (subst fls_base_factor_to_fps_shift, subst fls_shift_subdegree[OF \<open>F \<noteq> 0\<close>], subst power_int_diff)
     (auto simp: power_int_minus divide_simps)
qed auto

lemma eval_fls_add:
  assumes "ereal (norm z) < fls_conv_radius F" "ereal (norm z) < fls_conv_radius G" "z \<noteq> 0"
  shows   "eval_fls (F + G) z = eval_fls F z + eval_fls G z"
  using assms
proof (induction "fls_subdegree F" "fls_subdegree G" arbitrary: F G rule: linorder_wlog)
  case (sym F G)
  show ?case
    using sym(1)[of G F] sym(2-) by (simp add: add_ac)
next
  case (le F G)
  show ?case
  proof (cases "F = 0 \<or> G = 0")
    case False
    hence [simp]: "F \<noteq> 0" "G \<noteq> 0"
      by auto
    note [simp] = \<open>z \<noteq> 0\<close>
    define F' G' where "F' = fls_base_factor_to_fps F" "G' = fls_base_factor_to_fps G"
    define m n where "m = fls_subdegree F" "n = fls_subdegree G"
    have "m \<le> n"
      using le by (auto simp: m_n_def)
    have conv1: "ereal (cmod z) < fps_conv_radius F'" "ereal (cmod z) < fps_conv_radius G'"
      using assms le by (simp_all add: F'_G'_def fls_conv_radius_altdef)
    have conv2: "ereal (cmod z) < fps_conv_radius (G' * fps_X ^ nat (n - m))"
      using conv1 by (intro less_le_trans[OF _ fps_conv_radius_mult]) auto
    have conv3: "ereal (cmod z) < fps_conv_radius (F' + G' * fps_X ^ nat (n - m))"
      using conv1 conv2 by (intro less_le_trans[OF _ fps_conv_radius_add]) auto

    have "eval_fls F z + eval_fls G z = eval_fps F' z * z powi m + eval_fps G' z * z powi n"
      unfolding eval_fls_def m_n_def[symmetric] F'_G'_def[symmetric]
      by (simp add: power_int_add algebra_simps)
    also have "\<dots> = (eval_fps F' z + eval_fps G' z * z powi (n - m)) * z powi m"
      by (simp add: algebra_simps power_int_diff)
    also have "eval_fps G' z * z powi (n - m) = eval_fps (G' * fps_X ^ nat (n - m)) z"
      using assms \<open>m \<le> n\<close> conv1 by (subst eval_fps_mult) (auto simp: power_int_def)
    also have "eval_fps F' z + \<dots> = eval_fps (F' + G' * fps_X ^ nat (n - m)) z"
      using conv1 conv2 by (subst eval_fps_add) auto
    also have "\<dots> = eval_fls (fps_to_fls (F' + G' * fps_X ^ nat (n - m))) z"
      using conv3 by (subst eval_fps_to_fls) auto
    also have "\<dots> * z powi m = eval_fls (fls_shift (-m) (fps_to_fls (F' + G' * fps_X ^ nat (n - m)))) z"
      by (subst eval_fls_shift) auto
    also have "fls_shift (-m) (fps_to_fls (F' + G' * fps_X ^ nat (n - m))) = F + G"
      using \<open>m \<le> n\<close>
      by (simp add: fls_times_fps_to_fls fps_to_fls_power fls_X_power_conv_shift_1
                    fls_shifted_times_simps F'_G'_def m_n_def)
    finally show ?thesis ..
  qed auto
qed

lemma eval_fls_minus:
  assumes "ereal (norm z) < fls_conv_radius F"
  shows   "eval_fls (-F) z = -eval_fls F z"
  using assms by (simp add: eval_fls_def eval_fps_minus fls_conv_radius_altdef)

lemma eval_fls_diff:
  assumes "ereal (norm z) < fls_conv_radius F" "ereal (norm z) < fls_conv_radius G"
     and [simp]: "z \<noteq> 0"
  shows   "eval_fls (F - G) z = eval_fls F z - eval_fls G z"
proof -
  have "eval_fls (F + (-G)) z = eval_fls F z - eval_fls G z"
    using assms by (subst eval_fls_add) (auto simp: eval_fls_minus)
  thus ?thesis
    by simp
qed

lemma eval_fls_mult:
  assumes "ereal (norm z) < fls_conv_radius F" "ereal (norm z) < fls_conv_radius G" "z \<noteq> 0"
  shows   "eval_fls (F * G) z = eval_fls F z * eval_fls G z"
proof (cases "F = 0 \<or> G = 0")
  case False
  hence [simp]: "F \<noteq> 0" "G \<noteq> 0"
    by auto
  note [simp] = \<open>z \<noteq> 0\<close>
  define F' G' where "F' = fls_base_factor_to_fps F" "G' = fls_base_factor_to_fps G"
  define m n where "m = fls_subdegree F" "n = fls_subdegree G"
  have "eval_fls F z * eval_fls G z = (eval_fps F' z * eval_fps G' z) * z powi (m + n)"
    unfolding eval_fls_def m_n_def[symmetric] F'_G'_def[symmetric]
    by (simp add: power_int_add algebra_simps)
  also have "\<dots> = eval_fps (F' * G') z * z powi (m + n)"
    using assms by (subst eval_fps_mult) (auto simp: F'_G'_def fls_conv_radius_altdef)
  also have "\<dots> = eval_fls (F * G) z"
    by (simp add: eval_fls_def F'_G'_def m_n_def) (simp add: fls_times_def)
  finally show ?thesis ..
qed auto

lemma eval_fls_power:
  assumes "ereal (norm z) < fls_conv_radius F" "z \<noteq> 0"
  shows   "eval_fls (F ^ n) z = eval_fls F z ^ n"
proof (induction n)
  case (Suc n)
  have "eval_fls (F ^ Suc n) z = eval_fls (F * F ^ n) z"
    by simp
  also have "\<dots> = eval_fls F z * eval_fls (F ^ n) z"
    using assms by (subst eval_fls_mult) (auto intro!: less_le_trans[OF _ fls_conv_radius_power])
  finally show ?case
    using Suc by simp
qed auto

lemma norm_summable_fls:
  "norm z < fls_conv_radius f \<Longrightarrow> summable (\<lambda>n. norm (fls_nth f n * z ^ n))"
  using norm_summable_fps[of z "fls_regpart f"] by (simp add: fls_conv_radius_def)

lemma norm_summable_fls':
  "norm z < fls_conv_radius f \<Longrightarrow> summable (\<lambda>n. norm (fls_nth f (n + fls_subdegree f) * z ^ n))"
  using norm_summable_fps[of z "fls_base_factor_to_fps f"] by (simp add: fls_conv_radius_altdef)

lemma summable_fls:
  "norm z < fls_conv_radius f \<Longrightarrow> summable (\<lambda>n. fls_nth f n * z ^ n)"
  by (rule summable_norm_cancel[OF norm_summable_fls])

theorem sums_eval_fls:
  fixes f
  defines "n \<equiv> fls_subdegree f"
  assumes "norm z < fls_conv_radius f" and "z \<noteq> 0 \<or> n \<ge> 0"
  shows   "(\<lambda>k. fls_nth f (int k + n) * z powi (int k + n)) sums eval_fls f z"
proof (cases "z = 0")
  case [simp]: False
  have "(\<lambda>k. fps_nth (fls_base_factor_to_fps f) k * z ^ k * z powi n) sums
          (eval_fps (fls_base_factor_to_fps f) z * z powi n)"
    using assms(2) by (intro sums_eval_fps sums_mult2) (auto simp: fls_conv_radius_altdef)
  thus ?thesis
    by (simp add: power_int_add n_def eval_fls_def mult_ac)
next
  case [simp]: True
  with assms have "n \<ge> 0"
    by auto
  have "(\<lambda>k. fls_nth f (int k + n) * z powi (int k + n)) sums
          (\<Sum>k\<in>(if n \<le> 0 then {nat (-n)} else {}). fls_nth f (int k + n) * z powi (int k + n))"
    by (intro sums_finite) (auto split: if_splits)
  also have "\<dots> = eval_fls f z"
    using \<open>n \<ge> 0\<close> by (auto simp: eval_fls_at_0 n_def not_le)
  finally show ?thesis .
qed

lemma holomorphic_on_eval_fls:
  fixes f
  defines "n \<equiv> fls_subdegree f"
  assumes "A \<subseteq> eball 0 (fls_conv_radius f) - (if n \<ge> 0 then {} else {0})"
  shows   "eval_fls f holomorphic_on A"
proof (cases "n \<ge> 0")
  case True
  have "eval_fls f = (\<lambda>z. eval_fps (fls_base_factor_to_fps f) z * z ^ nat n)"
    using True by (simp add: fun_eq_iff eval_fls_def power_int_def n_def)
  moreover have "\<dots> holomorphic_on A"
    using True assms(2) by (intro holomorphic_intros) (auto simp: fls_conv_radius_altdef)
  ultimately show ?thesis
    by simp
next
  case False
  show ?thesis using assms
    unfolding eval_fls_def by (intro holomorphic_intros) (auto simp: fls_conv_radius_altdef)
qed

lemma holomorphic_on_eval_fls' [holomorphic_intros]:
  assumes "g holomorphic_on A"
  assumes "g ` A \<subseteq> eball 0 (fls_conv_radius f) - (if fls_subdegree f \<ge> 0 then {} else {0})"
  shows   "(\<lambda>x. eval_fls f (g x)) holomorphic_on A"
  by (meson assms holomorphic_on_compose holomorphic_on_eval_fls holomorphic_transform o_def)

lemma continuous_on_eval_fls:
  fixes f
  defines "n \<equiv> fls_subdegree f"
  assumes "A \<subseteq> eball 0 (fls_conv_radius f) - (if n \<ge> 0 then {} else {0})"
  shows   "continuous_on A (eval_fls f)"
  using assms holomorphic_on_eval_fls holomorphic_on_imp_continuous_on by blast

lemma continuous_on_eval_fls' [continuous_intros]:
  fixes f
  defines "n \<equiv> fls_subdegree f"
  assumes "g ` A \<subseteq> eball 0 (fls_conv_radius f) - (if n \<ge> 0 then {} else {0})"
  assumes "continuous_on A g"
  shows   "continuous_on A (\<lambda>x. eval_fls f (g x))"
  by (metis assms continuous_on_compose2 continuous_on_eval_fls order.refl)

lemmas has_field_derivative_eval_fps' [derivative_intros] =
  DERIV_chain2[OF has_field_derivative_eval_fps]

lemma fps_deriv_fls_regpart: "fps_deriv (fls_regpart F) = fls_regpart (fls_deriv F)"
  by (intro fps_ext) (auto simp: add_ac)

(* TODO: generalise for nonneg subdegree *)
lemma has_field_derivative_eval_fls:
  assumes "z \<in> eball 0 (fls_conv_radius f) - {0}"
  shows   "(eval_fls f has_field_derivative eval_fls (fls_deriv f) z) (at z within A)"
proof -
  define g where "g = fls_base_factor_to_fps f"
  define n where "n = fls_subdegree f"
  have [simp]: "fps_conv_radius g = fls_conv_radius f"
    by (simp add: fls_conv_radius_altdef g_def)
  have conv1: "fps_conv_radius (fps_deriv g * fps_X) \<ge> fls_conv_radius f"
    by (intro fps_conv_radius_mult_ge order.trans[OF _ fps_conv_radius_deriv]) auto
  have conv2: "fps_conv_radius (of_int n * g) \<ge> fls_conv_radius f"
    by (intro fps_conv_radius_mult_ge) auto
  have conv3: "fps_conv_radius (fps_deriv g * fps_X + of_int n * g) \<ge> fls_conv_radius f"
    by (intro fps_conv_radius_add_ge conv1 conv2)

  have [simp]: "fps_conv_radius g = fls_conv_radius f"
    by (simp add: g_def fls_conv_radius_altdef)
  have "((\<lambda>z. eval_fps g z * z powi fls_subdegree f) has_field_derivative
          (eval_fps (fps_deriv g) z * z powi n + of_int n * z powi (n - 1) * eval_fps g z))
          (at z within A)"
    using assms by (auto intro!: derivative_eq_intros simp: n_def)
  also have "(\<lambda>z. eval_fps g z * z powi fls_subdegree f) = eval_fls f"
    by (simp add: eval_fls_def g_def fun_eq_iff)
  also have "eval_fps (fps_deriv g) z * z powi n + of_int n * z powi (n - 1) * eval_fps g z =
             (z * eval_fps (fps_deriv g) z + of_int n * eval_fps g z) * z powi (n - 1)"
    using assms by (auto simp: power_int_diff field_simps)
  also have "(z * eval_fps (fps_deriv g) z + of_int n * eval_fps g z) =
             eval_fps (fps_deriv g * fps_X + of_int n * g) z"
    using conv1 conv2 assms fps_conv_radius_deriv[of g]
    by (subst eval_fps_add) (auto simp: eval_fps_mult)
  also have "\<dots> = eval_fls (fps_to_fls (fps_deriv g * fps_X + of_int n * g)) z"
    using conv3 assms by (subst eval_fps_to_fls) auto
  also have "\<dots> * z powi (n - 1) = eval_fls (fls_shift (1 - n) (fps_to_fls (fps_deriv g * fps_X + of_int n * g))) z"
    using assms by (subst eval_fls_shift) auto
  also have "fls_shift (1 - n) (fps_to_fls (fps_deriv g * fps_X + of_int n * g)) = fls_deriv f"
    by (intro fls_eqI) (auto simp: g_def n_def algebra_simps eq_commute[of _ "fls_subdegree f"])
  finally show ?thesis .
qed

lemma eval_fls_deriv:
  assumes "z \<in> eball 0 (fls_conv_radius F) - {0}"
  shows   "eval_fls (fls_deriv F) z = deriv (eval_fls F) z"
  by (metis DERIV_imp_deriv assms has_field_derivative_eval_fls)

lemma analytic_on_eval_fls:
  assumes "A \<subseteq> eball 0 (fls_conv_radius f) - (if fls_subdegree f \<ge> 0 then {} else {0})"
  shows   "eval_fls f analytic_on A"
proof (rule analytic_on_subset [OF _ assms])
  show "eval_fls f analytic_on eball 0 (fls_conv_radius f) - (if fls_subdegree f \<ge> 0 then {} else {0})"
    using holomorphic_on_eval_fls[OF order.refl]
    by (subst analytic_on_open) auto
qed

lemma analytic_on_eval_fls' [analytic_intros]:
  assumes "g analytic_on A"
  assumes "g ` A \<subseteq> eball 0 (fls_conv_radius f) - (if fls_subdegree f \<ge> 0 then {} else {0})"
  shows   "(\<lambda>x. eval_fls f (g x)) analytic_on A"
proof -
  have "eval_fls f \<circ> g analytic_on A"
    by (intro analytic_on_compose[OF assms(1) analytic_on_eval_fls]) (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma continuous_eval_fls [continuous_intros]:
  assumes "z \<in> eball 0 (fls_conv_radius F) - (if fls_subdegree F \<ge> 0 then {} else {0})"
  shows   "continuous (at z within A) (eval_fls F)"
proof -
  have "isCont (eval_fls F) z"
    using continuous_on_eval_fls[OF order.refl] assms
    by (subst (asm) continuous_on_eq_continuous_at) auto
  thus ?thesis
    using continuous_at_imp_continuous_at_within by blast
qed




named_theorems laurent_expansion_intros

lemma has_laurent_expansion_imp_asymp_equiv_0:
  assumes F: "f has_laurent_expansion F"
  defines "n \<equiv> fls_subdegree F"
  shows   "f \<sim>[at 0] (\<lambda>z. fls_nth F n * z powi n)"
proof (cases "F = 0")
  case True
  thus ?thesis using assms
    by (auto simp: has_laurent_expansion_def)
next
  case [simp]: False
  define G where "G = fls_base_factor_to_fps F"
  have "fls_conv_radius F > 0"
    using F by (auto simp: has_laurent_expansion_def)
  hence "isCont (eval_fps G) 0"
    by (intro continuous_intros) (auto simp: G_def fps_conv_radius_fls_regpart zero_ereal_def)
  hence lim: "eval_fps G \<midarrow>0\<rightarrow> eval_fps G 0"
    by (meson isContD)
  have [simp]: "fps_nth G 0 \<noteq> 0"
    by (auto simp: G_def)

  have "f \<sim>[at 0] eval_fls F"
    using F by (intro asymp_equiv_refl_ev) (auto simp: has_laurent_expansion_def eq_commute)
  also have "\<dots> = (\<lambda>z. eval_fps G z * z powi n)"
    by (intro ext) (simp_all add: eval_fls_def G_def n_def)
  also have "\<dots> \<sim>[at 0] (\<lambda>z. fps_nth G 0 * z powi n)" using lim
    by (intro asymp_equiv_intros tendsto_imp_asymp_equiv_const) (auto simp: eval_fps_at_0)
  also have "fps_nth G 0 = fls_nth F n"
    by (simp add: G_def n_def)
  finally show ?thesis
    by simp
qed

lemma has_laurent_expansion_imp_asymp_equiv:
  assumes F: "(\<lambda>w. f (z + w)) has_laurent_expansion F"
  defines "n \<equiv> fls_subdegree F"
  shows   "f \<sim>[at z] (\<lambda>w. fls_nth F n * (w - z) powi n)"
  using has_laurent_expansion_imp_asymp_equiv_0[OF assms(1)] unfolding n_def
  by (simp add: at_to_0[of z] asymp_equiv_filtermap_iff add_ac)


lemmas [tendsto_intros del] = tendsto_power_int

lemma has_laurent_expansion_imp_tendsto_0:
  assumes F: "f has_laurent_expansion F" and "fls_subdegree F \<ge> 0"
  shows   "f \<midarrow>0\<rightarrow> fls_nth F 0"
proof (rule asymp_equiv_tendsto_transfer)
  show "(\<lambda>z. fls_nth F (fls_subdegree F) * z powi fls_subdegree F) \<sim>[at 0] f"
    by (rule asymp_equiv_symI, rule has_laurent_expansion_imp_asymp_equiv_0) fact
  show "(\<lambda>z. fls_nth F (fls_subdegree F) * z powi fls_subdegree F) \<midarrow>0\<rightarrow> fls_nth F 0"
    by (rule tendsto_eq_intros refl | use assms(2) in simp)+
       (use assms(2) in \<open>auto simp: power_int_0_left_If\<close>)
qed

lemma has_laurent_expansion_imp_tendsto:
  assumes F: "(\<lambda>w. f (z + w)) has_laurent_expansion F" and "fls_subdegree F \<ge> 0"
  shows   "f \<midarrow>z\<rightarrow> fls_nth F 0"
  using has_laurent_expansion_imp_tendsto_0[OF assms]
  by (simp add: at_to_0[of z] filterlim_filtermap add_ac)

lemma has_laurent_expansion_imp_filterlim_infinity_0:
  assumes F: "f has_laurent_expansion F" and "fls_subdegree F < 0"
  shows   "filterlim f at_infinity (at 0)"
proof (rule asymp_equiv_at_infinity_transfer)
  have [simp]: "F \<noteq> 0"
    using assms(2) by auto
  show "(\<lambda>z. fls_nth F (fls_subdegree F) * z powi fls_subdegree F) \<sim>[at 0] f"
    by (rule asymp_equiv_symI, rule has_laurent_expansion_imp_asymp_equiv_0) fact
  show "filterlim (\<lambda>z. fls_nth F (fls_subdegree F) * z powi fls_subdegree F) at_infinity (at 0)"
    by (rule tendsto_mult_filterlim_at_infinity tendsto_const
             filterlim_power_int_neg_at_infinity | use assms(2) in simp)+
       (auto simp: eventually_at_filter)
qed

lemma has_laurent_expansion_imp_neg_fls_subdegree:
  assumes F: "f has_laurent_expansion F"
    and infy:"filterlim f at_infinity (at 0)"
  shows   "fls_subdegree F < 0"
proof (rule ccontr)
  assume asm:"\<not> fls_subdegree F < 0"
  define ff where "ff=(\<lambda>z. fls_nth F (fls_subdegree F)
                              * z powi fls_subdegree F)"

  have "(ff \<longlongrightarrow> (if fls_subdegree F =0 then fls_nth F 0 else 0)) (at 0)"
    using asm unfolding ff_def
    by (auto intro!: tendsto_eq_intros)
  moreover have "filterlim ff at_infinity (at 0)"
  proof (rule asymp_equiv_at_infinity_transfer)
    show "f \<sim>[at 0] ff" unfolding ff_def
      using has_laurent_expansion_imp_asymp_equiv_0[OF F] unfolding ff_def .
    show "filterlim f at_infinity (at 0)" by fact
  qed
  ultimately show False
    using not_tendsto_and_filterlim_at_infinity[of "at (0::complex)"] by auto
qed

lemma has_laurent_expansion_imp_filterlim_infinity:
  assumes F: "(\<lambda>w. f (z + w)) has_laurent_expansion F" and "fls_subdegree F < 0"
  shows   "filterlim f at_infinity (at z)"
  using has_laurent_expansion_imp_filterlim_infinity_0[OF assms]
  by (simp add: at_to_0[of z] filterlim_filtermap add_ac)

lemma has_laurent_expansion_imp_is_pole_0:
  assumes F: "f has_laurent_expansion F" and "fls_subdegree F < 0"
  shows   "is_pole f 0"
  using has_laurent_expansion_imp_filterlim_infinity_0[OF assms]
  by (simp add: is_pole_def)

lemma is_pole_0_imp_neg_fls_subdegree:
  assumes F: "f has_laurent_expansion F" and "is_pole f 0"
  shows   "fls_subdegree F < 0"
  using F assms(2) has_laurent_expansion_imp_neg_fls_subdegree is_pole_def
  by blast

lemma has_laurent_expansion_imp_is_pole:
  assumes F: "(\<lambda>x. f (z + x)) has_laurent_expansion F" and "fls_subdegree F < 0"
  shows   "is_pole f z"
  using has_laurent_expansion_imp_is_pole_0[OF assms]
  by (simp add: is_pole_shift_0')

lemma is_pole_imp_neg_fls_subdegree:
  assumes F: "(\<lambda>x. f (z + x)) has_laurent_expansion F" and "is_pole f z"
  shows   "fls_subdegree F < 0"
proof -
  have "is_pole (\<lambda>x. f (z + x)) 0"
    using assms(2) is_pole_shift_0 by blast
  then show ?thesis
    using F is_pole_0_imp_neg_fls_subdegree by blast
qed

lemma is_pole_fls_subdegree_iff:
  assumes "(\<lambda>x. f (z + x)) has_laurent_expansion F"
  shows "is_pole f z \<longleftrightarrow> fls_subdegree F < 0"
  using assms is_pole_imp_neg_fls_subdegree has_laurent_expansion_imp_is_pole
  by auto

lemma
  assumes "f has_laurent_expansion F"
  shows   has_laurent_expansion_isolated_0: "isolated_singularity_at f 0"
    and   has_laurent_expansion_not_essential_0: "not_essential f 0"
proof -
  from assms have "eventually (\<lambda>z. eval_fls F z = f z) (at 0)"
    by (auto simp: has_laurent_expansion_def)
  then obtain r where r: "r > 0" "\<And>z. z \<in> ball 0 r - {0} \<Longrightarrow> eval_fls F z = f z"
    by (auto simp: eventually_at_filter ball_def eventually_nhds_metric)

  have "fls_conv_radius F > 0"
    using assms by (auto simp: has_laurent_expansion_def)
  then obtain R :: real where R: "R > 0" "R \<le> min r (fls_conv_radius F)"
    using \<open>r > 0\<close> by (metis dual_order.strict_implies_order ereal_dense2 ereal_less(2) min_def)

  have "eval_fls F holomorphic_on ball 0 R - {0}"
    using r R by (intro holomorphic_intros ball_eball_mono Diff_mono)  (auto simp: ereal_le_less)
  also have "?this \<longleftrightarrow> f holomorphic_on ball 0 R - {0}"
    using r R by (intro holomorphic_cong) auto
  also have "\<dots> \<longleftrightarrow> f analytic_on ball 0 R - {0}"
    by (subst analytic_on_open) auto
  finally show "isolated_singularity_at f 0"
    unfolding isolated_singularity_at_def using \<open>R > 0\<close> by blast

  show "not_essential f 0"
  proof (cases "fls_subdegree F \<ge> 0")
    case True
    hence "f \<midarrow>0\<rightarrow> fls_nth F 0"
      by (intro has_laurent_expansion_imp_tendsto_0[OF assms])
    thus ?thesis
      by (auto simp: not_essential_def)
  next
    case False
    hence "is_pole f 0"
      by (intro has_laurent_expansion_imp_is_pole_0[OF assms]) auto
    thus ?thesis
      by (auto simp: not_essential_def)
  qed
qed

lemma
  assumes "(\<lambda>w. f (z + w)) has_laurent_expansion F"
  shows   has_laurent_expansion_isolated: "isolated_singularity_at f z"
    and   has_laurent_expansion_not_essential: "not_essential f z"
  using has_laurent_expansion_isolated_0[OF assms] has_laurent_expansion_not_essential_0[OF assms]
  by (simp_all add: isolated_singularity_at_shift_0 not_essential_shift_0)

lemma has_laurent_expansion_fps:
  assumes "f has_fps_expansion F"
  shows   "f has_laurent_expansion fps_to_fls F"
proof -
  from assms have radius: "0 < fps_conv_radius F" and eval: "\<forall>\<^sub>F z in nhds 0. eval_fps F z = f z"
    by (auto simp: has_fps_expansion_def)
  from eval have eval': "\<forall>\<^sub>F z in at 0. eval_fps F z = f z"
    using eventually_at_filter eventually_mono by fastforce
  moreover have "eventually (\<lambda>z. z \<in> eball 0 (fps_conv_radius F) - {0}) (at 0)"
    using radius by (intro eventually_at_in_open) (auto simp: zero_ereal_def)
  ultimately have "eventually (\<lambda>z. eval_fls (fps_to_fls F) z = f z) (at 0)"
    by eventually_elim (auto simp: eval_fps_to_fls)
  thus ?thesis using radius
    by (auto simp: has_laurent_expansion_def)
qed

lemma has_laurent_expansion_const [simp, intro, laurent_expansion_intros]:
  "(\<lambda>_. c) has_laurent_expansion fls_const c"
  by (auto simp: has_laurent_expansion_def)

lemma has_laurent_expansion_0 [simp, intro, laurent_expansion_intros]:
  "(\<lambda>_. 0) has_laurent_expansion 0"
  by (auto simp: has_laurent_expansion_def)

lemma has_fps_expansion_0_iff: "f has_fps_expansion 0 \<longleftrightarrow> eventually (\<lambda>z. f z = 0) (nhds 0)"
  by (auto simp: has_fps_expansion_def)

lemma has_laurent_expansion_1 [simp, intro, laurent_expansion_intros]:
  "(\<lambda>_. 1) has_laurent_expansion 1"
  by (auto simp: has_laurent_expansion_def)

lemma has_laurent_expansion_numeral [simp, intro, laurent_expansion_intros]:
  "(\<lambda>_. numeral n) has_laurent_expansion numeral n"
  by (auto simp: has_laurent_expansion_def)

lemma has_laurent_expansion_fps_X_power [laurent_expansion_intros]:
  "(\<lambda>x. x ^ n) has_laurent_expansion (fls_X_intpow n)"
  by (auto simp: has_laurent_expansion_def)

lemma has_laurent_expansion_fps_X_power_int [laurent_expansion_intros]:
  "(\<lambda>x. x powi n) has_laurent_expansion (fls_X_intpow n)"
  by (auto simp: has_laurent_expansion_def)

lemma has_laurent_expansion_fps_X [laurent_expansion_intros]:
  "(\<lambda>x. x) has_laurent_expansion fls_X"
  by (auto simp: has_laurent_expansion_def)

lemma has_laurent_expansion_cmult_left [laurent_expansion_intros]:
  assumes "f has_laurent_expansion F"
  shows   "(\<lambda>x. c * f x) has_laurent_expansion fls_const c * F"
proof -
  from assms have "eventually (\<lambda>z. z \<in> eball 0 (fls_conv_radius F) - {0}) (at 0)"
    by (intro eventually_at_in_open) (auto simp: has_laurent_expansion_def zero_ereal_def)
  moreover from assms have "eventually (\<lambda>z. eval_fls F z = f z) (at 0)"
    by (auto simp: has_laurent_expansion_def)
  ultimately have "eventually (\<lambda>z. eval_fls (fls_const c * F) z = c * f z) (at 0)"
    by eventually_elim (simp_all add: eval_fls_mult)
  with assms show ?thesis
    by (auto simp: has_laurent_expansion_def intro!: less_le_trans[OF _ fls_conv_radius_mult])
qed

lemma has_laurent_expansion_cmult_right [laurent_expansion_intros]:
  assumes "f has_laurent_expansion F"
  shows   "(\<lambda>x. f x * c) has_laurent_expansion F * fls_const c"
proof -
  have "F * fls_const c = fls_const c * F"
    by (intro fls_eqI) (auto simp: mult.commute)
  with has_laurent_expansion_cmult_left [OF assms] show ?thesis
    by (simp add: mult.commute)
qed

lemma has_fps_expansion_scaleR [fps_expansion_intros]:
  fixes F :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  shows "f has_fps_expansion F \<Longrightarrow> (\<lambda>x. c *\<^sub>R f x) has_fps_expansion fps_const (of_real c) * F"
  unfolding scaleR_conv_of_real by (intro fps_expansion_intros)

lemma has_laurent_expansion_scaleR [laurent_expansion_intros]:
  "f has_laurent_expansion F \<Longrightarrow> (\<lambda>x. c *\<^sub>R f x) has_laurent_expansion fls_const (of_real c) * F"
  unfolding scaleR_conv_of_real by (intro laurent_expansion_intros)

lemma has_laurent_expansion_minus [laurent_expansion_intros]:
  assumes "f has_laurent_expansion F"
  shows   "(\<lambda>x. - f x) has_laurent_expansion -F"
proof -
  from assms have "eventually (\<lambda>x. x \<in> eball 0 (fls_conv_radius F) - {0}) (at 0)"
    by (intro eventually_at_in_open) (auto simp: has_laurent_expansion_def zero_ereal_def)
  moreover from assms have "eventually (\<lambda>x. eval_fls F x = f x) (at 0)"
    by (auto simp: has_laurent_expansion_def)
  ultimately have "eventually (\<lambda>x. eval_fls (-F) x = -f x) (at 0)"
    by eventually_elim (auto simp: eval_fls_minus)
  thus ?thesis using assms by (auto simp: has_laurent_expansion_def)
qed

lemma has_laurent_expansion_add [laurent_expansion_intros]:
  assumes "f has_laurent_expansion F" "g has_laurent_expansion G"
  shows   "(\<lambda>x. f x + g x) has_laurent_expansion F + G"
proof -
  from assms have "0 < min (fls_conv_radius F) (fls_conv_radius G)"
    by (auto simp: has_laurent_expansion_def)
  also have "\<dots> \<le> fls_conv_radius (F + G)"
    by (rule fls_conv_radius_add)
  finally have radius: "\<dots> > 0" .

  from assms have "eventually (\<lambda>x. x \<in> eball 0 (fls_conv_radius F) - {0}) (at 0)"
                  "eventually (\<lambda>x. x \<in> eball 0 (fls_conv_radius G) - {0}) (at 0)"
    by (intro eventually_at_in_open; force simp: has_laurent_expansion_def zero_ereal_def)+
  moreover have "eventually (\<lambda>x. eval_fls F x = f x) (at 0)"
            and "eventually (\<lambda>x. eval_fls G x = g x) (at 0)"
    using assms by (auto simp: has_laurent_expansion_def)
  ultimately have "eventually (\<lambda>x. eval_fls (F + G) x = f x + g x) (at 0)"
    by eventually_elim (auto simp: eval_fls_add)
  with radius show ?thesis by (auto simp: has_laurent_expansion_def)
qed

lemma has_laurent_expansion_diff [laurent_expansion_intros]:
  assumes "f has_laurent_expansion F" "g has_laurent_expansion G"
  shows   "(\<lambda>x. f x - g x) has_laurent_expansion F - G"
  using has_laurent_expansion_add[of f F "\<lambda>x. - g x" "-G"] assms
  by (simp add: has_laurent_expansion_minus)

lemma has_laurent_expansion_mult [laurent_expansion_intros]:
  assumes "f has_laurent_expansion F" "g has_laurent_expansion G"
  shows   "(\<lambda>x. f x * g x) has_laurent_expansion F * G"
proof -
  from assms have "0 < min (fls_conv_radius F) (fls_conv_radius G)"
    by (auto simp: has_laurent_expansion_def)
  also have "\<dots> \<le> fls_conv_radius (F * G)"
    by (rule fls_conv_radius_mult)
  finally have radius: "\<dots> > 0" .

  from assms have "eventually (\<lambda>x. x \<in> eball 0 (fls_conv_radius F) - {0}) (at 0)"
                  "eventually (\<lambda>x. x \<in> eball 0 (fls_conv_radius G) - {0}) (at 0)"
    by (intro eventually_at_in_open; force simp: has_laurent_expansion_def zero_ereal_def)+
  moreover have "eventually (\<lambda>x. eval_fls F x = f x) (at 0)"
            and "eventually (\<lambda>x. eval_fls G x = g x) (at 0)"
    using assms by (auto simp: has_laurent_expansion_def)
  ultimately have "eventually (\<lambda>x. eval_fls (F * G) x = f x * g x) (at 0)"
    by eventually_elim (auto simp: eval_fls_mult)
  with radius show ?thesis by (auto simp: has_laurent_expansion_def)
qed

lemma has_fps_expansion_power [fps_expansion_intros]:
  fixes F :: "'a :: {banach, real_normed_div_algebra, comm_ring_1} fps"
  shows "f has_fps_expansion F \<Longrightarrow> (\<lambda>x. f x ^ m) has_fps_expansion F ^ m"
  by (induction m) (auto intro!: fps_expansion_intros)

lemma has_laurent_expansion_power [laurent_expansion_intros]:
  assumes "f has_laurent_expansion F"
  shows   "(\<lambda>x. f x ^ n) has_laurent_expansion F ^ n"
  by (induction n) (auto intro!: laurent_expansion_intros assms)

lemma has_laurent_expansion_sum [laurent_expansion_intros]:
  assumes "\<And>x. x \<in> I \<Longrightarrow> f x has_laurent_expansion F x"
  shows   "(\<lambda>y. \<Sum>x\<in>I. f x y) has_laurent_expansion (\<Sum>x\<in>I. F x)"
  using assms by (induction I rule: infinite_finite_induct) (auto intro!: laurent_expansion_intros)

lemma has_laurent_expansion_prod [laurent_expansion_intros]:
  assumes "\<And>x. x \<in> I \<Longrightarrow> f x has_laurent_expansion F x"
  shows   "(\<lambda>y. \<Prod>x\<in>I. f x y) has_laurent_expansion (\<Prod>x\<in>I. F x)"
  using assms by (induction I rule: infinite_finite_induct) (auto intro!: laurent_expansion_intros)

lemma has_laurent_expansion_deriv [laurent_expansion_intros]:
  assumes "f has_laurent_expansion F"
  shows   "deriv f has_laurent_expansion fls_deriv F"
proof -
  have "eventually (\<lambda>z. z \<in> eball 0 (fls_conv_radius F) - {0}) (at 0)"
    using assms by (intro eventually_at_in_open)
                   (auto simp: has_laurent_expansion_def zero_ereal_def)
  moreover from assms have "eventually (\<lambda>z. eval_fls F z = f z) (at 0)"
    by (auto simp: has_laurent_expansion_def)
  then obtain s where "open s" "0 \<in> s" and s: "\<And>w. w \<in> s - {0} \<Longrightarrow> eval_fls F w = f w"
    by (auto simp: eventually_nhds eventually_at_filter)
  hence "eventually (\<lambda>w. w \<in> s - {0}) (at 0)"
    by (intro eventually_at_in_open) auto
  ultimately have "eventually (\<lambda>z. eval_fls (fls_deriv F) z = deriv f z) (at 0)"
  proof eventually_elim
    case (elim z)
    hence "eval_fls (fls_deriv F) z = deriv (eval_fls F) z"
      by (simp add: eval_fls_deriv)
    also have "eventually (\<lambda>w. w \<in> s - {0}) (nhds z)"
      using elim and \<open>open s\<close> by (intro eventually_nhds_in_open) auto
    hence "eventually (\<lambda>w. eval_fls F w = f w) (nhds z)"
      by eventually_elim (use s in auto)
    hence "deriv (eval_fls F) z = deriv f z"
      by (intro deriv_cong_ev refl)
    finally show ?case .
  qed
  with assms show ?thesis
    by (auto simp: has_laurent_expansion_def intro!: less_le_trans[OF _ fls_conv_radius_deriv])
qed

lemma has_laurent_expansion_shift [laurent_expansion_intros]:
  assumes "f has_laurent_expansion F"
  shows   "(\<lambda>x. f x * x powi n) has_laurent_expansion (fls_shift (-n) F)"
proof -
  have "eventually (\<lambda>x. x \<in> eball 0 (fls_conv_radius F) - {0}) (at 0)"
    using assms by (intro eventually_at_in_open) (auto simp: has_laurent_expansion_def zero_ereal_def)
  moreover have "eventually (\<lambda>x. eval_fls F x = f x) (at 0)"
    using assms by (auto simp: has_laurent_expansion_def)
  ultimately have "eventually (\<lambda>x. eval_fls (fls_shift (-n) F) x = f x * x powi n) (at 0)"
    by eventually_elim (auto simp: eval_fls_shift assms)
  with assms show ?thesis by (auto simp: has_laurent_expansion_def)
qed

lemma has_laurent_expansion_shift' [laurent_expansion_intros]:
  assumes "f has_laurent_expansion F"
  shows   "(\<lambda>x. f x * x powi (-n)) has_laurent_expansion (fls_shift n F)"
  using has_laurent_expansion_shift[OF assms, of "-n"] by simp


lemma has_laurent_expansion_deriv':
  assumes "f has_laurent_expansion F"
  assumes "open A" "0 \<in> A" "\<And>x. x \<in> A - {0} \<Longrightarrow> (f has_field_derivative f' x) (at x)"
  shows   "f' has_laurent_expansion fls_deriv F"
proof -
  have "deriv f has_laurent_expansion fls_deriv F"
    by (intro laurent_expansion_intros assms)
  also have "?this \<longleftrightarrow> ?thesis"
  proof (intro has_laurent_expansion_cong refl)
    have "eventually (\<lambda>z. z \<in> A - {0}) (at 0)"
      by (intro eventually_at_in_open assms)
    thus "eventually (\<lambda>z. deriv f z = f' z) (at 0)"
      by eventually_elim (auto intro!: DERIV_imp_deriv assms)
  qed
  finally show ?thesis .
qed

definition laurent_expansion :: "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> complex fls" where
  "laurent_expansion f z =
     (if eventually (\<lambda>z. f z = 0) (at z) then 0
      else fls_shift (-zorder f z) (fps_to_fls (fps_expansion (zor_poly f z) z)))"

lemma laurent_expansion_cong:
  assumes "eventually (\<lambda>w. f w = g w) (at z)" "z = z'"
  shows   "laurent_expansion f z = laurent_expansion g z'"
  unfolding laurent_expansion_def
  using zor_poly_cong[OF assms(1,2)] zorder_cong[OF assms] assms
  by (intro if_cong refl) (auto elim: eventually_elim2)

theorem not_essential_has_laurent_expansion_0:
  assumes "isolated_singularity_at f 0" "not_essential f 0"
  shows   "f has_laurent_expansion laurent_expansion f 0"
proof (cases "\<exists>\<^sub>F w in at 0. f w \<noteq> 0")
  case False
  have "(\<lambda>_. 0) has_laurent_expansion 0"
    by simp
  also have "?this \<longleftrightarrow> f has_laurent_expansion 0"
    using False by (intro has_laurent_expansion_cong) (auto simp: frequently_def)
  finally show ?thesis
    using False by (simp add: laurent_expansion_def frequently_def)
next
  case True
  define n where "n = zorder f 0"
  obtain r where r: "zor_poly f 0 0 \<noteq> 0" "zor_poly f 0 holomorphic_on cball 0 r" "r > 0"
                    "\<forall>w\<in>cball 0 r - {0}. f w = zor_poly f 0 w * w powi n \<and>
                                         zor_poly f 0 w \<noteq> 0"
    using zorder_exist[OF assms True] unfolding n_def by auto
  have holo: "zor_poly f 0 holomorphic_on ball 0 r"
    by (rule holomorphic_on_subset[OF r(2)]) auto

  define F where "F = fps_expansion (zor_poly f 0) 0"
  have F: "zor_poly f 0 has_fps_expansion F"
    unfolding F_def by (rule has_fps_expansion_fps_expansion[OF _ _ holo]) (use \<open>r > 0\<close> in auto)
  have "(\<lambda>z. zor_poly f 0 z * z powi n) has_laurent_expansion fls_shift (-n) (fps_to_fls F)"
    by (intro laurent_expansion_intros has_laurent_expansion_fps[OF F])
  also have "?this \<longleftrightarrow> f has_laurent_expansion fls_shift (-n) (fps_to_fls F)"
    by (intro has_laurent_expansion_cong refl eventually_mono[OF eventually_at_in_open[of "ball 0 r"]])
       (use r in \<open>auto simp: complex_powr_of_int\<close>)
  finally show ?thesis using True
    by (simp add: laurent_expansion_def F_def n_def frequently_def)
qed

lemma not_essential_has_laurent_expansion:
  assumes "isolated_singularity_at f z" "not_essential f z"
  shows   "(\<lambda>x. f (z + x)) has_laurent_expansion laurent_expansion f z"
proof -
  from assms(1) have iso:"isolated_singularity_at (\<lambda>x. f (z + x)) 0"
    by (simp add: isolated_singularity_at_shift_0)
  moreover from assms(2) have ness:"not_essential (\<lambda>x. f (z + x)) 0"
    by (simp add: not_essential_shift_0)
  ultimately have "(\<lambda>x. f (z + x)) has_laurent_expansion laurent_expansion (\<lambda>x. f (z + x)) 0"
    by (rule not_essential_has_laurent_expansion_0)

  also have "\<dots> = laurent_expansion f z"
  proof (cases "\<exists>\<^sub>F w in at z. f w \<noteq> 0")
    case False
    then have "\<forall>\<^sub>F w in at z. f w = 0" using not_frequently by force
    then have "laurent_expansion (\<lambda>x. f (z + x)) 0 = 0"
      by (smt (verit, best) add.commute eventually_at_to_0 eventually_mono
          laurent_expansion_def)
    moreover have "laurent_expansion f z = 0"
      using \<open>\<forall>\<^sub>F w in at z. f w = 0\<close> unfolding laurent_expansion_def by auto
    ultimately show ?thesis by auto
  next
    case True
    define df where "df=zor_poly (\<lambda>x. f (z + x)) 0"
    define g where "g=(\<lambda>u. u-z)"

    have "fps_expansion df 0
        =  fps_expansion (df o g) z"
    proof -
      have "\<exists>\<^sub>F w in at 0. f (z + w) \<noteq> 0" using True
        by (smt (verit, best) add.commute eventually_at_to_0
            eventually_mono not_frequently)
      from zorder_exist[OF iso ness this,folded df_def]
      obtain r where "r>0" and df_holo:"df holomorphic_on cball 0 r" and "df 0 \<noteq> 0"
          "\<forall>w\<in>cball 0 r - {0}.
             f (z + w) = df w * w powi (zorder (\<lambda>w. f (z + w)) 0) \<and>
             df w \<noteq> 0"
        by auto
      then have df_nz:"\<forall>w\<in>ball 0 r. df w\<noteq>0" by auto

      have "(deriv ^^ n) df 0 =  (deriv ^^ n) (df \<circ> g) z" for n
        unfolding comp_def g_def
      proof (subst higher_deriv_compose_linear'[where u=1 and c="-z",simplified])
        show "df holomorphic_on ball 0 r"
          using df_holo by auto
        show "open (ball z r)" "open (ball 0 r)" "z \<in> ball z r"
          using \<open>r>0\<close> by auto
        show " \<And>w. w \<in> ball z r \<Longrightarrow> w - z \<in> ball 0 r"
          by (simp add: dist_norm)
      qed auto
      then show ?thesis
        unfolding fps_expansion_def by auto
    qed
    also have "... = fps_expansion (zor_poly f z) z"
    proof (rule fps_expansion_cong)
      have "\<forall>\<^sub>F w in nhds z. zor_poly f z w
                = zor_poly (\<lambda>u. f (z + u)) 0 (w - z)"
        apply (rule zor_poly_shift)
        using True assms by auto
      then show "\<forall>\<^sub>F w in nhds z. (df \<circ> g) w = zor_poly f z w"
        unfolding df_def g_def comp_def
        by (auto elim:eventually_mono)
    qed
    finally show ?thesis unfolding df_def
      by (auto simp: laurent_expansion_def at_to_0[of z]
          eventually_filtermap add_ac zorder_shift')
  qed
  finally show ?thesis .
qed

lemma has_fps_expansion_to_laurent:
  "f has_fps_expansion F \<longleftrightarrow> f has_laurent_expansion fps_to_fls F \<and> f 0 = fps_nth F 0"
proof safe
  assume *: "f has_laurent_expansion fps_to_fls F" "f 0 = fps_nth F 0"
  have "eventually (\<lambda>z. z \<in> eball 0 (fps_conv_radius F)) (nhds 0)"
    using * by (intro eventually_nhds_in_open) (auto simp: has_laurent_expansion_def zero_ereal_def)
  moreover have "eventually (\<lambda>z. z \<noteq> 0 \<longrightarrow> eval_fls (fps_to_fls F) z = f z) (nhds 0)"
    using * by (auto simp: has_laurent_expansion_def eventually_at_filter)
  ultimately have "eventually (\<lambda>z. f z = eval_fps F z) (nhds 0)"
    by eventually_elim
       (auto simp: has_laurent_expansion_def eventually_at_filter eval_fps_at_0 eval_fps_to_fls *(2))
  thus "f has_fps_expansion F"
    using * by (auto simp: has_fps_expansion_def has_laurent_expansion_def eq_commute)
next
  assume "f has_fps_expansion F"
  thus "f 0 = fps_nth F 0"
    by (metis eval_fps_at_0 has_fps_expansion_imp_holomorphic)
qed (auto intro: has_laurent_expansion_fps)

lemma eval_fps_fls_base_factor [simp]:
  assumes "z \<noteq> 0"
  shows   "eval_fps (fls_base_factor_to_fps F) z = eval_fls F z * z powi -fls_subdegree F"
  using assms unfolding eval_fls_def by (simp add: power_int_minus field_simps)

lemma has_fps_expansion_imp_analytic_0:
  assumes "f has_fps_expansion F"
  shows   "f analytic_on {0}"
  by (meson analytic_at_two assms has_fps_expansion_imp_holomorphic)

lemma has_fps_expansion_imp_analytic:
  assumes "(\<lambda>x. f (z + x)) has_fps_expansion F"
  shows   "f analytic_on {z}"
proof -
  have "(\<lambda>x. f (z + x)) analytic_on {0}"
    by (rule has_fps_expansion_imp_analytic_0) fact
  hence "(\<lambda>x. f (z + x)) \<circ> (\<lambda>x. x - z) analytic_on {z}"
    by (intro analytic_on_compose_gen analytic_intros) auto
  thus ?thesis
    by (simp add: o_def)
qed

lemma is_pole_cong_asymp_equiv:
  assumes "f \<sim>[at z] g" "z = z'"
  shows   "is_pole f z = is_pole g z'"
  using asymp_equiv_at_infinity_transfer[OF assms(1)]
        asymp_equiv_at_infinity_transfer[OF asymp_equiv_symI[OF assms(1)]] assms(2)
  unfolding is_pole_def by auto

lemma not_is_pole_const [simp]: "\<not>is_pole (\<lambda>_::'a::perfect_space. c :: complex) z"
  using not_tendsto_and_filterlim_at_infinity[of "at z" "\<lambda>_::'a. c" c] by (auto simp: is_pole_def)

lemma has_laurent_expansion_imp_is_pole_iff:
  assumes F: "(\<lambda>x. f (z + x)) has_laurent_expansion F"
  shows   "is_pole f z \<longleftrightarrow> fls_subdegree F < 0"
proof
  assume pole: "is_pole f z"
  have [simp]: "F \<noteq> 0"
  proof
    assume "F = 0"
    hence "is_pole f z \<longleftrightarrow> is_pole (\<lambda>_. 0 :: complex) z" using assms
      by (intro is_pole_cong)
         (auto simp: has_laurent_expansion_def at_to_0[of z] eventually_filtermap add_ac)
    with pole show False
      by simp
  qed

  note pole
  also have "is_pole f z \<longleftrightarrow>
             is_pole (\<lambda>w. fls_nth F (fls_subdegree F) * (w - z) powi fls_subdegree F) z"
    using has_laurent_expansion_imp_asymp_equiv[OF F] by (intro is_pole_cong_asymp_equiv refl)
  also have "\<dots> \<longleftrightarrow> is_pole (\<lambda>w. (w - z) powi fls_subdegree F) z"
    by simp
  finally have pole': \<dots> .

  have False if "fls_subdegree F \<ge> 0"
  proof -
    have "(\<lambda>w. (w - z) powi fls_subdegree F) holomorphic_on UNIV"
      using that by (intro holomorphic_intros) auto
    hence "\<not>is_pole (\<lambda>w. (w - z) powi fls_subdegree F) z"
      by (meson UNIV_I not_is_pole_holomorphic open_UNIV)
    with pole' show False
      by simp
  qed
  thus "fls_subdegree F < 0"
    by force
qed (use has_laurent_expansion_imp_is_pole[OF assms] in auto)

lemma analytic_at_imp_has_fps_expansion_0:
  assumes "f analytic_on {0}"
  shows   "f has_fps_expansion fps_expansion f 0"
  using assms has_fps_expansion_fps_expansion analytic_at by fast

lemma deriv_shift_0: "deriv f z = deriv (f \<circ> (\<lambda>x. z + x)) 0"
proof -
  have *: "(f \<circ> (+) z has_field_derivative D) (at z')"
    if "(f has_field_derivative D) (at (z + z'))" for D z z' and f :: "'a \<Rightarrow> 'a"
  proof -
    have "(f \<circ> (+) z has_field_derivative D * 1) (at z')"
      by (rule DERIV_chain that derivative_eq_intros refl)+ auto
    thus ?thesis by simp
  qed
  have "(\<lambda>D. (f has_field_derivative D) (at z)) = (\<lambda> D. (f \<circ> (+) z has_field_derivative D) (at 0))"
    using *[of f _ z 0] *[of "f \<circ> (+) z" _ "-z" z] by (intro ext iffI) (auto simp: o_def)
  thus ?thesis
    by (simp add: deriv_def)
qed

lemma deriv_shift_0': "NO_MATCH 0 z \<Longrightarrow> deriv f z = deriv (f \<circ> (\<lambda>x. z + x)) 0"
  by (rule deriv_shift_0)

lemma higher_deriv_shift_0: "(deriv ^^ n) f z = (deriv ^^ n) (f \<circ> (\<lambda>x. z + x)) 0"
proof (induction n arbitrary: f)
  case (Suc n)
  have "(deriv ^^ Suc n) f z = (deriv ^^ n) (deriv f) z"
    by (subst funpow_Suc_right) auto
  also have "\<dots> = (deriv ^^ n) (\<lambda>x. deriv f (z + x)) 0"
    by (subst Suc) (auto simp: o_def)
  also have "\<dots> = (deriv ^^ n) (\<lambda>x. deriv (\<lambda>xa. f (z + x + xa)) 0) 0"
    by (subst deriv_shift_0) (auto simp: o_def)
  also have "(\<lambda>x. deriv (\<lambda>xa. f (z + x + xa)) 0) = deriv (\<lambda>x. f (z + x))"
    by (rule ext) (simp add: deriv_shift_0' o_def add_ac)
  also have "(deriv ^^ n) \<dots> 0 = (deriv ^^ Suc n) (f \<circ> (\<lambda>x. z + x)) 0"
    by (subst funpow_Suc_right) (auto simp: o_def)
  finally show ?case .
qed auto

lemma higher_deriv_shift_0': "NO_MATCH 0 z \<Longrightarrow> (deriv ^^ n) f z = (deriv ^^ n) (f \<circ> (\<lambda>x. z + x)) 0"
  by (rule higher_deriv_shift_0)

lemma analytic_at_imp_has_fps_expansion:
  assumes "f analytic_on {z}"
  shows   "(\<lambda>x. f (z + x)) has_fps_expansion fps_expansion f z"
proof -
  have "f \<circ> (\<lambda>x. z + x) analytic_on {0}"
    by (intro analytic_on_compose_gen[OF _ assms] analytic_intros) auto
  hence "(f \<circ> (\<lambda>x. z + x)) has_fps_expansion fps_expansion (f \<circ> (\<lambda>x. z + x)) 0"
    unfolding o_def by (intro analytic_at_imp_has_fps_expansion_0) auto
  also have "\<dots> = fps_expansion f z"
    by (simp add: fps_expansion_def higher_deriv_shift_0')
  finally show ?thesis by (simp add: add_ac)
qed

lemma has_laurent_expansion_zorder_0:
  assumes "f has_laurent_expansion F" "F \<noteq> 0"
  shows   "zorder f 0 = fls_subdegree F"
proof -
  define G where "G = fls_base_factor_to_fps F"
  from assms obtain A where A: "0 \<in> A" "open A" "\<And>x. x \<in> A - {0} \<Longrightarrow> eval_fls F x = f x"
    unfolding has_laurent_expansion_def eventually_at_filter eventually_nhds
    by blast

  show ?thesis
  proof (rule zorder_eqI)
    show "open (A \<inter> eball 0 (fls_conv_radius F))" "0 \<in> A \<inter>  eball 0 (fls_conv_radius F)"
      using assms A by (auto simp: has_laurent_expansion_def zero_ereal_def)
    show "eval_fps G holomorphic_on A \<inter> eball 0 (fls_conv_radius F)"
      by (intro holomorphic_intros) (auto simp: fls_conv_radius_altdef G_def)
    show "eval_fps G 0 \<noteq> 0" using \<open>F \<noteq> 0\<close>
      by (auto simp: eval_fps_at_0 G_def)
  next
    fix w :: complex assume "w \<in> A \<inter> eball 0 (fls_conv_radius F)" "w \<noteq> 0"
    thus "f w = eval_fps G w * (w - 0) powi (fls_subdegree F)"
      using A unfolding G_def
      by (subst eval_fps_fls_base_factor)
         (auto simp: complex_powr_of_int power_int_minus field_simps)
  qed
qed

lemma has_laurent_expansion_zorder:
  assumes "(\<lambda>w. f (z + w)) has_laurent_expansion F" "F \<noteq> 0"
  shows   "zorder f z = fls_subdegree F"
  using has_laurent_expansion_zorder_0[OF assms] by (simp add: zorder_shift' add_ac)

lemma has_fps_expansion_zorder_0:
  assumes "f has_fps_expansion F" "F \<noteq> 0"
  shows   "zorder f 0 = int (subdegree F)"
  using assms has_laurent_expansion_zorder_0[of f "fps_to_fls F"]
  by (auto simp: has_fps_expansion_to_laurent fls_subdegree_fls_to_fps)

lemma has_fps_expansion_zorder:
  assumes "(\<lambda>w. f (z + w)) has_fps_expansion F" "F \<noteq> 0"
  shows   "zorder f z = int (subdegree F)"
  using has_fps_expansion_zorder_0[OF assms]
  by (simp add: zorder_shift' add_ac)

lemma has_fps_expansion_fls_base_factor_to_fps:
  assumes "f has_laurent_expansion F"
  defines "n \<equiv> fls_subdegree F"
  defines "c \<equiv> fps_nth (fls_base_factor_to_fps F) 0"
  shows   "(\<lambda>z. if z = 0 then c else f z * z powi -n) has_fps_expansion fls_base_factor_to_fps F"
proof -
  have "(\<lambda>z. f z * z powi -n) has_laurent_expansion fls_shift (-(-n)) F"
    by (intro laurent_expansion_intros assms)
  also have "fls_shift (-(-n)) F = fps_to_fls (fls_base_factor_to_fps F)"
    by (simp add: n_def fls_shift_nonneg_subdegree)
  also have "(\<lambda>z. f z * z powi - n) has_laurent_expansion fps_to_fls (fls_base_factor_to_fps F) \<longleftrightarrow>
             (\<lambda>z. if z = 0 then c else f z * z powi -n) has_laurent_expansion fps_to_fls (fls_base_factor_to_fps F)"
    by (intro has_laurent_expansion_cong) (auto simp: eventually_at_filter)
  also have "\<dots> \<longleftrightarrow> (\<lambda>z. if z = 0 then c else f z * z powi -n) has_fps_expansion fls_base_factor_to_fps F"
    by (subst has_fps_expansion_to_laurent) (auto simp: c_def)
  finally show ?thesis .
qed

lemma zero_has_laurent_expansion_imp_eq_0:
  assumes "(\<lambda>_. 0) has_laurent_expansion F"
  shows   "F = 0"
proof -
  have "at (0 :: complex) \<noteq> bot"
    by auto
  moreover have "(\<lambda>z. if z = 0 then fls_nth F (fls_subdegree F) else 0) has_fps_expansion
          fls_base_factor_to_fps F" (is "?f has_fps_expansion _")
    using has_fps_expansion_fls_base_factor_to_fps[OF assms] by (simp cong: if_cong)
  hence "isCont ?f 0"
    using has_fps_expansion_imp_continuous by blast
  hence "?f \<midarrow>0\<rightarrow> fls_nth F (fls_subdegree F)"
    by (auto simp: isCont_def)
  moreover have "?f \<midarrow>0\<rightarrow> 0 \<longleftrightarrow> (\<lambda>_::complex. 0 :: complex) \<midarrow>0\<rightarrow> 0"
    by (intro filterlim_cong) (auto simp: eventually_at_filter)
  hence "?f \<midarrow>0\<rightarrow> 0"
    by simp
  ultimately have "fls_nth F (fls_subdegree F) = 0"
    by (rule tendsto_unique)
  thus ?thesis
    by (meson nth_fls_subdegree_nonzero)
qed

lemma has_laurent_expansion_unique:
  assumes "f has_laurent_expansion F" "f has_laurent_expansion G"
  shows   "F = G"
proof -
  from assms have "(\<lambda>x. f x - f x) has_laurent_expansion F - G"
    by (intro laurent_expansion_intros)
  hence "(\<lambda>_. 0) has_laurent_expansion F - G"
    by simp
  hence "F - G = 0"
    by (rule zero_has_laurent_expansion_imp_eq_0)
  thus ?thesis
    by simp
qed

lemma laurent_expansion_eqI:
  assumes "(\<lambda>x. f (z + x)) has_laurent_expansion F"
  shows   "laurent_expansion f z = F"
  using assms has_laurent_expansion_isolated has_laurent_expansion_not_essential
        has_laurent_expansion_unique not_essential_has_laurent_expansion by blast

lemma laurent_expansion_0_eqI:
  assumes "f has_laurent_expansion F"
  shows   "laurent_expansion f 0 = F"
  using assms laurent_expansion_eqI[of f 0] by simp

lemma has_laurent_expansion_nonzero_imp_eventually_nonzero:
  assumes "f has_laurent_expansion F" "F \<noteq> 0"
  shows   "eventually (\<lambda>x. f x \<noteq> 0) (at 0)"
proof (rule ccontr)
  assume "\<not>eventually (\<lambda>x. f x \<noteq> 0) (at 0)"
  with assms have "eventually (\<lambda>x. f x = 0) (at 0)"
    by (intro not_essential_frequently_0_imp_eventually_0 has_laurent_expansion_isolated
              has_laurent_expansion_not_essential)
       (auto simp: frequently_def)
  hence "(f has_laurent_expansion 0) \<longleftrightarrow> ((\<lambda>_. 0) has_laurent_expansion 0)"
    by (intro has_laurent_expansion_cong) auto
  hence "f has_laurent_expansion 0"
    by simp
  with assms(1) have "F = 0"
    using has_laurent_expansion_unique by blast
  with \<open>F \<noteq> 0\<close> show False
    by contradiction
qed

lemma has_laurent_expansion_eventually_nonzero_iff':
  assumes "f has_laurent_expansion F"
  shows   "eventually (\<lambda>x. f x \<noteq> 0) (at 0) \<longleftrightarrow> F \<noteq> 0 "
proof
  assume "\<forall>\<^sub>F x in at 0. f x \<noteq> 0"
  moreover have "\<not> (\<forall>\<^sub>F x in at 0. f x \<noteq> 0)" if "F=0"
  proof -
    have "\<forall>\<^sub>F x in at 0. f x = 0"
      using assms that unfolding has_laurent_expansion_def by simp
    then show ?thesis unfolding not_eventually
      by (auto elim:eventually_frequentlyE)
  qed
  ultimately show "F \<noteq> 0" by auto
qed (simp add:has_laurent_expansion_nonzero_imp_eventually_nonzero[OF assms])

lemma has_laurent_expansion_eventually_nonzero_iff:
  assumes "(\<lambda>w. f (z+w)) has_laurent_expansion F"
  shows   "eventually (\<lambda>x. f x \<noteq> 0) (at z)  \<longleftrightarrow> F \<noteq> 0"
  apply (subst eventually_at_to_0)
  apply (rule has_laurent_expansion_eventually_nonzero_iff')
  using assms by (simp add:add.commute)

lemma has_laurent_expansion_inverse [laurent_expansion_intros]:
  assumes "f has_laurent_expansion F"
  shows   "(\<lambda>x. inverse (f x)) has_laurent_expansion inverse F"
proof (cases "F = 0")
  case True
  thus ?thesis using assms
    by (auto simp: has_laurent_expansion_def)
next
  case False
  define G where "G = laurent_expansion (\<lambda>x. inverse (f x)) 0"
  from False have ev: "eventually (\<lambda>z. f z \<noteq> 0) (at 0)"
    by (intro has_laurent_expansion_nonzero_imp_eventually_nonzero[OF assms])

  have *: "(\<lambda>x. inverse (f x)) has_laurent_expansion G" unfolding G_def
    by (intro not_essential_has_laurent_expansion_0 isolated_singularity_at_inverse not_essential_inverse
              has_laurent_expansion_isolated_0[OF assms] has_laurent_expansion_not_essential_0[OF assms])
  have "(\<lambda>x. f x * inverse (f x)) has_laurent_expansion F * G"
    by (intro laurent_expansion_intros assms *)
  also have "?this \<longleftrightarrow> (\<lambda>x. 1) has_laurent_expansion F * G"
    by (intro has_laurent_expansion_cong refl eventually_mono[OF ev]) auto
  finally have "(\<lambda>_. 1) has_laurent_expansion F * G" .
  moreover have "(\<lambda>_. 1) has_laurent_expansion 1"
    by simp
  ultimately have "F * G = 1"
    using has_laurent_expansion_unique by blast
  hence "G = inverse F"
    using inverse_unique by blast
  with * show ?thesis
    by simp
qed

lemma has_laurent_expansion_power_int [laurent_expansion_intros]:
  "f has_laurent_expansion F \<Longrightarrow> (\<lambda>x. f x powi n) has_laurent_expansion (F powi n)"
  by (auto simp: power_int_def intro!: laurent_expansion_intros)


lemma has_fps_expansion_0_analytic_continuation:
  assumes "f has_fps_expansion 0" "f holomorphic_on A"
  assumes "open A" "connected A" "0 \<in> A" "x \<in> A"
  shows   "f x = 0"
proof -
  have "eventually (\<lambda>z. z \<in> A \<and> f z = 0) (nhds 0)" using assms
    by (intro eventually_conj eventually_nhds_in_open) (auto simp: has_fps_expansion_def)
  then obtain B where B: "open B" "0 \<in> B" "\<forall>z\<in>B. z \<in> A \<and> f z = 0"
    unfolding eventually_nhds by blast
  show ?thesis
  proof (rule analytic_continuation_open[where f = f and g = "\<lambda>_. 0"])
    show "B \<noteq> {}"
      using \<open>open B\<close> B by auto
    show "connected A"
      using assms by auto
  qed (use assms B in auto)
qed

lemma has_laurent_expansion_0_analytic_continuation:
  assumes "f has_laurent_expansion 0" "f holomorphic_on A - {0}"
  assumes "open A" "connected A" "0 \<in> A" "x \<in> A - {0}"
  shows   "f x = 0"
proof -
  have "eventually (\<lambda>z. z \<in> A - {0} \<and> f z = 0) (at 0)" using assms
    by (intro eventually_conj eventually_at_in_open) (auto simp: has_laurent_expansion_def)
  then obtain B where B: "open B" "0 \<in> B" "\<forall>z\<in>B - {0}. z \<in> A - {0} \<and> f z = 0"
    unfolding eventually_at_filter eventually_nhds by blast
  show ?thesis
  proof (rule analytic_continuation_open[where f = f and g = "\<lambda>_. 0"])
    show "B - {0} \<noteq> {}"
      using \<open>open B\<close> \<open>0 \<in> B\<close> by (metis insert_Diff not_open_singleton)
    show "connected (A - {0})"
      using assms by (intro connected_open_delete) auto
  qed (use assms B in auto)
qed

lemma has_fps_expansion_cong:
  assumes "eventually (\<lambda>x. f x = g x) (nhds 0)" "F = G"
  shows   "f has_fps_expansion F \<longleftrightarrow> g has_fps_expansion G"
  using assms(2) by (auto simp: has_fps_expansion_def elim!: eventually_elim2[OF assms(1)])

lemma zor_poly_has_fps_expansion:
  assumes "f has_laurent_expansion F" "F \<noteq> 0"
  shows   "zor_poly f 0 has_fps_expansion fls_base_factor_to_fps F"
proof -
  note [simp] = \<open>F \<noteq> 0\<close>
  have "eventually (\<lambda>z. f z \<noteq> 0) (at 0)"
    by (rule has_laurent_expansion_nonzero_imp_eventually_nonzero[OF assms])
  hence freq: "frequently (\<lambda>z. f z \<noteq> 0) (at 0)"
    by (rule eventually_frequently[rotated]) auto

  have *: "isolated_singularity_at f 0" "not_essential f 0"
    using has_laurent_expansion_isolated_0[OF assms(1)] has_laurent_expansion_not_essential_0[OF assms(1)]
    by auto

  define G where "G = fls_base_factor_to_fps F"
  define n where "n = zorder f 0"
  have n_altdef: "n = fls_subdegree F"
    using has_laurent_expansion_zorder_0 [OF assms(1)] by (simp add: n_def)
  obtain r where r: "zor_poly f 0 0 \<noteq> 0" "zor_poly f 0 holomorphic_on cball 0 r" "r > 0"
                    "\<forall>w\<in>cball 0 r - {0}. f w = zor_poly f 0 w * w powi n \<and>
                                         zor_poly f 0 w \<noteq> 0"
    using zorder_exist[OF * freq] unfolding n_def by auto
  obtain r' where r': "r' > 0" "\<forall>x\<in>ball 0 r'-{0}. eval_fls F x = f x"
    using assms(1) unfolding has_laurent_expansion_def eventually_at_filter eventually_nhds_metric ball_def
    by (auto simp: dist_commute)
  have holo: "zor_poly f 0 holomorphic_on ball 0 r"
    by (rule holomorphic_on_subset[OF r(2)]) auto

  have "(\<lambda>z. if z = 0 then fps_nth G 0 else f z * z powi -n) has_fps_expansion G"
    unfolding G_def n_altdef by (intro has_fps_expansion_fls_base_factor_to_fps assms)
  also have "?this \<longleftrightarrow> zor_poly f 0 has_fps_expansion G"
  proof (intro has_fps_expansion_cong)
    have "eventually (\<lambda>z. z \<in> ball 0 (min r r')) (nhds 0)"
      using \<open>r > 0\<close> \<open>r' > 0\<close> by (intro eventually_nhds_in_open) auto
    thus "\<forall>\<^sub>F x in nhds 0. (if x = 0 then G $ 0 else f x * x powi - n) = zor_poly f 0 x"
    proof eventually_elim
      case (elim w)
      have w: "w \<in> ball 0 r" "w \<in> ball 0 r'"
        using elim by auto
      show ?case
      proof (cases "w = 0")
        case False
        hence "f w = zor_poly f 0 w * w powi n"
          using r w by auto
        thus ?thesis using False
          by (simp add: powr_minus complex_powr_of_int power_int_minus)
      next
        case [simp]: True
        obtain R where R: "R > 0" "R \<le> r" "R \<le> r'" "R \<le> fls_conv_radius F"
          using \<open>r > 0\<close> \<open>r' > 0\<close> assms(1) unfolding has_laurent_expansion_def
          by (smt (verit, ccfv_SIG) ereal_dense2 ereal_less(2) less_ereal.simps(1) order.strict_implies_order order_trans)
        have "eval_fps G 0 = zor_poly f 0 0"
        proof (rule analytic_continuation_open[where f = "eval_fps G" and g = "zor_poly f 0"])
          show "connected (ball 0 R :: complex set)"
            by auto
          have "of_real R / 2 \<in> ball 0 R - {0 :: complex}"
            using R by auto
          thus "ball 0 R - {0 :: complex} \<noteq> {}"
            by blast
          show "eval_fps G holomorphic_on ball 0 R"
            using R less_le_trans[OF _ R(4)] unfolding G_def
            by (intro holomorphic_intros) (auto simp: fls_conv_radius_altdef)
          show "zor_poly f 0 holomorphic_on ball 0 R"
            by (rule holomorphic_on_subset[OF holo]) (use R in auto)
          show "eval_fps G z = zor_poly f 0 z" if "z \<in> ball 0 R - {0}" for z
            using that r r' R n_altdef unfolding G_def
            by (subst eval_fps_fls_base_factor)
               (auto simp: complex_powr_of_int field_simps power_int_minus n_def)
        qed (use R in auto)
        hence "zor_poly f 0 0 = fps_nth G 0"
          by (simp add: eval_fps_at_0)
        thus ?thesis by simp
      qed
    qed
  qed (use r' in auto)
  finally show ?thesis
    by (simp add: G_def)
qed

lemma zorder_geI_0:
  assumes "f analytic_on {0}" "f holomorphic_on A" "open A" "connected A" "0 \<in> A" "z \<in> A" "f z \<noteq> 0"
  assumes "\<And>k. k < n \<Longrightarrow> (deriv ^^ k) f 0 = 0"
  shows   "zorder f 0 \<ge> n"
proof -
  define F where "F = fps_expansion f 0"
  from assms have "f has_fps_expansion F"
    unfolding F_def using analytic_at_imp_has_fps_expansion_0 by blast
  hence laurent: "f has_laurent_expansion fps_to_fls F" and [simp]: "f 0 = fps_nth F 0"
    by (simp_all add: has_fps_expansion_to_laurent)

  have [simp]: "F \<noteq> 0"
  proof
    assume [simp]: "F = 0"
    hence "f z = 0"
    proof (cases "z = 0")
      case False
      have "f has_laurent_expansion 0"
        using laurent by simp
      thus ?thesis
      proof (rule has_laurent_expansion_0_analytic_continuation)
        show "f holomorphic_on A - {0}"
          using assms(2) by (rule holomorphic_on_subset) auto
      qed (use assms False in auto)
    qed auto
    with \<open>f z \<noteq> 0\<close> show False by contradiction
  qed

  have "zorder f 0 = int (subdegree F)"
    using has_laurent_expansion_zorder_0[OF laurent] by (simp add: fls_subdegree_fls_to_fps)
  also have "subdegree F \<ge> n"
    using assms by (intro subdegree_geI \<open>F \<noteq> 0\<close>) (auto simp: F_def fps_expansion_def)
  hence "int (subdegree F) \<ge> int n"
    by simp
  finally show ?thesis .
qed

lemma zorder_geI:
  assumes "f analytic_on {x}" "f holomorphic_on A" "open A" "connected A" "x \<in> A" "z \<in> A" "f z \<noteq> 0"
  assumes "\<And>k. k < n \<Longrightarrow> (deriv ^^ k) f x = 0"
  shows   "zorder f x \<ge> n"
proof -
  have "zorder f x = zorder (f \<circ> (\<lambda>u. u + x)) 0"
    by (subst zorder_shift) (auto simp: o_def)
  also have "\<dots> \<ge> n"
  proof (rule zorder_geI_0)
    show "(f \<circ> (\<lambda>u. u + x)) analytic_on {0}"
      by (intro analytic_on_compose_gen[OF _ assms(1)] analytic_intros) auto
    show "f \<circ> (\<lambda>u. u + x) holomorphic_on ((+) (-x)) ` A"
      by (intro holomorphic_on_compose_gen[OF _ assms(2)] holomorphic_intros) auto
    show "connected ((+) (- x) ` A)"
      by (intro connected_continuous_image continuous_intros assms)
    show "open ((+) (- x) ` A)"
      by (intro open_translation assms)
    show "z - x \<in> (+) (- x) ` A"
      using \<open>z \<in> A\<close> by auto
    show "0 \<in> (+) (- x) ` A"
      using \<open>x \<in> A\<close> by auto
    show "(f \<circ> (\<lambda>u. u + x)) (z - x) \<noteq> 0"
      using \<open>f z \<noteq> 0\<close> by auto
  next
    fix k :: nat assume "k < n"
    hence "(deriv ^^ k) f x = 0"
      using assms by simp
    also have "(deriv ^^ k) f x = (deriv ^^ k) (f \<circ> (+) x) 0"
      by (subst higher_deriv_shift_0) auto
    finally show "(deriv ^^ k) (f \<circ> (\<lambda>u. u + x)) 0 = 0"
      by (subst add.commute) auto
  qed
  finally show ?thesis .
qed

lemma has_laurent_expansion_divide [laurent_expansion_intros]:
  assumes "f has_laurent_expansion F" and "g has_laurent_expansion G"
  shows   "(\<lambda>x. f x / g x) has_laurent_expansion (F / G)"
proof -
  have "(\<lambda>x. f x * inverse (g x)) has_laurent_expansion (F * inverse G)"
    by (intro laurent_expansion_intros assms)
  thus ?thesis
    by (simp add: field_simps)
qed

lemma vector_derivative_translate [simp]:
  "vector_derivative ((+) z \<circ> g) (at x within A) = vector_derivative g (at x within A)"
proof -
  have "(((+) z \<circ> g) has_vector_derivative g') (at x within A)"
    if "(g has_vector_derivative g') (at x within A)" for g :: "real \<Rightarrow> 'a" and z g'
    unfolding o_def using that by (auto intro!: derivative_eq_intros)
  from this[of g _ z] this[of "\<lambda>x. z + g x" _ "-z"] show ?thesis
    unfolding vector_derivative_def
    by (intro arg_cong[where f = Eps] ext) (auto simp: o_def algebra_simps)
qed

lemma has_contour_integral_translate:
  "(f has_contour_integral I) ((+) z \<circ> g) \<longleftrightarrow> ((\<lambda>x. f (x + z)) has_contour_integral I) g"
  by (simp add: has_contour_integral_def add_ac)

lemma contour_integrable_translate:
  "f contour_integrable_on ((+) z \<circ> g) \<longleftrightarrow> (\<lambda>x. f (x + z)) contour_integrable_on g"
  by (simp add: contour_integrable_on_def has_contour_integral_translate)

lemma contour_integral_translate:
  "contour_integral ((+) z \<circ> g) f = contour_integral g (\<lambda>x. f (x + z))"
  by (simp add: contour_integral_def contour_integrable_translate has_contour_integral_translate)

lemma residue_shift_0: "residue f z = residue (\<lambda>x. f (z + x)) 0"
proof -
  define Q where
    "Q = (\<lambda>r f z \<epsilon>. (f has_contour_integral complex_of_real (2 * pi) * \<i> * r) (circlepath z \<epsilon>))"
  define P where
    "P = (\<lambda>r f z. \<exists>e>0. \<forall>\<epsilon>>0. \<epsilon> < e \<longrightarrow> Q r f z \<epsilon>)"
  have path_eq: "circlepath (z - w) \<epsilon> = (+) (-w) \<circ> circlepath z \<epsilon>" for z w \<epsilon>
    by (simp add: circlepath_def o_def part_circlepath_def algebra_simps)
  have *: "P r f z" if "P r (\<lambda>x. f (x + w)) (z - w)" for r w f z
    using that by (auto simp: P_def Q_def path_eq has_contour_integral_translate)
  have "(SOME r. P r f z) = (SOME r. P r (\<lambda>x. f (z + x)) 0)"
    using *[of _ f z z] *[of _ "\<lambda>x. f (z + x)" "-z"]
    by (intro arg_cong[where f = Eps] ext iffI) (simp_all add: add_ac)
  thus ?thesis
    by (simp add: residue_def P_def Q_def)
qed

lemma residue_shift_0': "NO_MATCH 0 z \<Longrightarrow> residue f z = residue (\<lambda>x. f (z + x)) 0"
  by (rule residue_shift_0)

lemma has_laurent_expansion_residue_0:
  assumes "f has_laurent_expansion F"
  shows   "residue f 0 = fls_residue F"
proof (cases "fls_subdegree F \<ge> 0")
  case True
  have "residue f 0 = residue (eval_fls F) 0"
    using assms by (intro residue_cong) (auto simp: has_laurent_expansion_def eq_commute)
  also have "\<dots> = 0"
    by (rule residue_holo[OF _ _ holomorphic_on_eval_fls[OF order.refl]])
       (use True assms in \<open>auto simp: has_laurent_expansion_def zero_ereal_def\<close>)
  also have "\<dots> = fls_residue F"
    using True by simp
  finally show ?thesis .
next
  case False
  hence "F \<noteq> 0"
    by auto
  have *: "zor_poly f 0 has_fps_expansion fls_base_factor_to_fps F"
    by (intro zor_poly_has_fps_expansion False assms \<open>F \<noteq> 0\<close>)

  have "residue f 0 = (deriv ^^ (nat (-zorder f 0) - 1)) (zor_poly f 0) 0 / fact (nat (- zorder f 0) - 1)"
    by (intro residue_pole_order has_laurent_expansion_isolated_0[OF assms]
              has_laurent_expansion_imp_is_pole_0[OF assms]) (use False in auto)
  also have "\<dots> = fls_residue F"
    using has_laurent_expansion_zorder_0[OF assms \<open>F \<noteq> 0\<close>] False
    by (subst fps_nth_fps_expansion [OF *, symmetric]) (auto simp: of_nat_diff)
  finally show ?thesis .
qed

lemma has_laurent_expansion_residue:
  assumes "(\<lambda>x. f (z + x)) has_laurent_expansion F"
  shows   "residue f z = fls_residue F"
  using has_laurent_expansion_residue_0[OF assms] by (simp add: residue_shift_0')

lemma eval_fls_has_laurent_expansion [laurent_expansion_intros]:
  assumes "fls_conv_radius F > 0"
  shows   "eval_fls F has_laurent_expansion F"
  using assms by (auto simp: has_laurent_expansion_def)

lemma fps_expansion_unique_complex:
  fixes F G :: "complex fps"
  assumes "f has_fps_expansion F" "f has_fps_expansion G"
  shows   "F = G"
  using assms unfolding fps_eq_iff by (auto simp: fps_eq_iff fps_nth_fps_expansion)

lemma fps_expansion_eqI:
  assumes "f has_fps_expansion F"
  shows   "fps_expansion f 0 = F"
  using assms unfolding fps_eq_iff
  by (auto simp: fps_eq_iff fps_nth_fps_expansion fps_expansion_def)

lemma has_fps_expansion_imp_eval_fps_eq:
  assumes "f has_fps_expansion F" "norm z < r"
  assumes "f holomorphic_on ball 0 r"
  shows   "eval_fps F z = f z"
proof -
  have [simp]: "fps_expansion f 0 = F"
    by (rule fps_expansion_eqI) fact
  have *: "f holomorphic_on eball 0 (ereal r)"
    using assms by simp
  from conv_radius_fps_expansion[OF *] have "fps_conv_radius F \<ge> ereal r"
    by simp
  have "eval_fps (fps_expansion f 0) z = f (0 + z)"
    by (rule eval_fps_expansion'[OF *]) (use assms in auto)
  thus ?thesis
    by simp
qed

lemma fls_conv_radius_ge:
  assumes "f has_laurent_expansion F"
  assumes "f holomorphic_on eball 0 r - {0}"
  shows   "fls_conv_radius F \<ge> r"
proof -
  define n where "n = fls_subdegree F"
  define G where "G = fls_base_factor_to_fps F"
  define g where "g = (\<lambda>z. if z = 0 then fps_nth G 0 else f z * z powi -n)"
  have G: "g has_fps_expansion G"
    unfolding G_def g_def n_def
    by (intro has_fps_expansion_fls_base_factor_to_fps assms)
  have "(\<lambda>z. f z * z powi -n) holomorphic_on eball 0 r - {0}"
    by (intro holomorphic_intros assms) auto
  also have "?this \<longleftrightarrow> g holomorphic_on eball 0 r - {0}"
    by (intro holomorphic_cong) (auto simp: g_def)
  finally have "g analytic_on eball 0 r - {0}"
    by (subst analytic_on_open) auto
  moreover have "g analytic_on {0}"
    using G has_fps_expansion_imp_analytic_0 by auto
  ultimately have "g analytic_on (eball 0 r - {0} \<union> {0})"
    by (subst analytic_on_Un) auto
  hence "g analytic_on eball 0 r"
    by (rule analytic_on_subset) auto
  hence "g holomorphic_on eball 0 r"
    by (subst (asm) analytic_on_open) auto
  hence "fps_conv_radius (fps_expansion g 0) \<ge> r"
    by (intro conv_radius_fps_expansion)
  also have "fps_expansion g 0 = G"
    using G by (intro fps_expansion_eqI)
  finally show ?thesis
    by (simp add: fls_conv_radius_altdef G_def)
qed

lemma connected_eball [intro]: "connected (eball (z :: 'a :: real_normed_vector) r)"
  by (cases r) auto

lemma eval_fls_eqI:
  assumes "f has_laurent_expansion F" "f holomorphic_on eball 0 r - {0}"
  assumes "z \<in> eball 0 r - {0}"
  shows   "eval_fls F z = f z"
proof -
  have conv: "fls_conv_radius F \<ge> r"
    by (intro fls_conv_radius_ge[OF assms(1,2)])
  have "(\<lambda>z. eval_fls F z - f z) has_laurent_expansion F - F"
    using assms by (intro laurent_expansion_intros assms) (auto simp: has_laurent_expansion_def)
  hence "(\<lambda>z. eval_fls F z - f z) has_laurent_expansion 0"
    by simp
  hence "eval_fls F z - f z = 0"
  proof (rule has_laurent_expansion_0_analytic_continuation)
    have "ereal 0 \<le> ereal (norm z)"
      by simp
    also have "norm z < r"
      using assms by auto
    finally have "r > 0"
      by (simp add: zero_ereal_def)
    thus "open (eball 0 r :: complex set)" "connected (eball 0 r :: complex set)"
         "0 \<in> eball 0 r" "z \<in> eball 0 r - {0}"
      using assms by (auto simp: zero_ereal_def)
  qed (auto intro!: holomorphic_intros assms less_le_trans[OF _ conv] split: if_splits)
  thus ?thesis by simp
qed

lemma fls_nth_as_contour_integral:
  assumes F: "f has_laurent_expansion F"
  assumes holo: "f holomorphic_on ball 0 r - {0}"
  assumes R: "0 < R" "R < r"
  shows "((\<lambda>z. f z * z powi (-(n+1))) has_contour_integral
            complex_of_real (2 * pi) * \<i> * fls_nth F n) (circlepath 0 R)"
proof -
  define I where "I = (\<lambda>z. f z * z powi (-(n+1)))"
  have "(I has_contour_integral complex_of_real (2 * pi) * \<i> * residue I 0) (circlepath 0 R)"
  proof (rule base_residue)
    show "open (ball (0::complex) r)" "0 \<in> ball (0::complex) r"
      using R F by (auto simp: has_laurent_expansion_def zero_ereal_def)
  qed (use R in \<open>auto intro!: holomorphic_intros holomorphic_on_subset[OF holo]
                      simp: I_def split: if_splits\<close>)
  also have "residue I 0 = fls_residue (fls_shift (n + 1) F)"
    unfolding I_def by (intro has_laurent_expansion_residue_0 laurent_expansion_intros F)
  also have "\<dots> = fls_nth F n"
    by simp
  finally show ?thesis
    by (simp add: I_def)
qed

lemma tendsto_0_subdegree_iff_0:
  assumes F:"f has_laurent_expansion F" and "F\<noteq>0"
  shows "(f \<midarrow>0\<rightarrow>0) \<longleftrightarrow> fls_subdegree F > 0"
proof -
  have ?thesis if "is_pole f 0"
  proof -
    have "fls_subdegree F <0"
      using is_pole_0_imp_neg_fls_subdegree[OF F that] .
    moreover then have "\<not> f \<midarrow>0\<rightarrow>0"
      using \<open>is_pole f 0\<close> F at_neq_bot
        has_laurent_expansion_imp_filterlim_infinity_0
        not_tendsto_and_filterlim_at_infinity that
      by blast
    ultimately show ?thesis by auto
  qed
  moreover have ?thesis if "\<not>is_pole f 0" "\<exists>x. f \<midarrow>0\<rightarrow>x"
  proof -
    have "fls_subdegree F \<ge>0"
      using has_laurent_expansion_imp_is_pole_0[OF F] that(1)
      by linarith
    have "f \<midarrow>0\<rightarrow>0" if "fls_subdegree F > 0"
      using fls_eq0_below_subdegree[OF that]
      by (metis F \<open>0 \<le> fls_subdegree F\<close> has_laurent_expansion_imp_tendsto_0)
    moreover have "fls_subdegree F > 0" if "f \<midarrow>0\<rightarrow>0"
    proof -
      have False if "fls_subdegree F = 0"
      proof -
        have "f \<midarrow>0\<rightarrow> fls_nth F 0"
          using has_laurent_expansion_imp_tendsto_0
              [OF F \<open>fls_subdegree F \<ge>0\<close>] .
        then have "fls_nth F 0 = 0" using \<open>f \<midarrow>0\<rightarrow>0\<close>
          using LIM_unique by blast
        then have "F = 0"
          using nth_fls_subdegree_zero_iff \<open>fls_subdegree F = 0\<close>
          by metis
        with \<open>F\<noteq>0\<close> show False by auto
      qed
      with \<open>fls_subdegree F \<ge>0\<close>
      show ?thesis by fastforce
    qed
    ultimately show ?thesis by auto
  qed
  moreover have "is_pole f 0 \<or> (\<exists>x. f \<midarrow>0\<rightarrow>x)"
  proof -
    have "not_essential f 0"
      using F has_laurent_expansion_not_essential_0 by auto
    then show ?thesis unfolding not_essential_def
      by auto
  qed
  ultimately show ?thesis by auto
qed

lemma tendsto_0_subdegree_iff:
  assumes F:"(\<lambda>w. f (z+w)) has_laurent_expansion F" and "F\<noteq>0"
  shows "(f \<midarrow>z\<rightarrow>0) \<longleftrightarrow> fls_subdegree F > 0"
  apply (subst Lim_at_zero)
  apply (rule tendsto_0_subdegree_iff_0)
  using assms by auto

lemma is_pole_0_deriv_divide_iff:
  assumes F:"f has_laurent_expansion F" and "F\<noteq>0"
  shows "is_pole (\<lambda>x. deriv f x / f x) 0 \<longleftrightarrow> is_pole f 0 \<or> (f \<midarrow>0\<rightarrow>0)"
proof -
  have "(\<lambda>x. deriv f x / f x) has_laurent_expansion fls_deriv F / F"
    using F by (auto intro:laurent_expansion_intros)

  have "is_pole (\<lambda>x. deriv f x / f x) 0 \<longleftrightarrow>
            fls_subdegree (fls_deriv F / F) < 0"
    apply (rule is_pole_fls_subdegree_iff)
    using F by (auto intro:laurent_expansion_intros)
  also have "... \<longleftrightarrow> is_pole f 0 \<or> (f \<midarrow>0\<rightarrow>0)"
  proof (cases "fls_subdegree F = 0")
    case True
    then have "fls_subdegree (fls_deriv F / F) \<ge> 0"
      by (metis diff_zero div_0 \<open>F\<noteq>0\<close> fls_deriv_subdegree0
          fls_divide_subdegree)
    moreover then have "\<not> is_pole f 0"
      by (metis F True is_pole_0_imp_neg_fls_subdegree less_le)
    moreover have "\<not> (f \<midarrow>0\<rightarrow>0)"
      using tendsto_0_subdegree_iff_0[OF F \<open>F\<noteq>0\<close>] True by auto
    ultimately show ?thesis by auto
  next
    case False
    then have "fls_deriv F \<noteq> 0"
      by (metis fls_const_subdegree fls_deriv_eq_0_iff)
    then have "fls_subdegree (fls_deriv F / F) =
              fls_subdegree (fls_deriv F) - fls_subdegree F"
      by (rule fls_divide_subdegree[OF _ \<open>F\<noteq>0\<close>])
    moreover have "fls_subdegree (fls_deriv F) = fls_subdegree F - 1"
      using fls_subdegree_deriv[OF False] .
    ultimately have "fls_subdegree (fls_deriv F / F) < 0" by auto
    moreover have "f \<midarrow>0\<rightarrow> 0 = (0 < fls_subdegree F)"
      using tendsto_0_subdegree_iff_0[OF F \<open>F \<noteq> 0\<close>] .
    moreover have "is_pole f 0 = (fls_subdegree F < 0)"
      using is_pole_fls_subdegree_iff F by auto
    ultimately show ?thesis using False by auto
  qed
  finally show ?thesis .
qed

lemma is_pole_deriv_divide_iff:
  assumes F:"(\<lambda>w. f (z+w))  has_laurent_expansion F" and "F\<noteq>0"
  shows "is_pole (\<lambda>x. deriv f x / f x) z \<longleftrightarrow> is_pole f z \<or> (f \<midarrow>z\<rightarrow>0)"
proof -
  define ff df where "ff=(\<lambda>w. f (z+w))" and "df=(\<lambda>w. deriv f (z + w))"
  have "is_pole (\<lambda>x. deriv f x / f x) z
          \<longleftrightarrow> is_pole (\<lambda>x. deriv ff x / ff x) 0"
    unfolding ff_def df_def
    by (simp add:deriv_shift_0' is_pole_shift_0' comp_def algebra_simps)
  moreover have "is_pole f z \<longleftrightarrow> is_pole ff 0"
    unfolding ff_def by (auto simp:is_pole_shift_0')
  moreover have "(f \<midarrow>z\<rightarrow>0) \<longleftrightarrow> (ff \<midarrow>0\<rightarrow>0)"
    unfolding ff_def by (simp add: LIM_offset_zero_iff)
  moreover have "is_pole (\<lambda>x. deriv ff x / ff x) 0 = (is_pole ff 0 \<or> ff \<midarrow>0\<rightarrow> 0)"
    apply (rule is_pole_0_deriv_divide_iff)
    using F ff_def \<open>F\<noteq>0\<close> by blast+
  ultimately show ?thesis by auto
qed

lemma subdegree_imp_eventually_deriv_nzero_0:
  assumes F:"f has_laurent_expansion F" and "fls_subdegree F\<noteq>0"
  shows "eventually (\<lambda>z. deriv f z \<noteq> 0) (at 0)"
proof -
  have "deriv f has_laurent_expansion fls_deriv F"
    using has_laurent_expansion_deriv[OF F] .
  moreover have "fls_deriv F\<noteq>0"
    using \<open>fls_subdegree F\<noteq>0\<close>
    by (metis fls_const_subdegree fls_deriv_eq_0_iff)
  ultimately show ?thesis
    using has_laurent_expansion_eventually_nonzero_iff' by blast
qed

lemma subdegree_imp_eventually_deriv_nzero:
  assumes F:"(\<lambda>w. f (z+w)) has_laurent_expansion F"
      and "fls_subdegree F\<noteq>0"
  shows "eventually (\<lambda>w. deriv f w \<noteq> 0) (at z)"
proof -
  have "\<forall>\<^sub>F x in at 0. deriv (\<lambda>w. f (z + w)) x \<noteq> 0"
    using subdegree_imp_eventually_deriv_nzero_0 assms by auto
  then show ?thesis
    apply (subst eventually_at_to_0)
    by (simp add:deriv_shift_0' comp_def algebra_simps)
qed

lemma has_fps_expansion_imp_asymp_equiv_0:
  fixes f :: "complex \<Rightarrow> complex"
  assumes F: "f has_fps_expansion F"
  defines "n \<equiv> subdegree F"
  shows   "f \<sim>[nhds 0] (\<lambda>z. fps_nth F n * z ^ n)"
proof -
  have F': "f has_laurent_expansion fps_to_fls F"
    using F has_laurent_expansion_fps by blast

  have "f \<sim>[at 0] (\<lambda>z. fps_nth F n * z ^ n)"
    using has_laurent_expansion_imp_asymp_equiv_0[OF F']
    by (simp add: fls_subdegree_fls_to_fps n_def)
  moreover have "f 0 = fps_nth F n * 0 ^ n"
    using F by (auto simp: n_def has_fps_expansion_to_laurent power_0_left)
  ultimately show ?thesis
    by (auto simp: asymp_equiv_nhds_iff)
qed

lemma has_fps_expansion_imp_tendsto_0:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "f has_fps_expansion F"
  shows   "(f \<longlongrightarrow> fps_nth F 0) (nhds 0)"
proof (rule asymp_equiv_tendsto_transfer)
  show "(\<lambda>z. fps_nth F (subdegree F) * z ^ subdegree F) \<sim>[nhds 0] f"
    by (rule asymp_equiv_symI, rule has_fps_expansion_imp_asymp_equiv_0) fact
  have "((\<lambda>z. F $ subdegree F * z ^ subdegree F) \<longlongrightarrow> F $ 0) (at 0)"
    by (rule tendsto_eq_intros refl | simp)+ (auto simp: power_0_left)
  thus "((\<lambda>z. F $ subdegree F * z ^ subdegree F) \<longlongrightarrow> F $ 0) (nhds 0)"
    by (auto simp: tendsto_nhds_iff power_0_left)
qed

lemma has_fps_expansion_imp_0_eq_fps_nth_0:
  assumes "f has_fps_expansion F"
  shows   "f 0 = fps_nth F 0"
proof -
  have "eventually (\<lambda>x. f x = eval_fps F x) (nhds 0)"
    using assms by (auto simp: has_fps_expansion_def eq_commute)
  then obtain A where "open A" "0 \<in> A" "\<forall>x\<in>A. f x = eval_fps F x"
    unfolding eventually_nhds by blast
  hence "f 0 = eval_fps F 0"
    by blast
  thus ?thesis
    by (simp add: eval_fps_at_0)
qed

lemma fls_nth_compose_aux:
  assumes "f has_fps_expansion F"
  assumes G: "g has_fps_expansion G" "fps_nth G 0 = 0" "fps_deriv G \<noteq> 0"
  assumes "(f \<circ> g) has_laurent_expansion H"
  shows   "fls_nth H (int n) = fps_nth (fps_compose F G) n"
  using assms(1,5)
proof (induction n arbitrary: f F H rule: less_induct)
  case (less n f F H)
  have [simp]: "g 0 = 0"
    using has_fps_expansion_imp_0_eq_fps_nth_0[OF G(1)] G(2) by simp
  have ana_f: "f analytic_on {0}"
    using less.prems by (meson has_fps_expansion_imp_analytic_0)
  have ana_g: "g analytic_on {0}"
    using G by (meson has_fps_expansion_imp_analytic_0)
  have "(f \<circ> g) has_laurent_expansion fps_to_fls (fps_expansion (f \<circ> g) 0)"
    by (rule analytic_at_imp_has_fps_expansion_0 analytic_intros has_laurent_expansion_fps
             analytic_on_compose_gen ana_f ana_g)+ auto
  with less.prems have "H = fps_to_fls (fps_expansion (f \<circ> g) 0)"
    using has_laurent_expansion_unique by blast
  also have "fls_subdegree \<dots> \<ge> 0"
    by (simp add: fls_subdegree_fls_to_fps)
  finally have subdeg: "fls_subdegree H \<ge> 0" .

  show ?case
  proof (cases "n = 0")
    case [simp]: True
    have lim_g: "g \<midarrow>0\<rightarrow> 0"
      using has_laurent_expansion_imp_tendsto_0[of g "fps_to_fls G"] G
      by (auto simp: fls_subdegree_fls_to_fps_gt0 has_fps_expansion_to_laurent)
    have lim_f: "(f \<longlongrightarrow> fps_nth F 0) (nhds 0)"
      by (intro has_fps_expansion_imp_tendsto_0 less.prems)
    have "(\<lambda>x. f (g x)) \<midarrow>0\<rightarrow> fps_nth F 0"
      by (rule filterlim_compose[OF lim_f lim_g])
    moreover have "(f \<circ> g) \<midarrow>0\<rightarrow> fls_nth H 0"
      by (intro has_laurent_expansion_imp_tendsto_0 less.prems subdeg)
    ultimately have "fps_nth F 0 = fls_nth H 0"
      using tendsto_unique by (force simp: o_def)
    thus ?thesis
      by simp
  next
    case n: False
    define GH where "GH = (fls_deriv H / fls_deriv (fps_to_fls G))"
    define GH' where "GH' = fls_regpart GH"

    have "(\<lambda>x. deriv (f \<circ> g) x / deriv g x) has_laurent_expansion
          fls_deriv H / fls_deriv (fps_to_fls G)"
      by (intro laurent_expansion_intros less.prems has_laurent_expansion_fps[of _ G] G)
    also have "?this \<longleftrightarrow> (deriv f \<circ> g) has_laurent_expansion fls_deriv H / fls_deriv (fps_to_fls G)"
    proof (rule has_laurent_expansion_cong)
      from ana_f obtain r1 where r1: "r1 > 0" "f holomorphic_on ball 0 r1"
        unfolding analytic_on_def by blast
      from ana_g obtain r2 where r2: "r2 > 0" "g holomorphic_on ball 0 r2"
        unfolding analytic_on_def by blast
      have lim_g: "g \<midarrow>0\<rightarrow> 0"
        using has_laurent_expansion_imp_tendsto_0[of g "fps_to_fls G"] G
        by (auto simp: fls_subdegree_fls_to_fps_gt0 has_fps_expansion_to_laurent)
      moreover have "open (ball 0 r1)" "0 \<in> ball 0 r1"
        using r1 by auto
      ultimately have "eventually (\<lambda>x. g x \<in> ball 0 r1) (at 0)"
        unfolding tendsto_def by blast
      moreover have "eventually (\<lambda>x. deriv g x \<noteq> 0) (at 0)"
        using G fps_to_fls_eq_0_iff has_fps_expansion_deriv has_fps_expansion_to_laurent
              has_laurent_expansion_nonzero_imp_eventually_nonzero by blast
      moreover have "eventually (\<lambda>x. x \<in> ball 0 (min r1 r2) - {0}) (at 0)"
        by (intro eventually_at_in_open) (use r1 r2 in auto)
      ultimately show "eventually (\<lambda>x. deriv (f \<circ> g) x / deriv g x = (deriv f \<circ> g) x) (at 0)"
      proof eventually_elim
        case (elim x)
        thus ?case using r1 r2
          by (subst deriv_chain)
             (auto simp: field_simps holomorphic_on_def at_within_open[of _ "ball _ _"])
      qed
    qed auto
    finally have GH: "(deriv f \<circ> g) has_laurent_expansion GH"
      unfolding GH_def .

    have "(deriv f \<circ> g) has_laurent_expansion fps_to_fls (fps_expansion (deriv f \<circ> g) 0)"
      by (rule analytic_at_imp_has_fps_expansion_0 analytic_intros has_laurent_expansion_fps
               analytic_on_compose_gen ana_f ana_g)+ auto
    with GH have "GH = fps_to_fls (fps_expansion (deriv f \<circ> g) 0)"
      using has_laurent_expansion_unique by blast
    also have "fls_subdegree \<dots> \<ge> 0"
      by (simp add: fls_subdegree_fls_to_fps)
    finally have subdeg': "fls_subdegree GH \<ge> 0" .

    have "deriv f has_fps_expansion fps_deriv F"
      by (intro fps_expansion_intros less.prems)
    from this and GH have IH: "fls_nth GH (int k) = fps_nth (fps_compose (fps_deriv F) G) k"
      if "k < n" for k
      by (intro less.IH that)

    have "fps_nth (fps_compose (fps_deriv F) G) n = (\<Sum>i=0..n. of_nat (Suc i) * F $ Suc i * G ^ i $ n)"
      by (simp add: fps_compose_nth)

    have "fps_nth (fps_compose F G) n =
            fps_nth (fps_deriv (fps_compose F G)) (n - 1) / of_nat n"
      using n by (cases n) (auto simp del: of_nat_Suc)
    also have "fps_deriv (fps_compose F G) = fps_compose (fps_deriv F) G * fps_deriv G "
      using G by (subst fps_compose_deriv) auto
    also have "fps_nth \<dots> (n - 1) = (\<Sum>i=0..n-1. (fps_deriv F oo G) $ i * fps_deriv G $ (n - 1 - i))"
      unfolding fps_mult_nth ..
    also have "\<dots> = (\<Sum>i=0..n-1. fps_nth GH' i * of_nat (n - i) * G $ (n - i))"
      using n by (intro sum.cong) (auto simp: IH Suc_diff_Suc GH'_def)
    also have "\<dots> = (\<Sum>i=0..n. fps_nth GH' i * of_nat (n - i) * G $ (n - i))"
      by (intro sum.mono_neutral_left) auto
    also have "\<dots> = fps_nth (GH' * Abs_fps (\<lambda>i. of_nat i * fps_nth G i)) n"
      by (simp add: fps_mult_nth mult_ac)
    also have "Abs_fps (\<lambda>i. of_nat i * fps_nth G i) = fps_X * fps_deriv G"
      by (simp add: fps_mult_fps_X_deriv_shift)
    also have "fps_nth (GH' * (fps_X * fps_deriv G)) n =
               fls_nth (fps_to_fls (GH' * (fps_X * fps_deriv G))) (int n)"
      by simp
    also have "fps_to_fls (GH' * (fps_X * fps_deriv G)) =
                 GH * fps_to_fls (fps_deriv G) * fls_X"
      using subdeg' by (simp add: mult_ac fls_times_fps_to_fls GH'_def)
    also have "GH * fps_to_fls (fps_deriv G) = fls_deriv H"
      unfolding GH_def using G  by (simp add: fls_deriv_fps_to_fls)
    also have "fls_deriv H * fls_X = fls_shift (-1) (fls_deriv H)"
      using fls_X_times_conv_shift(2) by blast
    finally show ?thesis
      using n by simp
  qed
qed

lemma has_fps_expansion_compose [fps_expansion_intros]:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes F: "f has_fps_expansion F"
  assumes G: "g has_fps_expansion G" "fps_nth G 0 = 0"
  shows   "(f \<circ> g) has_fps_expansion fps_compose F G"
proof (cases "fps_deriv G = 0")
  case False
  have [simp]: "g 0 = 0"
    using has_fps_expansion_imp_0_eq_fps_nth_0[OF G(1)] G(2) False by simp
  have ana_f: "f analytic_on {0}"
    using F by (meson has_fps_expansion_imp_analytic_0)
  have ana_g: "g analytic_on {0}"
    using G by (meson has_fps_expansion_imp_analytic_0)
  have fg: "(f \<circ> g) has_fps_expansion fps_expansion (f \<circ> g) 0"
    by (rule analytic_at_imp_has_fps_expansion_0 analytic_intros
         analytic_on_compose_gen ana_f ana_g)+ auto

  have "fls_nth (fps_to_fls (fps_expansion (f \<circ> g) 0)) (int n) = fps_nth (fps_compose F G) n" for n
    by (rule fls_nth_compose_aux has_laurent_expansion_fps F G False fg)+
  hence "fps_expansion (f \<circ> g) 0 = fps_compose F G"
    by (simp add: fps_eq_iff)
  thus ?thesis using fg
    by simp
next
  case True
  have [simp]: "f 0 = fps_nth F 0"
    using F by (auto dest: has_fps_expansion_imp_0_eq_fps_nth_0)
  from True have "fps_nth G n = 0" for n
    using G(2) by (cases n) (auto simp del: of_nat_Suc)
  hence [simp]: "G = 0"
    by (auto simp: fps_eq_iff)
  have "(\<lambda>_. f 0) has_fps_expansion fps_const (f 0)"
    by (intro fps_expansion_intros)
  also have "eventually (\<lambda>x. g x = 0) (nhds 0)"
    using G by (auto simp: has_fps_expansion_def)
  hence "(\<lambda>_. f 0) has_fps_expansion fps_const (f 0) \<longleftrightarrow> (f \<circ> g) has_fps_expansion fps_const (f 0)"
    by (intro has_fps_expansion_cong) (auto elim!: eventually_mono)
  thus ?thesis
    by simp
qed

hide_const (open) fls_compose_fps

definition fls_compose_fps :: "'a :: field fls \<Rightarrow> 'a fps \<Rightarrow> 'a fls" where
  "fls_compose_fps F G =
     fps_to_fls (fps_compose (fls_base_factor_to_fps F) G) * fps_to_fls G powi fls_subdegree F"

lemma fps_compose_of_nat [simp]: "fps_compose (of_nat n :: 'a :: comm_ring_1 fps) H = of_nat n"
  and fps_compose_of_int [simp]: "fps_compose (of_int i) H = of_int i"
  unfolding fps_of_nat [symmetric] fps_of_int [symmetric] numeral_fps_const
  by (rule fps_const_compose)+

lemmas [simp] = fps_to_fls_of_nat fps_to_fls_of_int

lemma fls_compose_fps_0 [simp]: "fls_compose_fps 0 H = 0"
  and fls_compose_fps_1 [simp]: "fls_compose_fps 1 H = 1"
  and fls_compose_fps_const [simp]: "fls_compose_fps (fls_const c) H = fls_const c"
  and fls_compose_fps_of_nat [simp]: "fls_compose_fps (of_nat n) H = of_nat n"
  and fls_compose_fps_of_int [simp]: "fls_compose_fps (of_int i) H = of_int i"
  and fls_compose_fps_X [simp]: "fls_compose_fps fls_X F = fps_to_fls F"
  by (simp_all add: fls_compose_fps_def)

lemma fls_compose_fps_0_right:
  "fls_compose_fps F 0 = (if fls_subdegree F \<ge> 0 then fls_const (fls_nth F 0) else 0)"
  by (cases "fls_subdegree F = 0") (simp_all add: fls_compose_fps_def)

lemma fls_compose_fps_shift:
  assumes "H \<noteq> 0"
  shows   "fls_compose_fps (fls_shift n F) H = fls_compose_fps F H * fps_to_fls H powi (-n)"
proof (cases "F = 0")
  case False
  thus ?thesis
    using assms by (simp add: fls_compose_fps_def power_int_diff power_int_minus field_simps)
qed auto

lemma fls_compose_fps_to_fls [simp]:
  assumes [simp]: "G \<noteq> 0" "fps_nth G 0 = 0"
  shows   "fls_compose_fps (fps_to_fls F) G = fps_to_fls (fps_compose F G)"
proof (cases "F = 0")
  case False
  define n where "n = subdegree F"
  define F' where "F' = fps_shift n F"
  have [simp]: "F' \<noteq> 0" "subdegree F' = 0"
    using False by (auto simp: F'_def n_def)
  have F_eq: "F = F' * fps_X ^ n"
    unfolding F'_def n_def using subdegree_decompose by blast
  have "fls_compose_fps (fps_to_fls F) G =
          fps_to_fls (fps_shift n (fls_regpart (fps_to_fls F' * fls_X_intpow (int n))) oo G) * fps_to_fls (G ^ n)"
    unfolding F_eq fls_compose_fps_def
    by (simp add: fls_times_fps_to_fls fls_X_power_conv_shift_1 power_int_add
                  fls_subdegree_fls_to_fps fps_to_fls_power fls_regpart_shift_conv_fps_shift
             flip: fls_times_both_shifted_simp)
  also have "fps_to_fls F' * fls_X_intpow (int n) = fps_to_fls F"
    by (simp add: F_eq fls_times_fps_to_fls fps_to_fls_power fls_X_power_conv_shift_1)
  also have "fps_to_fls (fps_shift n (fls_regpart (fps_to_fls F)) oo G) * fps_to_fls (G ^ n) =
             fps_to_fls ((fps_shift n (fls_regpart (fps_to_fls F)) * fps_X ^ n) oo G)"
    by (simp add: fls_times_fps_to_fls flip: fps_compose_power add: fps_compose_mult_distrib)
  also have "fps_shift n (fls_regpart (fps_to_fls F)) * fps_X ^ n = F"
    by (simp add: F_eq)
  finally show ?thesis .
qed (auto simp: fls_compose_fps_def)

lemma fls_compose_fps_mult:
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (F * G) H = fls_compose_fps F H * fls_compose_fps G H"
  using assms
proof (cases "F * G = 0")
  case False
  hence [simp]: "F \<noteq> 0" "G \<noteq> 0"
    by auto
  define n m where "n = fls_subdegree F" "m = fls_subdegree G"
  define F' where "F' = fls_regpart (fls_shift n F)"
  define G' where "G' = fls_regpart (fls_shift m G)"
  have F_eq: "F = fls_shift (-n) (fps_to_fls F')" and G_eq: "G = fls_shift (-m) (fps_to_fls G')"
    by (simp_all add: F'_def G'_def n_m_def)
  have "fls_compose_fps (F * G) H = fls_compose_fps (fls_shift (-(n + m)) (fps_to_fls (F' * G'))) H"
    by (simp add: fls_times_fps_to_fls F_eq G_eq fls_shifted_times_simps)
  also have "\<dots> = fps_to_fls ((F' oo H) * (G' oo H)) * fps_to_fls H powi (m + n)"
    by (simp add: fls_compose_fps_shift fps_compose_mult_distrib)
  also have "\<dots> = fls_compose_fps F H * fls_compose_fps G H"
    by (simp add: F_eq G_eq fls_compose_fps_shift fls_times_fps_to_fls power_int_add)
  finally show ?thesis .
qed auto

lemma fls_compose_fps_power:
  assumes [simp]: "G \<noteq> 0" "fps_nth G 0 = 0"
  shows   "fls_compose_fps (F ^ n) G = fls_compose_fps F G ^ n"
  by (induction n) (auto simp: fls_compose_fps_mult)

lemma fls_compose_fps_add:
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (F + G) H = fls_compose_fps F H + fls_compose_fps G H"
proof (cases "F = 0 \<or> G = 0")
  case False
  hence [simp]: "F \<noteq> 0" "G \<noteq> 0"
    by auto
  define n where "n = min (fls_subdegree F) (fls_subdegree G)"
  define F' where "F' = fls_regpart (fls_shift n F)"
  define G' where "G' = fls_regpart (fls_shift n G)"
  have F_eq: "F = fls_shift (-n) (fps_to_fls F')" and G_eq: "G = fls_shift (-n) (fps_to_fls G')"
    unfolding n_def by (simp_all add: F'_def G'_def n_def)
  have "F + G = fls_shift (-n) (fps_to_fls (F' + G'))"
    by (simp add: F_eq G_eq)
  also have "fls_compose_fps \<dots> H = fls_compose_fps (fps_to_fls (F' + G')) H * fps_to_fls H powi n"
    by (subst fls_compose_fps_shift) auto
  also have "\<dots> = fps_to_fls (fps_compose (F' + G') H) * fps_to_fls H powi n"
    by (subst fls_compose_fps_to_fls) auto
  also have "\<dots> = fls_compose_fps F H + fls_compose_fps G H"
    by (simp add: F_eq G_eq fls_compose_fps_shift fps_compose_add_distrib algebra_simps)
  finally show ?thesis .
qed auto

lemma fls_compose_fps_uminus [simp]: "fls_compose_fps (-F) H = -fls_compose_fps F H"
  by (simp add: fls_compose_fps_def fps_compose_uminus)

lemma fls_compose_fps_diff:
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (F - G) H = fls_compose_fps F H - fls_compose_fps G H"
  using fls_compose_fps_add[of H F "-G"] by simp

lemma fps_compose_eq_0_iff:
  fixes F G :: "'a :: idom fps"
  assumes "fps_nth G 0 = 0"
  shows "fps_compose F G = 0 \<longleftrightarrow> F = 0 \<or> (G = 0 \<and> fps_nth F 0 = 0)"
proof safe
  assume *: "fps_compose F G = 0" "F \<noteq> 0"
  have "fps_nth (fps_compose F G) 0 = fps_nth F 0"
    by simp
  also have "fps_compose F G = 0"
    by (simp add: *)
  finally show "fps_nth F 0 = 0"
    by simp
  show "G = 0"
  proof (rule ccontr)
    assume "G \<noteq> 0"
    hence "subdegree G > 0" using assms
      using subdegree_eq_0_iff by blast
    define N where "N = subdegree F * subdegree G"
    have "fps_nth (fps_compose F G) N = (\<Sum>i = 0..N. fps_nth F i * fps_nth (G ^ i) N)"
      unfolding fps_compose_def by (simp add: N_def)
    also have "\<dots> = (\<Sum>i\<in>{subdegree F}. fps_nth F i * fps_nth (G ^ i) N)"
    proof (intro sum.mono_neutral_right ballI)
      fix i assume i: "i \<in> {0..N} - {subdegree F}"
      show "fps_nth F i * fps_nth (G ^ i) N = 0"
      proof (cases i "subdegree F" rule: linorder_cases)
        assume "i > subdegree F"
        hence "fps_nth (G ^ i) N = 0"
          using i \<open>subdegree G > 0\<close> by (intro fps_pow_nth_below_subdegree) (auto simp: N_def)
        thus ?thesis by simp
      qed (use i in \<open>auto simp: N_def\<close>)
    qed (use \<open>subdegree G > 0\<close> in \<open>auto simp: N_def\<close>)
    also have "\<dots> = fps_nth F (subdegree F) * fps_nth (G ^ subdegree F) N"
      by simp
    also have "\<dots> \<noteq> 0"
      using \<open>G \<noteq> 0\<close> \<open>F \<noteq> 0\<close> by (auto simp: N_def)
    finally show False using * by auto
  qed
qed auto

lemma fls_compose_fps_eq_0_iff:
  assumes "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps F H = 0 \<longleftrightarrow> F = 0"
  using assms fls_base_factor_to_fps_nonzero[of F]
  by (cases "F = 0") (auto simp: fls_compose_fps_def fps_compose_eq_0_iff)

lemma fls_compose_fps_inverse:
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (inverse F) H = inverse (fls_compose_fps F H)"
proof (cases "F = 0")
  case False
  have "fls_compose_fps (inverse F) H * fls_compose_fps F H =
        fls_compose_fps (inverse F * F) H"
    by (subst fls_compose_fps_mult) auto
  also have "inverse F * F = 1"
    using False by simp
  finally show ?thesis
    using False by (simp add: field_simps fls_compose_fps_eq_0_iff)
qed auto

lemma fls_compose_fps_divide:
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (F / G) H = fls_compose_fps F H / fls_compose_fps G H"
  using fls_compose_fps_mult[of H F "inverse G"] fls_compose_fps_inverse[of H G]
  by (simp add: field_simps)

lemma fls_compose_fps_powi:
  assumes [simp]: "H \<noteq> 0" "fps_nth H 0 = 0"
  shows   "fls_compose_fps (F powi n) H = fls_compose_fps F H powi n"
  by (simp add: power_int_def fls_compose_fps_power fls_compose_fps_inverse)

lemma fls_compose_fps_assoc:
  assumes [simp]: "G \<noteq> 0" "fps_nth G 0 = 0" "H \<noteq> 0" "fps_nth H 0 = 0"
  shows "fls_compose_fps (fls_compose_fps F G) H = fls_compose_fps F (fps_compose G H)"
proof (cases "F = 0")
  case [simp]: False
  define n where "n = fls_subdegree F"
  define F' where "F' = fls_regpart (fls_shift n F)"
  have F_eq: "F = fls_shift (-n) (fps_to_fls F')"
    by (simp add: F'_def n_def)
  show ?thesis
    by (simp add: F_eq fls_compose_fps_shift fls_compose_fps_mult fls_compose_fps_powi
                  fps_compose_eq_0_iff fps_compose_assoc)
qed auto

lemma subdegree_pos_iff: "subdegree F > 0 \<longleftrightarrow> F \<noteq> 0 \<and> fps_nth F 0 = 0"
  using subdegree_eq_0_iff[of F] by auto

lemma has_fps_expansion_fps_to_fls:
  assumes "f has_laurent_expansion fps_to_fls F"
  shows   "(\<lambda>z. if z = 0 then fps_nth F 0 else f z) has_fps_expansion F"
  (is "?f' has_fps_expansion _")
proof -
  have "f has_laurent_expansion fps_to_fls F \<longleftrightarrow> ?f' has_laurent_expansion fps_to_fls F"
    by (intro has_laurent_expansion_cong) (auto simp: eventually_at_filter)
  with assms show ?thesis
    by (auto simp: has_fps_expansion_to_laurent)
qed


lemma has_laurent_expansion_compose [laurent_expansion_intros]:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes F: "f has_laurent_expansion F"
  assumes G: "g has_laurent_expansion fps_to_fls G" "fps_nth G 0 = 0" "G \<noteq> 0"
  shows   "(f \<circ> g) has_laurent_expansion fls_compose_fps F G"
proof -
  from assms have lim_g: "g \<midarrow>0\<rightarrow> 0"
    by (subst tendsto_0_subdegree_iff_0[OF G(1)])
       (auto simp: fls_subdegree_fls_to_fps subdegree_pos_iff)
  have ev1: "eventually (\<lambda>z. g z \<noteq> 0) (at 0)"
    using \<open>G \<noteq> 0\<close> G(1) fps_to_fls_eq_0_iff has_laurent_expansion_fps
           has_laurent_expansion_nonzero_imp_eventually_nonzero by blast
  moreover have "eventually (\<lambda>z. z \<noteq> 0) (at (0 :: complex))"
    by (auto simp: eventually_at_filter)
  ultimately have ev: "eventually (\<lambda>z. z \<noteq> 0 \<and> g z \<noteq> 0) (at 0)"
    by eventually_elim blast
  from ev1 and lim_g have lim_g': "filterlim g (at 0) (at 0)"
    by (auto simp: filterlim_at)
  define g' where "g' = (\<lambda>z. if z = 0 then fps_nth G 0 else g z)"

  show ?thesis
  proof (cases "F = 0")
    assume [simp]: "F = 0"
    have "eventually (\<lambda>z. f z = 0) (at 0)"
      using F by (auto simp: has_laurent_expansion_def)
    hence "eventually (\<lambda>z. f (g z) = 0) (at 0)"
      using lim_g' by (rule eventually_compose_filterlim)
    thus ?thesis
      by (auto simp: has_laurent_expansion_def)
  next
    assume [simp]: "F \<noteq> 0"
    define n where "n = fls_subdegree F"
    define f' where
      "f' = (\<lambda>z. if z = 0 then fps_nth (fls_base_factor_to_fps F) 0 else f z * z powi -n)"
    have "((\<lambda>z. (f' \<circ> g') z * g z powi n)) has_laurent_expansion fls_compose_fps F G"
      unfolding f'_def n_def fls_compose_fps_def g'_def
      by (intro fps_expansion_intros laurent_expansion_intros has_fps_expansion_fps_to_fls
                has_fps_expansion_fls_base_factor_to_fps assms has_laurent_expansion_fps)
    also have "?this \<longleftrightarrow> ?thesis"
      by (intro has_laurent_expansion_cong eventually_mono[OF ev])
         (auto simp: f'_def power_int_minus g'_def)
    finally show ?thesis .
  qed
qed

lemma has_laurent_expansion_fls_X_inv [laurent_expansion_intros]:
  "inverse has_laurent_expansion fls_X_inv"
  using has_laurent_expansion_inverse[OF has_laurent_expansion_fps_X]
  by (simp add: fls_inverse_X)

lemma fls_X_power_int [simp]: "fls_X powi n = (fls_X_intpow n :: 'a :: division_ring fls)"
  by (auto simp: power_int_def fls_X_power_conv_shift_1 fls_inverse_X fls_inverse_shift
           simp flip: fls_inverse_X_power)

lemma fls_const_power_int: "fls_const (c powi n) = fls_const (c :: 'a :: division_ring) powi n"
  by (auto simp: power_int_def fls_const_power fls_inverse_const)

lemma fls_nth_fls_compose_fps_linear:
  fixes c :: "'a :: field"
  assumes [simp]: "c \<noteq> 0"
  shows "fls_nth (fls_compose_fps F (fps_const c * fps_X)) n = fls_nth F n * c powi n"
proof -
  {
    assume *: "n \<ge> fls_subdegree F"
    hence "c ^ nat (n - fls_subdegree F) = c powi int (nat (n - fls_subdegree F))"
      by (simp add: power_int_def)
    also have "\<dots> * c powi fls_subdegree F = c powi (int (nat (n - fls_subdegree F)) + fls_subdegree F)"
      using * by (subst power_int_add) auto
    also have "\<dots> = c powi n"
      using * by simp
    finally have "c ^ nat (n - fls_subdegree F) * c powi fls_subdegree F = c powi n" .
  }
  thus ?thesis
    by (simp add: fls_compose_fps_def fps_compose_linear fls_times_fps_to_fls power_int_mult_distrib
                  fls_shifted_times_simps
             flip: fls_const_power_int)
qed

lemma zorder_times_analytic:
  assumes "f analytic_on {z}" "g analytic_on {z}"
  assumes "eventually (\<lambda>z. f z * g z \<noteq> 0) (at z)"
  shows   "zorder (\<lambda>z. f z * g z) z = zorder f z + zorder g z"
proof -
  have *: "(\<lambda>w. f (z + w)) has_fps_expansion fps_expansion f z"
          "(\<lambda>w. g (z + w)) has_fps_expansion fps_expansion g z"
          "(\<lambda>w. f (z + w) * g (z + w)) has_fps_expansion fps_expansion f z * fps_expansion g z"
    by (intro fps_expansion_intros analytic_at_imp_has_fps_expansion assms)+
  have [simp]: "fps_expansion f z \<noteq> 0"
  proof
    assume "fps_expansion f z = 0"
    hence "eventually (\<lambda>z. f z * g z = 0) (at z)" using *(1)
      by (auto simp: has_fps_expansion_0_iff nhds_to_0' eventually_filtermap eventually_at_filter
               elim: eventually_mono)
    with assms(3) have "eventually (\<lambda>z. False) (at z)"
      by eventually_elim auto
    thus False by simp
  qed
  have [simp]: "fps_expansion g z \<noteq> 0"
  proof
    assume "fps_expansion g z = 0"
    hence "eventually (\<lambda>z. f z * g z = 0) (at z)" using *(2)
      by (auto simp: has_fps_expansion_0_iff nhds_to_0' eventually_filtermap eventually_at_filter
               elim: eventually_mono)
    with assms(3) have "eventually (\<lambda>z. False) (at z)"
      by eventually_elim auto
    thus False by simp
  qed
  from *[THEN has_fps_expansion_zorder] show ?thesis
    by auto
qed

lemma zorder_const [simp]: "c \<noteq> 0 \<Longrightarrow> zorder (\<lambda>_. c) z = 0"
  by (intro zorder_eqI[where S = UNIV]) auto

lemma zorder_prod_analytic:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x analytic_on {z}"
  assumes "eventually (\<lambda>z. (\<Prod>x\<in>A. f x z) \<noteq> 0) (at z)"
  shows   "zorder (\<lambda>z. \<Prod>x\<in>A. f x z) z = (\<Sum>x\<in>A. zorder (f x) z)"
  using assms
proof (induction A rule: infinite_finite_induct)
  case (insert x A)
  have "zorder (\<lambda>z. f x z * (\<Prod>x\<in>A. f x z)) z = zorder (f x) z + zorder (\<lambda>z. \<Prod>x\<in>A. f x z) z"
    using insert.prems insert.hyps by (intro zorder_times_analytic analytic_intros) auto
  also have "zorder (\<lambda>z. \<Prod>x\<in>A. f x z) z = (\<Sum>x\<in>A. zorder (f x) z)"
    using insert.prems insert.hyps by (intro insert.IH) (auto elim!: eventually_mono)
  finally show ?case using insert
    by simp
qed auto

lemma zorder_eq_0I:
  assumes "g analytic_on {z}" "g z \<noteq> 0"
  shows   "zorder g z = 0"
  using analytic_at assms zorder_eqI by fastforce

lemma zorder_pos_iff:
  assumes "f holomorphic_on A" "open A" "z \<in> A" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  shows   "zorder f z > 0 \<longleftrightarrow> f z = 0"
proof -
  have "f analytic_on {z}"
    using assms analytic_at by blast
  hence *: "(\<lambda>w. f (z + w)) has_fps_expansion fps_expansion f z"
    using analytic_at_imp_has_fps_expansion by blast
  have nz: "fps_expansion f z \<noteq> 0"
  proof
    assume "fps_expansion f z = 0"
    hence "eventually (\<lambda>z. f z = 0) (nhds z)"
      using * by (auto simp: has_fps_expansion_def nhds_to_0' eventually_filtermap add_ac)
    hence "eventually (\<lambda>z. f z = 0) (at z)"
      by (auto simp: eventually_at_filter elim: eventually_mono)
    with assms show False
      by (auto simp: frequently_def)
  qed
  from has_fps_expansion_zorder[OF * this] have eq: "zorder f z = int (subdegree (fps_expansion f z))"
    by auto
  moreover have "subdegree (fps_expansion f z) = 0 \<longleftrightarrow> fps_nth (fps_expansion f z) 0 \<noteq> 0"
    using nz by (auto simp: subdegree_eq_0_iff)
  moreover have "fps_nth (fps_expansion f z) 0 = f z"
    by (auto simp: fps_expansion_def)
  ultimately show ?thesis
    by auto
qed

lemma zorder_pos_iff':
  assumes "f analytic_on {z}" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  shows   "zorder f z > 0 \<longleftrightarrow> f z = 0"
  using analytic_at assms zorder_pos_iff by blast

lemma zorder_ge_0:
  assumes "f analytic_on {z}" "frequently (\<lambda>z. f z \<noteq> 0) (at z)"
  shows   "zorder f z \<ge> 0"
proof -
  have *: "(\<lambda>w. f (z + w)) has_laurent_expansion fps_to_fls (fps_expansion f z)"
    using assms by (simp add: analytic_at_imp_has_fps_expansion has_laurent_expansion_fps)
  from * assms(2) have "fps_to_fls (fps_expansion f z) \<noteq> 0"
    by (auto simp: has_laurent_expansion_def frequently_def at_to_0' eventually_filtermap add_ac)
  with has_laurent_expansion_zorder[OF *] show ?thesis
    by (simp add: fls_subdegree_fls_to_fps)
qed

lemma zorder_eq_0_iff:
  assumes "f analytic_on {z}" "frequently (\<lambda>w. f w \<noteq> 0) (at z)"
  shows   "zorder f z = 0 \<longleftrightarrow> f z \<noteq> 0"
  using assms zorder_eq_0I zorder_pos_iff' by fastforce

lemma dist_mult_left:
  "dist (a * b) (a * c :: 'a :: real_normed_field) = norm a * dist b c"
  unfolding dist_norm right_diff_distrib [symmetric] norm_mult by simp

lemma dist_mult_right:
  "dist (b * a) (c * a :: 'a :: real_normed_field) = norm a * dist b c"
  using dist_mult_left[of a b c] by (simp add: mult_ac)

lemma zorder_scale:
  assumes "f analytic_on {a * z}" "eventually (\<lambda>w. f w \<noteq> 0) (at (a * z))" "a \<noteq> 0"
  shows "zorder (\<lambda>w. f (a * w)) z = zorder f (a * z)"
proof -
  from assms(1) obtain r where r: "r > 0" "f holomorphic_on ball (a * z) r"
    by (auto simp: analytic_on_def)
  have *: "open (ball (a * z) r)" "connected (ball (a * z) r)" "a * z \<in> ball (a * z) r"
    using r \<open>a \<noteq> 0\<close> by (auto simp: dist_norm)
  from assms(2) have "eventually (\<lambda>w. f w \<noteq> 0 \<and> w \<in> ball (a * z) r - {a * z}) (at (a * z))"
    using \<open>r > 0\<close> by (intro eventually_conj eventually_at_in_open) auto
  then obtain z0 where "f z0 \<noteq> 0 \<and> z0 \<in> ball (a * z) r - {a * z}"
    using eventually_happens[of _ "at (a * z)"] by force
  hence **: "\<exists>w\<in>ball (a * z) r. f w \<noteq> 0"
    by blast

  define n where "n = nat (zorder f (a * z))"
  obtain r' where r':
     "(if f (a * z) = 0 then 0 < zorder f (a * z) else zorder f (a * z) = 0)"
     "r' > 0" "cball (a * z) r' \<subseteq> ball (a * z) r" "zor_poly f (a * z) holomorphic_on cball (a * z) r'"
     "\<And>w. w \<in> cball (a * z) r' \<Longrightarrow>
        f w = zor_poly f (a * z) w * (w - a * z) ^ n \<and> zor_poly f (a * z) w \<noteq> 0"
    unfolding n_def using zorder_exist_zero[OF r(2) * **] by blast

  show ?thesis
  proof (rule zorder_eqI)
    show "open (ball z (r' / norm a))" "z \<in> ball z (r' / norm a)"
      using r \<open>r' > 0\<close> \<open>a \<noteq> 0\<close> by auto
    have "(*) a ` ball z (r' / cmod a) \<subseteq> cball (a * z) r'"
    proof safe
      fix w assume "w \<in> ball z (r' / cmod a)"
      thus "a * w \<in> cball (a * z) r'"
        using dist_mult_left[of a z w] \<open>a \<noteq> 0\<close> by (auto simp: divide_simps mult_ac)
    qed
    thus "(\<lambda>w. a ^ n * (zor_poly f (a * z) \<circ> (\<lambda>w. a * w)) w) holomorphic_on ball z (r' / norm a)"
      using \<open>a \<noteq> 0\<close> by (intro holomorphic_on_compose_gen[OF _ r'(4)] holomorphic_intros) auto
    show "a ^ n * (zor_poly f (a * z) \<circ> (\<lambda>w. a * w)) z \<noteq> 0"
      using r' \<open>a \<noteq> 0\<close> by auto
    show "f (a * w) = a ^ n * (zor_poly f (a * z) \<circ> (*) a) w * (w - z) powi (zorder f (a * z))"
      if "w \<in> ball z (r' / norm a)" "w \<noteq> z" for w
    proof -
      have "f (a * w) = zor_poly f (a * z) (a * w) * (a * (w - z)) ^ n"
        using that r'(5)[of "a * w"] dist_mult_left[of a z w] \<open>a \<noteq> 0\<close> unfolding ring_distribs
        by (auto simp: divide_simps mult_ac)
      also have "\<dots> = a ^ n * zor_poly f (a * z) (a * w) * (w - z) ^ n"
        by (subst power_mult_distrib) (auto simp: mult_ac)
      also have "(w - z) ^ n = (w - z) powi of_nat n"
        by simp
      also have "of_nat n = zorder f (a * z)"
        using r'(1) by (auto simp: n_def split: if_splits)
      finally show ?thesis
        unfolding o_def n_def .
    qed
  qed
qed

lemma subdegree_fps_compose [simp]:
  fixes F G :: "'a :: idom fps"
  assumes [simp]: "fps_nth G 0 = 0"
  shows "subdegree (fps_compose F G) = subdegree F * subdegree G"
proof (cases "G = 0"; cases "F = 0")
  assume [simp]: "G \<noteq> 0" "F \<noteq> 0"
  define m where "m = subdegree F"
  define F' where "F' = fps_shift m F"
  have F_eq: "F = F' * fps_X ^ m"
    unfolding F'_def by (simp add: fps_shift_times_fps_X_power m_def)
  have [simp]: "F' \<noteq> 0"
    using \<open>F \<noteq> 0\<close> unfolding F_eq by auto
  have "subdegree (fps_compose F G) = subdegree (fps_compose F' G) + m * subdegree G"
    by (simp add: F_eq fps_compose_mult_distrib fps_compose_eq_0_iff flip: fps_compose_power)
  also have "subdegree (fps_compose F' G) = 0"
    by (intro subdegree_eq_0) (auto simp: F'_def m_def)
  finally show ?thesis by (simp add: m_def)
qed auto

lemma fls_subdegree_power_int [simp]:
  fixes   F :: "'a :: field fls"
  shows "fls_subdegree (F powi n) = n * fls_subdegree F"
  by (auto simp: power_int_def fls_subdegree_pow)

lemma subdegree_fls_compose_fps [simp]:
  fixes G :: "'a :: field fps"
  assumes [simp]: "fps_nth G 0 = 0"
  shows "fls_subdegree (fls_compose_fps F G) = fls_subdegree F * subdegree G"
proof (cases "F = 0"; cases "G = 0")
  assume [simp]: "G \<noteq> 0" "F \<noteq> 0"
  have nz1: "fls_base_factor_to_fps F \<noteq> 0"
    using \<open>F \<noteq> 0\<close> fls_base_factor_to_fps_nonzero by blast
  show ?thesis
    unfolding fls_compose_fps_def using nz1
    by (subst fls_subdegree_mult) (simp_all add: fps_compose_eq_0_iff fls_subdegree_fls_to_fps)
qed (auto simp: fls_compose_fps_0_right)

lemma zorder_compose_aux:
  assumes "isolated_singularity_at f 0" "not_essential f 0"
  assumes G: "g has_fps_expansion G" "G \<noteq> 0" "g 0 = 0"
  assumes "eventually (\<lambda>w. f w \<noteq> 0) (at 0)"
  shows   "zorder (f \<circ> g) 0 = zorder f 0 * subdegree G"
proof -
  obtain F where F: "f has_laurent_expansion F"
    using not_essential_has_laurent_expansion_0[OF assms(1,2)] by blast
  have [simp]: "fps_nth G 0 = 0"
   using G \<open>g 0 = 0\<close> by (simp add: has_fps_expansion_imp_0_eq_fps_nth_0)
  note [simp] = \<open>G \<noteq> 0\<close> \<open>g 0 = 0\<close>
  have [simp]: "F \<noteq> 0"
    using has_laurent_expansion_eventually_nonzero_iff[of f 0 F] F assms by simp
  have FG: "(f \<circ> g) has_laurent_expansion fls_compose_fps F G"
    by (intro has_laurent_expansion_compose has_laurent_expansion_fps F G) auto

  have "zorder (f \<circ> g) 0 = fls_subdegree (fls_compose_fps F G)"
    using has_laurent_expansion_zorder_0 [OF FG] by (auto simp: fls_compose_fps_eq_0_iff)
  also have "\<dots> = fls_subdegree F * int (subdegree G)"
    by simp
  also have "fls_subdegree F = zorder f 0"
    using has_laurent_expansion_zorder_0 [OF F] by auto
  finally show ?thesis .
qed

lemma zorder_compose:
  assumes "isolated_singularity_at f (g z)" "not_essential f (g z)"
  assumes G: "(\<lambda>x. g (z + x) - g z) has_fps_expansion G" "G \<noteq> 0"
  assumes "eventually (\<lambda>w. f w \<noteq> 0) (at (g z))"
  shows   "zorder (f \<circ> g) z = zorder f (g z) * subdegree G"
proof -
  define f' where "f' = (\<lambda>w. f (g z + w))"
  define g' where "g' = (\<lambda>w. g (z + w) - g z)"
  have "zorder f (g z) = zorder f' 0"
    by (simp add: f'_def zorder_shift' add_ac)
  have "zorder (\<lambda>x. g x - g z) z = zorder g' 0"
    by (simp add: g'_def zorder_shift' add_ac)
  have "zorder (f \<circ> g) z = zorder (f' \<circ> g') 0"
    by (simp add: zorder_shift' f'_def g'_def add_ac o_def)
  also have "\<dots> = zorder f' 0 * int (subdegree G)"
  proof (rule zorder_compose_aux)
    show "isolated_singularity_at f' 0" unfolding f'_def
      using assms has_laurent_expansion_isolated_0 not_essential_has_laurent_expansion by blast
    show "not_essential f' 0" unfolding f'_def
      using assms has_laurent_expansion_not_essential_0 not_essential_has_laurent_expansion by blast
  qed (use assms in \<open>auto simp: f'_def g'_def at_to_0' eventually_filtermap add_ac\<close>)
  also have "zorder f' 0 = zorder f (g z)"
    by (simp add: f'_def zorder_shift' add_ac)
  finally show ?thesis .
qed

lemma fps_to_fls_eq_fls_const_iff [simp]: "fps_to_fls F = fls_const c \<longleftrightarrow> F = fps_const c"
  using fps_to_fls_eq_iff by fastforce

lemma zorder_compose':
  assumes "isolated_singularity_at f (g z)" "not_essential f (g z)"
  assumes "g analytic_on {z}"
  assumes "eventually (\<lambda>w. f w \<noteq> 0) (at (g z))"
  assumes "eventually (\<lambda>w. g w \<noteq> g z) (at z)"
  shows   "zorder (f \<circ> g) z = zorder f (g z) * zorder (\<lambda>x. g x - g z) z"
proof -
  obtain G where G [fps_expansion_intros]: "(\<lambda>x. g (z + x)) has_fps_expansion G"
    using assms analytic_at_imp_has_fps_expansion by blast
  have G': "(\<lambda>x. g (z + x) - g z) has_fps_expansion G - fps_const (g z)"
    by (intro fps_expansion_intros)
  hence G'': "(\<lambda>x. g (z + x) - g z) has_laurent_expansion fps_to_fls (G - fps_const (g z))"
    using has_laurent_expansion_fps by blast
  have nz: "G - fps_const (g z) \<noteq> 0"
    using has_laurent_expansion_eventually_nonzero_iff[OF G''] assms by auto
  have "zorder (f \<circ> g) z = zorder f (g z) * subdegree (G - fps_const (g z))"
  proof (rule zorder_compose)
    show "(\<lambda>x. g (z + x) - g z) has_fps_expansion G - fps_const (g z)"
      by (intro fps_expansion_intros)
  qed (use assms nz in auto)
  also have "int (subdegree (G - fps_const (g z))) = fls_subdegree (fps_to_fls G - fls_const (g z))"
    by (simp flip: fls_subdegree_fls_to_fps)
  also have "\<dots> = zorder (\<lambda>x. g x - g z) z"
    using has_laurent_expansion_zorder [OF G''] nz by auto
  finally show ?thesis .
qed

lemma analytic_at_cong:
  assumes "eventually (\<lambda>x. f x = g x) (nhds x)" "x = y"
  shows "f analytic_on {x} \<longleftrightarrow> g analytic_on {y}"
proof -
  have "g analytic_on {x}" if "f analytic_on {x}" "eventually (\<lambda>x. f x = g x) (nhds x)" for f g
  proof -
    have "(\<lambda>y. f (x + y)) has_fps_expansion fps_expansion f x"
      by (rule analytic_at_imp_has_fps_expansion) fact
    also have "?this \<longleftrightarrow> (\<lambda>y. g (x + y)) has_fps_expansion fps_expansion f x"
      using that by (intro has_fps_expansion_cong refl) (auto simp: nhds_to_0' eventually_filtermap)
    finally show ?thesis
      by (rule has_fps_expansion_imp_analytic)
  qed
  from this[of f g] this[of g f] show ?thesis using assms
    by (auto simp: eq_commute)
qed


lemma has_laurent_expansion_sin' [laurent_expansion_intros]:
  "sin has_laurent_expansion fps_to_fls (fps_sin 1)"
  using has_fps_expansion_sin' has_fps_expansion_to_laurent by blast

lemma has_laurent_expansion_cos' [laurent_expansion_intros]:
  "cos has_laurent_expansion fps_to_fls (fps_cos 1)"
  using has_fps_expansion_cos' has_fps_expansion_to_laurent by blast

lemma has_laurent_expansion_sin [laurent_expansion_intros]:
  "(\<lambda>z. sin (c * z)) has_laurent_expansion fps_to_fls (fps_sin c)"
  by (intro has_laurent_expansion_fps has_fps_expansion_sin)

lemma has_laurent_expansion_cos [laurent_expansion_intros]:
  "(\<lambda>z. cos (c * z)) has_laurent_expansion fps_to_fls (fps_cos c)"
  by (intro has_laurent_expansion_fps has_fps_expansion_cos)

lemma has_laurent_expansion_tan' [laurent_expansion_intros]:
  "tan has_laurent_expansion fps_to_fls (fps_tan 1)"
  using has_fps_expansion_tan' has_fps_expansion_to_laurent by blast

lemma has_laurent_expansion_tan [laurent_expansion_intros]:
  "(\<lambda>z. tan (c * z)) has_laurent_expansion fps_to_fls (fps_tan c)"
  by (intro has_laurent_expansion_fps has_fps_expansion_tan)

end
