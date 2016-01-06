(*  Title:      HOL/Probability/Lebesgue_Integral_Substitution.thy
    Author:     Manuel Eberl

    Provides lemmas for integration by substitution for the basic integral types.
    Note that the substitution function must have a nonnegative derivative.
    This could probably be weakened somehow.
*)

section \<open>Integration by Substition\<close>

theory Lebesgue_Integral_Substitution
imports Interval_Integral
begin

lemma nn_integral_substitution_aux:
  fixes f :: "real \<Rightarrow> ereal"
  assumes Mf: "f \<in> borel_measurable borel"
  assumes nonnegf: "\<And>x. f x \<ge> 0"
  assumes derivg: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' x) (at x)"
  assumes contg': "continuous_on {a..b} g'" 
  assumes derivg_nonneg: "\<And>x. x \<in> {a..b} \<Longrightarrow> g' x \<ge> 0"
  assumes "a < b"
  shows "(\<integral>\<^sup>+x. f x * indicator {g a..g b} x \<partial>lborel) = 
             (\<integral>\<^sup>+x. f (g x) * g' x * indicator {a..b} x \<partial>lborel)"
proof-
  from \<open>a < b\<close> have [simp]: "a \<le> b" by simp
  from derivg have contg: "continuous_on {a..b} g" by (rule has_real_derivative_imp_continuous_on)
  from this and contg' have Mg: "set_borel_measurable borel {a..b} g" and 
                             Mg': "set_borel_measurable borel {a..b} g'" 
      by (simp_all only: set_measurable_continuous_on_ivl)
  from derivg have derivg': "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_vector_derivative g' x) (at x)"
    by (simp only: has_field_derivative_iff_has_vector_derivative)

  have real_ind[simp]: "\<And>A x. real_of_ereal (indicator A x :: ereal) = indicator A x" 
      by (auto split: split_indicator)
  have ereal_ind[simp]: "\<And>A x. ereal (indicator A x) = indicator A x" 
      by (auto split: split_indicator)
  have [simp]: "\<And>x A. indicator A (g x) = indicator (g -` A) x" 
      by (auto split: split_indicator)

  from derivg derivg_nonneg have monog: "\<And>x y. a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> b \<Longrightarrow> g x \<le> g y"
    by (rule deriv_nonneg_imp_mono) simp_all
  with monog have [simp]: "g a \<le> g b" by (auto intro: mono_onD)

  show ?thesis
  proof (induction rule: borel_measurable_induct[OF Mf nonnegf, case_names cong set mult add sup])
    case (cong f1 f2)
    from cong.hyps(3) have "f1 = f2" by auto
    with cong show ?case by simp
  next
    case (set A)
    from set.hyps show ?case
    proof (induction rule: borel_set_induct)
      case empty
      thus ?case by simp
    next
      case (interval c d)
      {
        fix u v :: real assume asm: "{u..v} \<subseteq> {g a..g b}" "u \<le> v"
        
        obtain u' v' where u'v': "{a..b} \<inter> g-`{u..v} = {u'..v'}" "u' \<le> v'" "g u' = u" "g v' = v"
             using asm by (rule_tac continuous_interval_vimage_Int[OF contg monog, of u v]) simp_all
        hence "{u'..v'} \<subseteq> {a..b}" "{u'..v'} \<subseteq> g -` {u..v}" by blast+
        with u'v'(2) have "u' \<in> g -` {u..v}" "v' \<in> g -` {u..v}" by auto
        from u'v'(1) have [simp]: "{a..b} \<inter> g -` {u..v} \<in> sets borel" by simp
        
        have A: "continuous_on {min u' v'..max u' v'} g'"
            by (simp only: u'v' max_absorb2 min_absorb1) 
               (intro continuous_on_subset[OF contg'], insert u'v', auto)
        have "\<And>x. x \<in> {u'..v'} \<Longrightarrow> (g has_real_derivative g' x) (at x within {u'..v'})"
           using asm by (intro has_field_derivative_subset[OF derivg] set_mp[OF \<open>{u'..v'} \<subseteq> {a..b}\<close>]) auto
        hence B: "\<And>x. min u' v' \<le> x \<Longrightarrow> x \<le> max u' v' \<Longrightarrow> 
                      (g has_vector_derivative g' x) (at x within {min u' v'..max u' v'})" 
            by (simp only: u'v' max_absorb2 min_absorb1) 
               (auto simp: has_field_derivative_iff_has_vector_derivative)
        have "integrable lborel (\<lambda>x. indicator ({a..b} \<inter> g -` {u..v}) x *\<^sub>R g' x)"
          by (rule set_integrable_subset[OF borel_integrable_atLeastAtMost'[OF contg']]) simp_all
        hence "(\<integral>\<^sup>+x. ereal (g' x) * indicator ({a..b} \<inter> g-` {u..v}) x \<partial>lborel) = 
                   LBINT x:{a..b} \<inter> g-`{u..v}. g' x" 
          by (subst ereal_ind[symmetric], subst times_ereal.simps, subst nn_integral_eq_integral)
             (auto intro: measurable_sets Mg simp: derivg_nonneg mult.commute split: split_indicator)
        also from interval_integral_FTC_finite[OF A B]
            have "LBINT x:{a..b} \<inter> g-`{u..v}. g' x = v - u"
                by (simp add: u'v' interval_integral_Icc \<open>u \<le> v\<close>)
        finally have "(\<integral>\<^sup>+ x. ereal (g' x) * indicator ({a..b} \<inter> g -` {u..v}) x \<partial>lborel) =
                           ereal (v - u)" .
      } note A = this
  
      have "(\<integral>\<^sup>+x. indicator {c..d} (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel) =
               (\<integral>\<^sup>+ x. ereal (g' x) * indicator ({a..b} \<inter> g -` {c..d}) x \<partial>lborel)" 
        by (intro nn_integral_cong) (simp split: split_indicator)
      also have "{a..b} \<inter> g-`{c..d} = {a..b} \<inter> g-`{max (g a) c..min (g b) d}" 
        using \<open>a \<le> b\<close> \<open>c \<le> d\<close>
        by (auto intro!: monog intro: order.trans)
      also have "(\<integral>\<^sup>+ x. ereal (g' x) * indicator ... x \<partial>lborel) =
        (if max (g a) c \<le> min (g b) d then min (g b) d - max (g a) c else 0)"
         using \<open>c \<le> d\<close> by (simp add: A)
      also have "... = (\<integral>\<^sup>+ x. indicator ({g a..g b} \<inter> {c..d}) x \<partial>lborel)"
        by (subst nn_integral_indicator) (auto intro!: measurable_sets Mg simp:)
      also have "... = (\<integral>\<^sup>+ x. indicator {c..d} x * indicator {g a..g b} x \<partial>lborel)"
        by (intro nn_integral_cong) (auto split: split_indicator)
      finally show ?case ..

      next

      case (compl A)
      note \<open>A \<in> sets borel\<close>[measurable]
      from emeasure_mono[of "A \<inter> {g a..g b}" "{g a..g b}" lborel]
          have [simp]: "emeasure lborel (A \<inter> {g a..g b}) \<noteq> \<infinity>" by auto
      have [simp]: "g -` A \<inter> {a..b} \<in> sets borel"
        by (rule set_borel_measurable_sets[OF Mg]) auto
      have [simp]: "g -` (-A) \<inter> {a..b} \<in> sets borel"
        by (rule set_borel_measurable_sets[OF Mg]) auto

      have "(\<integral>\<^sup>+x. indicator (-A) x * indicator {g a..g b} x \<partial>lborel) = 
                (\<integral>\<^sup>+x. indicator (-A \<inter> {g a..g b}) x \<partial>lborel)" 
        by (rule nn_integral_cong) (simp split: split_indicator)
      also from compl have "... = emeasure lborel ({g a..g b} - A)" using derivg_nonneg
        by (simp add: vimage_Compl diff_eq Int_commute[of "-A"])
      also have "{g a..g b} - A = {g a..g b} - A \<inter> {g a..g b}" by blast
      also have "emeasure lborel ... = g b - g a - emeasure lborel (A \<inter> {g a..g b})"
             using \<open>A \<in> sets borel\<close> by (subst emeasure_Diff) (auto simp: real_of_ereal_minus)
     also have "emeasure lborel (A \<inter> {g a..g b}) = 
                    \<integral>\<^sup>+x. indicator A x * indicator {g a..g b} x \<partial>lborel" 
       using \<open>A \<in> sets borel\<close>
       by (subst nn_integral_indicator[symmetric], simp, intro nn_integral_cong)
          (simp split: split_indicator)
      also have "... = \<integral>\<^sup>+ x. indicator (g-`A \<inter> {a..b}) x * ereal (g' x * indicator {a..b} x) \<partial>lborel" (is "_ = ?I")
        by (subst compl.IH, intro nn_integral_cong) (simp split: split_indicator)
      also have "g b - g a = LBINT x:{a..b}. g' x" using derivg'
        by (intro integral_FTC_atLeastAtMost[symmetric])
           (auto intro: continuous_on_subset[OF contg'] has_field_derivative_subset[OF derivg]
                 has_vector_derivative_at_within)
      also have "ereal ... = \<integral>\<^sup>+ x. g' x * indicator {a..b} x \<partial>lborel"
        using borel_integrable_atLeastAtMost'[OF contg']
        by (subst nn_integral_eq_integral)
           (simp_all add: mult.commute derivg_nonneg split: split_indicator)
      also have Mg'': "(\<lambda>x. indicator (g -` A \<inter> {a..b}) x * ereal (g' x * indicator {a..b} x))
                            \<in> borel_measurable borel" using Mg'
        by (intro borel_measurable_ereal_times borel_measurable_indicator)
           (simp_all add: mult.commute)
      have le: "(\<integral>\<^sup>+x. indicator (g-`A \<inter> {a..b}) x * ereal (g' x * indicator {a..b} x) \<partial>lborel) \<le>
                        (\<integral>\<^sup>+x. ereal (g' x) * indicator {a..b} x \<partial>lborel)"
         by (intro nn_integral_mono) (simp split: split_indicator add: derivg_nonneg)
      note integrable = borel_integrable_atLeastAtMost'[OF contg']
      with le have notinf: "(\<integral>\<^sup>+x. indicator (g-`A \<inter> {a..b}) x * ereal (g' x * indicator {a..b} x) \<partial>lborel) \<noteq> \<infinity>"
          by (auto simp: real_integrable_def nn_integral_set_ereal mult.commute)
      have "(\<integral>\<^sup>+ x. g' x * indicator {a..b} x \<partial>lborel) - ?I = 
                  \<integral>\<^sup>+ x. ereal (g' x * indicator {a..b} x) - 
                        indicator (g -` A \<inter> {a..b}) x * ereal (g' x * indicator {a..b} x) \<partial>lborel"
        apply (intro nn_integral_diff[symmetric])
        apply (insert Mg', simp add: mult.commute) []
        apply (insert Mg'', simp) []
        apply (simp split: split_indicator add: derivg_nonneg)
        apply (rule notinf)
        apply (simp split: split_indicator add: derivg_nonneg)
        done
      also have "... = \<integral>\<^sup>+ x. indicator (-A) (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel"
        by (intro nn_integral_cong) (simp split: split_indicator)
      finally show ?case .

    next
      case (union f)
      then have [simp]: "\<And>i. {a..b} \<inter> g -` f i \<in> sets borel"
        by (subst Int_commute, intro set_borel_measurable_sets[OF Mg]) auto
      have "g -` (\<Union>i. f i) \<inter> {a..b} = (\<Union>i. {a..b} \<inter> g -` f i)" by auto
      hence "g -` (\<Union>i. f i) \<inter> {a..b} \<in> sets borel" by (auto simp del: UN_simps)

      have "(\<integral>\<^sup>+x. indicator (\<Union>i. f i) x * indicator {g a..g b} x \<partial>lborel) = 
                \<integral>\<^sup>+x. indicator (\<Union>i. {g a..g b} \<inter> f i) x \<partial>lborel"
          by (intro nn_integral_cong) (simp split: split_indicator)
      also from union have "... = emeasure lborel (\<Union>i. {g a..g b} \<inter> f i)" by simp
      also from union have "... = (\<Sum>i. emeasure lborel ({g a..g b} \<inter> f i))"
        by (intro suminf_emeasure[symmetric]) (auto simp: disjoint_family_on_def)
      also from union have "... = (\<Sum>i. \<integral>\<^sup>+x. indicator ({g a..g b} \<inter> f i) x \<partial>lborel)" by simp
      also have "(\<lambda>i. \<integral>\<^sup>+x. indicator ({g a..g b} \<inter> f i) x \<partial>lborel) = 
                           (\<lambda>i. \<integral>\<^sup>+x. indicator (f i) x * indicator {g a..g b} x \<partial>lborel)"
        by (intro ext nn_integral_cong) (simp split: split_indicator)
      also from union.IH have "(\<Sum>i. \<integral>\<^sup>+x. indicator (f i) x * indicator {g a..g b} x \<partial>lborel) = 
          (\<Sum>i. \<integral>\<^sup>+ x. indicator (f i) (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel)" by simp
      also have "(\<lambda>i. \<integral>\<^sup>+ x. indicator (f i) (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel) =
                         (\<lambda>i. \<integral>\<^sup>+ x. ereal (g' x * indicator {a..b} x) * indicator ({a..b} \<inter> g -` f i) x \<partial>lborel)"
        by (intro ext nn_integral_cong) (simp split: split_indicator)
      also have "(\<Sum>i. ... i) = \<integral>\<^sup>+ x. (\<Sum>i. ereal (g' x * indicator {a..b} x) * indicator ({a..b} \<inter> g -` f i) x) \<partial>lborel"
        using Mg'
        apply (intro nn_integral_suminf[symmetric])
        apply (rule borel_measurable_ereal_times, simp add: borel_measurable_ereal mult.commute)
        apply (rule borel_measurable_indicator, subst sets_lborel)
        apply (simp_all split: split_indicator add: derivg_nonneg)
        done
      also have "(\<lambda>x i. ereal (g' x * indicator {a..b} x) * indicator ({a..b} \<inter> g -` f i) x) =
                      (\<lambda>x i. ereal (g' x * indicator {a..b} x) * indicator (g -` f i) x)"
        by (intro ext) (simp split: split_indicator)
      also have "(\<integral>\<^sup>+ x. (\<Sum>i. ereal (g' x * indicator {a..b} x) * indicator (g -` f i) x) \<partial>lborel) =
                     \<integral>\<^sup>+ x. ereal (g' x * indicator {a..b} x) * (\<Sum>i. indicator (g -` f i) x) \<partial>lborel"
        by (intro nn_integral_cong suminf_cmult_ereal) (auto split: split_indicator simp: derivg_nonneg)
      also from union have "(\<lambda>x. \<Sum>i. indicator (g -` f i) x :: ereal) = (\<lambda>x. indicator (\<Union>i. g -` f i) x)"
        by (intro ext suminf_indicator) (auto simp: disjoint_family_on_def)
      also have "(\<integral>\<^sup>+x. ereal (g' x * indicator {a..b} x) * ... x \<partial>lborel) =
                    (\<integral>\<^sup>+x. indicator (\<Union>i. f i) (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel)"
       by (intro nn_integral_cong) (simp split: split_indicator)
      finally show ?case .
  qed

next
  case (mult f c)
    note Mf[measurable] = \<open>f \<in> borel_measurable borel\<close>
    let ?I = "indicator {a..b}"
    have "(\<lambda>x. f (g x * ?I x) * ereal (g' x * ?I x)) \<in> borel_measurable borel" using Mg Mg'
      by (intro borel_measurable_ereal_times measurable_compose[OF _ Mf])
         (simp_all add: borel_measurable_ereal mult.commute)
    also have "(\<lambda>x. f (g x * ?I x) * ereal (g' x * ?I x)) = (\<lambda>x. f (g x) * ereal (g' x) * ?I x)"
      by (intro ext) (simp split: split_indicator)
    finally have Mf': "(\<lambda>x. f (g x) * ereal (g' x) * ?I x) \<in> borel_measurable borel" .
    with mult show ?case
      by (subst (1 2 3) mult_ac, subst (1 2) nn_integral_cmult) (simp_all add: mult_ac)
 
next
  case (add f2 f1)
    let ?I = "indicator {a..b}"
    {
      fix f :: "real \<Rightarrow> ereal" assume Mf: "f \<in> borel_measurable borel"
      have "(\<lambda>x. f (g x * ?I x) * ereal (g' x * ?I x)) \<in> borel_measurable borel" using Mg Mg'
        by (intro borel_measurable_ereal_times measurable_compose[OF _ Mf])
           (simp_all add: borel_measurable_ereal mult.commute)
      also have "(\<lambda>x. f (g x * ?I x) * ereal (g' x * ?I x)) = (\<lambda>x. f (g x) * ereal (g' x) * ?I x)"
        by (intro ext) (simp split: split_indicator)
      finally have "(\<lambda>x. f (g x) * ereal (g' x) * ?I x) \<in> borel_measurable borel" .
    } note Mf' = this[OF \<open>f1 \<in> borel_measurable borel\<close>] this[OF \<open>f2 \<in> borel_measurable borel\<close>]
    from add have not_neginf: "\<And>x. f1 x \<noteq> -\<infinity>" "\<And>x. f2 x \<noteq> -\<infinity>" 
      by (metis Infty_neq_0(1) ereal_0_le_uminus_iff ereal_infty_less_eq(1))+

    have "(\<integral>\<^sup>+ x. (f1 x + f2 x) * indicator {g a..g b} x \<partial>lborel) =
             (\<integral>\<^sup>+ x. f1 x * indicator {g a..g b} x + f2 x * indicator {g a..g b} x \<partial>lborel)"
      by (intro nn_integral_cong) (simp split: split_indicator)
    also from add have "... = (\<integral>\<^sup>+ x. f1 (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel) +
                                (\<integral>\<^sup>+ x. f2 (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel)"
      by (simp_all add: nn_integral_add)
    also from add have "... = (\<integral>\<^sup>+ x. f1 (g x) * ereal (g' x) * indicator {a..b} x + 
                                      f2 (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel)"
      by (intro nn_integral_add[symmetric])
         (auto simp add: Mf' derivg_nonneg split: split_indicator)
    also from not_neginf have "... = \<integral>\<^sup>+ x. (f1 (g x) + f2 (g x)) * ereal (g' x) * indicator {a..b} x \<partial>lborel"
      by (intro nn_integral_cong) (simp split: split_indicator add: ereal_distrib)
    finally show ?case .

next
  case (sup F)
  {
    fix i
    let ?I = "indicator {a..b}"
    have "(\<lambda>x. F i (g x * ?I x) * ereal (g' x * ?I x)) \<in> borel_measurable borel" using Mg Mg'
      by (rule_tac borel_measurable_ereal_times, rule_tac measurable_compose[OF _ sup.hyps(1)])
         (simp_all add: mult.commute)
    also have "(\<lambda>x. F i (g x * ?I x) * ereal (g' x * ?I x)) = (\<lambda>x. F i (g x) * ereal (g' x) * ?I x)"
      by (intro ext) (simp split: split_indicator)
     finally have "... \<in> borel_measurable borel" .
  } note Mf' = this

    have "(\<integral>\<^sup>+x. (SUP i. F i x) * indicator {g a..g b} x \<partial>lborel) = 
               \<integral>\<^sup>+x. (SUP i. F i x* indicator {g a..g b} x) \<partial>lborel"
      by (intro nn_integral_cong) (simp split: split_indicator)
    also from sup have "... = (SUP i. \<integral>\<^sup>+x. F i x* indicator {g a..g b} x \<partial>lborel)"
      by (intro nn_integral_monotone_convergence_SUP)
         (auto simp: incseq_def le_fun_def split: split_indicator)
    also from sup have "... = (SUP i. \<integral>\<^sup>+x. F i (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel)"
      by simp
    also from sup have "... =  \<integral>\<^sup>+x. (SUP i. F i (g x) * ereal (g' x) * indicator {a..b} x) \<partial>lborel"
      by (intro nn_integral_monotone_convergence_SUP[symmetric])
         (auto simp: incseq_def le_fun_def derivg_nonneg Mf' split: split_indicator
               intro!: ereal_mult_right_mono)
    also from sup have "... = \<integral>\<^sup>+x. (SUP i. F i (g x)) * ereal (g' x) * indicator {a..b} x \<partial>lborel"
      by (subst mult.assoc, subst mult.commute, subst SUP_ereal_mult_left)
         (auto split: split_indicator simp: derivg_nonneg mult_ac)
    finally show ?case by simp
  qed
qed

lemma nn_integral_substitution:
  fixes f :: "real \<Rightarrow> real"
  assumes Mf[measurable]: "set_borel_measurable borel {g a..g b} f"
  assumes derivg: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' x) (at x)"
  assumes contg': "continuous_on {a..b} g'" 
  assumes derivg_nonneg: "\<And>x. x \<in> {a..b} \<Longrightarrow> g' x \<ge> 0"
  assumes "a \<le> b"
  shows "(\<integral>\<^sup>+x. f x * indicator {g a..g b} x \<partial>lborel) = 
             (\<integral>\<^sup>+x. f (g x) * g' x * indicator {a..b} x \<partial>lborel)"
proof (cases "a = b")
  assume "a \<noteq> b"
  with \<open>a \<le> b\<close> have "a < b" by auto
  let ?f' = "\<lambda>x. max 0 (f x * indicator {g a..g b} x)"

  from derivg derivg_nonneg have monog: "\<And>x y. a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> b \<Longrightarrow> g x \<le> g y"
    by (rule deriv_nonneg_imp_mono) simp_all
  have bounds: "\<And>x. x \<ge> a \<Longrightarrow> x \<le> b \<Longrightarrow> g x \<ge> g a" "\<And>x. x \<ge> a \<Longrightarrow> x \<le> b \<Longrightarrow> g x \<le> g b"
    by (auto intro: monog)

  from derivg_nonneg have nonneg: 
    "\<And>f x. x \<ge> a \<Longrightarrow> x \<le> b \<Longrightarrow> g' x \<noteq> 0 \<Longrightarrow> f x * ereal (g' x) \<ge> 0 \<Longrightarrow> f x \<ge> 0"
    by (force simp: ereal_zero_le_0_iff field_simps)
  have nonneg': "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> \<not> 0 \<le> f (g x) \<Longrightarrow> 0 \<le> f (g x) * g' x \<Longrightarrow> g' x = 0"
    by (metis atLeastAtMost_iff derivg_nonneg eq_iff mult_eq_0_iff mult_le_0_iff)

  have "(\<integral>\<^sup>+x. f x * indicator {g a..g b} x \<partial>lborel) = 
            (\<integral>\<^sup>+x. ereal (?f' x) * indicator {g a..g b} x \<partial>lborel)"
    by (subst nn_integral_max_0[symmetric], intro nn_integral_cong) 
       (auto split: split_indicator simp: zero_ereal_def)
  also have "... = \<integral>\<^sup>+ x. ?f' (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel" using Mf
    by (subst nn_integral_substitution_aux[OF _ _ derivg contg' derivg_nonneg \<open>a < b\<close>]) 
       (auto simp add: zero_ereal_def mult.commute)
  also have "... = \<integral>\<^sup>+ x. max 0 (f (g x)) * ereal (g' x) * indicator {a..b} x \<partial>lborel"
    by (intro nn_integral_cong) 
       (auto split: split_indicator simp: max_def dest: bounds)
  also have "... = \<integral>\<^sup>+ x. max 0 (f (g x) * ereal (g' x) * indicator {a..b} x) \<partial>lborel"
    by (intro nn_integral_cong)
       (auto simp: max_def derivg_nonneg split: split_indicator intro!: nonneg')
  also have "... = \<integral>\<^sup>+ x. f (g x) * ereal (g' x) * indicator {a..b} x \<partial>lborel"
    by (rule nn_integral_max_0)
  also have "... = \<integral>\<^sup>+x. ereal (f (g x) * g' x * indicator {a..b} x) \<partial>lborel"
    by (intro nn_integral_cong) (simp split: split_indicator)
  finally show ?thesis .
qed auto

lemma integral_substitution:
  assumes integrable: "set_integrable lborel {g a..g b} f"
  assumes derivg: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' x) (at x)"
  assumes contg': "continuous_on {a..b} g'" 
  assumes derivg_nonneg: "\<And>x. x \<in> {a..b} \<Longrightarrow> g' x \<ge> 0"
  assumes "a \<le> b"
  shows "set_integrable lborel {a..b} (\<lambda>x. f (g x) * g' x)"
    and "(LBINT x. f x * indicator {g a..g b} x) = (LBINT x. f (g x) * g' x * indicator {a..b} x)"
proof-
  from derivg have contg: "continuous_on {a..b} g" by (rule has_real_derivative_imp_continuous_on)
  from this and contg' have Mg: "set_borel_measurable borel {a..b} g" and 
                             Mg': "set_borel_measurable borel {a..b} g'" 
      by (simp_all only: set_measurable_continuous_on_ivl)
  from derivg derivg_nonneg have monog: "\<And>x y. a \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> b \<Longrightarrow> g x \<le> g y"
    by (rule deriv_nonneg_imp_mono) simp_all

  have "(\<lambda>x. ereal (f x) * indicator {g a..g b} x) = 
           (\<lambda>x. ereal (f x * indicator {g a..g b} x))" 
    by (intro ext) (simp split: split_indicator)
  with integrable have M1: "(\<lambda>x. f x * indicator {g a..g b} x) \<in> borel_measurable borel"
    unfolding real_integrable_def by (force simp: mult.commute)
  have "(\<lambda>x. ereal (-f x) * indicator {g a..g b} x) = 
           (\<lambda>x. -ereal (f x * indicator {g a..g b} x))" 
    by (intro ext) (simp split: split_indicator)
  with integrable have M2: "(\<lambda>x. -f x * indicator {g a..g b} x) \<in> borel_measurable borel"
    unfolding real_integrable_def by (force simp: mult.commute)

  have "LBINT x. (f x :: real) * indicator {g a..g b} x = 
          real_of_ereal (\<integral>\<^sup>+ x. ereal (f x) * indicator {g a..g b} x \<partial>lborel) -
          real_of_ereal (\<integral>\<^sup>+ x. ereal (- (f x)) * indicator {g a..g b} x \<partial>lborel)" using integrable
    by (subst real_lebesgue_integral_def) (simp_all add: nn_integral_set_ereal mult.commute)
  also have "(\<integral>\<^sup>+x. ereal (f x) * indicator {g a..g b} x \<partial>lborel) =
               (\<integral>\<^sup>+x. ereal (f x * indicator {g a..g b} x) \<partial>lborel)"
    by (intro nn_integral_cong) (simp split: split_indicator)
  also with M1 have A: "(\<integral>\<^sup>+ x. ereal (f x * indicator {g a..g b} x) \<partial>lborel) =
                            (\<integral>\<^sup>+ x. ereal (f (g x) * g' x * indicator {a..b} x) \<partial>lborel)"
    by (subst nn_integral_substitution[OF _ derivg contg' derivg_nonneg \<open>a \<le> b\<close>]) 
       (auto simp: nn_integral_set_ereal mult.commute)
  also have "(\<integral>\<^sup>+ x. ereal (- (f x)) * indicator {g a..g b} x \<partial>lborel) =
               (\<integral>\<^sup>+ x. ereal (- (f x) * indicator {g a..g b} x) \<partial>lborel)"
    by (intro nn_integral_cong) (simp split: split_indicator)
  also with M2 have B: "(\<integral>\<^sup>+ x. ereal (- (f x) * indicator {g a..g b} x) \<partial>lborel) =
                            (\<integral>\<^sup>+ x. ereal (- (f (g x)) * g' x * indicator {a..b} x) \<partial>lborel)"
    by (subst nn_integral_substitution[OF _ derivg contg' derivg_nonneg \<open>a \<le> b\<close>])
       (auto simp: nn_integral_set_ereal mult.commute)

  also {
    from integrable have Mf: "set_borel_measurable borel {g a..g b} f" 
      unfolding real_integrable_def by simp
    from borel_measurable_times[OF measurable_compose[OF Mg Mf] Mg']
      have "(\<lambda>x. f (g x * indicator {a..b} x) * indicator {g a..g b} (g x * indicator {a..b} x) *
                     (g' x * indicator {a..b} x)) \<in> borel_measurable borel"  (is "?f \<in> _") 
      by (simp add: mult.commute)
    also have "?f = (\<lambda>x. f (g x) * g' x * indicator {a..b} x)"
      using monog by (intro ext) (auto split: split_indicator)
    finally show "set_integrable lborel {a..b} (\<lambda>x. f (g x) * g' x)"
      using A B integrable unfolding real_integrable_def 
      by (simp_all add: nn_integral_set_ereal mult.commute)
  } note integrable' = this

  have "real_of_ereal (\<integral>\<^sup>+ x. ereal (f (g x) * g' x * indicator {a..b} x) \<partial>lborel) -
                  real_of_ereal (\<integral>\<^sup>+ x. ereal (-f (g x) * g' x * indicator {a..b} x) \<partial>lborel) =
                (LBINT x. f (g x) * g' x * indicator {a..b} x)" using integrable'
    by (subst real_lebesgue_integral_def) (simp_all add: field_simps)
  finally show "(LBINT x. f x * indicator {g a..g b} x) = 
                     (LBINT x. f (g x) * g' x * indicator {a..b} x)" .
qed

lemma interval_integral_substitution:
  assumes integrable: "set_integrable lborel {g a..g b} f"
  assumes derivg: "\<And>x. x \<in> {a..b} \<Longrightarrow> (g has_real_derivative g' x) (at x)"
  assumes contg': "continuous_on {a..b} g'" 
  assumes derivg_nonneg: "\<And>x. x \<in> {a..b} \<Longrightarrow> g' x \<ge> 0"
  assumes "a \<le> b"
  shows "set_integrable lborel {a..b} (\<lambda>x. f (g x) * g' x)"
    and "(LBINT x=g a..g b. f x) = (LBINT x=a..b. f (g x) * g' x)"
  apply (rule integral_substitution[OF assms], simp, simp)
  apply (subst (1 2) interval_integral_Icc, fact)
  apply (rule deriv_nonneg_imp_mono[OF derivg derivg_nonneg], simp, simp, fact)
  using integral_substitution(2)[OF assms]
  apply (simp add: mult.commute)
  done

lemma set_borel_integrable_singleton[simp]:
  "set_integrable lborel {x} (f :: real \<Rightarrow> real)"
  by (subst integrable_discrete_difference[where X="{x}" and g="\<lambda>_. 0"]) auto

end
