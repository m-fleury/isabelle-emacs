(*  Title:      HOL/Library/Order_Continuity.thy
    Author:     David von Oheimb, TU Muenchen
*)

section \<open>Continuity and iterations (of set transformers)\<close>

theory Order_Continuity
imports Complex_Main
begin

(* TODO: Generalize theory to chain-complete partial orders *)

lemma SUP_nat_binary:
  "(SUP n::nat. if n = 0 then A else B) = (sup A B::'a::complete_lattice)"
  apply (auto intro!: antisym SUP_least)
  apply (rule SUP_upper2[where i=0])
  apply simp_all
  apply (rule SUP_upper2[where i=1])
  apply simp_all
  done

lemma INF_nat_binary:
  "(INF n::nat. if n = 0 then A else B) = (inf A B::'a::complete_lattice)"
  apply (auto intro!: antisym INF_greatest)
  apply (rule INF_lower2[where i=0])
  apply simp_all
  apply (rule INF_lower2[where i=1])
  apply simp_all
  done

text \<open>
  The name @{text continuous} is already taken in @{text "Complex_Main"}, so we use
  @{text "sup_continuous"} and @{text "inf_continuous"}. These names appear sometimes in literature
  and have the advantage that these names are duals.
\<close>

named_theorems order_continuous_intros

subsection \<open>Continuity for complete lattices\<close>

definition
  sup_continuous :: "('a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<Rightarrow> bool" where
  "sup_continuous F \<longleftrightarrow> (\<forall>M::nat \<Rightarrow> 'a. mono M \<longrightarrow> F (SUP i. M i) = (SUP i. F (M i)))"

lemma sup_continuousD: "sup_continuous F \<Longrightarrow> mono M \<Longrightarrow> F (SUP i::nat. M i) = (SUP i. F (M i))"
  by (auto simp: sup_continuous_def)

lemma sup_continuous_mono:
  assumes [simp]: "sup_continuous F" shows "mono F"
proof
  fix A B :: "'a" assume [simp]: "A \<le> B"
  have "F B = F (SUP n::nat. if n = 0 then A else B)"
    by (simp add: sup_absorb2 SUP_nat_binary)
  also have "\<dots> = (SUP n::nat. if n = 0 then F A else F B)"
    by (auto simp: sup_continuousD mono_def intro!: SUP_cong)
  finally show "F A \<le> F B"
    by (simp add: SUP_nat_binary le_iff_sup)
qed

lemma [order_continuous_intros]:
  shows sup_continuous_const: "sup_continuous (\<lambda>x. c)"
    and sup_continuous_id: "sup_continuous (\<lambda>x. x)"
    and sup_continuous_apply: "sup_continuous (\<lambda>f. f x)"
    and sup_continuous_fun: "(\<And>s. sup_continuous (\<lambda>x. P x s)) \<Longrightarrow> sup_continuous P"
    and sup_continuous_If: "sup_continuous F \<Longrightarrow> sup_continuous G \<Longrightarrow> sup_continuous (\<lambda>f. if C then F f else G f)"
  by (auto simp: sup_continuous_def)

lemma sup_continuous_compose:
  assumes f: "sup_continuous f" and g: "sup_continuous g"
  shows "sup_continuous (\<lambda>x. f (g x))"
  unfolding sup_continuous_def
proof safe
  fix M :: "nat \<Rightarrow> 'c" assume "mono M"
  moreover then have "mono (\<lambda>i. g (M i))"
    using sup_continuous_mono[OF g] by (auto simp: mono_def)
  ultimately show "f (g (SUPREMUM UNIV M)) = (SUP i. f (g (M i)))"
    by (auto simp: sup_continuous_def g[THEN sup_continuousD] f[THEN sup_continuousD])
qed

lemma sup_continuous_sup[order_continuous_intros]:
  "sup_continuous f \<Longrightarrow> sup_continuous g \<Longrightarrow> sup_continuous (\<lambda>x. sup (f x) (g x))"
  by (simp add: sup_continuous_def SUP_sup_distrib)

lemma sup_continuous_inf[order_continuous_intros]:
  fixes P Q :: "'a :: complete_lattice \<Rightarrow> 'b :: complete_distrib_lattice"
  assumes P: "sup_continuous P" and Q: "sup_continuous Q"
  shows "sup_continuous (\<lambda>x. inf (P x) (Q x))"
  unfolding sup_continuous_def
proof (safe intro!: antisym)
  fix M :: "nat \<Rightarrow> 'a" assume M: "incseq M"
  have "inf (P (SUP i. M i)) (Q (SUP i. M i)) \<le> (SUP j i. inf (P (M i)) (Q (M j)))"
    unfolding sup_continuousD[OF P M] sup_continuousD[OF Q M] inf_SUP SUP_inf ..
  also have "\<dots> \<le> (SUP i. inf (P (M i)) (Q (M i)))"
  proof (intro SUP_least)
    fix i j from M assms[THEN sup_continuous_mono] show "inf (P (M i)) (Q (M j)) \<le> (SUP i. inf (P (M i)) (Q (M i)))"
      by (intro SUP_upper2[of "sup i j"] inf_mono) (auto simp: mono_def)
  qed
  finally show "inf (P (SUP i. M i)) (Q (SUP i. M i)) \<le> (SUP i. inf (P (M i)) (Q (M i)))" .
  
  show "(SUP i. inf (P (M i)) (Q (M i))) \<le> inf (P (SUP i. M i)) (Q (SUP i. M i))"
    unfolding sup_continuousD[OF P M] sup_continuousD[OF Q M] by (intro SUP_least inf_mono SUP_upper)
qed

lemma sup_continuous_and[order_continuous_intros]:
  "sup_continuous P \<Longrightarrow> sup_continuous Q \<Longrightarrow> sup_continuous (\<lambda>x. P x \<and> Q x)"
  using sup_continuous_inf[of P Q] by simp

lemma sup_continuous_or[order_continuous_intros]:
  "sup_continuous P \<Longrightarrow> sup_continuous Q \<Longrightarrow> sup_continuous (\<lambda>x. P x \<or> Q x)"
  by (auto simp: sup_continuous_def)

lemma sup_continuous_lfp:
  assumes "sup_continuous F" shows "lfp F = (SUP i. (F ^^ i) bot)" (is "lfp F = ?U")
proof (rule antisym)
  note mono = sup_continuous_mono[OF \<open>sup_continuous F\<close>]
  show "?U \<le> lfp F"
  proof (rule SUP_least)
    fix i show "(F ^^ i) bot \<le> lfp F"
    proof (induct i)
      case (Suc i)
      have "(F ^^ Suc i) bot = F ((F ^^ i) bot)" by simp
      also have "\<dots> \<le> F (lfp F)" by (rule monoD[OF mono Suc])
      also have "\<dots> = lfp F" by (simp add: lfp_unfold[OF mono, symmetric])
      finally show ?case .
    qed simp
  qed
  show "lfp F \<le> ?U"
  proof (rule lfp_lowerbound)
    have "mono (\<lambda>i::nat. (F ^^ i) bot)"
    proof -
      { fix i::nat have "(F ^^ i) bot \<le> (F ^^ (Suc i)) bot"
        proof (induct i)
          case 0 show ?case by simp
        next
          case Suc thus ?case using monoD[OF mono Suc] by auto
        qed }
      thus ?thesis by (auto simp add: mono_iff_le_Suc)
    qed
    hence "F ?U = (SUP i. (F ^^ Suc i) bot)"
      using \<open>sup_continuous F\<close> by (simp add: sup_continuous_def)
    also have "\<dots> \<le> ?U"
      by (fast intro: SUP_least SUP_upper)
    finally show "F ?U \<le> ?U" .
  qed
qed

lemma lfp_transfer_bounded:
  assumes P: "P bot" "\<And>x. P x \<Longrightarrow> P (f x)" "\<And>M. (\<And>i. P (M i)) \<Longrightarrow> P (SUP i::nat. M i)"
  assumes \<alpha>: "\<And>M. mono M \<Longrightarrow> (\<And>i::nat. P (M i)) \<Longrightarrow> \<alpha> (SUP i. M i) = (SUP i. \<alpha> (M i))"
  assumes f: "sup_continuous f" and g: "sup_continuous g"
  assumes [simp]: "\<And>x. P x \<Longrightarrow> x \<le> lfp f \<Longrightarrow> \<alpha> (f x) = g (\<alpha> x)"
  assumes g_bound: "\<And>x. \<alpha> bot \<le> g x"
  shows "\<alpha> (lfp f) = lfp g"
proof (rule antisym)
  note mono_g = sup_continuous_mono[OF g]
  note mono_f = sup_continuous_mono[OF f]
  have lfp_bound: "\<alpha> bot \<le> lfp g"
    by (subst lfp_unfold[OF mono_g]) (rule g_bound)

  have P_pow: "P ((f ^^ i) bot)" for i
    by (induction i) (auto intro!: P)
  have incseq_pow: "mono (\<lambda>i. (f ^^ i) bot)"
    unfolding mono_iff_le_Suc
  proof
    fix i show "(f ^^ i) bot \<le> (f ^^ (Suc i)) bot"
    proof (induct i)
      case Suc thus ?case using monoD[OF sup_continuous_mono[OF f] Suc] by auto
    qed (simp add: le_fun_def)
  qed
  have P_lfp: "P (lfp f)"
    using P_pow unfolding sup_continuous_lfp[OF f] by (auto intro!: P)

  have iter_le_lfp: "(f ^^ n) bot \<le> lfp f" for n
    apply (induction n)
    apply simp
    apply (subst lfp_unfold[OF mono_f])
    apply (auto intro!: monoD[OF mono_f])
    done

  have "\<alpha> (lfp f) = (SUP i. \<alpha> ((f^^i) bot))"
    unfolding sup_continuous_lfp[OF f] using incseq_pow P_pow by (rule \<alpha>)
  also have "\<dots> \<le> lfp g"
  proof (rule SUP_least)
    fix i show "\<alpha> ((f^^i) bot) \<le> lfp g"
    proof (induction i)
      case (Suc n) then show ?case
        by (subst lfp_unfold[OF mono_g]) (simp add: monoD[OF mono_g] P_pow iter_le_lfp)
    qed (simp add: lfp_bound)
  qed
  finally show "\<alpha> (lfp f) \<le> lfp g" .

  show "lfp g \<le> \<alpha> (lfp f)"
  proof (induction rule: lfp_ordinal_induct[OF mono_g])
    case (1 S) then show ?case
      by (subst lfp_unfold[OF sup_continuous_mono[OF f]])
         (simp add: monoD[OF mono_g] P_lfp)
  qed (auto intro: Sup_least)
qed

lemma lfp_transfer:
  "sup_continuous \<alpha> \<Longrightarrow> sup_continuous f \<Longrightarrow> sup_continuous g \<Longrightarrow>
    (\<And>x. \<alpha> bot \<le> g x) \<Longrightarrow> (\<And>x. x \<le> lfp f \<Longrightarrow> \<alpha> (f x) = g (\<alpha> x)) \<Longrightarrow> \<alpha> (lfp f) = lfp g"
  by (rule lfp_transfer_bounded[where P=top]) (auto dest: sup_continuousD)

definition
  inf_continuous :: "('a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<Rightarrow> bool" where
  "inf_continuous F \<longleftrightarrow> (\<forall>M::nat \<Rightarrow> 'a. antimono M \<longrightarrow> F (INF i. M i) = (INF i. F (M i)))"

lemma inf_continuousD: "inf_continuous F \<Longrightarrow> antimono M \<Longrightarrow> F (INF i::nat. M i) = (INF i. F (M i))"
  by (auto simp: inf_continuous_def)

lemma inf_continuous_mono:
  assumes [simp]: "inf_continuous F" shows "mono F"
proof
  fix A B :: "'a" assume [simp]: "A \<le> B"
  have "F A = F (INF n::nat. if n = 0 then B else A)"
    by (simp add: inf_absorb2 INF_nat_binary)
  also have "\<dots> = (INF n::nat. if n = 0 then F B else F A)"
    by (auto simp: inf_continuousD antimono_def intro!: INF_cong)
  finally show "F A \<le> F B"
    by (simp add: INF_nat_binary le_iff_inf inf_commute)
qed

lemma [order_continuous_intros]:
  shows inf_continuous_const: "inf_continuous (\<lambda>x. c)"
    and inf_continuous_id: "inf_continuous (\<lambda>x. x)"
    and inf_continuous_apply: "inf_continuous (\<lambda>f. f x)"
    and inf_continuous_fun: "(\<And>s. inf_continuous (\<lambda>x. P x s)) \<Longrightarrow> inf_continuous P"
    and inf_continuous_If: "inf_continuous F \<Longrightarrow> inf_continuous G \<Longrightarrow> inf_continuous (\<lambda>f. if C then F f else G f)"
  by (auto simp: inf_continuous_def)

lemma inf_continuous_inf[order_continuous_intros]:
  "inf_continuous f \<Longrightarrow> inf_continuous g \<Longrightarrow> inf_continuous (\<lambda>x. inf (f x) (g x))"
  by (simp add: inf_continuous_def INF_inf_distrib)

lemma inf_continuous_sup[order_continuous_intros]:
  fixes P Q :: "'a :: complete_lattice \<Rightarrow> 'b :: complete_distrib_lattice"
  assumes P: "inf_continuous P" and Q: "inf_continuous Q"
  shows "inf_continuous (\<lambda>x. sup (P x) (Q x))"
  unfolding inf_continuous_def
proof (safe intro!: antisym)
  fix M :: "nat \<Rightarrow> 'a" assume M: "decseq M"
  show "sup (P (INF i. M i)) (Q (INF i. M i)) \<le> (INF i. sup (P (M i)) (Q (M i)))"
    unfolding inf_continuousD[OF P M] inf_continuousD[OF Q M] by (intro INF_greatest sup_mono INF_lower)

  have "(INF i. sup (P (M i)) (Q (M i))) \<le> (INF j i. sup (P (M i)) (Q (M j)))"
  proof (intro INF_greatest)
    fix i j from M assms[THEN inf_continuous_mono] show "sup (P (M i)) (Q (M j)) \<ge> (INF i. sup (P (M i)) (Q (M i)))"
      by (intro INF_lower2[of "sup i j"] sup_mono) (auto simp: mono_def antimono_def)
  qed
  also have "\<dots> \<le> sup (P (INF i. M i)) (Q (INF i. M i))"
    unfolding inf_continuousD[OF P M] inf_continuousD[OF Q M] INF_sup sup_INF ..
  finally show "sup (P (INF i. M i)) (Q (INF i. M i)) \<ge> (INF i. sup (P (M i)) (Q (M i)))" .
qed

lemma inf_continuous_and[order_continuous_intros]:
  "inf_continuous P \<Longrightarrow> inf_continuous Q \<Longrightarrow> inf_continuous (\<lambda>x. P x \<and> Q x)"
  using inf_continuous_inf[of P Q] by simp

lemma inf_continuous_or[order_continuous_intros]:
  "inf_continuous P \<Longrightarrow> inf_continuous Q \<Longrightarrow> inf_continuous (\<lambda>x. P x \<or> Q x)"
  using inf_continuous_sup[of P Q] by simp

lemma inf_continuous_compose:
  assumes f: "inf_continuous f" and g: "inf_continuous g"
  shows "inf_continuous (\<lambda>x. f (g x))"
  unfolding inf_continuous_def
proof safe
  fix M :: "nat \<Rightarrow> 'c" assume "antimono M"
  moreover then have "antimono (\<lambda>i. g (M i))"
    using inf_continuous_mono[OF g] by (auto simp: mono_def antimono_def)
  ultimately show "f (g (INFIMUM UNIV M)) = (INF i. f (g (M i)))"
    by (auto simp: inf_continuous_def g[THEN inf_continuousD] f[THEN inf_continuousD])
qed

lemma inf_continuous_gfp:
  assumes "inf_continuous F" shows "gfp F = (INF i. (F ^^ i) top)" (is "gfp F = ?U")
proof (rule antisym)
  note mono = inf_continuous_mono[OF \<open>inf_continuous F\<close>]
  show "gfp F \<le> ?U"
  proof (rule INF_greatest)
    fix i show "gfp F \<le> (F ^^ i) top"
    proof (induct i)
      case (Suc i)
      have "gfp F = F (gfp F)" by (simp add: gfp_unfold[OF mono, symmetric])
      also have "\<dots> \<le> F ((F ^^ i) top)" by (rule monoD[OF mono Suc])
      also have "\<dots> = (F ^^ Suc i) top" by simp
      finally show ?case .
    qed simp
  qed
  show "?U \<le> gfp F"
  proof (rule gfp_upperbound)
    have *: "antimono (\<lambda>i::nat. (F ^^ i) top)"
    proof -
      { fix i::nat have "(F ^^ Suc i) top \<le> (F ^^ i) top"
        proof (induct i)
          case 0 show ?case by simp
        next
          case Suc thus ?case using monoD[OF mono Suc] by auto
        qed }
      thus ?thesis by (auto simp add: antimono_iff_le_Suc)
    qed
    have "?U \<le> (INF i. (F ^^ Suc i) top)"
      by (fast intro: INF_greatest INF_lower)
    also have "\<dots> \<le> F ?U"
      by (simp add: inf_continuousD \<open>inf_continuous F\<close> *)
    finally show "?U \<le> F ?U" .
  qed
qed

lemma gfp_transfer:
  assumes \<alpha>: "inf_continuous \<alpha>" and f: "inf_continuous f" and g: "inf_continuous g"
  assumes [simp]: "\<alpha> top = top" "\<And>x. \<alpha> (f x) = g (\<alpha> x)"
  shows "\<alpha> (gfp f) = gfp g"
proof -
  have "\<alpha> (gfp f) = (INF i. \<alpha> ((f^^i) top))"
    unfolding inf_continuous_gfp[OF f] by (intro f \<alpha> inf_continuousD antimono_funpow inf_continuous_mono)
  moreover have "\<alpha> ((f^^i) top) = (g^^i) top" for i
    by (induction i; simp)
  ultimately show ?thesis
    unfolding inf_continuous_gfp[OF g] by simp
qed

lemma gfp_transfer_bounded:
  assumes P: "P (f top)" "\<And>x. P x \<Longrightarrow> P (f x)" "\<And>M. antimono M \<Longrightarrow> (\<And>i. P (M i)) \<Longrightarrow> P (INF i::nat. M i)"
  assumes \<alpha>: "\<And>M. antimono M \<Longrightarrow> (\<And>i::nat. P (M i)) \<Longrightarrow> \<alpha> (INF i. M i) = (INF i. \<alpha> (M i))"
  assumes f: "inf_continuous f" and g: "inf_continuous g"
  assumes [simp]: "\<And>x. P x \<Longrightarrow> \<alpha> (f x) = g (\<alpha> x)"
  assumes g_bound: "\<And>x. g x \<le> \<alpha> (f top)"
  shows "\<alpha> (gfp f) = gfp g"
proof (rule antisym)
  note mono_g = inf_continuous_mono[OF g]

  have P_pow: "P ((f ^^ i) (f top))" for i
    by (induction i) (auto intro!: P)

  have antimono_pow: "antimono (\<lambda>i. (f ^^ i) top)"
    unfolding antimono_iff_le_Suc
  proof
    fix i show "(f ^^ Suc i) top \<le> (f ^^ i) top"
    proof (induct i)
      case Suc thus ?case using monoD[OF inf_continuous_mono[OF f] Suc] by auto
    qed (simp add: le_fun_def)
  qed
  have antimono_pow2: "antimono (\<lambda>i. (f ^^ i) (f top))"
  proof
    show "x \<le> y \<Longrightarrow> (f ^^ y) (f top) \<le> (f ^^ x) (f top)" for x y
      using antimono_pow[THEN antimonoD, of "Suc x" "Suc y"]
      unfolding funpow_Suc_right by simp
  qed
    
  have gfp_f: "gfp f = (INF i. (f ^^ i) (f top))"
    unfolding inf_continuous_gfp[OF f]
  proof (rule INF_eq)
    show "\<exists>j\<in>UNIV. (f ^^ j) (f top) \<le> (f ^^ i) top" for i
      by (intro bexI[of _ "i - 1"]) (auto simp: diff_Suc funpow_Suc_right simp del: funpow.simps(2) split: nat.split)
    show "\<exists>j\<in>UNIV. (f ^^ j) top \<le> (f ^^ i) (f top)" for i
      by (intro bexI[of _ "Suc i"]) (auto simp: funpow_Suc_right simp del: funpow.simps(2))
  qed

  have P_lfp: "P (gfp f)"
    unfolding gfp_f by (auto intro!: P P_pow antimono_pow2)

  have "\<alpha> (gfp f) = (INF i. \<alpha> ((f^^i) (f top)))"
    unfolding gfp_f by (rule \<alpha>) (auto intro!: P_pow antimono_pow2)
  also have "\<dots> \<ge> gfp g"
  proof (rule INF_greatest)
    fix i show "gfp g \<le> \<alpha> ((f^^i) (f top))"
    proof (induction i)
      case (Suc n) then show ?case
        by (subst gfp_unfold[OF mono_g]) (simp add: monoD[OF mono_g] P_pow)
    next
      case 0
      have "gfp g \<le> \<alpha> (f top)"
        by (subst gfp_unfold[OF mono_g]) (rule g_bound)
      then show ?case
        by simp
    qed
  qed
  finally show "gfp g \<le> \<alpha> (gfp f)" .

  show "\<alpha> (gfp f) \<le> gfp g"
  proof (induction rule: gfp_ordinal_induct[OF mono_g])
    case (1 S) then show ?case
      by (subst gfp_unfold[OF inf_continuous_mono[OF f]])
         (simp add: monoD[OF mono_g] P_lfp)
  qed (auto intro: Inf_greatest)
qed

end
