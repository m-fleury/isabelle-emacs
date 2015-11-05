
(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Comparing growth of functions on natural numbers by a preorder relation\<close>

theory Function_Growth
imports Main Preorder Discrete
begin

subsection \<open>Motivation\<close>

text \<open>
  When comparing growth of functions in computer science, it is common to adhere
  on Landau Symbols (``O-Notation'').  However these come at the cost of notational
  oddities, particularly writing \<open>f = O(g)\<close> for \<open>f \<in> O(g)\<close> etc.
  
  Here we suggest a different way, following Hardy (G.~H.~Hardy and J.~E.~Littlewood,
  Some problems of Diophantine approximation, Acta Mathematica 37 (1914), p.~225).
  We establish a quasi order relation \<open>\<lesssim>\<close> on functions such that
  \<open>f \<lesssim> g \<longleftrightarrow> f \<in> O(g)\<close>.  From a didactic point of view, this does not only
  avoid the notational oddities mentioned above but also emphasizes the key insight
  of a growth hierarchy of functions:
  \<open>(\<lambda>n. 0) \<lesssim> (\<lambda>n. k) \<lesssim> Discrete.log \<lesssim> Discrete.sqrt \<lesssim> id \<lesssim> \<dots>\<close>.
\<close>

subsection \<open>Model\<close>

text \<open>
  Our growth functions are of type \<open>\<nat> \<Rightarrow> \<nat>\<close>.  This is different
  to the usual conventions for Landau symbols for which \<open>\<real> \<Rightarrow> \<real>\<close>
  would be appropriate, but we argue that \<open>\<real> \<Rightarrow> \<real>\<close> is more
  appropriate for analysis, whereas our setting is discrete.

  Note that we also restrict the additional coefficients to \<open>\<nat>\<close>, something
  we discuss at the particular definitions.
\<close>

subsection \<open>The \<open>\<lesssim>\<close> relation\<close>

definition less_eq_fun :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" (infix "\<lesssim>" 50)
where
  "f \<lesssim> g \<longleftrightarrow> (\<exists>c>0. \<exists>n. \<forall>m>n. f m \<le> c * g m)"

text \<open>
  This yields \<open>f \<lesssim> g \<longleftrightarrow> f \<in> O(g)\<close>.  Note that \<open>c\<close> is restricted to
  \<open>\<nat>\<close>.  This does not pose any problems since if \<open>f \<in> O(g)\<close> holds for
  a \<open>c \<in> \<real>\<close>, it also holds for \<open>\<lceil>c\<rceil> \<in> \<nat>\<close> by transitivity.
\<close>

lemma less_eq_funI [intro?]:
  assumes "\<exists>c>0. \<exists>n. \<forall>m>n. f m \<le> c * g m"
  shows "f \<lesssim> g"
  unfolding less_eq_fun_def by (rule assms)

lemma not_less_eq_funI:
  assumes "\<And>c n. c > 0 \<Longrightarrow> \<exists>m>n. c * g m < f m"
  shows "\<not> f \<lesssim> g"
  using assms unfolding less_eq_fun_def linorder_not_le [symmetric] by blast

lemma less_eq_funE [elim?]:
  assumes "f \<lesssim> g"
  obtains n c where "c > 0" and "\<And>m. m > n \<Longrightarrow> f m \<le> c * g m"
  using assms unfolding less_eq_fun_def by blast

lemma not_less_eq_funE:
  assumes "\<not> f \<lesssim> g" and "c > 0"
  obtains m where "m > n" and "c * g m < f m"
  using assms unfolding less_eq_fun_def linorder_not_le [symmetric] by blast


subsection \<open>The \<open>\<approx>\<close> relation, the equivalence relation induced by \<open>\<lesssim>\<close>\<close>

definition equiv_fun :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" (infix "\<cong>" 50)
where
  "f \<cong> g \<longleftrightarrow>
    (\<exists>c\<^sub>1>0. \<exists>c\<^sub>2>0. \<exists>n. \<forall>m>n. f m \<le> c\<^sub>1 * g m \<and> g m \<le> c\<^sub>2 * f m)"

text \<open>
  This yields \<open>f \<cong> g \<longleftrightarrow> f \<in> \<Theta>(g)\<close>.  Concerning \<open>c\<^sub>1\<close> and \<open>c\<^sub>2\<close>
  restricted to @{typ nat}, see note above on \<open>(\<lesssim>)\<close>.
\<close>

lemma equiv_funI [intro?]:
  assumes "\<exists>c\<^sub>1>0. \<exists>c\<^sub>2>0. \<exists>n. \<forall>m>n. f m \<le> c\<^sub>1 * g m \<and> g m \<le> c\<^sub>2 * f m"
  shows "f \<cong> g"
  unfolding equiv_fun_def by (rule assms)

lemma not_equiv_funI:
  assumes "\<And>c\<^sub>1 c\<^sub>2 n. c\<^sub>1 > 0 \<Longrightarrow> c\<^sub>2 > 0 \<Longrightarrow>
    \<exists>m>n. c\<^sub>1 * f m < g m \<or> c\<^sub>2 * g m < f m"
  shows "\<not> f \<cong> g"
  using assms unfolding equiv_fun_def linorder_not_le [symmetric] by blast

lemma equiv_funE [elim?]:
  assumes "f \<cong> g"
  obtains n c\<^sub>1 c\<^sub>2 where "c\<^sub>1 > 0" and "c\<^sub>2 > 0"
    and "\<And>m. m > n \<Longrightarrow> f m \<le> c\<^sub>1 * g m \<and> g m \<le> c\<^sub>2 * f m"
  using assms unfolding equiv_fun_def by blast

lemma not_equiv_funE:
  fixes n c\<^sub>1 c\<^sub>2
  assumes "\<not> f \<cong> g" and "c\<^sub>1 > 0" and "c\<^sub>2 > 0"
  obtains m where "m > n"
    and "c\<^sub>1 * f m < g m \<or> c\<^sub>2 * g m < f m"
  using assms unfolding equiv_fun_def linorder_not_le [symmetric] by blast


subsection \<open>The \<open>\<prec>\<close> relation, the strict part of \<open>\<lesssim>\<close>\<close>

definition less_fun :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" (infix "\<prec>" 50)
where
  "f \<prec> g \<longleftrightarrow> f \<lesssim> g \<and> \<not> g \<lesssim> f"

lemma less_funI:
  assumes "\<exists>c>0. \<exists>n. \<forall>m>n. f m \<le> c * g m"
    and "\<And>c n. c > 0 \<Longrightarrow> \<exists>m>n. c * f m < g m"
  shows "f \<prec> g"
  using assms unfolding less_fun_def less_eq_fun_def linorder_not_less [symmetric] by blast

lemma not_less_funI:
  assumes "\<And>c n. c > 0 \<Longrightarrow> \<exists>m>n. c * g m < f m"
    and "\<exists>c>0. \<exists>n. \<forall>m>n. g m \<le> c * f m"
  shows "\<not> f \<prec> g"
  using assms unfolding less_fun_def less_eq_fun_def linorder_not_less [symmetric] by blast

lemma less_funE [elim?]:
  assumes "f \<prec> g"
  obtains n c where "c > 0" and "\<And>m. m > n \<Longrightarrow> f m \<le> c * g m"
    and "\<And>c n. c > 0 \<Longrightarrow> \<exists>m>n. c * f m < g m"
proof -
  from assms have "f \<lesssim> g" and "\<not> g \<lesssim> f" by (simp_all add: less_fun_def)
  from \<open>f \<lesssim> g\<close> obtain n c where *:"c > 0" "\<And>m. m > n \<Longrightarrow> f m \<le> c * g m"
    by (rule less_eq_funE) blast
  { fix c n :: nat
    assume "c > 0"
    with \<open>\<not> g \<lesssim> f\<close> obtain m where "m > n" "c * f m < g m"
      by (rule not_less_eq_funE) blast
    then have **: "\<exists>m>n. c * f m < g m" by blast
  } note ** = this
  from * ** show thesis by (rule that)
qed

lemma not_less_funE:
  assumes "\<not> f \<prec> g" and "c > 0"
  obtains m where "m > n" and "c * g m < f m"
    | d q where "\<And>m. d > 0 \<Longrightarrow> m > q \<Longrightarrow> g q \<le> d * f q"
  using assms unfolding less_fun_def linorder_not_less [symmetric] by blast

text \<open>
  I did not find a proof for \<open>f \<prec> g \<longleftrightarrow> f \<in> o(g)\<close>.  Maybe this only
  holds if \<open>f\<close> and/or \<open>g\<close> are of a certain class of functions.
  However \<open>f \<in> o(g) \<longrightarrow> f \<prec> g\<close> is provable, and this yields a
  handy introduction rule.

  Note that D. Knuth ignores \<open>o\<close> altogether.  So what \dots

  Something still has to be said about the coefficient \<open>c\<close> in
  the definition of \<open>(\<prec>)\<close>.  In the typical definition of \<open>o\<close>,
  it occurs on the \emph{right} hand side of the \<open>(>)\<close>.  The reason
  is that the situation is dual to the definition of \<open>O\<close>: the definition
  works since \<open>c\<close> may become arbitrary small.  Since this is not possible
  within @{term \<nat>}, we push the coefficient to the left hand side instead such
  that it become arbitrary big instead.
\<close>

lemma less_fun_strongI:
  assumes "\<And>c. c > 0 \<Longrightarrow> \<exists>n. \<forall>m>n. c * f m < g m"
  shows "f \<prec> g"
proof (rule less_funI)
  have "1 > (0::nat)" by simp
  from assms \<open>1 > 0\<close> have "\<exists>n. \<forall>m>n. 1 * f m < g m" .
  then obtain n where *: "\<And>m. m > n \<Longrightarrow> 1 * f m < g m" by blast
  have "\<forall>m>n. f m \<le> 1 * g m"
  proof (rule allI, rule impI)
    fix m
    assume "m > n"
    with * have "1 * f m < g m" by simp
    then show "f m \<le> 1 * g m" by simp
  qed
  with \<open>1 > 0\<close> show "\<exists>c>0. \<exists>n. \<forall>m>n. f m \<le> c * g m" by blast
  fix c n :: nat
  assume "c > 0"
  with assms obtain q where "\<And>m. m > q \<Longrightarrow> c * f m < g m" by blast
  then have "c * f (Suc (q + n)) < g (Suc (q + n))" by simp
  moreover have "Suc (q + n) > n" by simp
  ultimately show "\<exists>m>n. c * f m < g m" by blast
qed


subsection \<open>\<open>\<lesssim>\<close> is a preorder\<close>

text \<open>This yields all lemmas relating \<open>\<lesssim>\<close>, \<open>\<prec>\<close> and \<open>\<cong>\<close>.\<close>

interpretation fun_order: preorder_equiv less_eq_fun less_fun
  rewrites "preorder_equiv.equiv less_eq_fun = equiv_fun"
proof -
  interpret preorder: preorder_equiv less_eq_fun less_fun
  proof
    fix f g h
    show "f \<lesssim> f"
    proof
      have "\<exists>n. \<forall>m>n. f m \<le> 1 * f m" by auto
      then show "\<exists>c>0. \<exists>n. \<forall>m>n. f m \<le> c * f m" by blast
    qed
    show "f \<prec> g \<longleftrightarrow> f \<lesssim> g \<and> \<not> g \<lesssim> f"
      by (fact less_fun_def)
    assume "f \<lesssim> g" and "g \<lesssim> h"
    show "f \<lesssim> h"
    proof
      from \<open>f \<lesssim> g\<close> obtain n\<^sub>1 c\<^sub>1
        where "c\<^sub>1 > 0" and P\<^sub>1: "\<And>m. m > n\<^sub>1 \<Longrightarrow> f m \<le> c\<^sub>1 * g m"
        by rule blast
      from \<open>g \<lesssim> h\<close> obtain n\<^sub>2 c\<^sub>2
        where "c\<^sub>2 > 0" and P\<^sub>2: "\<And>m. m > n\<^sub>2 \<Longrightarrow> g m \<le> c\<^sub>2 * h m"
        by rule blast
      have "\<forall>m>max n\<^sub>1 n\<^sub>2. f m \<le> (c\<^sub>1 * c\<^sub>2) * h m"
      proof (rule allI, rule impI)
        fix m
        assume Q: "m > max n\<^sub>1 n\<^sub>2"
        from P\<^sub>1 Q have *: "f m \<le> c\<^sub>1 * g m" by simp
        from P\<^sub>2 Q have "g m \<le> c\<^sub>2 * h m" by simp
        with \<open>c\<^sub>1 > 0\<close> have "c\<^sub>1 * g m \<le> (c\<^sub>1 * c\<^sub>2) * h m" by simp
        with * show "f m \<le> (c\<^sub>1 * c\<^sub>2) * h m" by (rule order_trans)
      qed
      then have "\<exists>n. \<forall>m>n. f m \<le> (c\<^sub>1 * c\<^sub>2) * h m" by rule
      moreover from \<open>c\<^sub>1 > 0\<close> \<open>c\<^sub>2 > 0\<close> have "c\<^sub>1 * c\<^sub>2 > 0" by simp
      ultimately show "\<exists>c>0. \<exists>n. \<forall>m>n. f m \<le> c * h m" by blast
    qed
  qed
  from preorder.preorder_equiv_axioms show "class.preorder_equiv less_eq_fun less_fun" .
  show "preorder_equiv.equiv less_eq_fun = equiv_fun"
  proof (rule ext, rule ext, unfold preorder.equiv_def)
    fix f g
    show "f \<lesssim> g \<and> g \<lesssim> f \<longleftrightarrow> f \<cong> g"
    proof
      assume "f \<cong> g"
      then obtain n c\<^sub>1 c\<^sub>2 where "c\<^sub>1 > 0" and "c\<^sub>2 > 0"
        and *: "\<And>m. m > n \<Longrightarrow> f m \<le> c\<^sub>1 * g m \<and> g m \<le> c\<^sub>2 * f m"
        by rule blast
      have "\<forall>m>n. f m \<le> c\<^sub>1 * g m"
      proof (rule allI, rule impI)
        fix m
        assume "m > n"
        with * show "f m \<le> c\<^sub>1 * g m" by simp
      qed
      with \<open>c\<^sub>1 > 0\<close> have "\<exists>c>0. \<exists>n. \<forall>m>n. f m \<le> c * g m" by blast
      then have "f \<lesssim> g" ..
      have "\<forall>m>n. g m \<le> c\<^sub>2 * f m"
      proof (rule allI, rule impI)
        fix m
        assume "m > n"
        with * show "g m \<le> c\<^sub>2 * f m" by simp
      qed
      with \<open>c\<^sub>2 > 0\<close> have "\<exists>c>0. \<exists>n. \<forall>m>n. g m \<le> c * f m" by blast
      then have "g \<lesssim> f" ..
      from \<open>f \<lesssim> g\<close> and \<open>g \<lesssim> f\<close> show "f \<lesssim> g \<and> g \<lesssim> f" ..
    next
      assume "f \<lesssim> g \<and> g \<lesssim> f"
      then have "f \<lesssim> g" and "g \<lesssim> f" by auto
      from \<open>f \<lesssim> g\<close> obtain n\<^sub>1 c\<^sub>1 where "c\<^sub>1 > 0"
        and P\<^sub>1: "\<And>m. m > n\<^sub>1 \<Longrightarrow> f m \<le> c\<^sub>1 * g m" by rule blast
      from \<open>g \<lesssim> f\<close> obtain n\<^sub>2 c\<^sub>2 where "c\<^sub>2 > 0"
        and P\<^sub>2: "\<And>m. m > n\<^sub>2 \<Longrightarrow> g m \<le> c\<^sub>2 * f m" by rule blast
      have "\<forall>m>max n\<^sub>1 n\<^sub>2. f m \<le> c\<^sub>1 * g m \<and> g m \<le> c\<^sub>2 * f m"
      proof (rule allI, rule impI)
        fix m
        assume Q: "m > max n\<^sub>1 n\<^sub>2"
        from P\<^sub>1 Q have "f m \<le> c\<^sub>1 * g m" by simp
        moreover from P\<^sub>2 Q have "g m \<le> c\<^sub>2 * f m" by simp
        ultimately show "f m \<le> c\<^sub>1 * g m \<and> g m \<le> c\<^sub>2 * f m" ..
      qed
      with \<open>c\<^sub>1 > 0\<close> \<open>c\<^sub>2 > 0\<close> have "\<exists>c\<^sub>1>0. \<exists>c\<^sub>2>0. \<exists>n.
        \<forall>m>n. f m \<le> c\<^sub>1 * g m \<and> g m \<le> c\<^sub>2 * f m" by blast
      then show "f \<cong> g" ..
    qed
  qed
qed


subsection \<open>Simple examples\<close>

text \<open>
  Most of these are left as constructive exercises for the reader.  Note that additional
  preconditions to the functions may be necessary.  The list here is by no means to be
  intended as complete construction set for typical functions, here surely something
  has to be added yet.
\<close>

text \<open>@{prop "(\<lambda>n. f n + k) \<cong> f"}\<close>

text \<open>@{prop "(\<lambda>n. Suc k * f n) \<cong> f"}\<close>

lemma "f \<lesssim> (\<lambda>n. f n + g n)"
  by rule auto

lemma "(\<lambda>_. 0) \<prec> (\<lambda>n. Suc k)"
  by (rule less_fun_strongI) auto

lemma "(\<lambda>_. k) \<prec> Discrete.log"
proof (rule less_fun_strongI)
  fix c :: nat
  have "\<forall>m>2 ^ (Suc (c * k)). c * k < Discrete.log m"
  proof (rule allI, rule impI)
    fix m :: nat
    assume "2 ^ Suc (c * k) < m"
    then have "2 ^ Suc (c * k) \<le> m" by simp
    with log_mono have "Discrete.log (2 ^ (Suc (c * k))) \<le> Discrete.log m"
      by (blast dest: monoD)
    moreover have "c * k < Discrete.log (2 ^ (Suc (c * k)))" by simp
    ultimately show "c * k < Discrete.log m" by auto
  qed
  then show "\<exists>n. \<forall>m>n. c * k < Discrete.log m" ..
qed
  
text \<open>@{prop "Discrete.log \<prec> Discrete.sqrt"}\<close>

lemma "Discrete.sqrt \<prec> id"
proof (rule less_fun_strongI)
  fix c :: nat
  assume "0 < c"
  have "\<forall>m>(Suc c)\<^sup>2. c * Discrete.sqrt m < id m"
  proof (rule allI, rule impI)
    fix m
    assume "(Suc c)\<^sup>2 < m"
    then have "(Suc c)\<^sup>2 \<le> m" by simp
    with mono_sqrt have "Discrete.sqrt ((Suc c)\<^sup>2) \<le> Discrete.sqrt m" by (rule monoE)
    then have "Suc c \<le> Discrete.sqrt m" by simp
    then have "c < Discrete.sqrt m" by simp
    moreover from \<open>(Suc c)\<^sup>2 < m\<close> have "Discrete.sqrt m > 0" by simp
    ultimately have "c * Discrete.sqrt m < Discrete.sqrt m * Discrete.sqrt m" by simp
    also have "\<dots> \<le> m" by (simp add: power2_eq_square [symmetric])
    finally show "c * Discrete.sqrt m < id m" by simp
  qed
  then show "\<exists>n. \<forall>m>n. c * Discrete.sqrt m < id m" ..
qed

lemma "id \<prec> (\<lambda>n. n\<^sup>2)"
  by (rule less_fun_strongI) (auto simp add: power2_eq_square)

lemma "(\<lambda>n. n ^ k) \<prec> (\<lambda>n. n ^ Suc k)"
  by (rule less_fun_strongI) auto

text \<open>@{prop "(\<lambda>n. n ^ k) \<prec> (\<lambda>n. 2 ^ n)"}\<close>

end

