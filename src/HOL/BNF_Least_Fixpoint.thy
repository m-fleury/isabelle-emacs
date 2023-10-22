(*  Title:      HOL/BNF_Least_Fixpoint.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013, 2014

Least fixpoint (datatype) operation on bounded natural functors.
*)

section \<open>Least Fixpoint (Datatype) Operation on Bounded Natural Functors\<close>

theory BNF_Least_Fixpoint
imports BNF_Fixpoint_Base
keywords
  "datatype" :: thy_defn and
  "datatype_compat" :: thy_defn
begin

lemma subset_emptyI: "(\<And>x. x \<in> A \<Longrightarrow> False) \<Longrightarrow> A \<subseteq> {}"
  by blast

lemma image_Collect_subsetI: "(\<And>x. P x \<Longrightarrow> f x \<in> B) \<Longrightarrow> f ` {x. P x} \<subseteq> B"
  by blast

lemma Collect_restrict: "{x. x \<in> X \<and> P x} \<subseteq> X"
  by auto

lemma prop_restrict: "\<lbrakk>x \<in> Z; Z \<subseteq> {x. x \<in> X \<and> P x}\<rbrakk> \<Longrightarrow> P x"
  by auto

lemma underS_I: "\<lbrakk>i \<noteq> j; (i, j) \<in> R\<rbrakk> \<Longrightarrow> i \<in> underS R j"
  unfolding underS_def by simp

lemma underS_E: "i \<in> underS R j \<Longrightarrow> i \<noteq> j \<and> (i, j) \<in> R"
  unfolding underS_def by simp

lemma underS_Field: "i \<in> underS R j \<Longrightarrow> i \<in> Field R"
  unfolding underS_def Field_def by auto

lemma ex_bij_betw: "|A| \<le>o (r :: 'b rel) \<Longrightarrow> \<exists>f B :: 'b set. bij_betw f B A"
  by (subst (asm) internalize_card_of_ordLeq) (auto dest!: iffD2[OF card_of_ordIso ordIso_symmetric])

lemma bij_betwI':
  "\<lbrakk>\<And>x y. \<lbrakk>x \<in> X; y \<in> X\<rbrakk> \<Longrightarrow> (f x = f y) = (x = y);
    \<And>x. x \<in> X \<Longrightarrow> f x \<in> Y;
    \<And>y. y \<in> Y \<Longrightarrow> \<exists>x \<in> X. y = f x\<rbrakk> \<Longrightarrow> bij_betw f X Y"
  unfolding bij_betw_def inj_on_def by blast

lemma surj_fun_eq:
  assumes surj_on: "f ` X = UNIV" and eq_on: "\<forall>x \<in> X. (g1 \<circ> f) x = (g2 \<circ> f) x"
  shows "g1 = g2"
proof (rule ext)
  fix y
  from surj_on obtain x where "x \<in> X" and "y = f x" by blast
  thus "g1 y = g2 y" using eq_on by simp
qed

lemma Card_order_wo_rel: "Card_order r \<Longrightarrow> wo_rel r"
  unfolding wo_rel_def card_order_on_def by blast

lemma Cinfinite_limit: "\<lbrakk>x \<in> Field r; Cinfinite r\<rbrakk> \<Longrightarrow> \<exists>y \<in> Field r. x \<noteq> y \<and> (x, y) \<in> r"
  unfolding cinfinite_def by (auto simp add: infinite_Card_order_limit)

lemma Card_order_trans:
  "\<lbrakk>Card_order r; x \<noteq> y; (x, y) \<in> r; y \<noteq> z; (y, z) \<in> r\<rbrakk> \<Longrightarrow> x \<noteq> z \<and> (x, z) \<in> r"
  unfolding card_order_on_def well_order_on_def linear_order_on_def
    partial_order_on_def preorder_on_def trans_def antisym_def by blast

lemma Cinfinite_limit2:
  assumes x1: "x1 \<in> Field r" and x2: "x2 \<in> Field r" and r: "Cinfinite r"
  shows "\<exists>y \<in> Field r. (x1 \<noteq> y \<and> (x1, y) \<in> r) \<and> (x2 \<noteq> y \<and> (x2, y) \<in> r)"
proof -
  from r have trans: "trans r" and total: "Total r" and antisym: "antisym r"
    unfolding card_order_on_def well_order_on_def linear_order_on_def
      partial_order_on_def preorder_on_def by auto
  obtain y1 where y1: "y1 \<in> Field r" "x1 \<noteq> y1" "(x1, y1) \<in> r"
    using Cinfinite_limit[OF x1 r] by blast
  obtain y2 where y2: "y2 \<in> Field r" "x2 \<noteq> y2" "(x2, y2) \<in> r"
    using Cinfinite_limit[OF x2 r] by blast
  show ?thesis
  proof (cases "y1 = y2")
    case True with y1 y2 show ?thesis by blast
  next
    case False
    with y1(1) y2(1) total have "(y1, y2) \<in> r \<or> (y2, y1) \<in> r"
      unfolding total_on_def by auto
    thus ?thesis
    proof
      assume *: "(y1, y2) \<in> r"
      with trans y1(3) have "(x1, y2) \<in> r" unfolding trans_def by blast
      with False y1 y2 * antisym show ?thesis by (cases "x1 = y2") (auto simp: antisym_def)
    next
      assume *: "(y2, y1) \<in> r"
      with trans y2(3) have "(x2, y1) \<in> r" unfolding trans_def by blast
      with False y1 y2 * antisym show ?thesis by (cases "x2 = y1") (auto simp: antisym_def)
    qed
  qed
qed

lemma Cinfinite_limit_finite:
  "\<lbrakk>finite X; X \<subseteq> Field r; Cinfinite r\<rbrakk> \<Longrightarrow> \<exists>y \<in> Field r. \<forall>x \<in> X. (x \<noteq> y \<and> (x, y) \<in> r)"
proof (induct X rule: finite_induct)
  case empty thus ?case unfolding cinfinite_def using ex_in_conv[of "Field r"] finite.emptyI by auto
next
  case (insert x X)
  then obtain y where y: "y \<in> Field r" "\<forall>x \<in> X. (x \<noteq> y \<and> (x, y) \<in> r)" by blast
  then obtain z where z: "z \<in> Field r" "x \<noteq> z \<and> (x, z) \<in> r" "y \<noteq> z \<and> (y, z) \<in> r"
    using Cinfinite_limit2[OF _ y(1) insert(5), of x] insert(4) by blast
  show ?case
    apply (intro bexI ballI)
    apply (erule insertE)
    apply hypsubst
    apply (rule z(2))
    using Card_order_trans[OF insert(5)[THEN conjunct2]] y(2) z(3)
    apply blast
    apply (rule z(1))
    done
qed

lemma insert_subsetI: "\<lbrakk>x \<in> A; X \<subseteq> A\<rbrakk> \<Longrightarrow> insert x X \<subseteq> A"
  by auto

lemmas well_order_induct_imp = wo_rel.well_order_induct[of r "\<lambda>x. x \<in> Field r \<longrightarrow> P x" for r P]

lemma meta_spec2:
  assumes "(\<And>x y. PROP P x y)"
  shows "PROP P x y"
  by (rule assms)

lemma nchotomy_relcomppE:
  assumes "\<And>y. \<exists>x. y = f x" "(r OO s) a c" "\<And>b. r a (f b) \<Longrightarrow> s (f b) c \<Longrightarrow> P"
  shows P
proof (rule relcompp.cases[OF assms(2)], hypsubst)
  fix b assume "r a b" "s b c"
  moreover from assms(1) obtain b' where "b = f b'" by blast
  ultimately show P by (blast intro: assms(3))
qed

lemma predicate2D_vimage2p: "\<lbrakk>R \<le> vimage2p f g S; R x y\<rbrakk> \<Longrightarrow> S (f x) (g y)"
  unfolding vimage2p_def by auto

lemma ssubst_Pair_rhs: "\<lbrakk>(r, s) \<in> R; s' = s\<rbrakk> \<Longrightarrow> (r, s') \<in> R"
  by (rule ssubst)

lemma all_mem_range1:
  "(\<And>y. y \<in> range f \<Longrightarrow> P y) \<equiv> (\<And>x. P (f x)) "
  by (rule equal_intr_rule) fast+

lemma all_mem_range2:
  "(\<And>fa y. fa \<in> range f \<Longrightarrow> y \<in> range fa \<Longrightarrow> P y) \<equiv> (\<And>x xa. P (f x xa))"
  by (rule equal_intr_rule) fast+

lemma all_mem_range3:
  "(\<And>fa fb y. fa \<in> range f \<Longrightarrow> fb \<in> range fa \<Longrightarrow> y \<in> range fb \<Longrightarrow> P y) \<equiv> (\<And>x xa xb. P (f x xa xb))"
  by (rule equal_intr_rule) fast+

lemma all_mem_range4:
  "(\<And>fa fb fc y. fa \<in> range f \<Longrightarrow> fb \<in> range fa \<Longrightarrow> fc \<in> range fb \<Longrightarrow> y \<in> range fc \<Longrightarrow> P y) \<equiv>
   (\<And>x xa xb xc. P (f x xa xb xc))"
  by (rule equal_intr_rule) fast+

lemma all_mem_range5:
  "(\<And>fa fb fc fd y. fa \<in> range f \<Longrightarrow> fb \<in> range fa \<Longrightarrow> fc \<in> range fb \<Longrightarrow> fd \<in> range fc \<Longrightarrow>
     y \<in> range fd \<Longrightarrow> P y) \<equiv>
   (\<And>x xa xb xc xd. P (f x xa xb xc xd))"
  by (rule equal_intr_rule) fast+

lemma all_mem_range6:
  "(\<And>fa fb fc fd fe ff y. fa \<in> range f \<Longrightarrow> fb \<in> range fa \<Longrightarrow> fc \<in> range fb \<Longrightarrow> fd \<in> range fc \<Longrightarrow>
     fe \<in> range fd \<Longrightarrow> ff \<in> range fe \<Longrightarrow> y \<in> range ff \<Longrightarrow> P y) \<equiv>
   (\<And>x xa xb xc xd xe xf. P (f x xa xb xc xd xe xf))"
  by (rule equal_intr_rule) (fastforce, fast)

lemma all_mem_range7:
  "(\<And>fa fb fc fd fe ff fg y. fa \<in> range f \<Longrightarrow> fb \<in> range fa \<Longrightarrow> fc \<in> range fb \<Longrightarrow> fd \<in> range fc \<Longrightarrow>
     fe \<in> range fd \<Longrightarrow> ff \<in> range fe \<Longrightarrow> fg \<in> range ff \<Longrightarrow> y \<in> range fg \<Longrightarrow> P y) \<equiv>
   (\<And>x xa xb xc xd xe xf xg. P (f x xa xb xc xd xe xf xg))"
  by (rule equal_intr_rule) (fastforce, fast)

lemma all_mem_range8:
  "(\<And>fa fb fc fd fe ff fg fh y. fa \<in> range f \<Longrightarrow> fb \<in> range fa \<Longrightarrow> fc \<in> range fb \<Longrightarrow> fd \<in> range fc \<Longrightarrow>
     fe \<in> range fd \<Longrightarrow> ff \<in> range fe \<Longrightarrow> fg \<in> range ff \<Longrightarrow> fh \<in> range fg \<Longrightarrow> y \<in> range fh \<Longrightarrow> P y) \<equiv>
   (\<And>x xa xb xc xd xe xf xg xh. P (f x xa xb xc xd xe xf xg xh))"
  by (rule equal_intr_rule) (fastforce, fast)

lemmas all_mem_range = all_mem_range1 all_mem_range2 all_mem_range3 all_mem_range4 all_mem_range5
  all_mem_range6 all_mem_range7 all_mem_range8

lemma pred_fun_True_id: "NO_MATCH id p \<Longrightarrow> pred_fun (\<lambda>x. True) p f = pred_fun (\<lambda>x. True) id (p \<circ> f)"
  unfolding fun.pred_map unfolding comp_def id_def ..

ML_file \<open>Tools/BNF/bnf_lfp_util.ML\<close>
ML_file \<open>Tools/BNF/bnf_lfp_tactics.ML\<close>
ML_file \<open>Tools/BNF/bnf_lfp.ML\<close>
ML_file \<open>Tools/BNF/bnf_lfp_compat.ML\<close>
ML_file \<open>Tools/BNF/bnf_lfp_rec_sugar_more.ML\<close>
ML_file \<open>Tools/BNF/bnf_lfp_size.ML\<close>

ML_file \<open>Tools/datatype_simprocs.ML\<close>

simproc_setup datatype_no_proper_subterm
  ("(x :: 'a :: size) = y") = \<open>K Datatype_Simprocs.no_proper_subterm_proc\<close>

end
