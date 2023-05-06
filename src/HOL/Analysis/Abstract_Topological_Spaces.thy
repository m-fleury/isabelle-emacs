(*  Author:     L C Paulson, University of Cambridge [ported from HOL Light] *)

section \<open>Various Forms of Topological Spaces\<close>

theory Abstract_Topological_Spaces
  imports
    Lindelof_Spaces Locally Sum_Topology
begin


subsection\<open>Connected topological spaces\<close>

lemma connected_space_eq_frontier_eq_empty:
   "connected_space X \<longleftrightarrow> (\<forall>S. S \<subseteq> topspace X \<and> X frontier_of S = {} \<longrightarrow> S = {} \<or> S = topspace X)"
  by (meson clopenin_eq_frontier_of connected_space_clopen_in)

lemma connected_space_frontier_eq_empty:
   "connected_space X \<and> S \<subseteq> topspace X
        \<Longrightarrow> (X frontier_of S = {} \<longleftrightarrow> S = {} \<or> S = topspace X)"
  by (meson connected_space_eq_frontier_eq_empty frontier_of_empty frontier_of_topspace)

lemma connectedin_eq_subset_separated_union:
   "connectedin X C \<longleftrightarrow>
        C \<subseteq> topspace X \<and> (\<forall>S T. separatedin X S T \<and> C \<subseteq> S \<union> T \<longrightarrow> C \<subseteq> S \<or> C \<subseteq> T)" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
  using connectedin_subset_topspace connectedin_subset_separated_union by blast
next
  assume ?rhs
  then show ?lhs
  by (metis closure_of_subset connectedin_separation dual_order.eq_iff inf.orderE separatedin_def sup.boundedE)
qed


lemma connectedin_clopen_cases:
   "\<lbrakk>connectedin X C; closedin X T; openin X T\<rbrakk> \<Longrightarrow> C \<subseteq> T \<or> disjnt C T"
  by (metis Diff_eq_empty_iff Int_empty_right clopenin_eq_frontier_of connectedin_Int_frontier_of disjnt_def)

lemma connected_space_quotient_map_image:
   "\<lbrakk>quotient_map X X' q; connected_space X\<rbrakk> \<Longrightarrow> connected_space X'"
  by (metis connectedin_continuous_map_image connectedin_topspace quotient_imp_continuous_map quotient_imp_surjective_map)

lemma connected_space_retraction_map_image:
   "\<lbrakk>retraction_map X X' r; connected_space X\<rbrakk> \<Longrightarrow> connected_space X'"
  using connected_space_quotient_map_image retraction_imp_quotient_map by blast

lemma connectedin_imp_perfect_gen:
  assumes X: "t1_space X" and S: "connectedin X S" and nontriv: "\<nexists>a. S = {a}"
  shows "S \<subseteq> X derived_set_of S"
unfolding derived_set_of_def
proof (intro subsetI CollectI conjI strip)
  show XS: "x \<in> topspace X" if "x \<in> S" for x
    using that S connectedin by fastforce 
  show "\<exists>y. y \<noteq> x \<and> y \<in> S \<and> y \<in> T"
    if "x \<in> S" and "x \<in> T \<and> openin X T" for x T
  proof -
    have opeXx: "openin X (topspace X - {x})"
      by (meson X openin_topspace t1_space_openin_delete_alt)
    moreover
    have "S \<subseteq> T \<union> (topspace X - {x})"
      using XS that(2) by auto
    moreover have "(topspace X - {x}) \<inter> S \<noteq> {}"
      by (metis Diff_triv S connectedin double_diff empty_subsetI inf_commute insert_subsetI nontriv that(1))
    ultimately show ?thesis
      using that connectedinD [OF S, of T "topspace X - {x}"]
      by blast
  qed
qed

lemma connectedin_imp_perfect:
  "\<lbrakk>Hausdorff_space X; connectedin X S; \<nexists>a. S = {a}\<rbrakk> \<Longrightarrow> S \<subseteq> X derived_set_of S"
  by (simp add: Hausdorff_imp_t1_space connectedin_imp_perfect_gen)


proposition connected_space_prod_topology:
   "connected_space(prod_topology X Y) \<longleftrightarrow>
    topspace(prod_topology X Y) = {} \<or> connected_space X \<and> connected_space Y" (is "?lhs=?rhs")
proof (cases "topspace(prod_topology X Y) = {}")
  case True
  then show ?thesis
    using connected_space_topspace_empty by blast
next
  case False
  then have nonempty: "topspace X \<noteq> {}" "topspace Y \<noteq> {}"
    by force+
  show ?thesis 
  proof
    assume ?lhs
    then show ?rhs
      by (meson connected_space_quotient_map_image nonempty quotient_map_fst quotient_map_snd)
  next
    assume ?rhs
    then have conX: "connected_space X" and conY: "connected_space Y"
      using False by blast+
    have False
      if "openin (prod_topology X Y) U" and "openin (prod_topology X Y) V"
        and UV: "topspace X \<times> topspace Y \<subseteq> U \<union> V" "U \<inter> V = {}" 
        and "U \<noteq> {}" and "V \<noteq> {}"
      for U V
    proof -
      have Usub: "U \<subseteq> topspace X \<times> topspace Y" and Vsub: "V \<subseteq> topspace X \<times> topspace Y"
        using that by (metis openin_subset topspace_prod_topology)+
      obtain a b where ab: "(a,b) \<in> U" and a: "a \<in> topspace X" and b: "b \<in> topspace Y"
        using \<open>U \<noteq> {}\<close> Usub by auto
      have "\<not> topspace X \<times> topspace Y \<subseteq> U"
        using Usub Vsub \<open>U \<inter> V = {}\<close> \<open>V \<noteq> {}\<close> by auto
      then obtain x y where x: "x \<in> topspace X" and y: "y \<in> topspace Y" and "(x,y) \<notin> U"
        by blast
      have oX: "openin X {x \<in> topspace X. (x,y) \<in> U}" "openin X {x \<in> topspace X. (x,y) \<in> V}"
       and oY: "openin Y {y \<in> topspace Y. (a,y) \<in> U}" "openin Y {y \<in> topspace Y. (a,y) \<in> V}"
        by (force intro: openin_continuous_map_preimage [where Y = "prod_topology X Y"] 
            simp: that continuous_map_pairwise o_def x y a)+
      have 1: "topspace Y \<subseteq> {y \<in> topspace Y. (a,y) \<in> U} \<union> {y \<in> topspace Y. (a,y) \<in> V}"
        using a that(3) by auto
      have 2: "{y \<in> topspace Y. (a,y) \<in> U} \<inter> {y \<in> topspace Y. (a,y) \<in> V} = {}"
        using that(4) by auto
      have 3: "{y \<in> topspace Y. (a,y) \<in> U} \<noteq> {}"
        using ab b by auto
      have 4: "{y \<in> topspace Y. (a,y) \<in> V} \<noteq> {}"
      proof -
        show ?thesis
          using connected_spaceD [OF conX oX] UV \<open>(x,y) \<notin> U\<close> a x y
                disjoint_iff_not_equal by blast
      qed
      show ?thesis
        using connected_spaceD [OF conY oY 1 2 3 4] by auto
    qed
    then show ?lhs
      unfolding connected_space_def topspace_prod_topology by blast 
  qed
qed

lemma connectedin_Times:
   "connectedin (prod_topology X Y) (S \<times> T) \<longleftrightarrow>
        S = {} \<or> T = {} \<or> connectedin X S \<and> connectedin Y T"
  by (force simp: connectedin_def subtopology_Times connected_space_prod_topology)


subsection\<open>The notion of "separated between" (complement of "connected between)"\<close>

definition separated_between 
  where "separated_between X S T \<equiv>
        \<exists>U V. openin X U \<and> openin X V \<and> U \<union> V = topspace X \<and> disjnt U V \<and> S \<subseteq> U \<and> T \<subseteq> V"

lemma separated_between_alt:
   "separated_between X S T \<longleftrightarrow>
        (\<exists>U V. closedin X U \<and> closedin X V \<and> U \<union> V = topspace X \<and> disjnt U V \<and> S \<subseteq> U \<and> T \<subseteq> V)"
  unfolding separated_between_def
  by (metis separatedin_open_sets separation_closedin_Un_gen subtopology_topspace 
            separatedin_closed_sets separation_openin_Un_gen)

lemma separated_between:
   "separated_between X S T \<longleftrightarrow>
        (\<exists>U. closedin X U \<and> openin X U \<and> S \<subseteq> U \<and> T \<subseteq> topspace X - U)"
  unfolding separated_between_def closedin_def disjnt_def
  by (smt (verit, del_insts) Diff_cancel Diff_disjoint Diff_partition Un_Diff Un_Diff_Int openin_subset)

lemma separated_between_mono:
   "\<lbrakk>separated_between X S T; S' \<subseteq> S; T' \<subseteq> T\<rbrakk> \<Longrightarrow> separated_between X S' T'"
  by (meson order.trans separated_between)

lemma separated_between_refl:
   "separated_between X S S \<longleftrightarrow> S = {}"
  unfolding separated_between_def
  by (metis Un_empty_right disjnt_def disjnt_empty2 disjnt_subset2 disjnt_sym le_iff_inf openin_empty openin_topspace)

lemma separated_between_sym:
   "separated_between X S T \<longleftrightarrow> separated_between X T S"
  by (metis disjnt_sym separated_between_alt sup_commute)

lemma separated_between_imp_subset:
   "separated_between X S T \<Longrightarrow> S \<subseteq> topspace X \<and> T \<subseteq> topspace X"
  by (metis le_supI1 le_supI2 separated_between_def)

lemma separated_between_empty: 
  "(separated_between X {} S \<longleftrightarrow> S \<subseteq> topspace X) \<and> (separated_between X S {} \<longleftrightarrow> S \<subseteq> topspace X)"
  by (metis Diff_empty bot.extremum closedin_empty openin_empty separated_between separated_between_imp_subset separated_between_sym)


lemma separated_between_Un: 
  "separated_between X S (T \<union> U) \<longleftrightarrow> separated_between X S T \<and> separated_between X S U"
  by (auto simp: separated_between)

lemma separated_between_Un': 
  "separated_between X (S \<union> T) U \<longleftrightarrow> separated_between X S U \<and> separated_between X T U"
  by (simp add: separated_between_Un separated_between_sym)

lemma separated_between_imp_disjoint:
   "separated_between X S T \<Longrightarrow> disjnt S T"
  by (meson disjnt_iff separated_between_def subsetD)

lemma separated_between_imp_separatedin:
   "separated_between X S T \<Longrightarrow> separatedin X S T"
  by (meson separated_between_def separatedin_mono separatedin_open_sets)

lemma separated_between_full:
  assumes "S \<union> T = topspace X"
  shows "separated_between X S T \<longleftrightarrow> disjnt S T \<and> closedin X S \<and> openin X S \<and> closedin X T \<and> openin X T"
proof -
  have "separated_between X S T \<longrightarrow> separatedin X S T"
    by (simp add: separated_between_imp_separatedin)
  then show ?thesis
    unfolding separated_between_def
    by (metis assms separation_closedin_Un_gen separation_openin_Un_gen subset_refl subtopology_topspace)
qed

lemma separated_between_eq_separatedin:
   "S \<union> T = topspace X \<Longrightarrow> (separated_between X S T \<longleftrightarrow> separatedin X S T)"
  by (simp add: separated_between_full separatedin_full)

lemma separated_between_pointwise_left:
  assumes "compactin X S"
  shows "separated_between X S T \<longleftrightarrow>
         (S = {} \<longrightarrow> T \<subseteq> topspace X) \<and> (\<forall>x \<in> S. separated_between X {x} T)"  (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    using separated_between_imp_subset separated_between_mono by fastforce
next
  assume R: ?rhs
  then have "T \<subseteq> topspace X"
    by (meson equals0I separated_between_imp_subset)
  show ?lhs
  proof -
    obtain U where U: "\<forall>x \<in> S. openin X (U x)"
      "\<forall>x \<in> S. \<exists>V. openin X V \<and> U x \<union> V = topspace X \<and> disjnt (U x) V \<and> {x} \<subseteq> U x \<and> T \<subseteq> V"
      using R unfolding separated_between_def by metis
    then have "S \<subseteq> \<Union>(U ` S)"
      by blast
    then obtain K where "finite K" "K \<subseteq> S" and K: "S \<subseteq> (\<Union>i\<in>K. U i)"
      using assms U unfolding compactin_def by (smt (verit) finite_subset_image imageE)
    show ?thesis
      unfolding separated_between
    proof (intro conjI exI)
      have "\<And>x. x \<in> K \<Longrightarrow> closedin X (U x)"
        by (smt (verit) \<open>K \<subseteq> S\<close> Diff_cancel U(2) Un_Diff Un_Diff_Int disjnt_def openin_closedin_eq subsetD)
      then show "closedin X (\<Union> (U ` K))"
        by (metis (mono_tags, lifting) \<open>finite K\<close> closedin_Union finite_imageI image_iff)
      show "openin X (\<Union> (U ` K))"
        using U(1) \<open>K \<subseteq> S\<close> by blast
      show "S \<subseteq> \<Union> (U ` K)"
        by (simp add: K)
      have "\<And>x i. \<lbrakk>x \<in> T; i \<in> K; x \<in> U i\<rbrakk> \<Longrightarrow> False"
        by (meson U(2) \<open>K \<subseteq> S\<close> disjnt_iff subsetD)
      then show "T \<subseteq> topspace X - \<Union> (U ` K)"
        using \<open>T \<subseteq> topspace X\<close> by auto
    qed
  qed
qed

lemma separated_between_pointwise_right:
   "compactin X T
        \<Longrightarrow> separated_between X S T \<longleftrightarrow> (T = {} \<longrightarrow> S \<subseteq> topspace X) \<and> (\<forall>y \<in> T. separated_between X S {y})"
  by (meson separated_between_pointwise_left separated_between_sym)

lemma separated_between_closure_of:
  "S \<subseteq> topspace X \<Longrightarrow> separated_between X (X closure_of S) T \<longleftrightarrow> separated_between X S T"
  by (meson closure_of_minimal_eq separated_between_alt)


lemma separated_between_closure_of':
 "T \<subseteq> topspace X \<Longrightarrow> separated_between X S (X closure_of T) \<longleftrightarrow> separated_between X S T"
  by (meson separated_between_closure_of separated_between_sym)

lemma separated_between_closure_of_eq:
 "separated_between X S T \<longleftrightarrow> S \<subseteq> topspace X \<and> separated_between X (X closure_of S) T"
  by (metis separated_between_closure_of separated_between_imp_subset)

lemma separated_between_closure_of_eq':
 "separated_between X S T \<longleftrightarrow> T \<subseteq> topspace X \<and> separated_between X S (X closure_of T)"
  by (metis separated_between_closure_of' separated_between_imp_subset)

lemma separated_between_frontier_of_eq':
  "separated_between X S T \<longleftrightarrow>
   T \<subseteq> topspace X \<and> disjnt S T \<and> separated_between X S (X frontier_of T)" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis interior_of_union_frontier_of separated_between_Un separated_between_closure_of_eq' 
        separated_between_imp_disjoint)
next
  assume R: ?rhs
  then obtain U where U: "closedin X U" "openin X U" "S \<subseteq> U" "X closure_of T - X interior_of T \<subseteq> topspace X - U"
    by (metis frontier_of_def separated_between)
  show ?lhs
  proof (rule separated_between_mono [of _ S "X closure_of T"])
    have "separated_between X S T"
      unfolding separated_between
    proof (intro conjI exI)
      show "S \<subseteq> U - T" "T \<subseteq> topspace X - (U - T)"
        using R U(3) by (force simp: disjnt_iff)+
      have "T \<subseteq> X closure_of T"
        by (simp add: R closure_of_subset)
      then have *: "U - T = U - X interior_of T"
        using U(4) interior_of_subset by fastforce
      then show "closedin X (U - T)"
        by (simp add: U(1) closedin_diff)
      have "U \<inter> X frontier_of T = {}"
        using U(4) frontier_of_def by fastforce
      then show "openin X (U - T)"
        by (metis * Diff_Un U(2) Un_Diff_Int Un_Int_eq(1) closedin_closure_of interior_of_union_frontier_of openin_diff sup_bot_right)
    qed
    then show "separated_between X S (X closure_of T)"
      by (simp add: R separated_between_closure_of')
  qed (auto simp: R closure_of_subset)
qed

lemma separated_between_frontier_of_eq:
  "separated_between X S T \<longleftrightarrow> S \<subseteq> topspace X \<and> disjnt S T \<and> separated_between X (X frontier_of S) T"
  by (metis disjnt_sym separated_between_frontier_of_eq' separated_between_sym)

lemma separated_between_frontier_of:
  "\<lbrakk>S \<subseteq> topspace X; disjnt S T\<rbrakk>
   \<Longrightarrow> (separated_between X (X frontier_of S) T \<longleftrightarrow> separated_between X S T)"
  using separated_between_frontier_of_eq by blast

lemma separated_between_frontier_of':
 "\<lbrakk>T \<subseteq> topspace X; disjnt S T\<rbrakk>
   \<Longrightarrow> (separated_between X S (X frontier_of T) \<longleftrightarrow> separated_between X S T)"
  using separated_between_frontier_of_eq' by auto

lemma connected_space_separated_between:
  "connected_space X \<longleftrightarrow> (\<forall>S T. separated_between X S T \<longrightarrow> S = {} \<or> T = {})" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis Diff_cancel connected_space_clopen_in separated_between subset_empty)
next
  assume ?rhs then show ?lhs
    by (meson connected_space_eq_not_separated separated_between_eq_separatedin)
qed

lemma connected_space_imp_separated_between_trivial:
   "connected_space X
        \<Longrightarrow> (separated_between X S T \<longleftrightarrow> S = {} \<and> T \<subseteq> topspace X \<or> S \<subseteq> topspace X \<and> T = {})"
  by (metis connected_space_separated_between separated_between_empty)


subsection\<open>Connected components\<close>

lemma connected_component_of_subtopology_eq:
   "connected_component_of (subtopology X U) a = connected_component_of X a \<longleftrightarrow>
    connected_component_of_set X a \<subseteq> U"
  by (force simp: connected_component_of_set connectedin_subtopology connected_component_of_def fun_eq_iff subset_iff)

lemma connected_components_of_subtopology:
  assumes "C \<in> connected_components_of X" "C \<subseteq> U"
  shows "C \<in> connected_components_of (subtopology X U)"
proof -
  obtain a where a: "connected_component_of_set X a \<subseteq> U" and "a \<in> topspace X"
             and Ceq: "C = connected_component_of_set X a"
    using assms by (force simp: connected_components_of_def)
  then have "a \<in> U"
    by (simp add: connected_component_of_refl in_mono)
  then have "connected_component_of_set X a = connected_component_of_set (subtopology X U) a"
    by (metis a connected_component_of_subtopology_eq)
  then show ?thesis
    by (simp add: Ceq \<open>a \<in> U\<close> \<open>a \<in> topspace X\<close> connected_component_in_connected_components_of)
qed

thm connected_space_iff_components_eq

lemma open_in_finite_connected_components:
  assumes "finite(connected_components_of X)" "C \<in> connected_components_of X"
  shows "openin X C"
proof -
  have "closedin X (topspace X - C)"
    by (metis DiffD1 assms closedin_Union closedin_connected_components_of complement_connected_components_of_Union finite_Diff)
  then show ?thesis
    by (simp add: assms connected_components_of_subset openin_closedin)
qed
thm connected_component_of_eq_overlap

lemma connected_components_of_disjoint:
  assumes "C \<in> connected_components_of X" "C' \<in> connected_components_of X"
    shows "(disjnt C C' \<longleftrightarrow> (C \<noteq> C'))"
proof -
  have "C \<noteq> {}"
    using nonempty_connected_components_of assms by blast
  with assms show ?thesis
    by (metis disjnt_self_iff_empty pairwiseD pairwise_disjoint_connected_components_of)
qed

lemma connected_components_of_overlap:
   "\<lbrakk>C \<in> connected_components_of X; C' \<in> connected_components_of X\<rbrakk> \<Longrightarrow> C \<inter> C' \<noteq> {} \<longleftrightarrow> C = C'"
  by (meson connected_components_of_disjoint disjnt_def)

lemma pairwise_separated_connected_components_of:
   "pairwise (separatedin X) (connected_components_of X)"
  by (simp add: closedin_connected_components_of connected_components_of_disjoint pairwiseI separatedin_closed_sets)

lemma finite_connected_components_of_finite:
   "finite(topspace X) \<Longrightarrow> finite(connected_components_of X)"
  by (simp add: Union_connected_components_of finite_UnionD)

lemma connected_component_of_unique:
   "\<lbrakk>x \<in> C; connectedin X C; \<And>C'. x \<in> C' \<and> connectedin X C' \<Longrightarrow> C' \<subseteq> C\<rbrakk>
        \<Longrightarrow> connected_component_of_set X x = C"
  by (meson connected_component_of_maximal connectedin_connected_component_of subsetD subset_antisym)

lemma closedin_connected_component_of_subtopology:
   "\<lbrakk>C \<in> connected_components_of (subtopology X s); X closure_of C \<subseteq> s\<rbrakk> \<Longrightarrow> closedin X C"
  by (metis closedin_Int_closure_of closedin_connected_components_of closure_of_eq inf.absorb_iff2)

lemma connected_component_of_discrete_topology:
   "connected_component_of_set (discrete_topology U) x = (if x \<in> U then {x} else {})"
  by (simp add: locally_path_connected_space_discrete_topology flip: path_component_eq_connected_component_of)

lemma connected_components_of_discrete_topology:
   "connected_components_of (discrete_topology U) = (\<lambda>x. {x}) ` U"
  by (simp add: connected_component_of_discrete_topology connected_components_of_def)

lemma connected_component_of_continuous_image:
   "\<lbrakk>continuous_map X Y f; connected_component_of X x y\<rbrakk>
        \<Longrightarrow> connected_component_of Y (f x) (f y)"
  by (meson connected_component_of_def connectedin_continuous_map_image image_eqI)

lemma homeomorphic_map_connected_component_of:
  assumes "homeomorphic_map X Y f" and x: "x \<in> topspace X"
  shows "connected_component_of_set Y (f x) = f ` (connected_component_of_set X x)"
proof -
  obtain g where g: "continuous_map X Y f"
    "continuous_map Y X g " "\<And>x. x \<in> topspace X \<Longrightarrow> g (f x) = x" 
    "\<And>y. y \<in> topspace Y \<Longrightarrow> f (g y) = y"
    using assms(1) homeomorphic_map_maps homeomorphic_maps_def by fastforce
  show ?thesis
    using connected_component_in_topspace [of Y] x g
          connected_component_of_continuous_image [of X Y f]
          connected_component_of_continuous_image [of Y X g]
    by force
qed

lemma homeomorphic_map_connected_components_of:
  assumes "homeomorphic_map X Y f"
  shows "connected_components_of Y = (image f) ` (connected_components_of X)"
proof -
  have "topspace Y = f ` topspace X"
    by (metis assms homeomorphic_imp_surjective_map)
  with homeomorphic_map_connected_component_of [OF assms] show ?thesis
    by (auto simp: connected_components_of_def image_iff)
qed

lemma connected_component_of_pair:
   "connected_component_of_set (prod_topology X Y) (x,y) =
        connected_component_of_set X x \<times> connected_component_of_set Y y"
proof (cases "x \<in> topspace X \<and> y \<in> topspace Y")
  case True
  show ?thesis
  proof (rule connected_component_of_unique)
    show "(x, y) \<in> connected_component_of_set X x \<times> connected_component_of_set Y y"
      using True by (simp add: connected_component_of_refl)
    show "connectedin (prod_topology X Y) (connected_component_of_set X x \<times> connected_component_of_set Y y)"
      by (metis connectedin_Times connectedin_connected_component_of)
    show "C \<subseteq> connected_component_of_set X x \<times> connected_component_of_set Y y"
      if "(x, y) \<in> C \<and> connectedin (prod_topology X Y) C" for C 
      using that unfolding connected_component_of_def
      apply clarsimp
      by (metis (no_types) connectedin_continuous_map_image continuous_map_fst continuous_map_snd fst_conv imageI snd_conv)
  qed
next
  case False then show ?thesis
    by (metis Sigma_empty1 Sigma_empty2 connected_component_of_eq_empty mem_Sigma_iff topspace_prod_topology)
qed

lemma connected_components_of_prod_topology:
  "connected_components_of (prod_topology X Y) =
    {C \<times> D |C D. C \<in> connected_components_of X \<and> D \<in> connected_components_of Y}" (is "?lhs=?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    apply (clarsimp simp: connected_components_of_def)
    by (metis (no_types) connected_component_of_pair imageI)
next
  show "?rhs \<subseteq> ?lhs"
    using connected_component_of_pair
    by (fastforce simp: connected_components_of_def)
qed


lemma connected_component_of_product_topology:
   "connected_component_of_set (product_topology X I) x =
    (if x \<in> extensional I then PiE I (\<lambda>i. connected_component_of_set (X i) (x i)) else {})"
    (is "?lhs = If _ ?R _")    
proof (cases "x \<in> topspace(product_topology X I)")
  case True
  have "?lhs = (\<Pi>\<^sub>E i\<in>I. connected_component_of_set (X i) (x i))"
    if xX: "\<And>i. i\<in>I \<Longrightarrow> x i \<in> topspace (X i)" and ext: "x \<in> extensional I"
  proof (rule connected_component_of_unique)
    show "x \<in> ?R"
      by (simp add: PiE_iff connected_component_of_refl local.ext xX)
    show "connectedin (product_topology X I) ?R"
      by (simp add: connectedin_PiE connectedin_connected_component_of)
    show "C \<subseteq> ?R"
      if "x \<in> C \<and> connectedin (product_topology X I) C" for C 
    proof -
      have "C \<subseteq> extensional I"
        using PiE_def connectedin_subset_topspace that by fastforce
      have "\<And>y. y \<in> C \<Longrightarrow> y \<in> (\<Pi> i\<in>I. connected_component_of_set (X i) (x i))"
        apply (simp add: connected_component_of_def Pi_def)
        by (metis connectedin_continuous_map_image continuous_map_product_projection imageI that)
      then show ?thesis
        using PiE_def \<open>C \<subseteq> extensional I\<close> by fastforce
    qed
  qed
  with True show ?thesis
    by (simp add: PiE_iff)
next
  case False
  then show ?thesis
    apply (simp add: PiE_iff)
    by (smt (verit) Collect_empty_eq False PiE_eq_empty_iff PiE_iff connected_component_of_eq_empty)
qed


lemma connected_components_of_product_topology:
   "connected_components_of (product_topology X I) =
    {PiE I B |B. \<forall>i \<in> I. B i \<in> connected_components_of(X i)}"  (is "?lhs=?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (auto simp: connected_components_of_def connected_component_of_product_topology PiE_iff)
  show "?rhs \<subseteq> ?lhs"
  proof
    fix F
    assume "F \<in> ?rhs"
    then obtain B where Feq: "F = Pi\<^sub>E I B" and
      "\<forall>i\<in>I. \<exists>x\<in>topspace (X i). B i = connected_component_of_set (X i) x"
      by (force simp: connected_components_of_def connected_component_of_product_topology image_iff)
    then obtain f where
      f: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> topspace (X i) \<and> B i = connected_component_of_set (X i) (f i)"
      by metis
    then have "(\<lambda>i\<in>I. f i) \<in> ((\<Pi>\<^sub>E i\<in>I. topspace (X i)) \<inter> extensional I)"
      by simp
    with f show "F \<in> ?lhs"
      unfolding Feq connected_components_of_def connected_component_of_product_topology image_iff
      by (smt (verit, del_insts) PiE_cong restrict_PiE_iff restrict_apply' restrict_extensional topspace_product_topology)
  qed
qed


subsection \<open>Monotone maps (in the general topological sense)\<close>


definition monotone_map 
  where "monotone_map X Y f ==
        f ` (topspace X) \<subseteq> topspace Y \<and>
        (\<forall>y \<in> topspace Y. connectedin X {x \<in> topspace X. f x = y})"

lemma monotone_map:
  "monotone_map X Y f \<longleftrightarrow>
   f ` (topspace X) \<subseteq> topspace Y \<and> (\<forall>y. connectedin X {x \<in> topspace X. f x = y})"
  apply (simp add: monotone_map_def)
  by (metis (mono_tags, lifting) connectedin_empty [of X] Collect_empty_eq image_subset_iff) 


lemma monotone_map_in_subtopology:
   "monotone_map X (subtopology Y S) f \<longleftrightarrow> monotone_map X Y f \<and> f ` (topspace X) \<subseteq> S"
  by (smt (verit, del_insts) le_inf_iff monotone_map topspace_subtopology)

lemma monotone_map_from_subtopology:
  assumes "monotone_map X Y f" 
    "\<And>x y. x \<in> topspace X \<and> y \<in> topspace X \<and> x \<in> S \<and> f x = f y \<Longrightarrow> y \<in> S"
  shows "monotone_map (subtopology X S) Y f"
  using assms
  unfolding monotone_map_def connectedin_subtopology
  by (smt (verit, del_insts) Collect_cong Collect_empty_eq IntE IntI connectedin_empty image_subset_iff mem_Collect_eq subsetI topspace_subtopology)

lemma monotone_map_restriction:
  "monotone_map X Y f \<and> {x \<in> topspace X. f x \<in> v} = u
        \<Longrightarrow> monotone_map (subtopology X u) (subtopology Y v) f"
  by (smt (verit, best) IntI Int_Collect image_subset_iff mem_Collect_eq monotone_map monotone_map_from_subtopology topspace_subtopology)

lemma injective_imp_monotone_map:
  assumes "f ` topspace X \<subseteq> topspace Y"  "inj_on f (topspace X)"
  shows "monotone_map X Y f"
  unfolding monotone_map_def
proof (intro conjI assms strip)
  fix y
  assume "y \<in> topspace Y"
  then have "{x \<in> topspace X. f x = y} = {} \<or> (\<exists>a \<in> topspace X. {x \<in> topspace X. f x = y} = {a})"
    using assms(2) unfolding inj_on_def by blast
  then show "connectedin X {x \<in> topspace X. f x = y}"
    by (metis (no_types, lifting) connectedin_empty connectedin_sing)
qed

lemma embedding_imp_monotone_map:
   "embedding_map X Y f \<Longrightarrow> monotone_map X Y f"
  by (metis (no_types) embedding_map_def homeomorphic_eq_everything_map inf.absorb_iff2 injective_imp_monotone_map topspace_subtopology)

lemma section_imp_monotone_map:
   "section_map X Y f \<Longrightarrow> monotone_map X Y f"
  by (simp add: embedding_imp_monotone_map section_imp_embedding_map)

lemma homeomorphic_imp_monotone_map:
   "homeomorphic_map X Y f \<Longrightarrow> monotone_map X Y f"
  by (meson section_and_retraction_eq_homeomorphic_map section_imp_monotone_map)

proposition connected_space_monotone_quotient_map_preimage:
  assumes f: "monotone_map X Y f" "quotient_map X Y f" and "connected_space Y"
  shows "connected_space X"
proof (rule ccontr)
  assume "\<not> connected_space X"
  then obtain U V where "openin X U" "openin X V" "U \<inter> V = {}"
    "U \<noteq> {}" "V \<noteq> {}" and topUV: "topspace X \<subseteq> U \<union> V"
    by (auto simp: connected_space_def)
  then have UVsub: "U \<subseteq> topspace X" "V \<subseteq> topspace X"
    by (auto simp: openin_subset)
  have "\<not> connected_space Y"
    unfolding connected_space_def not_not
  proof (intro exI conjI)
    show "topspace Y \<subseteq> f`U \<union> f`V"
      by (metis f(2) image_Un quotient_imp_surjective_map subset_Un_eq topUV)
    show "f`U \<noteq> {}"
      by (simp add: \<open>U \<noteq> {}\<close>)
    show "(f`V) \<noteq> {}"
      by (simp add: \<open>V \<noteq> {}\<close>)
    have *: "y \<notin> f ` V" if "y \<in> f ` U" for y
    proof -
      have \<section>: "connectedin X {x \<in> topspace X. f x = y}"
        using f(1) monotone_map by fastforce
      show ?thesis
        using connectedinD [OF \<section> \<open>openin X U\<close> \<open>openin X V\<close>] UVsub topUV \<open>U \<inter> V = {}\<close> that
        by (force simp: disjoint_iff)
    qed
    then show "f`U \<inter> f`V = {}"
      by blast
    show "openin Y (f`U)"
      using f \<open>openin X U\<close> topUV * unfolding quotient_map_saturated_open by force
    show "openin Y (f`V)"
      using f \<open>openin X V\<close> topUV * unfolding quotient_map_saturated_open by force
  qed
  then show False
    by (simp add: assms)
qed

lemma connectedin_monotone_quotient_map_preimage:
  assumes "monotone_map X Y f" "quotient_map X Y f" "connectedin Y C" "openin Y C \<or> closedin Y C"
  shows "connectedin X {x \<in> topspace X. f x \<in> C}"
proof -
  have "connected_space (subtopology X {x \<in> topspace X. f x \<in> C})"
  proof -
    have "connected_space (subtopology Y C)"
      using \<open>connectedin Y C\<close> connectedin_def by blast
    moreover have "quotient_map (subtopology X {a \<in> topspace X. f a \<in> C}) (subtopology Y C) f"
      by (simp add: assms quotient_map_restriction)
    ultimately show ?thesis
      using \<open>monotone_map X Y f\<close> connected_space_monotone_quotient_map_preimage monotone_map_restriction by blast
  qed
  then show ?thesis
    by (simp add: connectedin_def)
qed

lemma monotone_open_map:
  assumes "continuous_map X Y f" "open_map X Y f" and fim: "f ` (topspace X) = topspace Y"
  shows "monotone_map X Y f \<longleftrightarrow> (\<forall>C. connectedin Y C \<longrightarrow> connectedin X {x \<in> topspace X. f x \<in> C})"
         (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
    unfolding connectedin_def
  proof (intro strip conjI)
    fix C
    assume C: "C \<subseteq> topspace Y \<and> connected_space (subtopology Y C)"
    show "connected_space (subtopology X {x \<in> topspace X. f x \<in> C})"
    proof (rule connected_space_monotone_quotient_map_preimage)
      show "monotone_map (subtopology X {x \<in> topspace X. f x \<in> C}) (subtopology Y C) f"
        by (simp add: L monotone_map_restriction)
      show "quotient_map (subtopology X {x \<in> topspace X. f x \<in> C}) (subtopology Y C) f"
      proof (rule continuous_open_imp_quotient_map)
        show "continuous_map (subtopology X {x \<in> topspace X. f x \<in> C}) (subtopology Y C) f"
          using assms continuous_map_from_subtopology continuous_map_in_subtopology by fastforce
      qed (use open_map_restriction assms in fastforce)+
    qed (simp add: C)
  qed auto
next
  assume ?rhs 
  then have "\<forall>y. connectedin Y {y} \<longrightarrow> connectedin X {x \<in> topspace X. f x = y}"
    by (smt (verit) Collect_cong singletonD singletonI)
  then show ?lhs
    by (simp add: fim monotone_map_def)
qed

lemma monotone_closed_map:
  assumes "continuous_map X Y f" "closed_map X Y f" and fim: "f ` (topspace X) = topspace Y"
  shows "monotone_map X Y f \<longleftrightarrow> (\<forall>C. connectedin Y C \<longrightarrow> connectedin X {x \<in> topspace X. f x \<in> C})" 
         (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  show ?rhs
    unfolding connectedin_def
  proof (intro strip conjI)
    fix C
    assume C: "C \<subseteq> topspace Y \<and> connected_space (subtopology Y C)"
    show "connected_space (subtopology X {x \<in> topspace X. f x \<in> C})"
    proof (rule connected_space_monotone_quotient_map_preimage)
      show "monotone_map (subtopology X {x \<in> topspace X. f x \<in> C}) (subtopology Y C) f"
        by (simp add: L monotone_map_restriction)
      show "quotient_map (subtopology X {x \<in> topspace X. f x \<in> C}) (subtopology Y C) f"
      proof (rule continuous_closed_imp_quotient_map)
        show "continuous_map (subtopology X {x \<in> topspace X. f x \<in> C}) (subtopology Y C) f"
          using assms continuous_map_from_subtopology continuous_map_in_subtopology by fastforce
      qed (use closed_map_restriction assms in fastforce)+
    qed (simp add: C)
  qed auto
next
  assume ?rhs 
  then have "\<forall>y. connectedin Y {y} \<longrightarrow> connectedin X {x \<in> topspace X. f x = y}"
    by (smt (verit) Collect_cong singletonD singletonI)
  then show ?lhs
    by (simp add: fim monotone_map_def)
qed

subsection\<open>Other countability properties\<close>

definition second_countable
  where "second_countable X \<equiv>
         \<exists>\<B>. countable \<B> \<and> (\<forall>V \<in> \<B>. openin X V) \<and>
             (\<forall>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U))"

definition first_countable
  where "first_countable X \<equiv>
        \<forall>x \<in> topspace X.
         \<exists>\<B>. countable \<B> \<and> (\<forall>V \<in> \<B>. openin X V) \<and>
             (\<forall>U. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U))"

definition separable_space
  where "separable_space X \<equiv>
        \<exists>C. countable C \<and> C \<subseteq> topspace X \<and> X closure_of C = topspace X"

lemma second_countable:
   "second_countable X \<longleftrightarrow>
        (\<exists>\<B>. countable \<B> \<and> openin X = arbitrary union_of (\<lambda>x. x \<in> \<B>))"
  by (smt (verit) openin_topology_base_unique second_countable_def)

lemma second_countable_subtopology:
  assumes "second_countable X"
  shows "second_countable (subtopology X S)"
proof -
  obtain \<B> where \<B>: "countable \<B>" "\<And>V. V \<in> \<B> \<Longrightarrow> openin X V"
    "\<And>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U)"
    using assms by (auto simp: second_countable_def)
  show ?thesis
    unfolding second_countable_def
  proof (intro exI conjI)
    show "\<forall>V\<in>((\<inter>)S) ` \<B>. openin (subtopology X S) V"
      using openin_subtopology_Int2 \<B> by blast
    show "\<forall>U x. openin (subtopology X S) U \<and> x \<in> U \<longrightarrow> (\<exists>V\<in>((\<inter>)S) ` \<B>. x \<in> V \<and> V \<subseteq> U)"
      using \<B> unfolding openin_subtopology
      by (smt (verit, del_insts) IntI image_iff inf_commute inf_le1 subset_iff)
  qed (use \<B> in auto)
qed


lemma second_countable_discrete_topology:
   "second_countable(discrete_topology U) \<longleftrightarrow> countable U" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then
  obtain \<B> where \<B>: "countable \<B>" "\<And>V. V \<in> \<B> \<Longrightarrow> V \<subseteq> U"
    "\<And>W x. W \<subseteq> U \<and> x \<in> W \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> W)"
    by (auto simp: second_countable_def)
  then have "{x} \<in> \<B>" if "x \<in> U" for x
    by (metis empty_subsetI insertCI insert_subset subset_antisym that)
  then show ?rhs
    by (smt (verit) countable_subset image_subsetI \<open>countable \<B>\<close> countable_image_inj_on [OF _ inj_singleton])
next
  assume ?rhs 
  then show ?lhs
    unfolding second_countable_def
    by (rule_tac x="(\<lambda>x. {x}) ` U" in exI) auto
qed

lemma second_countable_open_map_image:
  assumes "continuous_map X Y f" "open_map X Y f" 
   and fim: "f ` (topspace X) = topspace Y" and "second_countable X"
 shows "second_countable Y"
proof -
  have openXYf: "\<And>U. openin X U \<longrightarrow> openin Y (f ` U)"
    using assms by (auto simp: open_map_def)
  obtain \<B> where \<B>: "countable \<B>" "\<And>V. V \<in> \<B> \<Longrightarrow> openin X V"
    and *: "\<And>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U)"
    using assms by (auto simp: second_countable_def)
  show ?thesis
    unfolding second_countable_def
  proof (intro exI conjI strip)
    fix V y
    assume V: "openin Y V \<and> y \<in> V"
    then obtain x where "x \<in> topspace X" and x: "f x = y"
      by (metis fim image_iff openin_subset subsetD)

    then obtain W where "W\<in>\<B>" "x \<in> W" "W \<subseteq> {x \<in> topspace X. f x \<in> V}"
      using * [of "{x \<in> topspace X. f x \<in> V}" x] V assms openin_continuous_map_preimage 
      by force
    then show "\<exists>W \<in> (image f) ` \<B>. y \<in> W \<and> W \<subseteq> V"
      using x by auto
  qed (use \<B> openXYf in auto)
qed

lemma homeomorphic_space_second_countability:
   "X homeomorphic_space Y \<Longrightarrow> (second_countable X \<longleftrightarrow> second_countable Y)"
  by (meson homeomorphic_eq_everything_map homeomorphic_space homeomorphic_space_sym second_countable_open_map_image)

lemma second_countable_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; second_countable X\<rbrakk> \<Longrightarrow> second_countable Y"
  using hereditary_imp_retractive_property homeomorphic_space_second_countability second_countable_subtopology by blast

lemma second_countable_imp_first_countable:
   "second_countable X \<Longrightarrow> first_countable X"
  by (metis first_countable_def second_countable_def)

lemma first_countable_subtopology:
  assumes "first_countable X"
  shows "first_countable (subtopology X S)"
  unfolding first_countable_def
proof
  fix x
  assume "x \<in> topspace (subtopology X S)"
  then obtain \<B> where "countable \<B>" and \<B>: "\<And>V. V \<in> \<B> \<Longrightarrow> openin X V"
    "\<And>U. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U)"
    using assms first_countable_def by force
  show "\<exists>\<B>. countable \<B> \<and> (\<forall>V\<in>\<B>. openin (subtopology X S) V) \<and> (\<forall>U. openin (subtopology X S) U \<and> x \<in> U \<longrightarrow> (\<exists>V\<in>\<B>. x \<in> V \<and> V \<subseteq> U))"
  proof (intro exI conjI strip)
    show "countable (((\<inter>)S) ` \<B>)"
      using \<open>countable \<B>\<close> by blast
    show "openin (subtopology X S) V" if "V \<in> ((\<inter>)S) ` \<B>" for V
      using \<B> openin_subtopology_Int2 that by fastforce
    show "\<exists>V\<in>((\<inter>)S) ` \<B>. x \<in> V \<and> V \<subseteq> U"
      if "openin (subtopology X S) U \<and> x \<in> U" for U 
      using that \<B>(2) by (clarsimp simp: openin_subtopology) (meson le_infI2)
  qed
qed

lemma first_countable_discrete_topology:
   "first_countable (discrete_topology U)"
  unfolding first_countable_def topspace_discrete_topology openin_discrete_topology
proof
  fix x assume "x \<in> U"
  show "\<exists>\<B>. countable \<B> \<and> (\<forall>V\<in>\<B>. V \<subseteq> U) \<and> (\<forall>Ua. Ua \<subseteq> U \<and> x \<in> Ua \<longrightarrow> (\<exists>V\<in>\<B>. x \<in> V \<and> V \<subseteq> Ua))"
    using \<open>x \<in> U\<close> by (rule_tac x="{{x}}" in exI) auto
qed

lemma first_countable_open_map_image:
  assumes "continuous_map X Y f" "open_map X Y f" 
   and fim: "f ` (topspace X) = topspace Y" and "first_countable X"
 shows "first_countable Y"
  unfolding first_countable_def
proof
  fix y
  assume "y \<in> topspace Y"
  have openXYf: "\<And>U. openin X U \<longrightarrow> openin Y (f ` U)"
    using assms by (auto simp: open_map_def)
  then obtain x where x: "x \<in> topspace X" "f x = y"
    by (metis \<open>y \<in> topspace Y\<close> fim imageE)
  obtain \<B> where \<B>: "countable \<B>" "\<And>V. V \<in> \<B> \<Longrightarrow> openin X V"
    and *: "\<And>U. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U)"
    using assms x first_countable_def by force
  show "\<exists>\<B>. countable \<B> \<and>
              (\<forall>V\<in>\<B>. openin Y V) \<and> (\<forall>U. openin Y U \<and> y \<in> U \<longrightarrow> (\<exists>V\<in>\<B>. y \<in> V \<and> V \<subseteq> U))"
  proof (intro exI conjI strip)
    fix V assume "openin Y V \<and> y \<in> V"
    then have "\<exists>W\<in>\<B>. x \<in> W \<and> W \<subseteq> {x \<in> topspace X. f x \<in> V}"
      using * [of "{x \<in> topspace X. f x \<in> V}"] assms openin_continuous_map_preimage x 
      by fastforce
    then show "\<exists>V' \<in> (image f) ` \<B>. y \<in> V' \<and> V' \<subseteq> V"
      using image_mono x by auto 
  qed (use \<B> openXYf in force)+
qed

lemma homeomorphic_space_first_countability:
  "X homeomorphic_space Y \<Longrightarrow> first_countable X \<longleftrightarrow> first_countable Y"
  by (meson first_countable_open_map_image homeomorphic_eq_everything_map homeomorphic_space homeomorphic_space_sym)

lemma first_countable_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; first_countable X\<rbrakk> \<Longrightarrow> first_countable Y"
  using first_countable_subtopology hereditary_imp_retractive_property homeomorphic_space_first_countability by blast

lemma separable_space_open_subset:
  assumes "separable_space X" "openin X S"
  shows "separable_space (subtopology X S)"
proof -
  obtain C where C: "countable C" "C \<subseteq> topspace X" "X closure_of C = topspace X"
    by (meson assms separable_space_def)
  then have "\<And>x T. \<lbrakk>x \<in> topspace X; x \<in> T; openin (subtopology X S) T\<rbrakk>
           \<Longrightarrow> \<exists>y. y \<in> S \<and> y \<in> C \<and> y \<in> T"
    by (smt (verit) \<open>openin X S\<close> in_closure_of openin_open_subtopology subsetD)
  with C \<open>openin X S\<close> show ?thesis
    unfolding separable_space_def
    by (rule_tac x="S \<inter> C" in exI) (force simp: in_closure_of)
qed

lemma separable_space_continuous_map_image:
  assumes "separable_space X" "continuous_map X Y f" 
    and fim: "f ` (topspace X) = topspace Y"
  shows "separable_space Y"
proof -
  have cont: "\<And>S. f ` (X closure_of S) \<subseteq> Y closure_of f ` S"
    by (simp add: assms continuous_map_image_closure_subset)
  obtain C where C: "countable C" "C \<subseteq> topspace X" "X closure_of C = topspace X"
    by (meson assms separable_space_def)
  then show ?thesis
    unfolding separable_space_def
    by (metis cont fim closure_of_subset_topspace countable_image image_mono subset_antisym)
qed

lemma separable_space_quotient_map_image:
  "\<lbrakk>quotient_map X Y q; separable_space X\<rbrakk> \<Longrightarrow> separable_space Y"
  by (meson quotient_imp_continuous_map quotient_imp_surjective_map separable_space_continuous_map_image)

lemma separable_space_retraction_map_image:
  "\<lbrakk>retraction_map X Y r; separable_space X\<rbrakk> \<Longrightarrow> separable_space Y"
  using retraction_imp_quotient_map separable_space_quotient_map_image by blast

lemma homeomorphic_separable_space:
  "X homeomorphic_space Y \<Longrightarrow> (separable_space X \<longleftrightarrow> separable_space Y)"
  by (meson homeomorphic_eq_everything_map homeomorphic_maps_map homeomorphic_space_def separable_space_continuous_map_image)

lemma separable_space_discrete_topology:
   "separable_space(discrete_topology U) \<longleftrightarrow> countable U"
  by (metis countable_Int2 discrete_topology_closure_of dual_order.refl inf.orderE separable_space_def topspace_discrete_topology)

lemma second_countable_imp_separable_space:
  assumes "second_countable X"
  shows "separable_space X"
proof -
  obtain \<B> where \<B>: "countable \<B>" "\<And>V. V \<in> \<B> \<Longrightarrow> openin X V"
    and *: "\<And>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U)"
    using assms by (auto simp: second_countable_def)
  obtain c where c: "\<And>V. \<lbrakk>V \<in> \<B>; V \<noteq> {}\<rbrakk> \<Longrightarrow> c V \<in> V"
    by (metis all_not_in_conv)
  then have **: "\<And>x. x \<in> topspace X \<Longrightarrow> x \<in> X closure_of c ` (\<B> - {{}})"
    using * by (force simp: closure_of_def)
  show ?thesis
    unfolding separable_space_def
  proof (intro exI conjI)
    show "countable (c ` (\<B>-{{}}))"
      using \<B>(1) by blast
    show "(c ` (\<B>-{{}})) \<subseteq> topspace X"
      using \<B>(2) c openin_subset by fastforce
    show "X closure_of (c ` (\<B>-{{}})) = topspace X"
      by (meson ** closure_of_subset_topspace subsetI subset_antisym)
  qed
qed

lemma second_countable_imp_Lindelof_space:
  assumes "second_countable X"
  shows "Lindelof_space X"
unfolding Lindelof_space_def
proof clarify
  fix \<U>
  assume "\<forall>U \<in> \<U>. openin X U" and UU: "\<Union>\<U> = topspace X"
  obtain \<B> where \<B>: "countable \<B>" "\<And>V. V \<in> \<B> \<Longrightarrow> openin X V"
    and *: "\<And>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V \<in> \<B>. x \<in> V \<and> V \<subseteq> U)"
    using assms by (auto simp: second_countable_def)
  define \<B>' where "\<B>' = {B \<in> \<B>. \<exists>U. U \<in> \<U> \<and> B \<subseteq> U}"
  have \<B>': "countable \<B>'" "\<Union>\<B>' = \<Union>\<U>"
    using \<B> using "*" \<open>\<forall>U\<in>\<U>. openin X U\<close> by (fastforce simp: \<B>'_def)+
  have "\<And>b. \<exists>U. b \<in> \<B>' \<longrightarrow> U \<in> \<U> \<and> b \<subseteq> U" 
    by (simp add: \<B>'_def)
  then obtain G where G: "\<And>b. b \<in> \<B>' \<longrightarrow> G b \<in> \<U> \<and> b \<subseteq> G b" 
    by metis
  with \<B>' UU show "\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<U> \<and> \<Union>\<V> = topspace X"
    by (rule_tac x="G ` \<B>'" in exI) fastforce
qed

subsection \<open>Neigbourhood bases EXTRAS\<close>
(* Neigbourhood bases (useful for "local" properties of various kind).       *)

lemma openin_topology_neighbourhood_base_unique:
   "openin X = arbitrary union_of P \<longleftrightarrow>
        (\<forall>u. P u \<longrightarrow> openin X u) \<and> neighbourhood_base_of P X"
  by (smt (verit, best) open_neighbourhood_base_of openin_topology_base_unique)

lemma neighbourhood_base_at_topology_base:
   "        openin X = arbitrary union_of b
        \<Longrightarrow> (neighbourhood_base_at x P X \<longleftrightarrow>
             (\<forall>w. b w \<and> x \<in> w \<longrightarrow> (\<exists>u v. openin X u \<and> P v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> w)))"
  apply (simp add: neighbourhood_base_at_def)
  by (smt (verit, del_insts) openin_topology_base_unique subset_trans)

lemma neighbourhood_base_of_unlocalized:
  assumes "\<And>S t. P S \<and> openin X t \<and> (t \<noteq> {}) \<and> t \<subseteq> S \<Longrightarrow> P t"
  shows "neighbourhood_base_of P X \<longleftrightarrow>
         (\<forall>x \<in> topspace X. \<exists>u v. openin X u \<and> P v \<and> x \<in> u \<and> u \<subseteq> v \<and> v \<subseteq> topspace X)"
  apply (simp add: neighbourhood_base_of_def)
  by (smt (verit, ccfv_SIG) assms empty_iff neighbourhood_base_at_unlocalized)

lemma neighbourhood_base_at_discrete_topology:
   "neighbourhood_base_at x P (discrete_topology u) \<longleftrightarrow> x \<in> u \<Longrightarrow> P {x}"
  apply (simp add: neighbourhood_base_at_def)
  by (smt (verit) empty_iff empty_subsetI insert_subset singletonI subsetD subset_singletonD)

lemma neighbourhood_base_of_discrete_topology:
   "neighbourhood_base_of P (discrete_topology u) \<longleftrightarrow> (\<forall>x \<in> u. P {x})"
  apply (simp add: neighbourhood_base_of_def)
  using neighbourhood_base_at_discrete_topology[of _ P u]
  by (metis empty_subsetI insert_subset neighbourhood_base_at_def openin_discrete_topology singletonI)

lemma second_countable_neighbourhood_base_alt:
  "second_countable X \<longleftrightarrow> 
  (\<exists>\<B>. countable \<B> \<and> (\<forall>V \<in> \<B>. openin X V) \<and> neighbourhood_base_of (\<lambda>A. A\<in>\<B>) X)"
  by (metis (full_types) openin_topology_neighbourhood_base_unique second_countable)

lemma first_countable_neighbourhood_base_alt:
   "first_countable X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<exists>\<B>. countable \<B> \<and> (\<forall>V \<in> \<B>. openin X V) \<and> neighbourhood_base_at x (\<lambda>V. V \<in> \<B>) X)"
  unfolding first_countable_def
  apply (intro ball_cong refl ex_cong conj_cong)
  by (metis (mono_tags, lifting) open_neighbourhood_base_at)

lemma second_countable_neighbourhood_base:
   "second_countable X \<longleftrightarrow>
        (\<exists>\<B>. countable \<B> \<and> neighbourhood_base_of (\<lambda>V. V \<in> \<B>) X)" (is "?lhs=?rhs")
proof
  assume ?lhs 
  then show ?rhs
    using second_countable_neighbourhood_base_alt by blast
next
  assume ?rhs 
  then obtain \<B> where "countable \<B>"
    and \<B>: "\<And>W x. openin X W \<and> x \<in> W \<longrightarrow> (\<exists>U. openin X U \<and> (\<exists>V. V \<in> \<B> \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W))"
    by (metis neighbourhood_base_of)
  then show ?lhs
    unfolding second_countable_neighbourhood_base_alt neighbourhood_base_of
    apply (rule_tac x="(\<lambda>u. X interior_of u) ` \<B>" in exI)
    by (smt (verit, best) interior_of_eq interior_of_mono countable_image image_iff openin_interior_of)
qed

lemma first_countable_neighbourhood_base:
   "first_countable X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<exists>\<B>. countable \<B> \<and> neighbourhood_base_at x (\<lambda>V. V \<in> \<B>) X)" (is "?lhs=?rhs")
proof
  assume ?lhs 
  then show ?rhs
    by (metis first_countable_neighbourhood_base_alt)
next
  assume R: ?rhs 
  show ?lhs
    unfolding first_countable_neighbourhood_base_alt
  proof
    fix x
    assume "x \<in> topspace X"
    with R obtain \<B> where "countable \<B>" and \<B>: "neighbourhood_base_at x (\<lambda>V. V \<in> \<B>) X"
      by blast
    then
    show "\<exists>\<B>. countable \<B> \<and> Ball \<B> (openin X) \<and> neighbourhood_base_at x (\<lambda>V. V \<in> \<B>) X"
      unfolding neighbourhood_base_at_def
      apply (rule_tac x="(\<lambda>u. X interior_of u) ` \<B>" in exI)
      by (smt (verit, best) countable_image image_iff interior_of_eq interior_of_mono openin_interior_of)
  qed
qed


subsection\<open>$T_0$ spaces and the Kolmogorov quotient\<close>

definition t0_space where
  "t0_space X \<equiv>
     \<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x \<noteq> y \<longrightarrow> (\<exists>U. openin X U \<and> (x \<notin> U \<longleftrightarrow> y \<in> U))"

lemma t0_space_expansive:
   "\<lbrakk>topspace Y = topspace X; \<And>U. openin X U \<Longrightarrow> openin Y U\<rbrakk> \<Longrightarrow> t0_space X \<Longrightarrow> t0_space Y"
  by (metis t0_space_def)

lemma t1_imp_t0_space: "t1_space X \<Longrightarrow> t0_space X"
  by (metis t0_space_def t1_space_def)

lemma t1_eq_symmetric_t0_space_alt:
   "t1_space X \<longleftrightarrow>
      t0_space X \<and>
      (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x \<in> X closure_of {y} \<longleftrightarrow> y \<in> X closure_of {x})"
  apply (simp add: t0_space_def t1_space_def closure_of_def)
  by (smt (verit, best) openin_topspace)

lemma t1_eq_symmetric_t0_space:
  "t1_space X \<longleftrightarrow> t0_space X \<and> (\<forall>x y. x \<in> X closure_of {y} \<longleftrightarrow> y \<in> X closure_of {x})"
  by (auto simp: t1_eq_symmetric_t0_space_alt in_closure_of)

lemma Hausdorff_imp_t0_space:
   "Hausdorff_space X \<Longrightarrow> t0_space X"
  by (simp add: Hausdorff_imp_t1_space t1_imp_t0_space)

lemma t0_space:
   "t0_space X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x \<noteq> y \<longrightarrow> (\<exists>C. closedin X C \<and> (x \<notin> C \<longleftrightarrow> y \<in> C)))"
  unfolding t0_space_def by (metis Diff_iff closedin_def openin_closedin_eq)

lemma homeomorphic_t0_space:
  assumes "X homeomorphic_space Y"
  shows "t0_space X \<longleftrightarrow> t0_space Y"
proof -
  obtain f where f: "homeomorphic_map X Y f" and F: "inj_on f (topspace X)" and "topspace Y = f ` topspace X"
    by (metis assms homeomorphic_imp_injective_map homeomorphic_imp_surjective_map homeomorphic_space)
  with inj_on_image_mem_iff [OF F] 
  show ?thesis
    apply (simp add: t0_space_def homeomorphic_eq_everything_map continuous_map_def open_map_def inj_on_def)
    by (smt (verit)  mem_Collect_eq openin_subset)
qed

lemma t0_space_closure_of_sing:
   "t0_space X \<longleftrightarrow>
    (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. X closure_of {x} = X closure_of {y} \<longrightarrow> x = y)"
  by (simp add: t0_space_def closure_of_def set_eq_iff) (smt (verit))

lemma t0_space_discrete_topology: "t0_space (discrete_topology S)"
  by (simp add: Hausdorff_imp_t0_space)

lemma t0_space_subtopology: "t0_space X \<Longrightarrow> t0_space (subtopology X U)"
  by (simp add: t0_space_def openin_subtopology) (metis Int_iff)

lemma t0_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; t0_space X\<rbrakk> \<Longrightarrow> t0_space Y"
  using hereditary_imp_retractive_property homeomorphic_t0_space t0_space_subtopology by blast

lemma XY: "{x}\<times>{y} = {(x,y)}"
  by simp

lemma t0_space_prod_topologyI: "\<lbrakk>t0_space X; t0_space Y\<rbrakk> \<Longrightarrow> t0_space (prod_topology X Y)"
  by (simp add: t0_space_closure_of_sing closure_of_Times closure_of_eq_empty_gen times_eq_iff flip: XY insert_Times_insert)


lemma t0_space_prod_topology_iff:
   "t0_space (prod_topology X Y) \<longleftrightarrow> topspace (prod_topology X Y) = {} \<or> t0_space X \<and> t0_space Y" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (metis Sigma_empty1 Sigma_empty2 retraction_map_fst retraction_map_snd t0_space_retraction_map_image topspace_prod_topology)
qed (metis empty_iff t0_space_def t0_space_prod_topologyI)

proposition t0_space_product_topology:
   "t0_space (product_topology X I) \<longleftrightarrow>
        topspace(product_topology X I) = {} \<or> (\<forall>i \<in> I. t0_space (X i))" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (meson retraction_map_product_projection t0_space_retraction_map_image)
next
  assume R: ?rhs 
  show ?lhs
  proof (cases "topspace(product_topology X I) = {}")
    case True
    then show ?thesis
      by (simp add: t0_space_def)
  next
    case False
    show ?thesis
      unfolding t0_space
    proof (intro strip)
      fix x y
      assume x: "x \<in> topspace (product_topology X I)"
        and y: "y \<in> topspace (product_topology X I)"
        and "x \<noteq> y"
      then obtain i where "i \<in> I" "x i \<noteq> y i"
        by (metis PiE_ext topspace_product_topology)
      then have "t0_space (X i)"
        using False R by blast
      then obtain U where "closedin (X i) U" "(x i \<notin> U \<longleftrightarrow> y i \<in> U)"
        by (metis t0_space PiE_mem \<open>i \<in> I\<close> \<open>x i \<noteq> y i\<close> topspace_product_topology x y)
      with \<open>i \<in> I\<close> x y show "\<exists>U. closedin (product_topology X I) U \<and> (x \<notin> U) = (y \<in> U)"
        by (rule_tac x="PiE I (\<lambda>j. if j = i then U else topspace(X j))" in exI)
          (simp add: closedin_product_topology PiE_iff)
    qed
  qed
qed


subsection \<open>Kolmogorov quotients\<close>

definition Kolmogorov_quotient 
  where "Kolmogorov_quotient X \<equiv> \<lambda>x. @y. \<forall>U. openin X U \<longrightarrow> (y \<in> U \<longleftrightarrow> x \<in> U)"

lemma Kolmogorov_quotient_in_open:
   "openin X U \<Longrightarrow> (Kolmogorov_quotient X x \<in> U \<longleftrightarrow> x \<in> U)"
  by (smt (verit, ccfv_SIG) Kolmogorov_quotient_def someI_ex)

lemma Kolmogorov_quotient_in_topspace:
   "Kolmogorov_quotient X x \<in> topspace X \<longleftrightarrow> x \<in> topspace X"
  by (simp add: Kolmogorov_quotient_in_open)

lemma Kolmogorov_quotient_in_closed:
  "closedin X C \<Longrightarrow> (Kolmogorov_quotient X x \<in> C \<longleftrightarrow> x \<in> C)"
  unfolding closedin_def
  by (meson DiffD2 DiffI Kolmogorov_quotient_in_open Kolmogorov_quotient_in_topspace in_mono)
 
lemma continuous_map_Kolmogorov_quotient:
   "continuous_map X X (Kolmogorov_quotient X)"
  using Kolmogorov_quotient_in_open openin_subopen openin_subset 
    by (fastforce simp: continuous_map_def Kolmogorov_quotient_in_topspace)

lemma open_map_Kolmogorov_quotient_explicit:
   "openin X U \<Longrightarrow> Kolmogorov_quotient X ` U = Kolmogorov_quotient X ` topspace X \<inter> U"
  using Kolmogorov_quotient_in_open openin_subset by fastforce


lemma open_map_Kolmogorov_quotient_gen:
   "open_map (subtopology X S) (subtopology X (image (Kolmogorov_quotient X) S)) (Kolmogorov_quotient X)"
proof (clarsimp simp: open_map_def openin_subtopology_alt image_iff)
  fix U
  assume "openin X U"
  then have "Kolmogorov_quotient X ` (S \<inter> U) = Kolmogorov_quotient X ` S \<inter> U"
    using Kolmogorov_quotient_in_open [of X U] by auto
  then show "\<exists>V. openin X V \<and> Kolmogorov_quotient X ` (S \<inter> U) = Kolmogorov_quotient X ` S \<inter> V"
    using \<open>openin X U\<close> by blast
qed

lemma open_map_Kolmogorov_quotient:
   "open_map X (subtopology X (Kolmogorov_quotient X ` topspace X))
     (Kolmogorov_quotient X)"
  by (metis open_map_Kolmogorov_quotient_gen subtopology_topspace)

lemma closed_map_Kolmogorov_quotient_explicit:
   "closedin X U \<Longrightarrow> Kolmogorov_quotient X ` U = Kolmogorov_quotient X ` topspace X \<inter> U"
  using closedin_subset by (fastforce simp: Kolmogorov_quotient_in_closed)

lemma closed_map_Kolmogorov_quotient_gen:
   "closed_map (subtopology X S) (subtopology X (Kolmogorov_quotient X ` S))
     (Kolmogorov_quotient X)"
  using Kolmogorov_quotient_in_closed by (force simp: closed_map_def closedin_subtopology_alt image_iff)

lemma closed_map_Kolmogorov_quotient:
   "closed_map X (subtopology X (Kolmogorov_quotient X ` topspace X))
     (Kolmogorov_quotient X)"
  by (metis closed_map_Kolmogorov_quotient_gen subtopology_topspace)

lemma quotient_map_Kolmogorov_quotient_gen:
  "quotient_map (subtopology X S) (subtopology X (Kolmogorov_quotient X ` S)) (Kolmogorov_quotient X)"
proof (intro continuous_open_imp_quotient_map)
  show "continuous_map (subtopology X S) (subtopology X (Kolmogorov_quotient X ` S)) (Kolmogorov_quotient X)"
    by (simp add: continuous_map_Kolmogorov_quotient continuous_map_from_subtopology continuous_map_in_subtopology image_mono)
  show "open_map (subtopology X S) (subtopology X (Kolmogorov_quotient X ` S)) (Kolmogorov_quotient X)"
    using open_map_Kolmogorov_quotient_gen by blast
  show "Kolmogorov_quotient X ` topspace (subtopology X S) = topspace (subtopology X (Kolmogorov_quotient X ` S))"
    by (force simp: Kolmogorov_quotient_in_open)
qed

lemma quotient_map_Kolmogorov_quotient:
   "quotient_map X (subtopology X (Kolmogorov_quotient X ` topspace X)) (Kolmogorov_quotient X)"
  by (metis quotient_map_Kolmogorov_quotient_gen subtopology_topspace)

lemma Kolmogorov_quotient_eq:
   "Kolmogorov_quotient X x = Kolmogorov_quotient X y \<longleftrightarrow>
    (\<forall>U. openin X U \<longrightarrow> (x \<in> U \<longleftrightarrow> y \<in> U))" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis Kolmogorov_quotient_in_open)
next
  assume ?rhs then show ?lhs
    by (simp add: Kolmogorov_quotient_def)
qed

lemma Kolmogorov_quotient_eq_alt:
   "Kolmogorov_quotient X x = Kolmogorov_quotient X y \<longleftrightarrow>
    (\<forall>U. closedin X U \<longrightarrow> (x \<in> U \<longleftrightarrow> y \<in> U))" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis Kolmogorov_quotient_in_closed)
next
  assume ?rhs then show ?lhs
    by (smt (verit) Diff_iff Kolmogorov_quotient_eq closedin_topspace in_mono openin_closedin_eq)
qed

lemma Kolmogorov_quotient_continuous_map:
  assumes "continuous_map X Y f" "t0_space Y" and x: "x \<in> topspace X"
  shows "f (Kolmogorov_quotient X x) = f x"
  using assms unfolding continuous_map_def t0_space_def
  by (smt (verit, ccfv_SIG) Kolmogorov_quotient_in_open Kolmogorov_quotient_in_topspace x mem_Collect_eq)

lemma t0_space_Kolmogorov_quotient:
  "t0_space (subtopology X (Kolmogorov_quotient X ` topspace X))"
  apply (clarsimp simp: t0_space_def )
  by (smt (verit, best) Kolmogorov_quotient_eq imageE image_eqI open_map_Kolmogorov_quotient open_map_def)

lemma Kolmogorov_quotient_id:
   "t0_space X \<Longrightarrow> x \<in> topspace X \<Longrightarrow> Kolmogorov_quotient X x = x"
  by (metis Kolmogorov_quotient_in_open Kolmogorov_quotient_in_topspace t0_space_def)

lemma Kolmogorov_quotient_idemp:
   "Kolmogorov_quotient X (Kolmogorov_quotient X x) = Kolmogorov_quotient X x"
  by (simp add: Kolmogorov_quotient_eq Kolmogorov_quotient_in_open)

lemma retraction_maps_Kolmogorov_quotient:
   "retraction_maps X
     (subtopology X (Kolmogorov_quotient X ` topspace X))
     (Kolmogorov_quotient X) id"
  unfolding retraction_maps_def continuous_map_in_subtopology
  using Kolmogorov_quotient_idemp continuous_map_Kolmogorov_quotient by force

lemma retraction_map_Kolmogorov_quotient:
   "retraction_map X
     (subtopology X (Kolmogorov_quotient X ` topspace X))
     (Kolmogorov_quotient X)"
  using retraction_map_def retraction_maps_Kolmogorov_quotient by blast

lemma retract_of_space_Kolmogorov_quotient_image:
   "Kolmogorov_quotient X ` topspace X retract_of_space X"
proof -
  have "continuous_map X X (Kolmogorov_quotient X)"
    by (simp add: continuous_map_Kolmogorov_quotient)
  then have "Kolmogorov_quotient X ` topspace X \<subseteq> topspace X"
    by (simp add: continuous_map_image_subset_topspace)
  then show ?thesis
    by (meson retract_of_space_retraction_maps retraction_maps_Kolmogorov_quotient)
qed

lemma Kolmogorov_quotient_lift_exists:
  assumes "S \<subseteq> topspace X" "t0_space Y" and f: "continuous_map (subtopology X S) Y f"
  obtains g where "continuous_map (subtopology X (image (Kolmogorov_quotient X) S)) Y g"
              "\<And>x. x \<in> S \<Longrightarrow> g(Kolmogorov_quotient X x) = f x"
proof -
  have "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; Kolmogorov_quotient X x = Kolmogorov_quotient X y\<rbrakk>
            \<Longrightarrow> f x = f y"
    using assms
    apply (simp add: Kolmogorov_quotient_eq t0_space_def continuous_map_def Int_absorb1 openin_subtopology)
    by (smt (verit, del_insts) Int_iff mem_Collect_eq)
  then obtain g where g: "continuous_map (subtopology X (Kolmogorov_quotient X ` S)) Y g"
    "g ` (topspace X \<inter> Kolmogorov_quotient X ` S) = f ` S"
    "\<And>x. x \<in> S \<Longrightarrow> g (Kolmogorov_quotient X x) = f x"
    using quotient_map_lift_exists [OF quotient_map_Kolmogorov_quotient_gen [of X S] f]
    by (metis assms(1) topspace_subtopology topspace_subtopology_subset) 
  show ?thesis
    proof qed (use g in auto)
qed

subsection\<open>Closed diagonals and graphs\<close>

lemma Hausdorff_space_closedin_diagonal:
  "Hausdorff_space X \<longleftrightarrow>
        closedin (prod_topology X X) ((\<lambda>x. (x,x)) ` topspace X)"
proof -
  have \<section>: "((\<lambda>x. (x, x)) ` topspace X) \<subseteq> topspace X \<times> topspace X"
    by auto
  show ?thesis
    apply (simp add: closedin_def openin_prod_topology_alt Hausdorff_space_def disjnt_iff \<section>)
    apply (intro all_cong1 imp_cong ex_cong1 conj_cong refl)
    by (force dest!: openin_subset)+
qed

lemma closed_map_diag_eq:
   "closed_map X (prod_topology X X) (\<lambda>x. (x,x)) \<longleftrightarrow> Hausdorff_space X"
proof -
  have "section_map X (prod_topology X X) (\<lambda>x. (x, x))"
    unfolding section_map_def retraction_maps_def
    by (smt (verit) continuous_map_fst continuous_map_of_fst continuous_map_on_empty continuous_map_pairwise fst_conv fst_diag_fst snd_diag_fst)
  then have "embedding_map X (prod_topology X X) (\<lambda>x. (x, x))"
    by (rule section_imp_embedding_map)
  then show ?thesis
    using Hausdorff_space_closedin_diagonal embedding_imp_closed_map_eq by blast
qed

lemma closedin_continuous_maps_eq:
  assumes "Hausdorff_space Y" and f: "continuous_map X Y f" and g: "continuous_map X Y g"
  shows "closedin X {x \<in> topspace X. f x = g x}"
proof -
  have \<section>:"{x \<in> topspace X. f x = g x} = {x \<in> topspace X. (f x,g x) \<in> ((\<lambda>y.(y,y)) ` topspace Y)}"
    using f continuous_map_image_subset_topspace by fastforce
  show ?thesis
    unfolding \<section>
  proof (intro closedin_continuous_map_preimage)
    show "continuous_map X (prod_topology Y Y) (\<lambda>x. (f x, g x))"
      by (simp add: continuous_map_pairedI f g)
    show "closedin (prod_topology Y Y) ((\<lambda>y. (y, y)) ` topspace Y)"
      using Hausdorff_space_closedin_diagonal assms by blast
  qed
qed

lemma retract_of_space_imp_closedin:
  assumes "Hausdorff_space X" and S: "S retract_of_space X"
  shows "closedin X S"
proof -
  obtain r where r: "continuous_map X (subtopology X S) r" "\<forall>x\<in>S. r x = x"
    using assms by (meson retract_of_space_def)
  then have \<section>: "S = {x \<in> topspace X. r x = x}"
    using S retract_of_space_imp_subset by (force simp: continuous_map_def)
  show ?thesis
    unfolding \<section> 
    using r continuous_map_into_fulltopology assms
    by (force intro: closedin_continuous_maps_eq)
qed

lemma homeomorphic_maps_graph:
   "homeomorphic_maps X (subtopology (prod_topology X Y) ((\<lambda>x. (x, f x)) ` (topspace X)))
         (\<lambda>x. (x, f x)) fst  \<longleftrightarrow>  continuous_map X Y f" 
   (is "?lhs=?rhs")
proof
  assume ?lhs
  then 
  have h: "homeomorphic_map X (subtopology (prod_topology X Y) ((\<lambda>x. (x, f x)) ` topspace X)) (\<lambda>x. (x, f x))"
    by (auto simp: homeomorphic_maps_map)
  have "f = snd \<circ> (\<lambda>x. (x, f x))"
    by force
  then show ?rhs
    by (metis (no_types, lifting) h continuous_map_in_subtopology continuous_map_snd_of homeomorphic_eq_everything_map)
next
  assume ?rhs
  then show ?lhs
    unfolding homeomorphic_maps_def
    by (smt (verit, ccfv_threshold) continuous_map_eq continuous_map_subtopology_fst embedding_map_def embedding_map_graph homeomorphic_eq_everything_map  image_cong image_iff prod.collapse prod.inject)
qed


subsection \<open> KC spaces, those where all compact sets are closed.\<close>

definition kc_space 
  where "kc_space X \<equiv> \<forall>S. compactin X S \<longrightarrow> closedin X S"

lemma kc_space_expansive:
   "\<lbrakk>kc_space X; topspace Y = topspace X; \<And>U. openin X U \<Longrightarrow> openin Y U\<rbrakk>
      \<Longrightarrow> kc_space Y"
  by (meson compactin_contractive kc_space_def topology_finer_closedin)

lemma compactin_imp_closedin_gen:
   "\<lbrakk>kc_space X; compactin X S\<rbrakk> \<Longrightarrow> closedin X S"
  using kc_space_def by blast

lemma Hausdorff_imp_kc_space: "Hausdorff_space X \<Longrightarrow> kc_space X"
  by (simp add: compactin_imp_closedin kc_space_def)

lemma kc_imp_t1_space: "kc_space X \<Longrightarrow> t1_space X"
  by (simp add: finite_imp_compactin kc_space_def t1_space_closedin_finite)

lemma kc_space_subtopology:
   "kc_space X \<Longrightarrow> kc_space(subtopology X S)"
  by (metis closedin_Int_closure_of closure_of_eq compactin_subtopology inf.absorb2 kc_space_def)

lemma kc_space_discrete_topology:
   "kc_space(discrete_topology U)"
  using Hausdorff_space_discrete_topology compactin_imp_closedin kc_space_def by blast

lemma kc_space_continuous_injective_map_preimage:
  assumes "kc_space Y" "continuous_map X Y f" and injf: "inj_on f (topspace X)"
  shows "kc_space X"
  unfolding kc_space_def
proof (intro strip)
  fix S
  assume S: "compactin X S"
  have "S = {x \<in> topspace X. f x \<in> f ` S}"
    using S compactin_subset_topspace inj_onD [OF injf] by blast
  with assms S show "closedin X S"
    by (metis (no_types, lifting) Collect_cong closedin_continuous_map_preimage compactin_imp_closedin_gen image_compactin)
qed

lemma kc_space_retraction_map_image:
  assumes "retraction_map X Y r" "kc_space X"
  shows "kc_space Y"
proof -
  obtain s where s: "continuous_map X Y r" "continuous_map Y X s" "\<And>x. x \<in> topspace Y \<Longrightarrow> r (s x) = x"
    using assms by (force simp: retraction_map_def retraction_maps_def)
  then have inj: "inj_on s (topspace Y)"
    by (metis inj_on_def)
  show ?thesis
    unfolding kc_space_def
  proof (intro strip)
    fix S
    assume S: "compactin Y S"
    have "S = {x \<in> topspace Y. s x \<in> s ` S}"
      using S compactin_subset_topspace inj_onD [OF inj] by blast
    with assms S show "closedin Y S"
      by (meson compactin_imp_closedin_gen inj kc_space_continuous_injective_map_preimage s(2))
  qed
qed

lemma homeomorphic_kc_space:
   "X homeomorphic_space Y \<Longrightarrow> kc_space X \<longleftrightarrow> kc_space Y"
  by (meson homeomorphic_eq_everything_map homeomorphic_space homeomorphic_space_sym kc_space_continuous_injective_map_preimage)

lemma compact_kc_eq_maximal_compact_space:
  assumes "compact_space X"
  shows "kc_space X \<longleftrightarrow>
         (\<forall>Y. topspace Y = topspace X \<and> (\<forall>S. openin X S \<longrightarrow> openin Y S) \<and> compact_space Y \<longrightarrow> Y = X)" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (metis closedin_compact_space compactin_contractive kc_space_def topology_eq topology_finer_closedin)    
next
  assume R: ?rhs
  show ?lhs
    unfolding kc_space_def
  proof (intro strip)
    fix S
    assume S: "compactin X S"
    define Y where 
      "Y \<equiv> topology (arbitrary union_of (finite intersection_of (\<lambda>A. A = topspace X - S \<or> openin X A)
                           relative_to (topspace X)))"
    have "topspace Y = topspace X"
      by (auto simp: Y_def)
    have "openin X T \<longrightarrow> openin Y T" for T
      by (simp add: Y_def arbitrary_union_of_inc finite_intersection_of_inc openin_subbase openin_subset relative_to_subset)
    have "compact_space Y"
    proof (rule Alexander_subbase_alt)
      show "\<exists>\<F>'. finite \<F>' \<and> \<F>' \<subseteq> \<C> \<and> topspace X \<subseteq> \<Union> \<F>'" 
        if \<C>: "\<C> \<subseteq> insert (topspace X - S) (Collect (openin X))" and sub: "topspace X \<subseteq> \<Union>\<C>" for \<C>
      proof -
        consider "\<C> \<subseteq> Collect (openin X)" | \<V> where "\<C> = insert (topspace X - S) \<V>" "\<V> \<subseteq> Collect (openin X)"
          using \<C> by (metis insert_Diff subset_insert_iff)
        then show ?thesis
        proof cases
          case 1
          then show ?thesis
            by (metis assms compact_space_alt mem_Collect_eq subsetD that(2))
        next
          case 2
          then have "S \<subseteq> \<Union>\<V>"
            using S sub compactin_subset_topspace by blast
          with 2 obtain \<F> where "finite \<F> \<and> \<F> \<subseteq> \<V> \<and> S \<subseteq> \<Union>\<F>"
            using S unfolding compactin_def by (metis Ball_Collect)
          with 2 show ?thesis
            by (rule_tac x="insert (topspace X - S) \<F>" in exI) blast
        qed
      qed
    qed (auto simp: Y_def)
    have "Y = X"
      using R \<open>\<And>S. openin X S \<longrightarrow> openin Y S\<close> \<open>compact_space Y\<close> \<open>topspace Y = topspace X\<close> by blast
    moreover have "openin Y (topspace X - S)"
      by (simp add: Y_def arbitrary_union_of_inc finite_intersection_of_inc openin_subbase relative_to_subset)
    ultimately show "closedin X S"
      unfolding closedin_def using S compactin_subset_topspace by blast
  qed
qed

lemma continuous_imp_closed_map_gen:
   "\<lbrakk>compact_space X; kc_space Y; continuous_map X Y f\<rbrakk> \<Longrightarrow> closed_map X Y f"
  by (meson closed_map_def closedin_compact_space compactin_imp_closedin_gen image_compactin)

lemma kc_space_compact_subtopologies:
  "kc_space X \<longleftrightarrow> (\<forall>K. compactin X K \<longrightarrow> kc_space(subtopology X K))" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (auto simp: kc_space_def closedin_closed_subtopology compactin_subtopology)
next
  assume R: ?rhs
  show ?lhs
    unfolding kc_space_def
  proof (intro strip)
    fix K
    assume K: "compactin X K"
    then have "K \<subseteq> topspace X"
      by (simp add: compactin_subset_topspace)
    moreover have "X closure_of K \<subseteq> K"
    proof
      fix x
      assume x: "x \<in> X closure_of K"
      have "kc_space (subtopology X K)"
        by (simp add: R \<open>compactin X K\<close>)
      have "compactin X (insert x K)"
        by (metis K x compactin_Un compactin_sing in_closure_of insert_is_Un)
      then show "x \<in> K"
        by (metis R x K Int_insert_left_if1 closedin_Int_closure_of compact_imp_compactin_subtopology 
            insertCI kc_space_def subset_insertI)
    qed
    ultimately show "closedin X K"
      using closure_of_subset_eq by blast
  qed
qed

lemma kc_space_compact_prod_topology:
  assumes "compact_space X"
  shows "kc_space(prod_topology X X) \<longleftrightarrow> Hausdorff_space X" (is "?lhs=?rhs")
proof
  assume L: ?lhs
  show ?rhs
    unfolding closed_map_diag_eq [symmetric]
  proof (intro continuous_imp_closed_map_gen)
    show "continuous_map X (prod_topology X X) (\<lambda>x. (x, x))"
      by (intro continuous_intros)
  qed (use L assms in auto)
next
  assume ?rhs then show ?lhs
    by (simp add: Hausdorff_imp_kc_space Hausdorff_space_prod_topology)
qed

lemma kc_space_prod_topology:
   "kc_space(prod_topology X X) \<longleftrightarrow> (\<forall>K. compactin X K \<longrightarrow> Hausdorff_space(subtopology X K))" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (metis compactin_subspace kc_space_compact_prod_topology kc_space_subtopology subtopology_Times)
next
  assume R: ?rhs  
  have "kc_space (subtopology (prod_topology X X) L)" if "compactin (prod_topology X X) L" for L 
  proof -
    define K where "K \<equiv> fst ` L \<union> snd ` L"
    have "L \<subseteq> K \<times> K"
      by (force simp: K_def)
    have "compactin X K"
      by (metis K_def compactin_Un continuous_map_fst continuous_map_snd image_compactin that)
    then have "Hausdorff_space (subtopology X K)"
      by (simp add: R)
    then have "kc_space (prod_topology (subtopology X K) (subtopology X K))"
      by (simp add: \<open>compactin X K\<close> compact_space_subtopology kc_space_compact_prod_topology)
    then have "kc_space (subtopology (prod_topology (subtopology X K) (subtopology X K)) L)"
      using kc_space_subtopology by blast
    then show ?thesis
      using \<open>L \<subseteq> K \<times> K\<close> subtopology_Times subtopology_subtopology
      by (metis (no_types, lifting) Sigma_cong inf.absorb_iff2)
  qed
  then show ?lhs
    using kc_space_compact_subtopologies by blast
qed

lemma kc_space_prod_topology_alt:
   "kc_space(prod_topology X X) \<longleftrightarrow>
        kc_space X \<and>
        (\<forall>K. compactin X K \<longrightarrow> Hausdorff_space(subtopology X K))"
  using Hausdorff_imp_kc_space kc_space_compact_subtopologies kc_space_prod_topology by blast

proposition kc_space_prod_topology_left:
  assumes X: "kc_space X" and Y: "Hausdorff_space Y"
  shows "kc_space (prod_topology X Y)"
  unfolding kc_space_def
proof (intro strip)
  fix K
  assume K: "compactin (prod_topology X Y) K"
  then have "K \<subseteq> topspace X \<times> topspace Y"
    using compactin_subset_topspace topspace_prod_topology by blast
  moreover have "\<exists>T. openin (prod_topology X Y) T \<and> (a,b) \<in> T \<and> T \<subseteq> (topspace X \<times> topspace Y) - K"
    if ab: "(a,b) \<in> (topspace X \<times> topspace Y) - K" for a b
  proof - 
    have "compactin Y {b}"
      using that by force
    moreover 
    have "compactin Y {y \<in> topspace Y. (a,y) \<in> K}"
    proof -
      have "compactin (prod_topology X Y) (K \<inter> {a} \<times> topspace Y)"
        using that compact_Int_closedin [OF K]
        by (simp add: X closedin_prod_Times_iff compactin_imp_closedin_gen)
      moreover have "subtopology (prod_topology X Y) (K \<inter> {a} \<times> topspace Y)  homeomorphic_space 
                     subtopology Y {y \<in> topspace Y. (a, y) \<in> K}"
        unfolding homeomorphic_space_def homeomorphic_maps_def
        using that
        apply (rule_tac x="snd" in exI)
        apply (rule_tac x="Pair a" in exI)
        by (force simp: continuous_map_in_subtopology continuous_map_from_subtopology continuous_map_subtopology_snd continuous_map_paired)
      ultimately show ?thesis
        by (simp add: compactin_subspace homeomorphic_compact_space) 
    qed
    moreover have "disjnt {b} {y \<in> topspace Y. (a,y) \<in> K}"
      using ab by force
    ultimately obtain V U where VU: "openin Y V" "openin Y U" "{b} \<subseteq> V" "{y \<in> topspace Y. (a,y) \<in> K} \<subseteq> U" "disjnt V U"
      using Hausdorff_space_compact_separation [OF Y] by blast
    define V' where "V' \<equiv> topspace Y - U"
    have W: "closedin Y V'" "{y \<in> topspace Y. (a,y) \<in> K} \<subseteq> topspace Y - V'" "disjnt V (topspace Y - V')"
      using VU by (auto simp: V'_def disjnt_iff)
    with VU obtain "V \<subseteq> topspace Y" "V' \<subseteq> topspace Y"
      by (meson closedin_subset openin_closedin_eq)
    then obtain "b \<in> V" "disjnt {y \<in> topspace Y. (a,y) \<in> K} V'" "V \<subseteq> V'"
      using VU unfolding disjnt_iff V'_def by force
    define C where "C \<equiv> image fst (K \<inter> {z \<in> topspace(prod_topology X Y). snd z \<in> V'})"
    have "closedin (prod_topology X Y) {z \<in> topspace (prod_topology X Y). snd z \<in> V'}"
        using closedin_continuous_map_preimage \<open>closedin Y V'\<close> continuous_map_snd by blast
    then have "compactin X C"
      unfolding C_def by (meson K compact_Int_closedin continuous_map_fst image_compactin)
    then have "closedin X C"
      using assms by (auto simp: kc_space_def)
    show ?thesis
    proof (intro exI conjI)
      show "openin (prod_topology X Y) ((topspace X - C) \<times> V)"
        by (simp add: VU \<open>closedin X C\<close> openin_diff openin_prod_Times_iff)
      have "a \<notin> C"
        using VU by (auto simp: C_def V'_def)
      then show "(a, b) \<in> (topspace X - C) \<times> V"
        using \<open>a \<notin> C\<close> \<open>b \<in> V\<close> that by blast
      show "(topspace X - C) \<times> V \<subseteq> topspace X \<times> topspace Y - K"
        using \<open>V \<subseteq> V'\<close> \<open>V \<subseteq> topspace Y\<close> 
        apply (simp add: C_def )
        by (smt (verit, ccfv_threshold) DiffE DiffI IntI SigmaE SigmaI image_eqI mem_Collect_eq prod.sel(1) snd_conv subset_iff)
    qed
  qed
  ultimately show "closedin (prod_topology X Y) K"
    by (metis surj_pair closedin_def openin_subopen topspace_prod_topology)
qed

lemma kc_space_prod_topology_right:
   "\<lbrakk>Hausdorff_space X; kc_space Y\<rbrakk> \<Longrightarrow> kc_space (prod_topology X Y)"
  using kc_space_prod_topology_left homeomorphic_kc_space homeomorphic_space_prod_topology_swap by blast


subsection \<open>Regular spaces\<close>

text \<open>Regular spaces are *not* a priori assumed to be Hausdorff or $T_1$\<close>

definition regular_space 
  where "regular_space X \<equiv>
        \<forall>C a. closedin X C \<and> a \<in> topspace X - C
                \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> a \<in> U \<and> C \<subseteq> V \<and> disjnt U V)"

lemma homeomorphic_regular_space_aux:
  assumes hom: "X homeomorphic_space Y" and X: "regular_space X"
  shows "regular_space Y"
proof -
  obtain f g where hmf: "homeomorphic_map X Y f" and hmg: "homeomorphic_map Y X g"
    and fg: "(\<forall>x \<in> topspace X. g(f x) = x) \<and> (\<forall>y \<in> topspace Y. f(g y) = y)"
    using assms X homeomorphic_maps_map homeomorphic_space_def by fastforce
  show ?thesis
    unfolding regular_space_def
  proof clarify
    fix C a
    assume Y: "closedin Y C" "a \<in> topspace Y" and "a \<notin> C"
    then obtain "closedin X (g ` C)" "g a \<in> topspace X" "g a \<notin> g ` C"
      using \<open>closedin Y C\<close> hmg homeomorphic_map_closedness_eq
      by (smt (verit, ccfv_SIG) fg homeomorphic_imp_surjective_map image_iff in_mono) 
    then obtain S T where ST: "openin X S" "openin X T" "g a \<in> S" "g`C \<subseteq> T" "disjnt S T"
      using X unfolding regular_space_def by (metis DiffI)
    then have "openin Y (f`S)" "openin Y (f`T)"
      by (meson hmf homeomorphic_map_openness_eq)+
    moreover have "a \<in> f`S \<and> C \<subseteq> f`T"
      using ST by (smt (verit, best) Y closedin_subset fg image_eqI subset_iff)   
    moreover have "disjnt (f`S) (f`T)"
      using ST by (smt (verit, ccfv_SIG) disjnt_iff fg image_iff openin_subset subsetD)
    ultimately show "\<exists>U V. openin Y U \<and> openin Y V \<and> a \<in> U \<and> C \<subseteq> V \<and> disjnt U V"
      by metis
  qed
qed

lemma homeomorphic_regular_space:
   "X homeomorphic_space Y
        \<Longrightarrow> (regular_space X \<longleftrightarrow> regular_space Y)"
  by (meson homeomorphic_regular_space_aux homeomorphic_space_sym)

lemma regular_space:
   "regular_space X \<longleftrightarrow>
        (\<forall>C a. closedin X C \<and> a \<in> topspace X - C
              \<longrightarrow> (\<exists>U. openin X U \<and> a \<in> U \<and> disjnt C (X closure_of U)))"
  unfolding regular_space_def
proof (intro all_cong1 imp_cong refl ex_cong1)
  fix C a U
  assume C: "closedin X C \<and> a \<in> topspace X - C"
  show "(\<exists>V. openin X U \<and> openin X V \<and> a \<in> U \<and> C \<subseteq> V \<and> disjnt U V)  
    \<longleftrightarrow> (openin X U \<and> a \<in> U \<and> disjnt C (X closure_of U))" (is "?lhs=?rhs")
  proof
    assume ?lhs
    then show ?rhs
      by (smt (verit, best) disjnt_iff in_closure_of subsetD)
  next
    assume R: ?rhs
    then have "disjnt U (topspace X - X closure_of U)"
      by (meson DiffD2 closure_of_subset disjnt_iff openin_subset subsetD)
    moreover have "C \<subseteq> topspace X - X closure_of U"
      by (meson C DiffI R closedin_subset disjnt_iff subset_eq)
    ultimately show ?lhs
      using R by (rule_tac x="topspace X - X closure_of U" in exI) auto
    qed
qed

lemma neighbourhood_base_of_closedin:
  "neighbourhood_base_of (closedin X) X \<longleftrightarrow> regular_space X" (is "?lhs=?rhs")
proof -
  have "?lhs \<longleftrightarrow> (\<forall>W x. openin X W \<and> x \<in> W \<longrightarrow>
                  (\<exists>U. openin X U \<and> (\<exists>V. closedin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W)))"
    by (simp add: neighbourhood_base_of)
  also have "\<dots> \<longleftrightarrow> (\<forall>W x. closedin X W \<and> x \<in> topspace X - W \<longrightarrow>
                     (\<exists>U. openin X U \<and> (\<exists>V. closedin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> topspace X - W)))"
    by (smt (verit) Diff_Diff_Int closedin_def inf.absorb_iff2 openin_closedin_eq)
  also have "\<dots> \<longleftrightarrow> ?rhs"
  proof -
    have \<section>: "(\<exists>V. closedin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> topspace X - W) 
         \<longleftrightarrow> (\<exists>V. openin X V \<and> x \<in> U \<and> W \<subseteq> V \<and> disjnt U V)" (is "?lhs=?rhs")
      if "openin X U"  "closedin X W" "x \<in> topspace X" "x \<notin> W" for W U x
    proof
      assume ?lhs with \<open>closedin X W\<close> show ?rhs
        unfolding closedin_def by (smt (verit) Diff_mono disjnt_Diff1 double_diff subset_eq)
    next
      assume ?rhs with \<open>openin X U\<close> show ?lhs
        unfolding openin_closedin_eq disjnt_def
        by (smt (verit) Diff_Diff_Int Diff_disjoint Diff_eq_empty_iff Int_Diff inf.orderE)
    qed
    show ?thesis
      unfolding regular_space_def
      by (intro all_cong1 ex_cong1 imp_cong refl) (metis \<section> DiffE)
  qed
  finally show ?thesis .
qed

lemma regular_space_discrete_topology:
   "regular_space (discrete_topology S)"
  using neighbourhood_base_of_closedin neighbourhood_base_of_discrete_topology by fastforce

lemma regular_space_subtopology:
 "regular_space X \<Longrightarrow> regular_space (subtopology X S)"
  unfolding regular_space_def openin_subtopology_alt closedin_subtopology_alt disjnt_iff
  by clarsimp (smt (verit, best) inf.orderE inf_le1 le_inf_iff)


lemma regular_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; regular_space X\<rbrakk> \<Longrightarrow> regular_space Y"
  using hereditary_imp_retractive_property homeomorphic_regular_space regular_space_subtopology by blast

lemma regular_t0_imp_Hausdorff_space:
   "\<lbrakk>regular_space X; t0_space X\<rbrakk> \<Longrightarrow> Hausdorff_space X"
  apply (clarsimp simp: regular_space_def t0_space Hausdorff_space_def)
  by (metis disjnt_sym subsetD)

lemma regular_t0_eq_Hausdorff_space:
   "regular_space X \<Longrightarrow> (t0_space X \<longleftrightarrow> Hausdorff_space X)"
  using Hausdorff_imp_t0_space regular_t0_imp_Hausdorff_space by blast

lemma regular_t1_imp_Hausdorff_space:
   "\<lbrakk>regular_space X; t1_space X\<rbrakk> \<Longrightarrow> Hausdorff_space X"
  by (simp add: regular_t0_imp_Hausdorff_space t1_imp_t0_space)

lemma regular_t1_eq_Hausdorff_space:
   "regular_space X \<Longrightarrow> t1_space X \<longleftrightarrow> Hausdorff_space X"
  using regular_t0_imp_Hausdorff_space t1_imp_t0_space t1_or_Hausdorff_space by blast

lemma compact_Hausdorff_imp_regular_space:
  assumes "compact_space X" "Hausdorff_space X"
  shows "regular_space X"
  unfolding regular_space_def
proof clarify
  fix S a
  assume "closedin X S" and "a \<in> topspace X" and "a \<notin> S"
  then show "\<exists>U V. openin X U \<and> openin X V \<and> a \<in> U \<and> S \<subseteq> V \<and> disjnt U V"
    using assms unfolding Hausdorff_space_compact_sets
    by (metis closedin_compact_space compactin_sing disjnt_empty1 insert_subset disjnt_insert1)
qed

lemma regular_space_topspace_empty: "topspace X = {} \<Longrightarrow> regular_space X"
  by (simp add: Hausdorff_space_topspace_empty compact_Hausdorff_imp_regular_space compact_space_topspace_empty)

lemma neighbourhood_base_of_closed_Hausdorff_space:
   "regular_space X \<and> Hausdorff_space X \<longleftrightarrow>
    neighbourhood_base_of (\<lambda>C. closedin X C \<and> Hausdorff_space(subtopology X C)) X" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: Hausdorff_space_subtopology neighbourhood_base_of_closedin)
next
  assume ?rhs then show ?lhs
  by (metis (mono_tags, lifting) Hausdorff_space_closed_neighbourhood neighbourhood_base_of neighbourhood_base_of_closedin openin_topspace)
qed

lemma locally_compact_imp_kc_eq_Hausdorff_space:
   "neighbourhood_base_of (compactin X) X \<Longrightarrow> kc_space X \<longleftrightarrow> Hausdorff_space X"
  by (metis Hausdorff_imp_kc_space kc_imp_t1_space kc_space_def neighbourhood_base_of_closedin neighbourhood_base_of_mono regular_t1_imp_Hausdorff_space)

lemma regular_space_compact_closed_separation:
  assumes X: "regular_space X"
      and S: "compactin X S"
      and T: "closedin X T"
      and "disjnt S T"
    shows "\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V"
proof (cases "S={}")
  case True
  then show ?thesis
    by (meson T closedin_def disjnt_empty1 empty_subsetI openin_empty openin_topspace)
next
  case False
  then have "\<exists>U V. x \<in> S \<longrightarrow> openin X U \<and> openin X V \<and> x \<in> U \<and> T \<subseteq> V \<and> disjnt U V" for x
    using assms unfolding regular_space_def
    by (smt (verit) Diff_iff compactin_subset_topspace disjnt_iff subsetD)
  then obtain U V where UV: "\<And>x. x \<in> S \<Longrightarrow> openin X (U x) \<and> openin X (V x) \<and> x \<in> (U x) \<and> T \<subseteq> (V x) \<and> disjnt (U x) (V x)" 
    by metis
  then obtain \<F> where "finite \<F>" "\<F> \<subseteq> U ` S" "S \<subseteq> \<Union> \<F>"
    using S unfolding compactin_def by (smt (verit) UN_iff image_iff subsetI)
  then obtain K where "finite K" "K \<subseteq> S" and K: "S \<subseteq> \<Union>(U ` K)"
    by (metis finite_subset_image)
  show ?thesis 
  proof (intro exI conjI)
    show "openin X (\<Union>(U ` K))"
      using \<open>K \<subseteq> S\<close> UV by blast
    show "openin X (\<Inter>(V ` K))"
      using False K UV \<open>K \<subseteq> S\<close> \<open>finite K\<close> by blast
    show "S \<subseteq> \<Union>(U ` K)"
      by (simp add: K)
    show "T \<subseteq> \<Inter>(V ` K)"
      using UV \<open>K \<subseteq> S\<close> by blast
    show "disjnt (\<Union>(U ` K)) (\<Inter>(V ` K))"
      by (smt (verit) Inter_iff UN_E UV \<open>K \<subseteq> S\<close> disjnt_iff image_eqI subset_iff)
  qed
qed

lemma regular_space_compact_closed_sets:
   "regular_space X \<longleftrightarrow>
        (\<forall>S T. compactin X S \<and> closedin X T \<and> disjnt S T
           \<longrightarrow> (\<exists>U V. openin X U \<and> openin X V \<and> S \<subseteq> U \<and> T \<subseteq> V \<and> disjnt U V))" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    using regular_space_compact_closed_separation by fastforce
next
  assume R: ?rhs
  show ?lhs
    unfolding regular_space
  proof clarify
    fix S x
    assume "closedin X S" and "x \<in> topspace X" and "x \<notin> S"
    then obtain U V where "openin X U \<and> openin X V \<and> {x} \<subseteq> U \<and> S \<subseteq> V \<and> disjnt U V"
      by (metis R compactin_sing disjnt_empty1 disjnt_insert1)
    then show "\<exists>U. openin X U \<and> x \<in> U \<and> disjnt S (X closure_of U)"
      by (smt (verit, best) disjnt_iff in_closure_of insert_subset subsetD)
  qed
qed


lemma regular_space_prod_topology:
   "regular_space (prod_topology X Y) \<longleftrightarrow>
        topspace X = {} \<or> topspace Y = {} \<or> regular_space X \<and> regular_space Y" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (metis regular_space_retraction_map_image retraction_map_fst retraction_map_snd)
next
  assume R: ?rhs  
  show ?lhs
  proof (cases "topspace X = {} \<or> topspace Y = {}")
    case True
    then show ?thesis
      by (simp add: regular_space_topspace_empty)
  next
    case False
    then have "regular_space X" "regular_space Y"
      using R by auto
    show ?thesis
      unfolding neighbourhood_base_of_closedin [symmetric] neighbourhood_base_of
    proof clarify
      fix W x y
      assume W: "openin (prod_topology X Y) W" and "(x,y) \<in> W"
      then obtain U V where U: "openin X U" "x \<in> U" and V: "openin Y V" "y \<in> V" 
        and "U \<times> V \<subseteq> W"
        by (metis openin_prod_topology_alt)
      obtain D1 C1 where 1: "openin X D1" "closedin X C1" "x \<in> D1" "D1 \<subseteq> C1" "C1 \<subseteq> U"
        by (metis \<open>regular_space X\<close> U neighbourhood_base_of neighbourhood_base_of_closedin)
      obtain D2 C2 where 2: "openin Y D2" "closedin Y C2" "y \<in> D2" "D2 \<subseteq> C2" "C2 \<subseteq> V"
        by (metis \<open>regular_space Y\<close> V neighbourhood_base_of neighbourhood_base_of_closedin)
      show "\<exists>U V. openin (prod_topology X Y) U \<and> closedin (prod_topology X Y) V \<and>
                  (x,y) \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W"
      proof (intro conjI exI)
        show "openin (prod_topology X Y) (D1 \<times> D2)"
          by (simp add: 1 2 openin_prod_Times_iff)
        show "closedin (prod_topology X Y) (C1 \<times> C2)"
          by (simp add: 1 2 closedin_prod_Times_iff)
      qed (use 1 2 \<open>U \<times> V \<subseteq> W\<close> in auto)
    qed
  qed
qed

lemma regular_space_product_topology:
   "regular_space (product_topology X I) \<longleftrightarrow>
    topspace (product_topology X I) = {} \<or> (\<forall>i \<in> I. regular_space (X i))" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (meson regular_space_retraction_map_image retraction_map_product_projection)
next
  assume R: ?rhs  
  show ?lhs
  proof (cases "topspace(product_topology X I) = {}")
    case True
    then show ?thesis
      by (simp add: regular_space_topspace_empty)
  next
    case False
    then obtain x where x: "x \<in> topspace (product_topology X I)"
      by blast
    define \<F> where "\<F> \<equiv> {Pi\<^sub>E I U |U. finite {i \<in> I. U i \<noteq> topspace (X i)}
                        \<and> (\<forall>i\<in>I. openin (X i) (U i))}"
    have oo: "openin (product_topology X I) = arbitrary union_of (\<lambda>W. W \<in> \<F>)"
      by (simp add: \<F>_def openin_product_topology product_topology_base_alt)
    have "\<exists>U V. openin (product_topology X I) U \<and> closedin (product_topology X I) V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> Pi\<^sub>E I W"
      if fin: "finite {i \<in> I. W i \<noteq> topspace (X i)}" 
        and opeW: "\<And>k. k \<in> I \<Longrightarrow> openin (X k) (W k)" and x: "x \<in> PiE I W" for W x
    proof -
      have "\<And>i. i \<in> I \<Longrightarrow> \<exists>U V. openin (X i) U \<and> closedin (X i) V \<and> x i \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W i"
        by (metis False PiE_iff R neighbourhood_base_of neighbourhood_base_of_closedin opeW x)
      then obtain U C where UC: 
        "\<And>i. i \<in> I \<Longrightarrow> openin (X i) (U i) \<and> closedin (X i) (C i) \<and> x i \<in> U i \<and> U i \<subseteq> C i \<and> C i \<subseteq> W i"
        by metis
      define PI where "PI \<equiv> \<lambda>V. PiE I (\<lambda>i. if W i = topspace(X i) then topspace(X i) else V i)"
      show ?thesis
      proof (intro conjI exI)
        have "\<forall>i\<in>I. W i \<noteq> topspace (X i) \<longrightarrow> openin (X i) (U i)"
          using UC by force
        with fin show "openin (product_topology X I) (PI U)"
          by (simp add: Collect_mono_iff PI_def openin_PiE_gen rev_finite_subset)
        show "closedin (product_topology X I) (PI C)"
          by (simp add: UC closedin_product_topology PI_def)
        show "x \<in> PI U"
          using UC x by (fastforce simp: PI_def)
        show "PI U \<subseteq> PI C"
          by (smt (verit) UC Orderings.order_eq_iff PiE_mono PI_def)
        show "PI C \<subseteq> Pi\<^sub>E I W"
          by (simp add: UC PI_def subset_PiE)
      qed
    qed
    then have "neighbourhood_base_of (closedin (product_topology X I)) (product_topology X I)"
      unfolding neighbourhood_base_of_topology_base [OF oo] by (force simp: \<F>_def)
    then show ?thesis
      by (simp add: neighbourhood_base_of_closedin)
  qed
qed

lemma closed_map_paired_gen_aux:
  assumes "regular_space Y" and f: "closed_map Z X f" and g: "closed_map Z Y g"
    and clo: "\<And>y. y \<in> topspace X \<Longrightarrow> closedin Z {x \<in> topspace Z. f x = y}"
    and contg: "continuous_map Z Y g"
  shows "closed_map Z (prod_topology X Y) (\<lambda>x. (f x, g x))"
  unfolding closed_map_def
proof (intro strip)
  fix C assume "closedin Z C"
  then have "C \<subseteq> topspace Z"
    by (simp add: closedin_subset)
  have "f ` topspace Z \<subseteq> topspace X" "g ` topspace Z \<subseteq> topspace Y"
    by (simp_all add: assms closed_map_imp_subset_topspace)
  show "closedin (prod_topology X Y) ((\<lambda>x. (f x, g x)) ` C)"
    unfolding closedin_def topspace_prod_topology
  proof (intro conjI)
    have "closedin Y (g ` C)"
      using \<open>closedin Z C\<close> assms(3) closed_map_def by blast
    with assms show "(\<lambda>x. (f x, g x)) ` C \<subseteq> topspace X \<times> topspace Y"
      using \<open>C \<subseteq> topspace Z\<close> \<open>f ` topspace Z \<subseteq> topspace X\<close> continuous_map_closedin subsetD by fastforce
    have *: "\<exists>T. openin (prod_topology X Y) T \<and> (y1,y2) \<in> T \<and> T \<subseteq> topspace X \<times> topspace Y - (\<lambda>x. (f x, g x)) ` C"
      if "(y1,y2) \<notin> (\<lambda>x. (f x, g x)) ` C" and y1: "y1 \<in> topspace X" and y2: "y2 \<in> topspace Y"
      for y1 y2
    proof -
      define A where "A \<equiv> topspace Z - (C \<inter> {x \<in> topspace Z. f x = y1})"
      have A: "openin Z A" "{x \<in> topspace Z. g x = y2} \<subseteq> A"
        using that \<open>closedin Z C\<close> clo that(2) by (auto simp: A_def)
      obtain V0 where "openin Y V0 \<and> y2 \<in> V0" and UA: "{x \<in> topspace Z. g x \<in> V0} \<subseteq> A"
        using g A y2 unfolding closed_map_fibre_neighbourhood by blast
      then obtain V V' where VV: "openin Y V \<and> closedin Y V' \<and> y2 \<in> V \<and> V \<subseteq> V'" and "V' \<subseteq> V0"
        by (metis (no_types, lifting) \<open>regular_space Y\<close> neighbourhood_base_of neighbourhood_base_of_closedin)
      with UA have subA: "{x \<in> topspace Z. g x \<in> V'} \<subseteq> A"
        by blast
      show ?thesis
      proof -
        define B where "B \<equiv> topspace Z - (C \<inter> {x \<in> topspace Z. g x \<in> V'})"
        have "openin Z B"
          using VV \<open>closedin Z C\<close> contg by (fastforce simp: B_def continuous_map_closedin)
        have "{x \<in> topspace Z. f x = y1} \<subseteq> B"
          using A_def subA by (auto simp: A_def B_def)
        then obtain U where "openin X U" "y1 \<in> U" and subB: "{x \<in> topspace Z. f x \<in> U} \<subseteq> B"
          using \<open>openin Z B\<close> y1 f unfolding closed_map_fibre_neighbourhood by meson
        show ?thesis
        proof (intro conjI exI)
          show "openin (prod_topology X Y) (U \<times> V)"
            by (metis VV \<open>openin X U\<close> openin_prod_Times_iff)
          show "(y1, y2) \<in> U \<times> V"
            by (simp add: VV \<open>y1 \<in> U\<close>)
          show "U \<times> V \<subseteq> topspace X \<times> topspace Y - (\<lambda>x. (f x, g x)) ` C"
            using VV \<open>C \<subseteq> topspace Z\<close> \<open>openin X U\<close> subB
            by (force simp: image_iff B_def subset_iff dest: openin_subset)
        qed
      qed
    qed
    then show "openin (prod_topology X Y) (topspace X \<times> topspace Y - (\<lambda>x. (f x, g x)) ` C)"
      by (smt (verit, ccfv_threshold) Diff_iff SigmaE openin_subopen)
  qed
qed


lemma closed_map_paired_gen:
  assumes f: "closed_map Z X f" and g: "closed_map Z Y g"
  and D: "(regular_space X \<and> continuous_map Z X f \<and> (\<forall>z \<in> topspace Y. closedin Z {x \<in> topspace Z. g x = z})
         \<or> regular_space Y \<and> continuous_map Z Y g \<and> (\<forall>y \<in> topspace X. closedin Z {x \<in> topspace Z. f x = y}))"
         (is "?RSX \<or> ?RSY")
       shows "closed_map Z (prod_topology X Y) (\<lambda>x. (f x, g x))"
  using D
proof
  assume RSX: ?RSX
  have eq: "(\<lambda>x. (f x, g x)) = (\<lambda>(x,y). (y,x)) \<circ> (\<lambda>x. (g x, f x))"
    by auto
  show ?thesis
    unfolding eq
  proof (rule closed_map_compose)
    show "closed_map Z (prod_topology Y X) (\<lambda>x. (g x, f x))"
      using RSX closed_map_paired_gen_aux f g by fastforce
    show "closed_map (prod_topology Y X) (prod_topology X Y) (\<lambda>(x, y). (y, x))"
      using homeomorphic_imp_closed_map homeomorphic_map_swap by blast
  qed
qed (blast intro: assms closed_map_paired_gen_aux)

lemma closed_map_paired:
  assumes "closed_map Z X f" and contf: "continuous_map Z X f"
          "closed_map Z Y g" and contg: "continuous_map Z Y g"
  and D: "t1_space X \<and> regular_space Y \<or> regular_space X \<and> t1_space Y"
  shows "closed_map Z (prod_topology X Y) (\<lambda>x. (f x, g x))"
proof (rule closed_map_paired_gen)
  show "regular_space X \<and> continuous_map Z X f \<and> (\<forall>z\<in>topspace Y. closedin Z {x \<in> topspace Z. g x = z}) \<or> regular_space Y \<and> continuous_map Z Y g \<and> (\<forall>y\<in>topspace X. closedin Z {x \<in> topspace Z. f x = y})"
    using D contf contg
    by (smt (verit, del_insts) Collect_cong closedin_continuous_map_preimage t1_space_closedin_singleton singleton_iff)
qed (use assms in auto)

lemma closed_map_pairwise:
  assumes  "closed_map Z X (fst \<circ> f)" "continuous_map Z X (fst \<circ> f)"
    "closed_map Z Y (snd \<circ> f)" "continuous_map Z Y (snd \<circ> f)"
    "t1_space X \<and> regular_space Y \<or> regular_space X \<and> t1_space Y"
  shows "closed_map Z (prod_topology X Y) f"
proof -
  have "closed_map Z (prod_topology X Y) (\<lambda>a. ((fst \<circ> f) a, (snd \<circ> f) a))"
    using assms closed_map_paired by blast
  then show ?thesis
    by auto
qed


lemma tube_lemma_right:
  assumes W: "openin (prod_topology X Y) W" and C: "compactin Y C" 
    and x: "x \<in> topspace X" and subW: "{x} \<times> C \<subseteq> W"
  shows "\<exists>U V. openin X U \<and> openin Y V \<and> x \<in> U \<and> C \<subseteq> V \<and> U \<times> V \<subseteq> W"
proof (cases "C = {}")
  case True
  with x show ?thesis by auto
next
  case False
  have "\<exists>U V. openin X U \<and> openin Y V \<and> x \<in> U \<and> y \<in> V \<and> U \<times> V \<subseteq> W" 
    if "y \<in> C" for y
    using W openin_prod_topology_alt subW subsetD that by fastforce
  then obtain U V where UV: "\<And>y. y \<in> C \<Longrightarrow> openin X (U y) \<and> openin Y (V y) \<and> x \<in> U y \<and> y \<in> V y \<and> U y \<times> V y \<subseteq> W" 
    by metis
  then obtain D where D: "finite D" "D \<subseteq> C" "C \<subseteq> \<Union> (V ` D)"
    using compactinD [OF C, of "V`C"]
    by (smt (verit) UN_I finite_subset_image imageE subsetI)
  show ?thesis
  proof (intro exI conjI)
    show "openin X (\<Inter> (U ` D))" "openin Y (\<Union> (V ` D))"
      using D False UV by blast+
    show "x \<in> \<Inter> (U ` D)" "C \<subseteq> \<Union> (V ` D)" "\<Inter> (U ` D) \<times> \<Union> (V ` D) \<subseteq> W"
      using D UV by force+
  qed
qed


lemma closed_map_fst:
  assumes "compact_space Y"
  shows "closed_map (prod_topology X Y) X fst"
proof -
  have *: "{x \<in> topspace X \<times> topspace Y. fst x \<in> U} = U \<times> topspace Y"
    if "U \<subseteq> topspace X" for U
    using that by force
  have **: "\<And>U y. \<lbrakk>openin (prod_topology X Y) U; y \<in> topspace X;
            {x \<in> topspace X \<times> topspace Y. fst x = y} \<subseteq> U\<rbrakk>
           \<Longrightarrow> \<exists>V. openin X V \<and> y \<in> V \<and> V \<times> topspace Y \<subseteq> U"
    using tube_lemma_right[of X Y _ "topspace Y"] assms compact_space_def
    by force
  show ?thesis
    unfolding closed_map_fibre_neighbourhood
    by (force simp: * openin_subset cong: conj_cong intro: **)
qed

lemma closed_map_snd:
  assumes "compact_space X"
  shows "closed_map (prod_topology X Y) Y snd"
proof -
  have "snd = fst o prod.swap"
    by force
  moreover have "closed_map (prod_topology X Y) Y (fst o prod.swap)"
  proof (rule closed_map_compose)
    show "closed_map (prod_topology X Y) (prod_topology Y X) prod.swap"
      by (metis (no_types, lifting) homeomorphic_imp_closed_map homeomorphic_map_eq homeomorphic_map_swap prod.swap_def split_beta)
    show "closed_map (prod_topology Y X) Y fst"
      by (simp add: closed_map_fst assms)
  qed
  ultimately show ?thesis
    by metis
qed

lemma closed_map_paired_closed_map_right:
   "\<lbrakk>closed_map X Y f; regular_space X;
     \<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}\<rbrakk>
    \<Longrightarrow> closed_map X (prod_topology X Y) (\<lambda>x. (x, f x))"
  by (rule closed_map_paired_gen [OF closed_map_id, unfolded id_def]) auto

lemma closed_map_paired_closed_map_left:
  assumes "closed_map X Y f"  "regular_space X"
    "\<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}"
  shows "closed_map X (prod_topology Y X) (\<lambda>x. (f x, x))"
proof -
  have eq: "(\<lambda>x. (f x, x)) = (\<lambda>(x,y). (y,x)) \<circ> (\<lambda>x. (x, f x))"
    by auto
  show ?thesis
    unfolding eq
  proof (rule closed_map_compose)
    show "closed_map X (prod_topology X Y) (\<lambda>x. (x, f x))"
      by (simp add: assms closed_map_paired_closed_map_right)
    show "closed_map (prod_topology X Y) (prod_topology Y X) (\<lambda>(x, y). (y, x))"
      using homeomorphic_imp_closed_map homeomorphic_map_swap by blast
  qed
qed

lemma closed_map_imp_closed_graph:
  assumes "closed_map X Y f" "regular_space X"
          "\<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}"
  shows "closedin (prod_topology X Y) ((\<lambda>x. (x, f x)) ` topspace X)"
  using assms closed_map_def closed_map_paired_closed_map_right by blast

lemma proper_map_paired_closed_map_right:
  assumes "closed_map X Y f" "regular_space X"
    "\<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}"
  shows "proper_map X (prod_topology X Y) (\<lambda>x. (x, f x))"
  by (simp add: assms closed_injective_imp_proper_map inj_on_def closed_map_paired_closed_map_right)

lemma proper_map_paired_closed_map_left:
  assumes "closed_map X Y f" "regular_space X"
    "\<And>y. y \<in> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x = y}"
  shows "proper_map X (prod_topology Y X) (\<lambda>x. (f x, x))"
  by (simp add: assms closed_injective_imp_proper_map inj_on_def closed_map_paired_closed_map_left)

proposition regular_space_continuous_proper_map_image:
  assumes "regular_space X" and contf: "continuous_map X Y f" and pmapf: "proper_map X Y f"
    and fim: "f ` (topspace X) = topspace Y"
  shows "regular_space Y"
  unfolding regular_space_def
proof clarify
  fix C y
  assume "closedin Y C" and "y \<in> topspace Y" and "y \<notin> C"
  have "closed_map X Y f" "(\<forall>y \<in> topspace Y. compactin X {x \<in> topspace X. f x = y})"
    using pmapf proper_map_def by force+
  moreover have "closedin X {z \<in> topspace X. f z \<in> C}"
    using \<open>closedin Y C\<close> contf continuous_map_closedin by fastforce
  moreover have "disjnt {z \<in> topspace X. f z = y} {z \<in> topspace X. f z \<in> C}"
    using \<open>y \<notin> C\<close> disjnt_iff by blast
  ultimately
  obtain U V where UV: "openin X U" "openin X V" "{z \<in> topspace X. f z = y} \<subseteq> U" "{z \<in> topspace X. f z \<in> C} \<subseteq> V"
                  and dUV: "disjnt U V"
    using \<open>y \<in> topspace Y\<close> \<open>regular_space X\<close> unfolding regular_space_compact_closed_sets
    by meson

  have *: "\<And>U T. openin X U \<and> T \<subseteq> topspace Y \<and> {x \<in> topspace X. f x \<in> T} \<subseteq> U \<longrightarrow>
         (\<exists>V. openin Y V \<and> T \<subseteq> V \<and> {x \<in> topspace X. f x \<in> V} \<subseteq> U)"
   using \<open>closed_map X Y f\<close> unfolding closed_map_preimage_neighbourhood by blast
  obtain V1 where V1: "openin Y V1 \<and> y \<in> V1" and sub1: "{x \<in> topspace X. f x \<in> V1} \<subseteq> U"
    using * [of U "{y}"] UV \<open>y \<in> topspace Y\<close> by auto
  moreover
  obtain V2 where "openin Y V2 \<and> C \<subseteq> V2" and sub2: "{x \<in> topspace X. f x \<in> V2} \<subseteq> V"
    by (smt (verit, ccfv_SIG) * UV \<open>closedin Y C\<close> closedin_subset mem_Collect_eq subset_iff)
  moreover have "disjnt V1 V2"
  proof -
    have "\<And>x. \<lbrakk>\<forall>x. x \<in> U \<longrightarrow> x \<notin> V; x \<in> V1; x \<in> V2\<rbrakk> \<Longrightarrow> False"
      by (smt (verit) V1 fim image_iff mem_Collect_eq openin_subset sub1 sub2 subsetD)
    with dUV show ?thesis by (auto simp: disjnt_iff)
  qed
  ultimately show "\<exists>U V. openin Y U \<and> openin Y V \<and> y \<in> U \<and> C \<subseteq> V \<and> disjnt U V"
    by meson
qed

lemma regular_space_perfect_map_image:
   "\<lbrakk>regular_space X; perfect_map X Y f\<rbrakk> \<Longrightarrow> regular_space Y"
  by (meson perfect_map_def regular_space_continuous_proper_map_image)

proposition regular_space_perfect_map_image_eq:
  assumes "Hausdorff_space X" and perf: "perfect_map X Y f"
  shows "regular_space X \<longleftrightarrow> regular_space Y" (is "?lhs=?rhs")
proof
  assume ?lhs
  then show ?rhs
    using perf regular_space_perfect_map_image by blast
next
  assume R: ?rhs  
  have "continuous_map X Y f" "proper_map X Y f" and fim: "f ` (topspace X) = topspace Y"
    using perf by (auto simp: perfect_map_def)
  then have "closed_map X Y f" and preYf: "(\<forall>y \<in> topspace Y. compactin X {x \<in> topspace X. f x = y})"
    by (simp_all add: proper_map_def)
  show ?lhs
    unfolding regular_space_def
  proof clarify
    fix C x
    assume "closedin X C" and "x \<in> topspace X" and "x \<notin> C"
    obtain U1 U2 where "openin X U1" "openin X U2" "{x} \<subseteq> U1" and "disjnt U1 U2"
      and subV: "C \<inter> {z \<in> topspace X. f z = f x} \<subseteq> U2"
    proof (rule Hausdorff_space_compact_separation [of X "{x}" "C \<inter> {z \<in> topspace X. f z = f x}", OF \<open>Hausdorff_space X\<close>])
      show "compactin X {x}"
        by (simp add: \<open>x \<in> topspace X\<close>)
      show "compactin X (C \<inter> {z \<in> topspace X. f z = f x})"
        using \<open>closedin X C\<close> fim \<open>x \<in> topspace X\<close> closed_Int_compactin preYf by fastforce
      show "disjnt {x} (C \<inter> {z \<in> topspace X. f z = f x})"
        using \<open>x \<notin> C\<close> by force
    qed
    have "closedin Y (f ` (C - U2))"
      using \<open>closed_map X Y f\<close> \<open>closedin X C\<close> \<open>openin X U2\<close> closed_map_def by blast
    moreover
    have "f x \<in> topspace Y - f ` (C - U2)"
      using \<open>closedin X C\<close> \<open>continuous_map X Y f\<close> \<open>x \<in> topspace X\<close> closedin_subset continuous_map_def subV by fastforce
    ultimately
    obtain V1 V2 where VV: "openin Y V1" "openin Y V2" "f x \<in> V1" 
                and subV2: "f ` (C - U2) \<subseteq> V2" and "disjnt V1 V2"
      by (meson R regular_space_def)
    show "\<exists>U U'. openin X U \<and> openin X U' \<and> x \<in> U \<and> C \<subseteq> U' \<and> disjnt U U'"
    proof (intro exI conjI)
      show "openin X (U1 \<inter> {x \<in> topspace X. f x \<in> V1})"
        using VV(1) \<open>continuous_map X Y f\<close> \<open>openin X U1\<close> continuous_map by fastforce
      show "openin X (U2 \<union> {x \<in> topspace X. f x \<in> V2})"
        using VV(2) \<open>continuous_map X Y f\<close> \<open>openin X U2\<close> continuous_map by fastforce
      show "x \<in> U1 \<inter> {x \<in> topspace X. f x \<in> V1}"
        using VV(3) \<open>x \<in> topspace X\<close> \<open>{x} \<subseteq> U1\<close> by auto
      show "C \<subseteq> U2 \<union> {x \<in> topspace X. f x \<in> V2}"
        using \<open>closedin X C\<close> closedin_subset subV2 by auto
      show "disjnt (U1 \<inter> {x \<in> topspace X. f x \<in> V1}) (U2 \<union> {x \<in> topspace X. f x \<in> V2})"
        using \<open>disjnt U1 U2\<close> \<open>disjnt V1 V2\<close> by (auto simp: disjnt_iff)
    qed
  qed
qed



subsection\<open>Locally compact spaces\<close>

definition locally_compact_space 
  where "locally_compact_space X \<equiv>
    \<forall>x \<in> topspace X. \<exists>U K. openin X U \<and> compactin X K \<and> x \<in> U \<and> U \<subseteq> K"

lemma homeomorphic_locally_compact_spaceD:
  assumes X: "locally_compact_space X" and "X homeomorphic_space Y"
  shows "locally_compact_space Y"
proof -
  obtain f where hmf: "homeomorphic_map X Y f"
    using assms homeomorphic_space by blast
  then have eq: "topspace Y = f ` (topspace X)"
    by (simp add: homeomorphic_imp_surjective_map)
  have "\<exists>V K. openin Y V \<and> compactin Y K \<and> f x \<in> V \<and> V \<subseteq> K"
    if "x \<in> topspace X" "openin X U" "compactin X K" "x \<in> U" "U \<subseteq> K" for x U K
    using that 
    by (meson hmf homeomorphic_map_compactness_eq homeomorphic_map_openness_eq image_mono image_eqI)
  with X show ?thesis
    by (smt (verit) eq image_iff locally_compact_space_def)
qed

lemma homeomorphic_locally_compact_space:
  assumes "X homeomorphic_space Y"
  shows "locally_compact_space X \<longleftrightarrow> locally_compact_space Y"
  by (meson assms homeomorphic_locally_compact_spaceD homeomorphic_space_sym)

lemma locally_compact_space_retraction_map_image:
  assumes "retraction_map X Y r" and X: "locally_compact_space X"
  shows "locally_compact_space Y"
proof -
  obtain s where s: "retraction_maps X Y r s"
    using assms retraction_map_def by blast
  obtain T where "T retract_of_space X" and Teq: "T = s ` topspace Y"
    using retraction_maps_section_image1 s by blast
  then obtain r where r: "continuous_map X (subtopology X T) r" "\<forall>x\<in>T. r x = x"
    by (meson retract_of_space_def)
  have "locally_compact_space (subtopology X T)"
    unfolding locally_compact_space_def openin_subtopology_alt
  proof clarsimp
    fix x
    assume "x \<in> topspace X" "x \<in> T"
    obtain U K where UK: "openin X U \<and> compactin X K \<and> x \<in> U \<and> U \<subseteq> K"
      by (meson X \<open>x \<in> topspace X\<close> locally_compact_space_def)
    then have "compactin (subtopology X T) (r ` K) \<and> T \<inter> U \<subseteq> r ` K"
      by (smt (verit) IntD1 image_compactin image_iff inf_le2 r subset_iff)
    then show "\<exists>U. openin X U \<and> (\<exists>K. compactin (subtopology X T) K \<and> x \<in> U \<and> T \<inter> U \<subseteq> K)"
      using UK by auto
  qed
  with Teq show ?thesis
    using homeomorphic_locally_compact_space retraction_maps_section_image2 s by blast
qed

lemma compact_imp_locally_compact_space:
   "compact_space X \<Longrightarrow> locally_compact_space X"
  using compact_space_def locally_compact_space_def by blast

lemma neighbourhood_base_imp_locally_compact_space:
   "neighbourhood_base_of (compactin X) X \<Longrightarrow> locally_compact_space X"
  by (metis locally_compact_space_def neighbourhood_base_of openin_topspace)

lemma locally_compact_imp_neighbourhood_base:
  assumes loc: "locally_compact_space X" and reg: "regular_space X"
  shows "neighbourhood_base_of (compactin X) X"
  unfolding neighbourhood_base_of
proof clarify
  fix W x
  assume "openin X W" and "x \<in> W"
  then obtain U K where "openin X U" "compactin X K" "x \<in> U" "U \<subseteq> K"
    by (metis loc locally_compact_space_def openin_subset subsetD)
  moreover have "openin X (U \<inter> W) \<and> x \<in> U \<inter> W"
    using \<open>openin X W\<close> \<open>x \<in> W\<close> \<open>openin X U\<close> \<open>x \<in> U\<close> by blast
  then have "\<exists>u' v. openin X u' \<and> closedin X v \<and> x \<in> u' \<and> u' \<subseteq> v \<and> v \<subseteq> U \<and> v \<subseteq> W"
    using reg
    by (metis le_infE neighbourhood_base_of neighbourhood_base_of_closedin)
  then show "\<exists>U V. openin X U \<and> compactin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W"
    by (meson \<open>U \<subseteq> K\<close> \<open>compactin X K\<close> closed_compactin subset_trans)
qed

lemma Hausdorff_regular: "\<lbrakk>Hausdorff_space X; neighbourhood_base_of (compactin X) X\<rbrakk> \<Longrightarrow> regular_space X"
  by (metis compactin_imp_closedin neighbourhood_base_of_closedin neighbourhood_base_of_mono)

lemma locally_compact_Hausdorff_imp_regular_space: 
  assumes loc: "locally_compact_space X" and "Hausdorff_space X"
  shows "regular_space X"
  unfolding neighbourhood_base_of_closedin [symmetric] neighbourhood_base_of
proof clarify
  fix W x
  assume "openin X W" and "x \<in> W"
  then have "x \<in> topspace X"
    using openin_subset by blast 
  then obtain U K where "openin X U" "compactin X K" and UK: "x \<in> U" "U \<subseteq> K"
    by (meson loc locally_compact_space_def)
  with \<open>Hausdorff_space X\<close> have "regular_space (subtopology X K)"
    using Hausdorff_space_subtopology compact_Hausdorff_imp_regular_space compact_space_subtopology by blast
  then have "\<exists>U' V'. openin (subtopology X K) U' \<and> closedin (subtopology X K) V' \<and> x \<in> U' \<and> U' \<subseteq> V' \<and> V' \<subseteq> K \<inter> W"
    unfolding neighbourhood_base_of_closedin [symmetric] neighbourhood_base_of
    by (meson IntI \<open>U \<subseteq> K\<close> \<open>openin X W\<close> \<open>x \<in> U\<close> \<open>x \<in> W\<close> openin_subtopology_Int2 subsetD)
  then obtain V C where "openin X V" "closedin X C" and VC: "x \<in> K \<inter> V" "K \<inter> V \<subseteq> K \<inter> C" "K \<inter> C \<subseteq> K \<inter> W"
    by (metis Int_commute closedin_subtopology openin_subtopology)
  show "\<exists>U V. openin X U \<and> closedin X V \<and> x \<in> U \<and> U \<subseteq> V \<and> V \<subseteq> W"
  proof (intro conjI exI)
    show "openin X (U \<inter> V)"
      using \<open>openin X U\<close> \<open>openin X V\<close> by blast
    show "closedin X (K \<inter> C)"
      using \<open>closedin X C\<close> \<open>compactin X K\<close> compactin_imp_closedin \<open>Hausdorff_space X\<close> by blast
  qed (use UK VC in auto)
qed

lemma locally_compact_space_neighbourhood_base:
  "Hausdorff_space X \<or> regular_space X
        \<Longrightarrow> locally_compact_space X \<longleftrightarrow> neighbourhood_base_of (compactin X) X"
  by (metis locally_compact_imp_neighbourhood_base locally_compact_Hausdorff_imp_regular_space 
            neighbourhood_base_imp_locally_compact_space)

lemma locally_compact_Hausdorff_or_regular:
   "locally_compact_space X \<and> (Hausdorff_space X \<or> regular_space X) \<longleftrightarrow> locally_compact_space X \<and> regular_space X"
  using locally_compact_Hausdorff_imp_regular_space by blast

lemma locally_compact_space_compact_closedin:
  assumes  "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow>
         (\<forall>x \<in> topspace X. \<exists>U K. openin X U \<and> compactin X K \<and> closedin X K \<and> x \<in> U \<and> U \<subseteq> K)"
  using locally_compact_Hausdorff_or_regular unfolding locally_compact_space_def
  by (metis assms closed_compactin inf.absorb_iff2 le_infE neighbourhood_base_of neighbourhood_base_of_closedin)

lemma locally_compact_space_compact_closure_of:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow>
         (\<forall>x \<in> topspace X. \<exists>U. openin X U \<and> compactin X (X closure_of U) \<and> x \<in> U)" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis assms closed_compactin closedin_closure_of closure_of_eq closure_of_mono locally_compact_space_compact_closedin)
next
  assume ?rhs then show ?lhs
    by (meson closure_of_subset locally_compact_space_def openin_subset)
qed

lemma locally_compact_space_neighbourhood_base_closedin:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow> neighbourhood_base_of (\<lambda>C. compactin X C \<and> closedin X C) X" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then have "regular_space X"
    using assms locally_compact_Hausdorff_imp_regular_space by blast
  with L have "neighbourhood_base_of (compactin X) X"
   by (simp add: locally_compact_imp_neighbourhood_base)
  with \<open>regular_space X\<close> show ?rhs
    by (smt (verit, ccfv_threshold) closed_compactin neighbourhood_base_of subset_trans neighbourhood_base_of_closedin)
next
  assume ?rhs then show ?lhs
    using neighbourhood_base_imp_locally_compact_space neighbourhood_base_of_mono by blast
qed

lemma locally_compact_space_neighbourhood_base_closure_of:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow> neighbourhood_base_of (\<lambda>T. compactin X (X closure_of T)) X" 
         (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then have "regular_space X"
    using assms locally_compact_Hausdorff_imp_regular_space by blast
  with L have "neighbourhood_base_of (\<lambda>A. compactin X A \<and> closedin X A) X"
    using locally_compact_space_neighbourhood_base_closedin by blast
  then show ?rhs
    by (simp add: closure_of_closedin neighbourhood_base_of_mono)
next
  assume ?rhs then show ?lhs
    unfolding locally_compact_space_def neighbourhood_base_of
    by (meson closure_of_subset openin_topspace subset_trans)
qed

lemma locally_compact_space_neighbourhood_base_open_closure_of:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow> 
             neighbourhood_base_of (\<lambda>U. openin X U \<and> compactin X (X closure_of U)) X"
         (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then have "regular_space X"
    using assms locally_compact_Hausdorff_imp_regular_space by blast
  then have "neighbourhood_base_of (\<lambda>T. compactin X (X closure_of T)) X"
    using L locally_compact_space_neighbourhood_base_closure_of by auto
  with L show ?rhs
    unfolding neighbourhood_base_of
    by (meson closed_compactin closure_of_closure_of closure_of_eq closure_of_mono subset_trans)
next
  assume ?rhs then show ?lhs
    unfolding locally_compact_space_def neighbourhood_base_of
    by (meson closure_of_subset openin_topspace subset_trans)
qed

lemma locally_compact_space_compact_closed_compact:
  assumes "Hausdorff_space X \<or> regular_space X"
  shows "locally_compact_space X \<longleftrightarrow>
         (\<forall>K. compactin X K
              \<longrightarrow> (\<exists>U L. openin X U \<and> compactin X L \<and> closedin X L \<and> K \<subseteq> U \<and> U \<subseteq> L))"
         (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then obtain U L where UL: "\<forall>x \<in> topspace X. openin X (U x) \<and> compactin X (L x) \<and> closedin X (L x) \<and> x \<in> U x \<and> U x \<subseteq> L x"
    unfolding locally_compact_space_compact_closedin [OF assms]
    by metis
  show ?rhs
  proof clarify
    fix K
    assume "compactin X K"
    then have "K \<subseteq> topspace X"
      by (simp add: compactin_subset_topspace)
    then have *: "(\<forall>U\<in>U ` K. openin X U) \<and> K \<subseteq> \<Union> (U ` K)"
      using UL by blast
    with \<open>compactin X K\<close> obtain KF where KF: "finite KF" "KF \<subseteq> K" "K \<subseteq> \<Union>(U ` KF)"
      by (metis compactinD finite_subset_image)
    show "\<exists>U L. openin X U \<and> compactin X L \<and> closedin X L \<and> K \<subseteq> U \<and> U \<subseteq> L"
    proof (intro conjI exI)
      show "openin X (\<Union> (U ` KF))"
        using "*" \<open>KF \<subseteq> K\<close> by fastforce
      show "compactin X (\<Union> (L ` KF))"
        by (smt (verit) UL \<open>K \<subseteq> topspace X\<close> KF compactin_Union finite_imageI imageE subset_iff)
      show "closedin X (\<Union> (L ` KF))"
        by (smt (verit) UL \<open>K \<subseteq> topspace X\<close> KF closedin_Union finite_imageI imageE subsetD)
    qed (use UL \<open>K \<subseteq> topspace X\<close> KF in auto)
  qed
next
  assume ?rhs then show ?lhs
    by (metis compactin_sing insert_subset locally_compact_space_def)
qed

lemma locally_compact_regular_space_neighbourhood_base:
   "locally_compact_space X \<and> regular_space X \<longleftrightarrow>
        neighbourhood_base_of (\<lambda>C. compactin X C \<and> closedin X C) X"
  using locally_compact_space_neighbourhood_base_closedin neighbourhood_base_of_closedin neighbourhood_base_of_mono by blast

lemma locally_compact_kc_space:
   "neighbourhood_base_of (compactin X) X \<and> kc_space X \<longleftrightarrow>
        locally_compact_space X \<and> Hausdorff_space X"
  using Hausdorff_imp_kc_space locally_compact_imp_kc_eq_Hausdorff_space locally_compact_space_neighbourhood_base by blast

lemma locally_compact_kc_space_alt:
   "neighbourhood_base_of (compactin X) X \<and> kc_space X \<longleftrightarrow>
        locally_compact_space X \<and> Hausdorff_space X \<and> regular_space X"
  using Hausdorff_regular locally_compact_kc_space by blast

lemma locally_compact_kc_imp_regular_space:
   "\<lbrakk>neighbourhood_base_of (compactin X) X; kc_space X\<rbrakk> \<Longrightarrow> regular_space X"
  using Hausdorff_regular locally_compact_imp_kc_eq_Hausdorff_space by blast

lemma kc_locally_compact_space:
   "kc_space X
    \<Longrightarrow> neighbourhood_base_of (compactin X) X \<longleftrightarrow> locally_compact_space X \<and> Hausdorff_space X \<and> regular_space X"
  using Hausdorff_regular locally_compact_kc_space by blast

lemma locally_compact_space_closed_subset:
  assumes loc: "locally_compact_space X" and "closedin X S"
  shows "locally_compact_space (subtopology X S)"
proof (clarsimp simp: locally_compact_space_def)
  fix x assume x: "x \<in> topspace X" "x \<in> S"
  then obtain U K where UK: "openin X U \<and> compactin X K \<and> x \<in> U \<and> U \<subseteq> K"
    by (meson loc locally_compact_space_def)
  show "\<exists>U. openin (subtopology X S) U \<and> 
            (\<exists>K. compactin (subtopology X S) K \<and> x \<in> U \<and> U \<subseteq> K)"
  proof (intro conjI exI)
    show "openin (subtopology X S) (S \<inter> U)"
      by (simp add: UK openin_subtopology_Int2)
    show "compactin (subtopology X S) (S \<inter> K)"
      by (simp add: UK assms(2) closed_Int_compactin compactin_subtopology)
  qed (use UK x in auto)
qed

lemma locally_compact_space_open_subset:
  assumes reg: "regular_space X" and loc: "locally_compact_space X" and "openin X S"
  shows "locally_compact_space (subtopology X S)"
proof (clarsimp simp: locally_compact_space_def)
  fix x assume x: "x \<in> topspace X" "x \<in> S"
  then obtain U K where UK: "openin X U" "compactin X K" "x \<in> U" "U \<subseteq> K"
    by (meson loc locally_compact_space_def)
  have "openin X (U \<inter> S)"
    by (simp add: UK \<open>openin X S\<close> openin_Int)
  with UK reg x obtain V C 
      where VC: "openin X V" "closedin X C" "x \<in> V" "V \<subseteq> C" "C \<subseteq> U" "C \<subseteq> S"
    by (metis IntI le_inf_iff neighbourhood_base_of neighbourhood_base_of_closedin)
  show "\<exists>U. openin (subtopology X S) U \<and> 
            (\<exists>K. compactin (subtopology X S) K \<and> x \<in> U \<and> U \<subseteq> K)"
  proof (intro conjI exI)
    show "openin (subtopology X S) V"
      using VC by (meson \<open>openin X S\<close> openin_open_subtopology order_trans)
    show "compactin (subtopology X S) (C \<inter> K)"
      using UK VC closed_Int_compactin compactin_subtopology by fastforce
  qed (use UK VC x in auto)
qed

lemma locally_compact_space_discrete_topology:
   "locally_compact_space (discrete_topology U)"
  by (simp add: neighbourhood_base_imp_locally_compact_space neighbourhood_base_of_discrete_topology)

lemma locally_compact_space_continuous_open_map_image:
  "\<lbrakk>continuous_map X X' f; open_map X X' f;
    f ` topspace X = topspace X'; locally_compact_space X\<rbrakk> \<Longrightarrow> locally_compact_space X'"
unfolding locally_compact_space_def open_map_def
  by (smt (verit, ccfv_SIG) image_compactin image_iff image_mono)

lemma locally_compact_subspace_openin_closure_of:
  assumes "Hausdorff_space X" and S: "S \<subseteq> topspace X" 
    and loc: "locally_compact_space (subtopology X S)"
  shows "openin (subtopology X (X closure_of S)) S"
  unfolding openin_subopen [where S=S]
proof clarify
  fix a assume "a \<in> S"
  then obtain T K where *: "openin X T" "compactin X K" "K \<subseteq> S" "a \<in> S" "a \<in> T" "S \<inter> T \<subseteq> K"
    using loc unfolding locally_compact_space_def
  by (metis IntE S compactin_subtopology inf_commute openin_subtopology topspace_subtopology_subset)
  have "T \<inter> X closure_of S \<subseteq> X closure_of (T \<inter> S)"
    by (simp add: "*"(1) openin_Int_closure_of_subset)
  also have "... \<subseteq> S"
    using * \<open>Hausdorff_space X\<close> by (metis closure_of_minimal compactin_imp_closedin order.trans inf_commute)
  finally have "T \<inter> X closure_of S \<subseteq> T \<inter> S" by simp 
  then have "openin (subtopology X (X closure_of S)) (T \<inter> S)"
    unfolding openin_subtopology using \<open>openin X T\<close> S closure_of_subset by fastforce
  with * show "\<exists>T. openin (subtopology X (X closure_of S)) T \<and> a \<in> T \<and> T \<subseteq> S"
    by blast
qed

lemma locally_compact_subspace_closed_Int_openin:
   "\<lbrakk>Hausdorff_space X \<and> S \<subseteq> topspace X \<and> locally_compact_space(subtopology X S)\<rbrakk>
        \<Longrightarrow> \<exists>C U. closedin X C \<and> openin X U \<and> C \<inter> U = S"
  by (metis closedin_closure_of inf_commute locally_compact_subspace_openin_closure_of openin_subtopology)

lemma locally_compact_subspace_open_in_closure_of_eq:
  assumes "Hausdorff_space X" and loc: "locally_compact_space X"
  shows "openin (subtopology X (X closure_of S)) S \<longleftrightarrow> S \<subseteq> topspace X \<and> locally_compact_space(subtopology X S)" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then obtain "S \<subseteq> topspace X" "regular_space X"
    using assms locally_compact_Hausdorff_imp_regular_space openin_subset by fastforce 
  then have "locally_compact_space (subtopology (subtopology X (X closure_of S)) S)"
    by (simp add: L loc locally_compact_space_closed_subset locally_compact_space_open_subset regular_space_subtopology)
  then show ?rhs
    by (metis L inf.orderE inf_commute le_inf_iff openin_subset subtopology_subtopology topspace_subtopology)
next
  assume ?rhs then show ?lhs
    using  assms locally_compact_subspace_openin_closure_of by blast
qed

lemma locally_compact_subspace_closed_Int_openin_eq:
  assumes "Hausdorff_space X" and loc: "locally_compact_space X"
  shows "(\<exists>C U. closedin X C \<and> openin X U \<and> C \<inter> U = S) \<longleftrightarrow> S \<subseteq> topspace X \<and> locally_compact_space(subtopology X S)" (is "?lhs=?rhs")
proof
  assume L: ?lhs 
  then obtain C U where "closedin X C" "openin X U" and Seq: "S = C \<inter> U"
    by blast
  then have "C \<subseteq> topspace X"
    by (simp add: closedin_subset)
  have "locally_compact_space (subtopology (subtopology X C) (topspace (subtopology X C) \<inter> U))"
    proof (rule locally_compact_space_open_subset)
  show "regular_space (subtopology X C)"
    by (simp add: \<open>Hausdorff_space X\<close> loc locally_compact_Hausdorff_imp_regular_space regular_space_subtopology)
  show "locally_compact_space (subtopology X C)"
    by (simp add: \<open>closedin X C\<close> loc locally_compact_space_closed_subset)
  show "openin (subtopology X C) (topspace (subtopology X C) \<inter> U)"
    by (simp add: \<open>openin X U\<close> Int_left_commute inf_commute openin_Int openin_subtopology_Int2)
qed
    then show ?rhs
      by (metis Seq \<open>C \<subseteq> topspace X\<close> inf.coboundedI1 subtopology_subtopology subtopology_topspace)
next
  assume ?rhs then show ?lhs
  using assms locally_compact_subspace_closed_Int_openin by blast
qed

lemma dense_locally_compact_openin_Hausdorff_space:
   "\<lbrakk>Hausdorff_space X; S \<subseteq> topspace X; X closure_of S = topspace X;
     locally_compact_space (subtopology X S)\<rbrakk> \<Longrightarrow> openin X S"
  by (metis locally_compact_subspace_openin_closure_of subtopology_topspace)

lemma locally_compact_space_prod_topology:
  "locally_compact_space (prod_topology X Y) \<longleftrightarrow>
        topspace (prod_topology X Y) = {} \<or>
        locally_compact_space X \<and> locally_compact_space Y" (is "?lhs=?rhs")
proof (cases "topspace (prod_topology X Y) = {}")
  case True
  then show ?thesis
    unfolding locally_compact_space_def by blast
next
  case False
  then obtain w z where wz: "w \<in> topspace X" "z \<in> topspace Y"
    by auto
  show ?thesis 
  proof
    assume L: ?lhs then show ?rhs
      by (metis wz empty_iff locally_compact_space_retraction_map_image retraction_map_fst retraction_map_snd)
  next
    assume R: ?rhs 
    show ?lhs
      unfolding locally_compact_space_def
    proof clarsimp
      fix x y
      assume "x \<in> topspace X" and "y \<in> topspace Y"
      obtain U C where "openin X U" "compactin X C" "x \<in> U" "U \<subseteq> C"
        by (meson False R \<open>x \<in> topspace X\<close> locally_compact_space_def)
      obtain V D where "openin Y V" "compactin Y D" "y \<in> V" "V \<subseteq> D"
        by (meson False R \<open>y \<in> topspace Y\<close> locally_compact_space_def)
      show "\<exists>U. openin (prod_topology X Y) U \<and> (\<exists>K. compactin (prod_topology X Y) K \<and> (x, y) \<in> U \<and> U \<subseteq> K)"
      proof (intro exI conjI)
        show "openin (prod_topology X Y) (U \<times> V)"
          by (simp add: \<open>openin X U\<close> \<open>openin Y V\<close> openin_prod_Times_iff)
        show "compactin (prod_topology X Y) (C \<times> D)"
          by (simp add: \<open>compactin X C\<close> \<open>compactin Y D\<close> compactin_Times)
        show "(x, y) \<in> U \<times> V"
          by (simp add: \<open>x \<in> U\<close> \<open>y \<in> V\<close>)
        show "U \<times> V \<subseteq> C \<times> D"
          by (simp add: Sigma_mono \<open>U \<subseteq> C\<close> \<open>V \<subseteq> D\<close>)
      qed
    qed
  qed
qed

lemma locally_compact_space_product_topology:
   "locally_compact_space(product_topology X I) \<longleftrightarrow>
        topspace(product_topology X I) = {} \<or>
        finite {i \<in> I. \<not> compact_space(X i)} \<and> (\<forall>i \<in> I. locally_compact_space(X i))" (is "?lhs=?rhs")
proof (cases "topspace (product_topology X I) = {}")
  case True
  then show ?thesis
    by (simp add: locally_compact_space_def)
next
  case False
  show ?thesis 
  proof
    assume L: ?lhs
    obtain z where z: "z \<in> topspace (product_topology X I)"
      using False by auto
    with L z obtain U C where "openin (product_topology X I) U" "compactin (product_topology X I) C" "z \<in> U" "U \<subseteq> C"
      by (meson locally_compact_space_def)
    then obtain V where finV: "finite {i \<in> I. V i \<noteq> topspace (X i)}" and "\<forall>i \<in> I. openin (X i) (V i)" 
                    and "z \<in> PiE I V" "PiE I V \<subseteq> U"
      by (auto simp: openin_product_topology_alt)
    have "compact_space (X i)" if "i \<in> I" "V i = topspace (X i)" for i
    proof -
      have "compactin (X i) ((\<lambda>x. x i) ` C)"
        using \<open>compactin (product_topology X I) C\<close> image_compactin
        by (metis continuous_map_product_projection \<open>i \<in> I\<close>)
      moreover have "V i \<subseteq> (\<lambda>x. x i) ` C"
      proof -
        have "V i \<subseteq> (\<lambda>x. x i) ` Pi\<^sub>E I V"
          by (metis \<open>z \<in> Pi\<^sub>E I V\<close> empty_iff image_projection_PiE order_refl \<open>i \<in> I\<close>)
        also have "\<dots> \<subseteq> (\<lambda>x. x i) ` C"
          using \<open>U \<subseteq> C\<close> \<open>Pi\<^sub>E I V \<subseteq> U\<close> by blast
        finally show ?thesis .
      qed
      ultimately show ?thesis
        by (metis closed_compactin closedin_topspace compact_space_def that(2))
    qed
    with finV have "finite {i \<in> I. \<not> compact_space (X i)}"
      by (metis (mono_tags, lifting) mem_Collect_eq finite_subset subsetI)
    moreover have "locally_compact_space (X i)" if "i \<in> I" for i
      by (meson False L locally_compact_space_retraction_map_image retraction_map_product_projection that)
    ultimately show ?rhs by metis
  next
    assume R: ?rhs 
    show ?lhs
      unfolding locally_compact_space_def
    proof clarsimp
      fix z
      assume z: "z \<in> (\<Pi>\<^sub>E i\<in>I. topspace (X i))"
      have "\<exists>U C. openin (X i) U \<and> compactin (X i) C \<and> z i \<in> U \<and> U \<subseteq> C \<and>
                    (compact_space(X i) \<longrightarrow> U = topspace(X i) \<and> C = topspace(X i))" 
        if "i \<in> I" for i
        using that R z unfolding locally_compact_space_def compact_space_def
        by (metis (no_types, lifting) False PiE_mem openin_topspace set_eq_subset)
      then obtain U C where UC: "\<And>i. i \<in> I \<Longrightarrow> 
             openin (X i) (U i) \<and> compactin (X i) (C i) \<and> z i \<in> U i \<and> U i \<subseteq> C i \<and>
                    (compact_space(X i) \<longrightarrow> U i = topspace(X i) \<and> C i = topspace(X i))"
        by metis
      show "\<exists>U. openin (product_topology X I) U \<and> (\<exists>K. compactin (product_topology X I) K \<and> z \<in> U \<and> U \<subseteq> K)"
      proof (intro exI conjI)
        show "openin (product_topology X I) (Pi\<^sub>E I U)"
        by (smt (verit) Collect_cong False R UC compactin_subspace openin_PiE_gen subset_antisym subtopology_topspace)
        show "compactin (product_topology X I) (Pi\<^sub>E I C)"
          by (simp add: UC compactin_PiE)
      qed (use UC z in blast)+
    qed
  qed
qed

lemma locally_compact_space_sum_topology:
   "locally_compact_space (sum_topology X I) \<longleftrightarrow> (\<forall>i \<in> I. locally_compact_space (X i))" (is "?lhs=?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis closed_map_component_injection embedding_map_imp_homeomorphic_space embedding_map_component_injection
        embedding_imp_closed_map_eq homeomorphic_locally_compact_space locally_compact_space_closed_subset)
next
  assume R: ?rhs
  show ?lhs
    unfolding locally_compact_space_def
  proof clarsimp
    fix i y
    assume "i \<in> I" and y: "y \<in> topspace (X i)"
    then obtain U K where UK: "openin (X i) U" "compactin (X i) K" "y \<in> U" "U \<subseteq> K"
      using R by (fastforce simp: locally_compact_space_def)
    then show "\<exists>U. openin (sum_topology X I) U \<and> (\<exists>K. compactin (sum_topology X I) K \<and> (i, y) \<in> U \<and> U \<subseteq> K)"
      by (metis \<open>i \<in> I\<close> continuous_map_component_injection image_compactin image_mono 
          imageI open_map_component_injection open_map_def)
  qed
qed

proposition quotient_map_prod_right:
  assumes loc: "locally_compact_space Z" 
    and reg: "Hausdorff_space Z \<or> regular_space Z" 
    and f: "quotient_map X Y f"
  shows "quotient_map (prod_topology Z X) (prod_topology Z Y) (\<lambda>(x,y). (x,f y))"
proof -
  define h where "h \<equiv> (\<lambda>(x::'a,y). (x,f y))"
  have "continuous_map (prod_topology Z X) Y (f o snd)"
    by (simp add: continuous_map_of_snd f quotient_imp_continuous_map)
  then have cmh: "continuous_map (prod_topology Z X) (prod_topology Z Y) h"
    by (simp add: h_def continuous_map_paired split_def continuous_map_fst o_def)
  have fim: "f ` topspace X = topspace Y"
    by (simp add: f quotient_imp_surjective_map)
  moreover
  have "openin (prod_topology Z X) {u \<in> topspace Z \<times> topspace X. h u \<in> W}
   \<longleftrightarrow> openin (prod_topology Z Y) W"   (is "?lhs=?rhs")
    if W: "W \<subseteq> topspace Z \<times> topspace Y" for W
  proof
    define S where "S \<equiv> {u \<in> topspace Z \<times> topspace X. h u \<in> W}"
    assume ?lhs 
    then have L: "openin (prod_topology Z X) S"
      using S_def by blast
    have "\<exists>T. openin (prod_topology Z Y) T \<and> (x0, z0) \<in> T \<and> T \<subseteq> W"
      if \<section>: "(x0,z0) \<in> W" for x0 z0 
    proof -
      have x0: "x0 \<in> topspace Z"
        using W that by blast
      obtain y0 where y0: "y0 \<in> topspace X" "f y0 = z0"
        by (metis W fim imageE insert_absorb insert_subset mem_Sigma_iff \<section>)
      then have "(x0, y0) \<in> S"
        by (simp add: S_def h_def that x0)
      have "continuous_map Z (prod_topology Z X) (\<lambda>x. (x, y0))"
        by (simp add: continuous_map_paired y0)
      with openin_continuous_map_preimage [OF _ L] 
      have ope_ZS: "openin Z {x \<in> topspace Z. (x,y0) \<in> S}"
        by blast
      obtain U U' where "openin Z U" "compactin Z U'" "closedin Z U'" 
        "x0 \<in> U"  "U \<subseteq> U'" "U' \<subseteq> {x \<in> topspace Z. (x,y0) \<in> S}"
        using loc ope_ZS x0 \<open>(x0, y0) \<in> S\<close>
        by (force simp: locally_compact_space_neighbourhood_base_closedin [OF reg] 
            neighbourhood_base_of)
      then have D: "U' \<times> {y0} \<subseteq> S"
        by (auto simp: )
      define V where "V \<equiv> {z \<in> topspace Y. U' \<times> {y \<in> topspace X. f y = z} \<subseteq> S}"
      have "z0 \<in> V"
        using D y0 Int_Collect fim by (fastforce simp: h_def V_def S_def)
      have "openin X {x \<in> topspace X. f x \<in> V} \<Longrightarrow> openin Y V"
        using f unfolding V_def quotient_map_def subset_iff
        by (smt (verit, del_insts) Collect_cong mem_Collect_eq)
      moreover have "openin X {x \<in> topspace X. f x \<in> V}"
      proof -
        let ?Z = "subtopology Z U'"
        have *: "{x \<in> topspace X. f x \<in> V} = topspace X - snd ` (U' \<times> topspace X - S)"
          by (force simp: V_def S_def h_def simp flip: fim)
        have "compact_space ?Z"
          using \<open>compactin Z U'\<close> compactin_subspace by auto
        moreover have "closedin (prod_topology ?Z X) (U' \<times> topspace X - S)"
          by (simp add: L \<open>closedin Z U'\<close> closedin_closed_subtopology closedin_diff closedin_prod_Times_iff 
              prod_topology_subtopology(1))
        ultimately show ?thesis
          using "*" closed_map_snd closed_map_def by fastforce
      qed
      ultimately have "openin Y V"
        by metis
      show ?thesis
      proof (intro conjI exI)
        show "openin (prod_topology Z Y) (U \<times> V)"
          by (simp add: openin_prod_Times_iff \<open>openin Z U\<close> \<open>openin Y V\<close>)
        show "(x0, z0) \<in> U \<times> V"
          by (simp add: \<open>x0 \<in> U\<close> \<open>z0 \<in> V\<close>)
        show "U \<times> V \<subseteq> W"
          using \<open>U \<subseteq> U'\<close> by (force simp: V_def S_def h_def simp flip: fim)
      qed
    qed
    with openin_subopen show ?rhs by force
  next
    assume ?rhs then show ?lhs
      using openin_continuous_map_preimage cmh by fastforce
  qed
  ultimately show ?thesis
    by (fastforce simp: image_iff quotient_map_def h_def)
qed

lemma quotient_map_prod_left:
  assumes loc: "locally_compact_space Z" 
    and reg: "Hausdorff_space Z \<or> regular_space Z" 
    and f: "quotient_map X Y f"
  shows "quotient_map (prod_topology X Z) (prod_topology Y Z) (\<lambda>(x,y). (f x,y))"
proof -
  have "(\<lambda>(x,y). (f x,y)) = prod.swap \<circ> (\<lambda>(x,y). (x,f y)) \<circ> prod.swap"
    by force
  then
  show ?thesis
    apply (rule ssubst)
  proof (intro quotient_map_compose)
    show "quotient_map (prod_topology X Z) (prod_topology Z X) prod.swap"
      "quotient_map (prod_topology Z Y) (prod_topology Y Z) prod.swap"
      using homeomorphic_map_def homeomorphic_map_swap quotient_map_eq by fastforce+
    show "quotient_map (prod_topology Z X) (prod_topology Z Y) (\<lambda>(x, y). (x, f y))"
      by (simp add: f loc quotient_map_prod_right reg)
  qed
qed

lemma locally_compact_space_perfect_map_preimage:
  assumes "locally_compact_space X'" and f: "perfect_map X X' f"
  shows "locally_compact_space X"
  unfolding locally_compact_space_def
proof (intro strip)
  fix x
  assume x: "x \<in> topspace X"
  then obtain U K where "openin X' U" "compactin X' K" "f x \<in> U" "U \<subseteq> K"
    using assms unfolding locally_compact_space_def perfect_map_def
    by (metis (no_types, lifting) continuous_map_closedin)
  show "\<exists>U K. openin X U \<and> compactin X K \<and> x \<in> U \<and> U \<subseteq> K"
  proof (intro exI conjI)
    have "continuous_map X X' f"
      using f perfect_map_def by blast
    then show "openin X {x \<in> topspace X. f x \<in> U}"
      by (simp add: \<open>openin X' U\<close> continuous_map)
    show "compactin X {x \<in> topspace X. f x \<in> K}"
      using \<open>compactin X' K\<close> f perfect_imp_proper_map proper_map_alt by blast
  qed (use x \<open>f x \<in> U\<close> \<open>U \<subseteq> K\<close> in auto)
qed

end

