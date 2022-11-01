(*  Title:      ZF/ex/Group.thy *)

section \<open>Groups\<close>

theory Group imports ZF begin

text\<open>Based on work by Clemens Ballarin, Florian Kammueller, L C Paulson and
Markus Wenzel.\<close>


subsection \<open>Monoids\<close>

(*First, we must simulate a record declaration:
record monoid =
  carrier :: i
  mult :: "[i,i] \<Rightarrow> i" (infixl "\<cdot>\<index>" 70)
  one :: i ("\<one>\<index>")
*)

definition
  carrier :: "i \<Rightarrow> i" where
  "carrier(M) \<equiv> fst(M)"

definition
  mmult :: "[i, i, i] \<Rightarrow> i" (infixl \<open>\<cdot>\<index>\<close> 70) where
  "mmult(M,x,y) \<equiv> fst(snd(M)) ` \<langle>x,y\<rangle>"

definition
  one :: "i \<Rightarrow> i" (\<open>\<one>\<index>\<close>) where
  "one(M) \<equiv> fst(snd(snd(M)))"

definition
  update_carrier :: "[i,i] \<Rightarrow> i" where
  "update_carrier(M,A) \<equiv> <A,snd(M)>"

definition
  m_inv :: "i \<Rightarrow> i \<Rightarrow> i" (\<open>inv\<index> _\<close> [81] 80) where
  "inv\<^bsub>G\<^esub> x \<equiv> (THE y. y \<in> carrier(G) \<and> y \<cdot>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub> \<and> x \<cdot>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub>)"

locale monoid = fixes G (structure)
  assumes m_closed [intro, simp]:
         "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> carrier(G)"
      and m_assoc:
         "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G); z \<in> carrier(G)\<rbrakk>
          \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
      and one_closed [intro, simp]: "\<one> \<in> carrier(G)"
      and l_one [simp]: "x \<in> carrier(G) \<Longrightarrow> \<one> \<cdot> x = x"
      and r_one [simp]: "x \<in> carrier(G) \<Longrightarrow> x \<cdot> \<one> = x"

text\<open>Simulating the record\<close>
lemma carrier_eq [simp]: "carrier(\<langle>A,Z\<rangle>) = A"
  by (simp add: carrier_def)

lemma mult_eq [simp]: "mmult(<A,M,Z>, x, y) = M ` \<langle>x,y\<rangle>"
  by (simp add: mmult_def)

lemma one_eq [simp]: "one(<A,M,I,Z>) = I"
  by (simp add: one_def)

lemma update_carrier_eq [simp]: "update_carrier(\<langle>A,Z\<rangle>,B) = \<langle>B,Z\<rangle>"
  by (simp add: update_carrier_def)

lemma carrier_update_carrier [simp]: "carrier(update_carrier(M,B)) = B"
  by (simp add: update_carrier_def)

lemma mult_update_carrier [simp]: "mmult(update_carrier(M,B),x,y) = mmult(M,x,y)"
  by (simp add: update_carrier_def mmult_def)

lemma one_update_carrier [simp]: "one(update_carrier(M,B)) = one(M)"
  by (simp add: update_carrier_def one_def)


lemma (in monoid) inv_unique:
  assumes eq: "y \<cdot> x = \<one>"  "x \<cdot> y' = \<one>"
    and G: "x \<in> carrier(G)"  "y \<in> carrier(G)"  "y' \<in> carrier(G)"
  shows "y = y'"
proof -
  from G eq have "y = y \<cdot> (x \<cdot> y')" by simp
  also from G have "... = (y \<cdot> x) \<cdot> y'" by (simp add: m_assoc)
  also from G eq have "... = y'" by simp
  finally show ?thesis .
qed

text \<open>
  A group is a monoid all of whose elements are invertible.
\<close>

locale group = monoid +
  assumes inv_ex:
     "\<And>x. x \<in> carrier(G) \<Longrightarrow> \<exists>y \<in> carrier(G). y \<cdot> x = \<one> \<and> x \<cdot> y = \<one>"

lemma (in group) is_group [simp]: "group(G)" by (rule group_axioms)

theorem groupI:
  fixes G (structure)
  assumes m_closed [simp]:
      "\<And>x y. \<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> carrier(G)"
    and one_closed [simp]: "\<one> \<in> carrier(G)"
    and m_assoc:
      "\<And>x y z. \<lbrakk>x \<in> carrier(G); y \<in> carrier(G); z \<in> carrier(G)\<rbrakk> \<Longrightarrow>
      (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    and l_one [simp]: "\<And>x. x \<in> carrier(G) \<Longrightarrow> \<one> \<cdot> x = x"
    and l_inv_ex: "\<And>x. x \<in> carrier(G) \<Longrightarrow> \<exists>y \<in> carrier(G). y \<cdot> x = \<one>"
  shows "group(G)"
proof -
  have l_cancel [simp]:
    "\<And>x y z. \<lbrakk>x \<in> carrier(G); y \<in> carrier(G); z \<in> carrier(G)\<rbrakk> \<Longrightarrow>
    (x \<cdot> y = x \<cdot> z) \<longleftrightarrow> (y = z)"
  proof
    fix x y z
    assume G: "x \<in> carrier(G)"  "y \<in> carrier(G)"  "z \<in> carrier(G)"
    {
      assume eq: "x \<cdot> y = x \<cdot> z"
      with G l_inv_ex obtain x_inv where xG: "x_inv \<in> carrier(G)"
        and l_inv: "x_inv \<cdot> x = \<one>" by fast
      from G eq xG have "(x_inv \<cdot> x) \<cdot> y = (x_inv \<cdot> x) \<cdot> z"
        by (simp add: m_assoc)
      with G show "y = z" by (simp add: l_inv)
    next
      assume eq: "y = z"
      with G show "x \<cdot> y = x \<cdot> z" by simp
    }
  qed
  have r_one:
    "\<And>x. x \<in> carrier(G) \<Longrightarrow> x \<cdot> \<one> = x"
  proof -
    fix x
    assume x: "x \<in> carrier(G)"
    with l_inv_ex obtain x_inv where xG: "x_inv \<in> carrier(G)"
      and l_inv: "x_inv \<cdot> x = \<one>" by fast
    from x xG have "x_inv \<cdot> (x \<cdot> \<one>) = x_inv \<cdot> x"
      by (simp add: m_assoc [symmetric] l_inv)
    with x xG show "x \<cdot> \<one> = x" by simp
  qed
  have inv_ex:
    "\<And>x. x \<in> carrier(G) \<Longrightarrow> \<exists>y \<in> carrier(G). y \<cdot> x = \<one> \<and> x \<cdot> y = \<one>"
  proof -
    fix x
    assume x: "x \<in> carrier(G)"
    with l_inv_ex obtain y where y: "y \<in> carrier(G)"
      and l_inv: "y \<cdot> x = \<one>" by fast
    from x y have "y \<cdot> (x \<cdot> y) = y \<cdot> \<one>"
      by (simp add: m_assoc [symmetric] l_inv r_one)
    with x y have r_inv: "x \<cdot> y = \<one>"
      by simp
    from x y show "\<exists>y \<in> carrier(G). y \<cdot> x = \<one> \<and> x \<cdot> y = \<one>"
      by (fast intro: l_inv r_inv)
  qed
  show ?thesis
    by (blast intro: group.intro monoid.intro group_axioms.intro
                     assms r_one inv_ex)
qed

lemma (in group) inv [simp]:
  "x \<in> carrier(G) \<Longrightarrow> inv x \<in> carrier(G) \<and> inv x \<cdot> x = \<one> \<and> x \<cdot> inv x = \<one>"
  apply (frule inv_ex)
    unfolding Bex_def m_inv_def
  apply (erule exE)
  apply (rule theI)
  apply (rule ex1I, assumption)
   apply (blast intro: inv_unique)
  done

lemma (in group) inv_closed [intro!]:
  "x \<in> carrier(G) \<Longrightarrow> inv x \<in> carrier(G)"
  by simp

lemma (in group) l_inv:
  "x \<in> carrier(G) \<Longrightarrow> inv x \<cdot> x = \<one>"
  by simp

lemma (in group) r_inv:
  "x \<in> carrier(G) \<Longrightarrow> x \<cdot> inv x = \<one>"
  by simp


subsection \<open>Cancellation Laws and Basic Properties\<close>

lemma (in group) l_cancel [simp]:
  assumes "x \<in> carrier(G)" "y \<in> carrier(G)" "z \<in> carrier(G)"
  shows "(x \<cdot> y = x \<cdot> z) \<longleftrightarrow> (y = z)"
proof
  assume eq: "x \<cdot> y = x \<cdot> z"
  hence  "(inv x \<cdot> x) \<cdot> y = (inv x \<cdot> x) \<cdot> z"
    by (simp only: m_assoc inv_closed assms)
  thus "y = z" by (simp add: assms)
next
  assume eq: "y = z"
  then show "x \<cdot> y = x \<cdot> z" by simp
qed

lemma (in group) r_cancel [simp]:
  assumes "x \<in> carrier(G)" "y \<in> carrier(G)" "z \<in> carrier(G)"
  shows "(y \<cdot> x = z \<cdot> x) \<longleftrightarrow> (y = z)"
proof
  assume eq: "y \<cdot> x = z \<cdot> x"
  then have "y \<cdot> (x \<cdot> inv x) = z \<cdot> (x \<cdot> inv x)"
    by (simp only: m_assoc [symmetric] inv_closed assms)
  thus "y = z" by (simp add: assms)
next
  assume eq: "y = z"
  thus  "y \<cdot> x = z \<cdot> x" by simp
qed

lemma (in group) inv_comm:
  assumes "x \<cdot> y = \<one>"
      and G: "x \<in> carrier(G)"  "y \<in> carrier(G)"
  shows "y \<cdot> x = \<one>"
proof -
  from G have "x \<cdot> y \<cdot> x = x \<cdot> \<one>" by (auto simp add: assms)
  with G show ?thesis by (simp del: r_one add: m_assoc)
qed

lemma (in group) inv_equality:
     "\<lbrakk>y \<cdot> x = \<one>; x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> inv x = y"
apply (simp add: m_inv_def)
apply (rule the_equality)
 apply (simp add: inv_comm [of y x])
apply (rule r_cancel [THEN iffD1], auto)
done

lemma (in group) inv_one [simp]:
  "inv \<one> = \<one>"
  by (auto intro: inv_equality)

lemma (in group) inv_inv [simp]: "x \<in> carrier(G) \<Longrightarrow> inv (inv x) = x"
  by (auto intro: inv_equality)

text\<open>This proof is by cancellation\<close>
lemma (in group) inv_mult_group:
  "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> inv (x \<cdot> y) = inv y \<cdot> inv x"
proof -
  assume G: "x \<in> carrier(G)"  "y \<in> carrier(G)"
  then have "inv (x \<cdot> y) \<cdot> (x \<cdot> y) = (inv y \<cdot> inv x) \<cdot> (x \<cdot> y)"
    by (simp add: m_assoc l_inv) (simp add: m_assoc [symmetric] l_inv)
  with G show ?thesis by (simp_all del: inv add: inv_closed)
qed


subsection \<open>Substructures\<close>

locale subgroup = fixes H and G (structure)
  assumes subset: "H \<subseteq> carrier(G)"
    and m_closed [intro, simp]: "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> H"
    and  one_closed [simp]: "\<one> \<in> H"
    and m_inv_closed [intro,simp]: "x \<in> H \<Longrightarrow> inv x \<in> H"


lemma (in subgroup) mem_carrier [simp]:
  "x \<in> H \<Longrightarrow> x \<in> carrier(G)"
  using subset by blast


lemma subgroup_imp_subset:
  "subgroup(H,G) \<Longrightarrow> H \<subseteq> carrier(G)"
  by (rule subgroup.subset)

lemma (in subgroup) group_axiomsI [intro]:
  assumes "group(G)"
  shows "group_axioms (update_carrier(G,H))"
proof -
  interpret group G by fact
  show ?thesis by (force intro: group_axioms.intro l_inv r_inv)
qed

lemma (in subgroup) is_group [intro]:
  assumes "group(G)"
  shows "group (update_carrier(G,H))"
proof -
  interpret group G by fact
  show ?thesis
  by (rule groupI) (auto intro: m_assoc l_inv mem_carrier)
qed

text \<open>
  Since \<^term>\<open>H\<close> is nonempty, it contains some element \<^term>\<open>x\<close>.  Since
  it is closed under inverse, it contains \<open>inv x\<close>.  Since
  it is closed under product, it contains \<open>x \<cdot> inv x = \<one>\<close>.
\<close>

text \<open>
  Since \<^term>\<open>H\<close> is nonempty, it contains some element \<^term>\<open>x\<close>.  Since
  it is closed under inverse, it contains \<open>inv x\<close>.  Since
  it is closed under product, it contains \<open>x \<cdot> inv x = \<one>\<close>.
\<close>

lemma (in group) one_in_subset:
  "\<lbrakk>H \<subseteq> carrier(G); H \<noteq> 0; \<forall>a \<in> H. inv a \<in> H; \<forall>a\<in>H. \<forall>b\<in>H. a \<cdot> b \<in> H\<rbrakk>
   \<Longrightarrow> \<one> \<in> H"
by (force simp add: l_inv)

text \<open>A characterization of subgroups: closed, non-empty subset.\<close>

declare monoid.one_closed [simp] group.inv_closed [simp]
  monoid.l_one [simp] monoid.r_one [simp] group.inv_inv [simp]

lemma subgroup_nonempty:
  "\<not> subgroup(0,G)"
  by (blast dest: subgroup.one_closed)


subsection \<open>Direct Products\<close>

definition
  DirProdGroup :: "[i,i] \<Rightarrow> i"  (infixr \<open>\<Otimes>\<close> 80) where
  "G \<Otimes> H \<equiv> <carrier(G) \<times> carrier(H),
              (\<lambda><\<langle>g,h\<rangle>, <g', h'>>
                   \<in> (carrier(G) \<times> carrier(H)) \<times> (carrier(G) \<times> carrier(H)).
                <g \<cdot>\<^bsub>G\<^esub> g', h \<cdot>\<^bsub>H\<^esub> h'>),
              <\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>>, 0>"

lemma DirProdGroup_group:
  assumes "group(G)" and "group(H)"
  shows "group (G \<Otimes> H)"
proof -
  interpret G: group G by fact
  interpret H: group H by fact
  show ?thesis by (force intro!: groupI G.m_assoc H.m_assoc G.l_inv H.l_inv
          simp add: DirProdGroup_def)
qed

lemma carrier_DirProdGroup [simp]:
     "carrier (G \<Otimes> H) = carrier(G) \<times> carrier(H)"
  by (simp add: DirProdGroup_def)

lemma one_DirProdGroup [simp]:
     "\<one>\<^bsub>G \<Otimes> H\<^esub> = <\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>>"
  by (simp add: DirProdGroup_def)

lemma mult_DirProdGroup [simp]:
     "\<lbrakk>g \<in> carrier(G); h \<in> carrier(H); g' \<in> carrier(G); h' \<in> carrier(H)\<rbrakk>
      \<Longrightarrow> \<langle>g, h\<rangle> \<cdot>\<^bsub>G \<Otimes> H\<^esub> <g', h'> = <g \<cdot>\<^bsub>G\<^esub> g', h \<cdot>\<^bsub>H\<^esub> h'>"
  by (simp add: DirProdGroup_def)

lemma inv_DirProdGroup [simp]:
  assumes "group(G)" and "group(H)"
  assumes g: "g \<in> carrier(G)"
      and h: "h \<in> carrier(H)"
  shows "inv \<^bsub>G \<Otimes> H\<^esub> \<langle>g, h\<rangle> = <inv\<^bsub>G\<^esub> g, inv\<^bsub>H\<^esub> h>"
  apply (rule group.inv_equality [OF DirProdGroup_group])
  apply (simp_all add: assms group.l_inv)
  done

subsection \<open>Isomorphisms\<close>

definition
  hom :: "[i,i] \<Rightarrow> i" where
  "hom(G,H) \<equiv>
    {h \<in> carrier(G) -> carrier(H).
      (\<forall>x \<in> carrier(G). \<forall>y \<in> carrier(G). h ` (x \<cdot>\<^bsub>G\<^esub> y) = (h ` x) \<cdot>\<^bsub>H\<^esub> (h ` y))}"

lemma hom_mult:
  "\<lbrakk>h \<in> hom(G,H); x \<in> carrier(G); y \<in> carrier(G)\<rbrakk>
   \<Longrightarrow> h ` (x \<cdot>\<^bsub>G\<^esub> y) = h ` x \<cdot>\<^bsub>H\<^esub> h ` y"
  by (simp add: hom_def)

lemma hom_closed:
  "\<lbrakk>h \<in> hom(G,H); x \<in> carrier(G)\<rbrakk> \<Longrightarrow> h ` x \<in> carrier(H)"
  by (auto simp add: hom_def)

lemma (in group) hom_compose:
     "\<lbrakk>h \<in> hom(G,H); i \<in> hom(H,I)\<rbrakk> \<Longrightarrow> i O h \<in> hom(G,I)"
by (force simp add: hom_def comp_fun)

lemma hom_is_fun:
  "h \<in> hom(G,H) \<Longrightarrow> h \<in> carrier(G) -> carrier(H)"
  by (simp add: hom_def)


subsection \<open>Isomorphisms\<close>

definition
  iso :: "[i,i] \<Rightarrow> i"  (infixr \<open>\<cong>\<close> 60) where
  "G \<cong> H \<equiv> hom(G,H) \<inter> bij(carrier(G), carrier(H))"

lemma (in group) iso_refl: "id(carrier(G)) \<in> G \<cong> G"
  by (simp add: iso_def hom_def id_type id_bij)


lemma (in group) iso_sym:
     "h \<in> G \<cong> H \<Longrightarrow> converse(h) \<in> H \<cong> G"
apply (simp add: iso_def bij_converse_bij, clarify)
apply (subgoal_tac "converse(h) \<in> carrier(H) \<rightarrow> carrier(G)")
 prefer 2 apply (simp add: bij_converse_bij bij_is_fun)
apply (auto intro: left_inverse_eq [of _ "carrier(G)" "carrier(H)"]
            simp add: hom_def bij_is_inj right_inverse_bij)
done

lemma (in group) iso_trans:
     "\<lbrakk>h \<in> G \<cong> H; i \<in> H \<cong> I\<rbrakk> \<Longrightarrow> i O h \<in> G \<cong> I"
  by (auto simp add: iso_def hom_compose comp_bij)

lemma DirProdGroup_commute_iso:
  assumes "group(G)" and "group(H)"
  shows "(\<lambda>\<langle>x,y\<rangle> \<in> carrier(G \<Otimes> H). \<langle>y,x\<rangle>) \<in> (G \<Otimes> H) \<cong> (H \<Otimes> G)"
proof -
  interpret group G by fact
  interpret group H by fact
  show ?thesis by (auto simp add: iso_def hom_def inj_def surj_def bij_def)
qed

lemma DirProdGroup_assoc_iso:
  assumes "group(G)" and "group(H)" and "group(I)"
  shows "(\<lambda><\<langle>x,y\<rangle>,z> \<in> carrier((G \<Otimes> H) \<Otimes> I). <x,\<langle>y,z\<rangle>>)
          \<in> ((G \<Otimes> H) \<Otimes> I) \<cong> (G \<Otimes> (H \<Otimes> I))"
proof -
  interpret group G by fact
  interpret group H by fact
  interpret group I by fact
  show ?thesis
    by (auto intro: lam_type simp add: iso_def hom_def inj_def surj_def bij_def)
qed

text\<open>Basis for homomorphism proofs: we assume two groups \<^term>\<open>G\<close> and
  \<^term>\<open>H\<close>, with a homomorphism \<^term>\<open>h\<close> between them\<close>
locale group_hom = G: group G + H: group H
  for G (structure) and H (structure) and h +
  assumes homh: "h \<in> hom(G,H)"
  notes hom_mult [simp] = hom_mult [OF homh]
    and hom_closed [simp] = hom_closed [OF homh]
    and hom_is_fun [simp] = hom_is_fun [OF homh]

lemma (in group_hom) one_closed [simp]:
  "h ` \<one> \<in> carrier(H)"
  by simp

lemma (in group_hom) hom_one [simp]:
  "h ` \<one> = \<one>\<^bsub>H\<^esub>"
proof -
  have "h ` \<one> \<cdot>\<^bsub>H\<^esub> \<one>\<^bsub>H\<^esub> = (h ` \<one>) \<cdot>\<^bsub>H\<^esub> (h ` \<one>)"
    by (simp add: hom_mult [symmetric] del: hom_mult)
  then show ?thesis by (simp del: H.r_one)
qed

lemma (in group_hom) inv_closed [simp]:
  "x \<in> carrier(G) \<Longrightarrow> h ` (inv x) \<in> carrier(H)"
  by simp

lemma (in group_hom) hom_inv [simp]:
  "x \<in> carrier(G) \<Longrightarrow> h ` (inv x) = inv\<^bsub>H\<^esub> (h ` x)"
proof -
  assume x: "x \<in> carrier(G)"
  then have "h ` x \<cdot>\<^bsub>H\<^esub> h ` (inv x) = \<one>\<^bsub>H\<^esub>"
    by (simp add: hom_mult [symmetric] G.r_inv del: hom_mult)
  also from x have "... = h ` x \<cdot>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h ` x)"
    by (simp add: hom_mult [symmetric] H.r_inv del: hom_mult)
  finally have "h ` x \<cdot>\<^bsub>H\<^esub> h ` (inv x) = h ` x \<cdot>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h ` x)" .
  with x show ?thesis by (simp del: H.inv)
qed

subsection \<open>Commutative Structures\<close>

text \<open>
  Naming convention: multiplicative structures that are commutative
  are called \emph{commutative}, additive structures are called
  \emph{Abelian}.
\<close>

subsection \<open>Definition\<close>

locale comm_monoid = monoid +
  assumes m_comm: "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> x \<cdot> y = y \<cdot> x"

lemma (in comm_monoid) m_lcomm:
  "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G); z \<in> carrier(G)\<rbrakk> \<Longrightarrow>
   x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  assume xyz: "x \<in> carrier(G)"  "y \<in> carrier(G)"  "z \<in> carrier(G)"
  from xyz have "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z" by (simp add: m_assoc)
  also from xyz have "... = (y \<cdot> x) \<cdot> z" by (simp add: m_comm)
  also from xyz have "... = y \<cdot> (x \<cdot> z)" by (simp add: m_assoc)
  finally show ?thesis .
qed

lemmas (in comm_monoid) m_ac = m_assoc m_comm m_lcomm

locale comm_group = comm_monoid + group

lemma (in comm_group) inv_mult:
  "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> inv (x \<cdot> y) = inv x \<cdot> inv y"
  by (simp add: m_ac inv_mult_group)


lemma (in group) subgroup_self: "subgroup (carrier(G),G)"
by (simp add: subgroup_def)

lemma (in group) subgroup_imp_group:
  "subgroup(H,G) \<Longrightarrow> group (update_carrier(G,H))"
by (simp add: subgroup.is_group)

lemma (in group) subgroupI:
  assumes subset: "H \<subseteq> carrier(G)" and non_empty: "H \<noteq> 0"
    and "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
    and "\<And>a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<cdot> b \<in> H"
  shows "subgroup(H,G)"
proof (simp add: subgroup_def assms)
  show "\<one> \<in> H"
    by (rule one_in_subset) (auto simp only: assms)
qed


subsection \<open>Bijections of a Set, Permutation Groups, Automorphism Groups\<close>

definition
  BijGroup :: "i\<Rightarrow>i" where
  "BijGroup(S) \<equiv>
    <bij(S,S),
     \<lambda>\<langle>g,f\<rangle> \<in> bij(S,S) \<times> bij(S,S). g O f,
     id(S), 0>"


subsection \<open>Bijections Form a Group\<close>

theorem group_BijGroup: "group(BijGroup(S))"
apply (simp add: BijGroup_def)
apply (rule groupI)
    apply (simp_all add: id_bij comp_bij comp_assoc)
 apply (simp add: id_bij bij_is_fun left_comp_id [of _ S S] fun_is_rel)
apply (blast intro: left_comp_inverse bij_is_inj bij_converse_bij)
done


subsection\<open>Automorphisms Form a Group\<close>

lemma Bij_Inv_mem: "\<lbrakk>f \<in> bij(S,S);  x \<in> S\<rbrakk> \<Longrightarrow> converse(f) ` x \<in> S"
by (blast intro: apply_funtype bij_is_fun bij_converse_bij)

lemma inv_BijGroup: "f \<in> bij(S,S) \<Longrightarrow> m_inv (BijGroup(S), f) = converse(f)"
apply (rule group.inv_equality)
apply (rule group_BijGroup)
apply (simp_all add: BijGroup_def bij_converse_bij
          left_comp_inverse [OF bij_is_inj])
done

lemma iso_is_bij: "h \<in> G \<cong> H \<Longrightarrow> h \<in> bij(carrier(G), carrier(H))"
by (simp add: iso_def)


definition
  auto :: "i\<Rightarrow>i" where
  "auto(G) \<equiv> iso(G,G)"

definition
  AutoGroup :: "i\<Rightarrow>i" where
  "AutoGroup(G) \<equiv> update_carrier(BijGroup(carrier(G)), auto(G))"


lemma (in group) id_in_auto: "id(carrier(G)) \<in> auto(G)"
  by (simp add: iso_refl auto_def)

lemma (in group) subgroup_auto:
      "subgroup (auto(G)) (BijGroup (carrier(G)))"
proof (rule subgroup.intro)
  show "auto(G) \<subseteq> carrier (BijGroup (carrier(G)))"
    by (auto simp add: auto_def BijGroup_def iso_def)
next
  fix x y
  assume "x \<in> auto(G)" "y \<in> auto(G)"
  thus "x \<cdot>\<^bsub>BijGroup (carrier(G))\<^esub> y \<in> auto(G)"
    by (auto simp add: BijGroup_def auto_def iso_def bij_is_fun
                       group.hom_compose comp_bij)
next
  show "\<one>\<^bsub>BijGroup (carrier(G))\<^esub> \<in> auto(G)" by (simp add:  BijGroup_def id_in_auto)
next
  fix x
  assume "x \<in> auto(G)"
  thus "inv\<^bsub>BijGroup (carrier(G))\<^esub> x \<in> auto(G)"
    by (simp add: auto_def inv_BijGroup iso_is_bij iso_sym)
qed

theorem (in group) AutoGroup: "group (AutoGroup(G))"
by (simp add: AutoGroup_def subgroup.is_group subgroup_auto group_BijGroup)



subsection\<open>Cosets and Quotient Groups\<close>

definition
  r_coset  :: "[i,i,i] \<Rightarrow> i"  (infixl \<open>#>\<index>\<close> 60) where
  "H #>\<^bsub>G\<^esub> a \<equiv> \<Union>h\<in>H. {h \<cdot>\<^bsub>G\<^esub> a}"

definition
  l_coset  :: "[i,i,i] \<Rightarrow> i"  (infixl \<open><#\<index>\<close> 60) where
  "a <#\<^bsub>G\<^esub> H \<equiv> \<Union>h\<in>H. {a \<cdot>\<^bsub>G\<^esub> h}"

definition
  RCOSETS  :: "[i,i] \<Rightarrow> i"  (\<open>rcosets\<index> _\<close> [81] 80) where
  "rcosets\<^bsub>G\<^esub> H \<equiv> \<Union>a\<in>carrier(G). {H #>\<^bsub>G\<^esub> a}"

definition
  set_mult :: "[i,i,i] \<Rightarrow> i"  (infixl \<open><#>\<index>\<close> 60) where
  "H <#>\<^bsub>G\<^esub> K \<equiv> \<Union>h\<in>H. \<Union>k\<in>K. {h \<cdot>\<^bsub>G\<^esub> k}"

definition
  SET_INV  :: "[i,i] \<Rightarrow> i"  (\<open>set'_inv\<index> _\<close> [81] 80) where
  "set_inv\<^bsub>G\<^esub> H \<equiv> \<Union>h\<in>H. {inv\<^bsub>G\<^esub> h}"


locale normal = subgroup + group +
  assumes coset_eq: "(\<forall>x \<in> carrier(G). H #> x = x <# H)"

notation
  normal  (infixl \<open>\<lhd>\<close> 60)


subsection \<open>Basic Properties of Cosets\<close>

lemma (in group) coset_mult_assoc:
     "\<lbrakk>M \<subseteq> carrier(G); g \<in> carrier(G); h \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (M #> g) #> h = M #> (g \<cdot> h)"
by (force simp add: r_coset_def m_assoc)

lemma (in group) coset_mult_one [simp]: "M \<subseteq> carrier(G) \<Longrightarrow> M #> \<one> = M"
by (force simp add: r_coset_def)

lemma (in group) solve_equation:
    "\<lbrakk>subgroup(H,G); x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> \<exists>h\<in>H. y = h \<cdot> x"
apply (rule bexI [of _ "y \<cdot> (inv x)"])
apply (auto simp add: subgroup.m_closed subgroup.m_inv_closed m_assoc
                      subgroup.subset [THEN subsetD])
done

lemma (in group) repr_independence:
     "\<lbrakk>y \<in> H #> x;  x \<in> carrier(G); subgroup(H,G)\<rbrakk> \<Longrightarrow> H #> x = H #> y"
by (auto simp add: r_coset_def m_assoc [symmetric]
                   subgroup.subset [THEN subsetD]
                   subgroup.m_closed solve_equation)

lemma (in group) coset_join2:
     "\<lbrakk>x \<in> carrier(G);  subgroup(H,G);  x\<in>H\<rbrakk> \<Longrightarrow> H #> x = H"
  \<comment> \<open>Alternative proof is to put \<^term>\<open>x=\<one>\<close> in \<open>repr_independence\<close>.\<close>
by (force simp add: subgroup.m_closed r_coset_def solve_equation)

lemma (in group) r_coset_subset_G:
     "\<lbrakk>H \<subseteq> carrier(G); x \<in> carrier(G)\<rbrakk> \<Longrightarrow> H #> x \<subseteq> carrier(G)"
by (auto simp add: r_coset_def)

lemma (in group) rcosI:
     "\<lbrakk>h \<in> H; H \<subseteq> carrier(G); x \<in> carrier(G)\<rbrakk> \<Longrightarrow> h \<cdot> x \<in> H #> x"
by (auto simp add: r_coset_def)

lemma (in group) rcosetsI:
     "\<lbrakk>H \<subseteq> carrier(G); x \<in> carrier(G)\<rbrakk> \<Longrightarrow> H #> x \<in> rcosets H"
by (auto simp add: RCOSETS_def)


text\<open>Really needed?\<close>
lemma (in group) transpose_inv:
     "\<lbrakk>x \<cdot> y = z;  x \<in> carrier(G);  y \<in> carrier(G);  z \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (inv x) \<cdot> z = y"
by (force simp add: m_assoc [symmetric])



subsection \<open>Normal subgroups\<close>

lemma normal_imp_subgroup: "H \<lhd> G \<Longrightarrow> subgroup(H,G)"
  by (simp add: normal_def subgroup_def)

lemma (in group) normalI:
  "subgroup(H,G) \<Longrightarrow> (\<forall>x \<in> carrier(G). H #> x = x <# H) \<Longrightarrow> H \<lhd> G"
  by (simp add: normal_def normal_axioms_def)

lemma (in normal) inv_op_closed1:
     "\<lbrakk>x \<in> carrier(G); h \<in> H\<rbrakk> \<Longrightarrow> (inv x) \<cdot> h \<cdot> x \<in> H"
apply (insert coset_eq)
apply (auto simp add: l_coset_def r_coset_def)
apply (drule bspec, assumption)
apply (drule equalityD1 [THEN subsetD], blast, clarify)
apply (simp add: m_assoc)
apply (simp add: m_assoc [symmetric])
done

lemma (in normal) inv_op_closed2:
     "\<lbrakk>x \<in> carrier(G); h \<in> H\<rbrakk> \<Longrightarrow> x \<cdot> h \<cdot> (inv x) \<in> H"
apply (subgoal_tac "inv (inv x) \<cdot> h \<cdot> (inv x) \<in> H")
apply simp
apply (blast intro: inv_op_closed1)
done

text\<open>Alternative characterization of normal subgroups\<close>
lemma (in group) normal_inv_iff:
     "(N \<lhd> G) \<longleftrightarrow>
      (subgroup(N,G) \<and> (\<forall>x \<in> carrier(G). \<forall>h \<in> N. x \<cdot> h \<cdot> (inv x) \<in> N))"
      (is "_ \<longleftrightarrow> ?rhs")
proof
  assume N: "N \<lhd> G"
  show ?rhs
    by (blast intro: N normal.inv_op_closed2 normal_imp_subgroup)
next
  assume ?rhs
  hence sg: "subgroup(N,G)"
    and closed: "\<And>x. x\<in>carrier(G) \<Longrightarrow> \<forall>h\<in>N. x \<cdot> h \<cdot> inv x \<in> N" by auto
  hence sb: "N \<subseteq> carrier(G)" by (simp add: subgroup.subset)
  show "N \<lhd> G"
  proof (intro normalI [OF sg], simp add: l_coset_def r_coset_def, clarify)
    fix x
    assume x: "x \<in> carrier(G)"
    show "(\<Union>h\<in>N. {h \<cdot> x}) = (\<Union>h\<in>N. {x \<cdot> h})"
    proof
      show "(\<Union>h\<in>N. {h \<cdot> x}) \<subseteq> (\<Union>h\<in>N. {x \<cdot> h})"
      proof clarify
        fix n
        assume n: "n \<in> N"
        show "n \<cdot> x \<in> (\<Union>h\<in>N. {x \<cdot> h})"
        proof (rule UN_I)
          from closed [of "inv x"]
          show "inv x \<cdot> n \<cdot> x \<in> N" by (simp add: x n)
          show "n \<cdot> x \<in> {x \<cdot> (inv x \<cdot> n \<cdot> x)}"
            by (simp add: x n m_assoc [symmetric] sb [THEN subsetD])
        qed
      qed
    next
      show "(\<Union>h\<in>N. {x \<cdot> h}) \<subseteq> (\<Union>h\<in>N. {h \<cdot> x})"
      proof clarify
        fix n
        assume n: "n \<in> N"
        show "x \<cdot> n \<in> (\<Union>h\<in>N. {h \<cdot> x})"
        proof (rule UN_I)
          show "x \<cdot> n \<cdot> inv x \<in> N" by (simp add: x n closed)
          show "x \<cdot> n \<in> {x \<cdot> n \<cdot> inv x \<cdot> x}"
            by (simp add: x n m_assoc sb [THEN subsetD])
        qed
      qed
    qed
  qed
qed


subsection\<open>More Properties of Cosets\<close>

lemma (in group) l_coset_subset_G:
     "\<lbrakk>H \<subseteq> carrier(G); x \<in> carrier(G)\<rbrakk> \<Longrightarrow> x <# H \<subseteq> carrier(G)"
by (auto simp add: l_coset_def subsetD)

lemma (in group) l_coset_swap:
     "\<lbrakk>y \<in> x <# H;  x \<in> carrier(G);  subgroup(H,G)\<rbrakk> \<Longrightarrow> x \<in> y <# H"
proof (simp add: l_coset_def)
  assume "\<exists>h\<in>H. y = x \<cdot> h"
    and x: "x \<in> carrier(G)"
    and sb: "subgroup(H,G)"
  then obtain h' where h': "h' \<in> H \<and> x \<cdot> h' = y" by blast
  show "\<exists>h\<in>H. x = y \<cdot> h"
  proof
    show "x = y \<cdot> inv h'" using h' x sb
      by (auto simp add: m_assoc subgroup.subset [THEN subsetD])
    show "inv h' \<in> H" using h' sb
      by (auto simp add: subgroup.subset [THEN subsetD] subgroup.m_inv_closed)
  qed
qed

lemma (in group) l_coset_carrier:
     "\<lbrakk>y \<in> x <# H;  x \<in> carrier(G);  subgroup(H,G)\<rbrakk> \<Longrightarrow> y \<in> carrier(G)"
by (auto simp add: l_coset_def m_assoc
                   subgroup.subset [THEN subsetD] subgroup.m_closed)

lemma (in group) l_repr_imp_subset:
  assumes y: "y \<in> x <# H" and x: "x \<in> carrier(G)" and sb: "subgroup(H,G)"
  shows "y <# H \<subseteq> x <# H"
proof -
  from y
  obtain h' where "h' \<in> H" "x \<cdot> h' = y" by (auto simp add: l_coset_def)
  thus ?thesis using x sb
    by (auto simp add: l_coset_def m_assoc
                       subgroup.subset [THEN subsetD] subgroup.m_closed)
qed

lemma (in group) l_repr_independence:
  assumes y: "y \<in> x <# H" and x: "x \<in> carrier(G)" and sb: "subgroup(H,G)"
  shows "x <# H = y <# H"
proof
  show "x <# H \<subseteq> y <# H"
    by (rule l_repr_imp_subset,
        (blast intro: l_coset_swap l_coset_carrier y x sb)+)
  show "y <# H \<subseteq> x <# H" by (rule l_repr_imp_subset [OF y x sb])
qed

lemma (in group) setmult_subset_G:
     "\<lbrakk>H \<subseteq> carrier(G); K \<subseteq> carrier(G)\<rbrakk> \<Longrightarrow> H <#> K \<subseteq> carrier(G)"
by (auto simp add: set_mult_def subsetD)

lemma (in group) subgroup_mult_id: "subgroup(H,G) \<Longrightarrow> H <#> H = H"
apply (rule equalityI)
apply (auto simp add: subgroup.m_closed set_mult_def Sigma_def image_def)
apply (rule_tac x = x in bexI)
apply (rule bexI [of _ "\<one>"])
apply (auto simp add: subgroup.one_closed subgroup.subset [THEN subsetD])
done


subsubsection \<open>Set of inverses of an \<open>r_coset\<close>.\<close>

lemma (in normal) rcos_inv:
  assumes x:     "x \<in> carrier(G)"
  shows "set_inv (H #> x) = H #> (inv x)"
proof (simp add: r_coset_def SET_INV_def x inv_mult_group, safe intro!: equalityI)
  fix h
  assume h: "h \<in> H"
  {
    show "inv x \<cdot> inv h \<in> (\<Union>j\<in>H. {j \<cdot> inv x})"
    proof (rule UN_I)
      show "inv x \<cdot> inv h \<cdot> x \<in> H"
        by (simp add: inv_op_closed1 h x)
      show "inv x \<cdot> inv h \<in> {inv x \<cdot> inv h \<cdot> x \<cdot> inv x}"
        by (simp add: h x m_assoc)
    qed
  next
    show "h \<cdot> inv x \<in> (\<Union>j\<in>H. {inv x \<cdot> inv j})"
    proof (rule UN_I)
      show "x \<cdot> inv h \<cdot> inv x \<in> H"
        by (simp add: inv_op_closed2 h x)
      show "h \<cdot> inv x \<in> {inv x \<cdot> inv (x \<cdot> inv h \<cdot> inv x)}"
        by (simp add: h x m_assoc [symmetric] inv_mult_group)
    qed
  }
qed



subsubsection \<open>Theorems for \<open><#>\<close> with \<open>#>\<close> or \<open><#\<close>.\<close>

lemma (in group) setmult_rcos_assoc:
     "\<lbrakk>H \<subseteq> carrier(G); K \<subseteq> carrier(G); x \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> H <#> (K #> x) = (H <#> K) #> x"
by (force simp add: r_coset_def set_mult_def m_assoc)

lemma (in group) rcos_assoc_lcos:
     "\<lbrakk>H \<subseteq> carrier(G); K \<subseteq> carrier(G); x \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (H #> x) <#> K = H <#> (x <# K)"
by (force simp add: r_coset_def l_coset_def set_mult_def m_assoc)

lemma (in normal) rcos_mult_step1:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (H #> x) <#> (H #> y) = (H <#> (x <# H)) #> y"
by (simp add: setmult_rcos_assoc subset
              r_coset_subset_G l_coset_subset_G rcos_assoc_lcos)

lemma (in normal) rcos_mult_step2:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (H <#> (x <# H)) #> y = (H <#> (H #> x)) #> y"
by (insert coset_eq, simp add: normal_def)

lemma (in normal) rcos_mult_step3:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (H <#> (H #> x)) #> y = H #> (x \<cdot> y)"
  by (simp add: setmult_rcos_assoc coset_mult_assoc
              subgroup_mult_id subset normal_axioms normal.axioms)

lemma (in normal) rcos_sum:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (H #> x) <#> (H #> y) = H #> (x \<cdot> y)"
by (simp add: rcos_mult_step1 rcos_mult_step2 rcos_mult_step3)

lemma (in normal) rcosets_mult_eq: "M \<in> rcosets H \<Longrightarrow> H <#> M = M"
  \<comment> \<open>generalizes \<open>subgroup_mult_id\<close>\<close>
  by (auto simp add: RCOSETS_def subset
        setmult_rcos_assoc subgroup_mult_id normal_axioms normal.axioms)


subsubsection\<open>Two distinct right cosets are disjoint\<close>

definition
  r_congruent :: "[i,i] \<Rightarrow> i" (\<open>rcong\<index> _\<close> [60] 60) where
  "rcong\<^bsub>G\<^esub> H \<equiv> {\<langle>x,y\<rangle> \<in> carrier(G) * carrier(G). inv\<^bsub>G\<^esub> x \<cdot>\<^bsub>G\<^esub> y \<in> H}"


lemma (in subgroup) equiv_rcong:
   assumes "group(G)"
   shows "equiv (carrier(G), rcong H)"
proof -
  interpret group G by fact
  show ?thesis proof (simp add: equiv_def, intro conjI)
    show "rcong H \<subseteq> carrier(G) \<times> carrier(G)"
      by (auto simp add: r_congruent_def)
  next
    show "refl (carrier(G), rcong H)"
      by (auto simp add: r_congruent_def refl_def)
  next
    show "sym (rcong H)"
    proof (simp add: r_congruent_def sym_def, clarify)
      fix x y
      assume [simp]: "x \<in> carrier(G)" "y \<in> carrier(G)"
        and "inv x \<cdot> y \<in> H"
      hence "inv (inv x \<cdot> y) \<in> H" by simp
      thus "inv y \<cdot> x \<in> H" by (simp add: inv_mult_group)
    qed
  next
    show "trans (rcong H)"
    proof (simp add: r_congruent_def trans_def, clarify)
      fix x y z
      assume [simp]: "x \<in> carrier(G)" "y \<in> carrier(G)" "z \<in> carrier(G)"
        and "inv x \<cdot> y \<in> H" and "inv y \<cdot> z \<in> H"
      hence "(inv x \<cdot> y) \<cdot> (inv y \<cdot> z) \<in> H" by simp
      hence "inv x \<cdot> (y \<cdot> inv y) \<cdot> z \<in> H" by (simp add: m_assoc del: inv)
      thus "inv x \<cdot> z \<in> H" by simp
    qed
  qed
qed

text\<open>Equivalence classes of \<open>rcong\<close> correspond to left cosets.
  Was there a mistake in the definitions? I'd have expected them to
  correspond to right cosets.\<close>
lemma (in subgroup) l_coset_eq_rcong:
  assumes "group(G)"
  assumes a: "a \<in> carrier(G)"
  shows "a <# H = (rcong H) `` {a}"
proof -
  interpret group G by fact
  show ?thesis
    by (force simp add: r_congruent_def l_coset_def m_assoc [symmetric] a
      Collect_image_eq)
qed

lemma (in group) rcos_equation:
  assumes "subgroup(H, G)"
  shows
     "\<lbrakk>ha \<cdot> a = h \<cdot> b; a \<in> carrier(G);  b \<in> carrier(G);
        h \<in> H;  ha \<in> H;  hb \<in> H\<rbrakk>
      \<Longrightarrow> hb \<cdot> a \<in> (\<Union>h\<in>H. {h \<cdot> b})" (is "PROP ?P")
proof -
  interpret subgroup H G by fact
  show "PROP ?P"
    apply (rule UN_I [of "hb \<cdot> ((inv ha) \<cdot> h)"], simp)
    apply (simp add: m_assoc transpose_inv)
    done
qed

lemma (in group) rcos_disjoint:
  assumes "subgroup(H, G)"
  shows "\<lbrakk>a \<in> rcosets H; b \<in> rcosets H; a\<noteq>b\<rbrakk> \<Longrightarrow> a \<inter> b = 0" (is "PROP ?P")
proof -
  interpret subgroup H G by fact
  show "PROP ?P"
    apply (simp add: RCOSETS_def r_coset_def)
    apply (blast intro: rcos_equation assms sym)
    done
qed


subsection \<open>Order of a Group and Lagrange's Theorem\<close>

definition
  order :: "i \<Rightarrow> i" where
  "order(S) \<equiv> |carrier(S)|"

lemma (in group) rcos_self:
  assumes "subgroup(H, G)"
  shows "x \<in> carrier(G) \<Longrightarrow> x \<in> H #> x" (is "PROP ?P")
proof -
  interpret subgroup H G by fact
  show "PROP ?P"
    apply (simp add: r_coset_def)
    apply (rule_tac x="\<one>" in bexI) apply (auto)
    done
qed

lemma (in group) rcosets_part_G:
  assumes "subgroup(H, G)"
  shows "\<Union>(rcosets H) = carrier(G)"
proof -
  interpret subgroup H G by fact
  show ?thesis
    apply (rule equalityI)
    apply (force simp add: RCOSETS_def r_coset_def)
    apply (auto simp add: RCOSETS_def intro: rcos_self assms)
    done
qed

lemma (in group) cosets_finite:
     "\<lbrakk>c \<in> rcosets H;  H \<subseteq> carrier(G);  Finite (carrier(G))\<rbrakk> \<Longrightarrow> Finite(c)"
apply (auto simp add: RCOSETS_def)
apply (simp add: r_coset_subset_G [THEN subset_Finite])
done

text\<open>More general than the HOL version, which also requires \<^term>\<open>G\<close> to
      be finite.\<close>
lemma (in group) card_cosets_equal:
  assumes H:   "H \<subseteq> carrier(G)"
  shows "c \<in> rcosets H \<Longrightarrow> |c| = |H|"
proof (simp add: RCOSETS_def, clarify)
  fix a
  assume a: "a \<in> carrier(G)"
  show "|H #> a| = |H|"
  proof (rule eqpollI [THEN cardinal_cong])
    show "H #> a \<lesssim> H"
    proof (simp add: lepoll_def, intro exI)
      show "(\<lambda>y \<in> H#>a. y \<cdot> inv a) \<in> inj(H #> a, H)"
        by (auto intro: lam_type
                 simp add: inj_def r_coset_def m_assoc subsetD [OF H] a)
    qed
    show "H \<lesssim> H #> a"
    proof (simp add: lepoll_def, intro exI)
      show "(\<lambda>y\<in> H. y \<cdot> a) \<in> inj(H, H #> a)"
        by (auto intro: lam_type
                 simp add: inj_def r_coset_def  subsetD [OF H] a)
    qed
  qed
qed


lemma (in group) rcosets_subset_PowG:
     "subgroup(H,G) \<Longrightarrow> rcosets H \<subseteq> Pow(carrier(G))"
apply (simp add: RCOSETS_def)
apply (blast dest: r_coset_subset_G subgroup.subset)
done

theorem (in group) lagrange:
     "\<lbrakk>Finite(carrier(G)); subgroup(H,G)\<rbrakk>
      \<Longrightarrow> |rcosets H| #* |H| = order(G)"
apply (simp (no_asm_simp) add: order_def rcosets_part_G [symmetric])
apply (subst mult_commute)
apply (rule card_partition)
   apply (simp add: rcosets_subset_PowG [THEN subset_Finite])
  apply (simp add: rcosets_part_G)
 apply (simp add: card_cosets_equal [OF subgroup.subset])
apply (simp add: rcos_disjoint)
done


subsection \<open>Quotient Groups: Factorization of a Group\<close>

definition
  FactGroup :: "[i,i] \<Rightarrow> i" (infixl \<open>Mod\<close> 65) where
    \<comment> \<open>Actually defined for groups rather than monoids\<close>
  "G Mod H \<equiv>
     <rcosets\<^bsub>G\<^esub> H, \<lambda>\<langle>K1,K2\<rangle> \<in> (rcosets\<^bsub>G\<^esub> H) \<times> (rcosets\<^bsub>G\<^esub> H). K1 <#>\<^bsub>G\<^esub> K2, H, 0>"

lemma (in normal) setmult_closed:
     "\<lbrakk>K1 \<in> rcosets H; K2 \<in> rcosets H\<rbrakk> \<Longrightarrow> K1 <#> K2 \<in> rcosets H"
by (auto simp add: rcos_sum RCOSETS_def)

lemma (in normal) setinv_closed:
     "K \<in> rcosets H \<Longrightarrow> set_inv K \<in> rcosets H"
by (auto simp add: rcos_inv RCOSETS_def)

lemma (in normal) rcosets_assoc:
     "\<lbrakk>M1 \<in> rcosets H; M2 \<in> rcosets H; M3 \<in> rcosets H\<rbrakk>
      \<Longrightarrow> M1 <#> M2 <#> M3 = M1 <#> (M2 <#> M3)"
by (auto simp add: RCOSETS_def rcos_sum m_assoc)

lemma (in subgroup) subgroup_in_rcosets:
  assumes "group(G)"
  shows "H \<in> rcosets H"
proof -
  interpret group G by fact
  have "H #> \<one> = H"
    using _ subgroup_axioms by (rule coset_join2) simp_all
  then show ?thesis
    by (auto simp add: RCOSETS_def intro: sym)
qed

lemma (in normal) rcosets_inv_mult_group_eq:
     "M \<in> rcosets H \<Longrightarrow> set_inv M <#> M = H"
by (auto simp add: RCOSETS_def rcos_inv rcos_sum subgroup.subset normal_axioms normal.axioms)

theorem (in normal) factorgroup_is_group:
  "group (G Mod H)"
apply (simp add: FactGroup_def)
apply (rule groupI)
    apply (simp add: setmult_closed)
   apply (simp add: normal_imp_subgroup subgroup_in_rcosets)
  apply (simp add: setmult_closed rcosets_assoc)
 apply (simp add: normal_imp_subgroup
                  subgroup_in_rcosets rcosets_mult_eq)
apply (auto dest: rcosets_inv_mult_group_eq simp add: setinv_closed)
done

lemma (in normal) inv_FactGroup:
     "X \<in> carrier (G Mod H) \<Longrightarrow> inv\<^bsub>G Mod H\<^esub> X = set_inv X"
apply (rule group.inv_equality [OF factorgroup_is_group])
apply (simp_all add: FactGroup_def setinv_closed rcosets_inv_mult_group_eq)
done

text\<open>The coset map is a homomorphism from \<^term>\<open>G\<close> to the quotient group
  \<^term>\<open>G Mod H\<close>\<close>
lemma (in normal) r_coset_hom_Mod:
  "(\<lambda>a \<in> carrier(G). H #> a) \<in> hom(G, G Mod H)"
by (auto simp add: FactGroup_def RCOSETS_def hom_def rcos_sum intro: lam_type)


subsection\<open>The First Isomorphism Theorem\<close>

text\<open>The quotient by the kernel of a homomorphism is isomorphic to the
  range of that homomorphism.\<close>

definition
  kernel :: "[i,i,i] \<Rightarrow> i" where
    \<comment> \<open>the kernel of a homomorphism\<close>
  "kernel(G,H,h) \<equiv> {x \<in> carrier(G). h ` x = \<one>\<^bsub>H\<^esub>}"

lemma (in group_hom) subgroup_kernel: "subgroup (kernel(G,H,h), G)"
apply (rule subgroup.intro)
apply (auto simp add: kernel_def group.intro)
done

text\<open>The kernel of a homomorphism is a normal subgroup\<close>
lemma (in group_hom) normal_kernel: "(kernel(G,H,h)) \<lhd> G"
apply (simp add: group.normal_inv_iff subgroup_kernel group.intro)
apply (simp add: kernel_def)
done

lemma (in group_hom) FactGroup_nonempty:
  assumes X: "X \<in> carrier (G Mod kernel(G,H,h))"
  shows "X \<noteq> 0"
proof -
  from X
  obtain g where "g \<in> carrier(G)"
             and "X = kernel(G,H,h) #> g"
    by (auto simp add: FactGroup_def RCOSETS_def)
  thus ?thesis
   by (auto simp add: kernel_def r_coset_def image_def intro: hom_one)
qed


lemma (in group_hom) FactGroup_contents_mem:
  assumes X: "X \<in> carrier (G Mod (kernel(G,H,h)))"
  shows "contents (h``X) \<in> carrier(H)"
proof -
  from X
  obtain g where g: "g \<in> carrier(G)"
             and "X = kernel(G,H,h) #> g"
    by (auto simp add: FactGroup_def RCOSETS_def)
  hence "h `` X = {h ` g}"
    by (auto simp add: kernel_def r_coset_def image_UN
                       image_eq_UN [OF hom_is_fun] g)
  thus ?thesis by (auto simp add: g)
qed

lemma mult_FactGroup:
     "\<lbrakk>X \<in> carrier(G Mod H); X' \<in> carrier(G Mod H)\<rbrakk>
      \<Longrightarrow> X \<cdot>\<^bsub>(G Mod H)\<^esub> X' = X <#>\<^bsub>G\<^esub> X'"
by (simp add: FactGroup_def)

lemma (in normal) FactGroup_m_closed:
     "\<lbrakk>X \<in> carrier(G Mod H); X' \<in> carrier(G Mod H)\<rbrakk>
      \<Longrightarrow> X <#>\<^bsub>G\<^esub> X' \<in> carrier(G Mod H)"
by (simp add: FactGroup_def setmult_closed)

lemma (in group_hom) FactGroup_hom:
     "(\<lambda>X \<in> carrier(G Mod (kernel(G,H,h))). contents (h``X))
      \<in> hom (G Mod (kernel(G,H,h)), H)"
proof (simp add: hom_def FactGroup_contents_mem lam_type mult_FactGroup normal.FactGroup_m_closed [OF normal_kernel], intro ballI)
  fix X and X'
  assume X:  "X  \<in> carrier (G Mod kernel(G,H,h))"
     and X': "X' \<in> carrier (G Mod kernel(G,H,h))"
  then
  obtain g and g'
           where "g \<in> carrier(G)" and "g' \<in> carrier(G)"
             and "X = kernel(G,H,h) #> g" and "X' = kernel(G,H,h) #> g'"
    by (auto simp add: FactGroup_def RCOSETS_def)
  hence all: "\<forall>x\<in>X. h ` x = h ` g" "\<forall>x\<in>X'. h ` x = h ` g'"
    and Xsub: "X \<subseteq> carrier(G)" and X'sub: "X' \<subseteq> carrier(G)"
    by (force simp add: kernel_def r_coset_def image_def)+
  hence "h `` (X <#> X') = {h ` g \<cdot>\<^bsub>H\<^esub> h ` g'}" using X X'
    by (auto dest!: FactGroup_nonempty
             simp add: set_mult_def image_eq_UN [OF hom_is_fun] image_UN
                       subsetD [OF Xsub] subsetD [OF X'sub])
  thus "contents (h `` (X <#> X')) = contents (h `` X) \<cdot>\<^bsub>H\<^esub> contents (h `` X')"
    by (simp add: all image_eq_UN [OF hom_is_fun] FactGroup_nonempty
                  X X' Xsub X'sub)
qed


text\<open>Lemma for the following injectivity result\<close>
lemma (in group_hom) FactGroup_subset:
     "\<lbrakk>g \<in> carrier(G); g' \<in> carrier(G); h ` g = h ` g'\<rbrakk>
      \<Longrightarrow>  kernel(G,H,h) #> g \<subseteq> kernel(G,H,h) #> g'"
apply (clarsimp simp add: kernel_def r_coset_def image_def)
apply (rename_tac y)
apply (rule_tac x="y \<cdot> g \<cdot> inv g'" in bexI)
apply (simp_all add: G.m_assoc)
done

lemma (in group_hom) FactGroup_inj:
     "(\<lambda>X\<in>carrier (G Mod kernel(G,H,h)). contents (h `` X))
      \<in> inj(carrier (G Mod kernel(G,H,h)), carrier(H))"
proof (simp add: inj_def FactGroup_contents_mem lam_type, clarify)
  fix X and X'
  assume X:  "X  \<in> carrier (G Mod kernel(G,H,h))"
     and X': "X' \<in> carrier (G Mod kernel(G,H,h))"
  then
  obtain g and g'
           where gX: "g \<in> carrier(G)"  "g' \<in> carrier(G)"
              "X = kernel(G,H,h) #> g" "X' = kernel(G,H,h) #> g'"
    by (auto simp add: FactGroup_def RCOSETS_def)
  hence all: "\<forall>x\<in>X. h ` x = h ` g" "\<forall>x\<in>X'. h ` x = h ` g'"
    and Xsub: "X \<subseteq> carrier(G)" and X'sub: "X' \<subseteq> carrier(G)"
    by (force simp add: kernel_def r_coset_def image_def)+
  assume "contents (h `` X) = contents (h `` X')"
  hence h: "h ` g = h ` g'"
    by (simp add: all image_eq_UN [OF hom_is_fun] FactGroup_nonempty
                  X X' Xsub X'sub)
  show "X=X'" by (rule equalityI) (simp_all add: FactGroup_subset h gX)
qed


lemma (in group_hom) kernel_rcoset_subset:
  assumes g: "g \<in> carrier(G)"
  shows "kernel(G,H,h) #> g \<subseteq> carrier (G)"
    by (auto simp add: g kernel_def r_coset_def)



text\<open>If the homomorphism \<^term>\<open>h\<close> is onto \<^term>\<open>H\<close>, then so is the
homomorphism from the quotient group\<close>
lemma (in group_hom) FactGroup_surj:
  assumes h: "h \<in> surj(carrier(G), carrier(H))"
  shows "(\<lambda>X\<in>carrier (G Mod kernel(G,H,h)). contents (h `` X))
         \<in> surj(carrier (G Mod kernel(G,H,h)), carrier(H))"
proof (simp add: surj_def FactGroup_contents_mem lam_type, clarify)
  fix y
  assume y: "y \<in> carrier(H)"
  with h obtain g where g: "g \<in> carrier(G)" "h ` g = y"
    by (auto simp add: surj_def)
  hence "(\<Union>x\<in>kernel(G,H,h) #> g. {h ` x}) = {y}"
    by (auto simp add: y kernel_def r_coset_def)
  with g show "\<exists>x\<in>carrier(G Mod kernel(G, H, h)). contents(h `` x) = y"
        \<comment> \<open>The witness is \<^term>\<open>kernel(G,H,h) #> g\<close>\<close>
    by (force simp add: FactGroup_def RCOSETS_def
           image_eq_UN [OF hom_is_fun] kernel_rcoset_subset)
qed


text\<open>If \<^term>\<open>h\<close> is a homomorphism from \<^term>\<open>G\<close> onto \<^term>\<open>H\<close>, then the
 quotient group \<^term>\<open>G Mod (kernel(G,H,h))\<close> is isomorphic to \<^term>\<open>H\<close>.\<close>
theorem (in group_hom) FactGroup_iso:
  "h \<in> surj(carrier(G), carrier(H))
   \<Longrightarrow> (\<lambda>X\<in>carrier (G Mod kernel(G,H,h)). contents (h``X)) \<in> (G Mod (kernel(G,H,h))) \<cong> H"
by (simp add: iso_def FactGroup_hom FactGroup_inj bij_def FactGroup_surj)

end
