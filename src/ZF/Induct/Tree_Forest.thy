(*  Title:      ZF/Induct/Tree_Forest.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section \<open>Trees and forests, a mutually recursive type definition\<close>

theory Tree_Forest imports ZF begin

subsection \<open>Datatype definition\<close>

consts
  tree :: "i \<Rightarrow> i"
  forest :: "i \<Rightarrow> i"
  tree_forest :: "i \<Rightarrow> i"

datatype "tree(A)" = Tcons ("a \<in> A", "f \<in> forest(A)")
  and "forest(A)" = Fnil | Fcons ("t \<in> tree(A)", "f \<in> forest(A)")

(* FIXME *)
lemmas tree'induct =
    tree_forest.mutual_induct [THEN conjunct1, THEN spec, THEN [2] rev_mp, of concl: _ t, consumes 1]
  and forest'induct =
    tree_forest.mutual_induct [THEN conjunct2, THEN spec, THEN [2] rev_mp, of concl: _ f, consumes 1]
  for t f

declare tree_forest.intros [simp, TC]

lemma tree_def: "tree(A) \<equiv> Part(tree_forest(A), Inl)"
  by (simp only: tree_forest.defs)

lemma forest_def: "forest(A) \<equiv> Part(tree_forest(A), Inr)"
  by (simp only: tree_forest.defs)


text \<open>
  \medskip \<^term>\<open>tree_forest(A)\<close> as the union of \<^term>\<open>tree(A)\<close>
  and \<^term>\<open>forest(A)\<close>.
\<close>

lemma tree_subset_TF: "tree(A) \<subseteq> tree_forest(A)"
    unfolding tree_forest.defs
  apply (rule Part_subset)
  done

lemma treeI [TC]: "x \<in> tree(A) \<Longrightarrow> x \<in> tree_forest(A)"
  by (rule tree_subset_TF [THEN subsetD])

lemma forest_subset_TF: "forest(A) \<subseteq> tree_forest(A)"
    unfolding tree_forest.defs
  apply (rule Part_subset)
  done

lemma treeI' [TC]: "x \<in> forest(A) \<Longrightarrow> x \<in> tree_forest(A)"
  by (rule forest_subset_TF [THEN subsetD])

lemma TF_equals_Un: "tree(A) \<union> forest(A) = tree_forest(A)"
  apply (insert tree_subset_TF forest_subset_TF)
  apply (auto intro!: equalityI tree_forest.intros elim: tree_forest.cases)
  done

lemma tree_forest_unfold:
  "tree_forest(A) = (A \<times> forest(A)) + ({0} + tree(A) \<times> forest(A))"
    \<comment> \<open>NOT useful, but interesting \dots\<close>
  supply rews = tree_forest.con_defs tree_def forest_def
    unfolding tree_def forest_def
  apply (fast intro!: tree_forest.intros [unfolded rews, THEN PartD1]
    elim: tree_forest.cases [unfolded rews])
  done

lemma tree_forest_unfold':
  "tree_forest(A) =
    A \<times> Part(tree_forest(A), \<lambda>w. Inr(w)) +
    {0} + Part(tree_forest(A), \<lambda>w. Inl(w)) * Part(tree_forest(A), \<lambda>w. Inr(w))"
  by (rule tree_forest_unfold [unfolded tree_def forest_def])

lemma tree_unfold: "tree(A) = {Inl(x). x \<in> A \<times> forest(A)}"
    unfolding tree_def forest_def
  apply (rule Part_Inl [THEN subst])
  apply (rule tree_forest_unfold' [THEN subst_context])
  done

lemma forest_unfold: "forest(A) = {Inr(x). x \<in> {0} + tree(A)*forest(A)}"
    unfolding tree_def forest_def
  apply (rule Part_Inr [THEN subst])
  apply (rule tree_forest_unfold' [THEN subst_context])
  done

text \<open>
  \medskip Type checking for recursor: Not needed; possibly interesting?
\<close>

lemma TF_rec_type:
  "\<lbrakk>z \<in> tree_forest(A);
      \<And>x f r. \<lbrakk>x \<in> A;  f \<in> forest(A);  r \<in> C(f)
\<rbrakk> \<Longrightarrow> b(x,f,r) \<in> C(Tcons(x,f));
      c \<in> C(Fnil);
      \<And>t f r1 r2. \<lbrakk>t \<in> tree(A);  f \<in> forest(A);  r1 \<in> C(t); r2 \<in> C(f)
\<rbrakk> \<Longrightarrow> d(t,f,r1,r2) \<in> C(Fcons(t,f))
\<rbrakk> \<Longrightarrow> tree_forest_rec(b,c,d,z) \<in> C(z)"
  by (induct_tac z) simp_all

lemma tree_forest_rec_type:
  "\<lbrakk>\<And>x f r. \<lbrakk>x \<in> A;  f \<in> forest(A);  r \<in> D(f)
\<rbrakk> \<Longrightarrow> b(x,f,r) \<in> C(Tcons(x,f));
      c \<in> D(Fnil);
      \<And>t f r1 r2. \<lbrakk>t \<in> tree(A);  f \<in> forest(A);  r1 \<in> C(t); r2 \<in> D(f)
\<rbrakk> \<Longrightarrow> d(t,f,r1,r2) \<in> D(Fcons(t,f))
\<rbrakk> \<Longrightarrow> (\<forall>t \<in> tree(A).    tree_forest_rec(b,c,d,t) \<in> C(t)) \<and>
          (\<forall>f \<in> forest(A). tree_forest_rec(b,c,d,f) \<in> D(f))"
    \<comment> \<open>Mutually recursive version.\<close>
    unfolding Ball_def
  apply (rule tree_forest.mutual_induct)
  apply simp_all
  done


subsection \<open>Operations\<close>

consts
  map :: "[i \<Rightarrow> i, i] \<Rightarrow> i"
  size :: "i \<Rightarrow> i"
  preorder :: "i \<Rightarrow> i"
  list_of_TF :: "i \<Rightarrow> i"
  of_list :: "i \<Rightarrow> i"
  reflect :: "i \<Rightarrow> i"

primrec
  "list_of_TF (Tcons(x,f)) = [Tcons(x,f)]"
  "list_of_TF (Fnil) = []"
  "list_of_TF (Fcons(t,tf)) = Cons (t, list_of_TF(tf))"

primrec
  "of_list([]) = Fnil"
  "of_list(Cons(t,l)) = Fcons(t, of_list(l))"

primrec
  "map (h, Tcons(x,f)) = Tcons(h(x), map(h,f))"
  "map (h, Fnil) = Fnil"
  "map (h, Fcons(t,tf)) = Fcons (map(h, t), map(h, tf))"

primrec
  "size (Tcons(x,f)) = succ(size(f))"
  "size (Fnil) = 0"
  "size (Fcons(t,tf)) = size(t) #+ size(tf)"

primrec
  "preorder (Tcons(x,f)) = Cons(x, preorder(f))"
  "preorder (Fnil) = Nil"
  "preorder (Fcons(t,tf)) = preorder(t) @ preorder(tf)"

primrec
  "reflect (Tcons(x,f)) = Tcons(x, reflect(f))"
  "reflect (Fnil) = Fnil"
  "reflect (Fcons(t,tf)) =
    of_list (list_of_TF (reflect(tf)) @ Cons(reflect(t), Nil))"


text \<open>
  \medskip \<open>list_of_TF\<close> and \<open>of_list\<close>.
\<close>

lemma list_of_TF_type [TC]:
    "z \<in> tree_forest(A) \<Longrightarrow> list_of_TF(z) \<in> list(tree(A))"
  by (induct set: tree_forest) simp_all

lemma of_list_type [TC]: "l \<in> list(tree(A)) \<Longrightarrow> of_list(l) \<in> forest(A)"
  by (induct set: list) simp_all

text \<open>
  \medskip \<open>map\<close>.
\<close>

lemma
  assumes "\<And>x. x \<in> A \<Longrightarrow> h(x): B"
  shows map_tree_type: "t \<in> tree(A) \<Longrightarrow> map(h,t) \<in> tree(B)"
    and map_forest_type: "f \<in> forest(A) \<Longrightarrow> map(h,f) \<in> forest(B)"
  using assms
  by (induct rule: tree'induct forest'induct) simp_all

text \<open>
  \medskip \<open>size\<close>.
\<close>

lemma size_type [TC]: "z \<in> tree_forest(A) \<Longrightarrow> size(z) \<in> nat"
  by (induct set: tree_forest) simp_all


text \<open>
  \medskip \<open>preorder\<close>.
\<close>

lemma preorder_type [TC]: "z \<in> tree_forest(A) \<Longrightarrow> preorder(z) \<in> list(A)"
  by (induct set: tree_forest) simp_all


text \<open>
  \medskip Theorems about \<open>list_of_TF\<close> and \<open>of_list\<close>.
\<close>

lemma forest_induct [consumes 1, case_names Fnil Fcons]:
  "\<lbrakk>f \<in> forest(A);
      R(Fnil);
      \<And>t f. \<lbrakk>t \<in> tree(A);  f \<in> forest(A);  R(f)\<rbrakk> \<Longrightarrow> R(Fcons(t,f))
\<rbrakk> \<Longrightarrow> R(f)"
  \<comment> \<open>Essentially the same as list induction.\<close>
  apply (erule tree_forest.mutual_induct
      [THEN conjunct2, THEN spec, THEN [2] rev_mp])
    apply (rule TrueI)
   apply simp
  apply simp
  done

lemma forest_iso: "f \<in> forest(A) \<Longrightarrow> of_list(list_of_TF(f)) = f"
  by (induct rule: forest_induct) simp_all

lemma tree_list_iso: "ts: list(tree(A)) \<Longrightarrow> list_of_TF(of_list(ts)) = ts"
  by (induct set: list) simp_all


text \<open>
  \medskip Theorems about \<open>map\<close>.
\<close>

lemma map_ident: "z \<in> tree_forest(A) \<Longrightarrow> map(\<lambda>u. u, z) = z"
  by (induct set: tree_forest) simp_all

lemma map_compose:
    "z \<in> tree_forest(A) \<Longrightarrow> map(h, map(j,z)) = map(\<lambda>u. h(j(u)), z)"
  by (induct set: tree_forest) simp_all


text \<open>
  \medskip Theorems about \<open>size\<close>.
\<close>

lemma size_map: "z \<in> tree_forest(A) \<Longrightarrow> size(map(h,z)) = size(z)"
  by (induct set: tree_forest) simp_all

lemma size_length: "z \<in> tree_forest(A) \<Longrightarrow> size(z) = length(preorder(z))"
  by (induct set: tree_forest) (simp_all add: length_app)

text \<open>
  \medskip Theorems about \<open>preorder\<close>.
\<close>

lemma preorder_map:
    "z \<in> tree_forest(A) \<Longrightarrow> preorder(map(h,z)) = List.map(h, preorder(z))"
  by (induct set: tree_forest) (simp_all add: map_app_distrib)

end
