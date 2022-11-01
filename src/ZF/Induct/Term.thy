(*  Title:      ZF/Induct/Term.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section \<open>Terms over an alphabet\<close>

theory Term imports ZF begin

text \<open>
  Illustrates the list functor (essentially the same type as in \<open>Trees_Forest\<close>).
\<close>

consts
  "term" :: "i \<Rightarrow> i"

datatype "term(A)" = Apply ("a \<in> A", "l \<in> list(term(A))")
  monos list_mono
  type_elims list_univ [THEN subsetD, elim_format]

declare Apply [TC]

definition
  term_rec :: "[i, [i, i, i] \<Rightarrow> i] \<Rightarrow> i"  where
  "term_rec(t,d) \<equiv>
    Vrec(t, \<lambda>t g. term_case(\<lambda>x zs. d(x, zs, map(\<lambda>z. g`z, zs)), t))"

definition
  term_map :: "[i \<Rightarrow> i, i] \<Rightarrow> i"  where
  "term_map(f,t) \<equiv> term_rec(t, \<lambda>x zs rs. Apply(f(x), rs))"

definition
  term_size :: "i \<Rightarrow> i"  where
  "term_size(t) \<equiv> term_rec(t, \<lambda>x zs rs. succ(list_add(rs)))"

definition
  reflect :: "i \<Rightarrow> i"  where
  "reflect(t) \<equiv> term_rec(t, \<lambda>x zs rs. Apply(x, rev(rs)))"

definition
  preorder :: "i \<Rightarrow> i"  where
  "preorder(t) \<equiv> term_rec(t, \<lambda>x zs rs. Cons(x, flat(rs)))"

definition
  postorder :: "i \<Rightarrow> i"  where
  "postorder(t) \<equiv> term_rec(t, \<lambda>x zs rs. flat(rs) @ [x])"

lemma term_unfold: "term(A) = A * list(term(A))"
  by (fast intro!: term.intros [unfolded term.con_defs]
    elim: term.cases [unfolded term.con_defs])

lemma term_induct2:
  "\<lbrakk>t \<in> term(A);
      \<And>x.      \<lbrakk>x \<in> A\<rbrakk> \<Longrightarrow> P(Apply(x,Nil));
      \<And>x z zs. \<lbrakk>x \<in> A;  z \<in> term(A);  zs: list(term(A));  P(Apply(x,zs))
\<rbrakk> \<Longrightarrow> P(Apply(x, Cons(z,zs)))
\<rbrakk> \<Longrightarrow> P(t)"
  \<comment> \<open>Induction on \<^term>\<open>term(A)\<close> followed by induction on \<^term>\<open>list\<close>.\<close>
  apply (induct_tac t)
  apply (erule list.induct)
   apply (auto dest: list_CollectD)
  done

lemma term_induct_eqn [consumes 1, case_names Apply]:
  "\<lbrakk>t \<in> term(A);
      \<And>x zs. \<lbrakk>x \<in> A;  zs: list(term(A));  map(f,zs) = map(g,zs)\<rbrakk> \<Longrightarrow>
              f(Apply(x,zs)) = g(Apply(x,zs))
\<rbrakk> \<Longrightarrow> f(t) = g(t)"
  \<comment> \<open>Induction on \<^term>\<open>term(A)\<close> to prove an equation.\<close>
  apply (induct_tac t)
  apply (auto dest: map_list_Collect list_CollectD)
  done

text \<open>
  \medskip Lemmas to justify using \<^term>\<open>term\<close> in other recursive
  type definitions.
\<close>

lemma term_mono: "A \<subseteq> B \<Longrightarrow> term(A) \<subseteq> term(B)"
    unfolding term.defs
  apply (rule lfp_mono)
    apply (rule term.bnd_mono)+
  apply (rule univ_mono basic_monos| assumption)+
  done

lemma term_univ: "term(univ(A)) \<subseteq> univ(A)"
  \<comment> \<open>Easily provable by induction also\<close>
    unfolding term.defs term.con_defs
  apply (rule lfp_lowerbound)
   apply (rule_tac [2] A_subset_univ [THEN univ_mono])
  apply safe
  apply (assumption | rule Pair_in_univ list_univ [THEN subsetD])+
  done

lemma term_subset_univ: "A \<subseteq> univ(B) \<Longrightarrow> term(A) \<subseteq> univ(B)"
  apply (rule subset_trans)
   apply (erule term_mono)
  apply (rule term_univ)
  done

lemma term_into_univ: "\<lbrakk>t \<in> term(A);  A \<subseteq> univ(B)\<rbrakk> \<Longrightarrow> t \<in> univ(B)"
  by (rule term_subset_univ [THEN subsetD])

text \<open>
  \medskip \<open>term_rec\<close> -- by \<open>Vset\<close> recursion.
\<close>

lemma map_lemma: "\<lbrakk>l \<in> list(A);  Ord(i);  rank(l)<i\<rbrakk>
    \<Longrightarrow> map(\<lambda>z. (\<lambda>x \<in> Vset(i).h(x)) ` z, l) = map(h,l)"
  \<comment> \<open>\<^term>\<open>map\<close> works correctly on the underlying list of terms.\<close>
  apply (induct set: list)
   apply simp
  apply (subgoal_tac "rank (a) <i \<and> rank (l) < i")
   apply (simp add: rank_of_Ord)
  apply (simp add: list.con_defs)
  apply (blast dest: rank_rls [THEN lt_trans])
  done

lemma term_rec [simp]: "ts \<in> list(A) \<Longrightarrow>
  term_rec(Apply(a,ts), d) = d(a, ts, map (\<lambda>z. term_rec(z,d), ts))"
  \<comment> \<open>Typing premise is necessary to invoke \<open>map_lemma\<close>.\<close>
  apply (rule term_rec_def [THEN def_Vrec, THEN trans])
    unfolding term.con_defs
  apply (simp add: rank_pair2 map_lemma)
  done

lemma term_rec_type:
  assumes t: "t \<in> term(A)"
    and a: "\<And>x zs r. \<lbrakk>x \<in> A;  zs: list(term(A));
                   r \<in> list(\<Union>t \<in> term(A). C(t))\<rbrakk>
                \<Longrightarrow> d(x, zs, r): C(Apply(x,zs))"
  shows "term_rec(t,d) \<in> C(t)"
  \<comment> \<open>Slightly odd typing condition on \<open>r\<close> in the second premise!\<close>
  using t
  apply induct
  apply (frule list_CollectD)
  apply (subst term_rec)
   apply (assumption | rule a)+
  apply (erule list.induct)
   apply auto
  done

lemma def_term_rec:
  "\<lbrakk>\<And>t. j(t)\<equiv>term_rec(t,d);  ts: list(A)\<rbrakk> \<Longrightarrow>
    j(Apply(a,ts)) = d(a, ts, map(\<lambda>Z. j(Z), ts))"
  apply (simp only:)
  apply (erule term_rec)
  done

lemma term_rec_simple_type [TC]:
  "\<lbrakk>t \<in> term(A);
      \<And>x zs r. \<lbrakk>x \<in> A;  zs: list(term(A));  r \<in> list(C)\<rbrakk>
                \<Longrightarrow> d(x, zs, r): C
\<rbrakk> \<Longrightarrow> term_rec(t,d) \<in> C"
  apply (erule term_rec_type)
  apply (drule subset_refl [THEN UN_least, THEN list_mono, THEN subsetD])
  apply simp
  done


text \<open>
  \medskip \<^term>\<open>term_map\<close>.
\<close>

lemma term_map [simp]:
  "ts \<in> list(A) \<Longrightarrow>
    term_map(f, Apply(a, ts)) = Apply(f(a), map(term_map(f), ts))"
  by (rule term_map_def [THEN def_term_rec])

lemma term_map_type [TC]:
    "\<lbrakk>t \<in> term(A);  \<And>x. x \<in> A \<Longrightarrow> f(x): B\<rbrakk> \<Longrightarrow> term_map(f,t) \<in> term(B)"
    unfolding term_map_def
  apply (erule term_rec_simple_type)
  apply fast
  done

lemma term_map_type2 [TC]:
    "t \<in> term(A) \<Longrightarrow> term_map(f,t) \<in> term({f(u). u \<in> A})"
  apply (erule term_map_type)
  apply (erule RepFunI)
  done

text \<open>
  \medskip \<^term>\<open>term_size\<close>.
\<close>

lemma term_size [simp]:
    "ts \<in> list(A) \<Longrightarrow> term_size(Apply(a, ts)) = succ(list_add(map(term_size, ts)))"
  by (rule term_size_def [THEN def_term_rec])

lemma term_size_type [TC]: "t \<in> term(A) \<Longrightarrow> term_size(t) \<in> nat"
  by (auto simp add: term_size_def)


text \<open>
  \medskip \<open>reflect\<close>.
\<close>

lemma reflect [simp]:
    "ts \<in> list(A) \<Longrightarrow> reflect(Apply(a, ts)) = Apply(a, rev(map(reflect, ts)))"
  by (rule reflect_def [THEN def_term_rec])

lemma reflect_type [TC]: "t \<in> term(A) \<Longrightarrow> reflect(t) \<in> term(A)"
  by (auto simp add: reflect_def)


text \<open>
  \medskip \<open>preorder\<close>.
\<close>

lemma preorder [simp]:
    "ts \<in> list(A) \<Longrightarrow> preorder(Apply(a, ts)) = Cons(a, flat(map(preorder, ts)))"
  by (rule preorder_def [THEN def_term_rec])

lemma preorder_type [TC]: "t \<in> term(A) \<Longrightarrow> preorder(t) \<in> list(A)"
  by (simp add: preorder_def)


text \<open>
  \medskip \<open>postorder\<close>.
\<close>

lemma postorder [simp]:
    "ts \<in> list(A) \<Longrightarrow> postorder(Apply(a, ts)) = flat(map(postorder, ts)) @ [a]"
  by (rule postorder_def [THEN def_term_rec])

lemma postorder_type [TC]: "t \<in> term(A) \<Longrightarrow> postorder(t) \<in> list(A)"
  by (simp add: postorder_def)


text \<open>
  \medskip Theorems about \<open>term_map\<close>.
\<close>

declare map_compose [simp]

lemma term_map_ident: "t \<in> term(A) \<Longrightarrow> term_map(\<lambda>u. u, t) = t"
  by (induct rule: term_induct_eqn) simp

lemma term_map_compose:
    "t \<in> term(A) \<Longrightarrow> term_map(f, term_map(g,t)) = term_map(\<lambda>u. f(g(u)), t)"
  by (induct rule: term_induct_eqn) simp

lemma term_map_reflect:
    "t \<in> term(A) \<Longrightarrow> term_map(f, reflect(t)) = reflect(term_map(f,t))"
  by (induct rule: term_induct_eqn) (simp add: rev_map_distrib [symmetric])


text \<open>
  \medskip Theorems about \<open>term_size\<close>.
\<close>

lemma term_size_term_map: "t \<in> term(A) \<Longrightarrow> term_size(term_map(f,t)) = term_size(t)"
  by (induct rule: term_induct_eqn) simp

lemma term_size_reflect: "t \<in> term(A) \<Longrightarrow> term_size(reflect(t)) = term_size(t)"
  by (induct rule: term_induct_eqn) (simp add: rev_map_distrib [symmetric] list_add_rev)

lemma term_size_length: "t \<in> term(A) \<Longrightarrow> term_size(t) = length(preorder(t))"
  by (induct rule: term_induct_eqn) (simp add: length_flat)


text \<open>
  \medskip Theorems about \<open>reflect\<close>.
\<close>

lemma reflect_reflect_ident: "t \<in> term(A) \<Longrightarrow> reflect(reflect(t)) = t"
  by (induct rule: term_induct_eqn) (simp add: rev_map_distrib)


text \<open>
  \medskip Theorems about preorder.
\<close>

lemma preorder_term_map:
    "t \<in> term(A) \<Longrightarrow> preorder(term_map(f,t)) = map(f, preorder(t))"
  by (induct rule: term_induct_eqn) (simp add: map_flat)

lemma preorder_reflect_eq_rev_postorder:
    "t \<in> term(A) \<Longrightarrow> preorder(reflect(t)) = rev(postorder(t))"
  by (induct rule: term_induct_eqn)
    (simp add: rev_app_distrib rev_flat rev_map_distrib [symmetric])

end
