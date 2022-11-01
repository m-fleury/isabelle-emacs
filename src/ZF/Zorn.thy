(*  Title:      ZF/Zorn.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section\<open>Zorn's Lemma\<close>

theory Zorn imports OrderArith AC Inductive begin

text\<open>Based upon the unpublished article ``Towards the Mechanization of the
Proofs of Some Classical Theorems of Set Theory,'' by Abrial and Laffitte.\<close>

definition
  Subset_rel :: "i\<Rightarrow>i"  where
   "Subset_rel(A) \<equiv> {z \<in> A*A . \<exists>x y. z=\<langle>x,y\<rangle> \<and> x<=y \<and> x\<noteq>y}"

definition
  chain      :: "i\<Rightarrow>i"  where
   "chain(A)      \<equiv> {F \<in> Pow(A). \<forall>X\<in>F. \<forall>Y\<in>F. X<=Y | Y<=X}"

definition
  super      :: "[i,i]\<Rightarrow>i"  where
   "super(A,c)    \<equiv> {d \<in> chain(A). c<=d \<and> c\<noteq>d}"

definition
  maxchain   :: "i\<Rightarrow>i"  where
   "maxchain(A)   \<equiv> {c \<in> chain(A). super(A,c)=0}"

definition
  increasing :: "i\<Rightarrow>i"  where
    "increasing(A) \<equiv> {f \<in> Pow(A)->Pow(A). \<forall>x. x<=A \<longrightarrow> x<=f`x}"


text\<open>Lemma for the inductive definition below\<close>
lemma Union_in_Pow: "Y \<in> Pow(Pow(A)) \<Longrightarrow> \<Union>(Y) \<in> Pow(A)"
by blast


text\<open>We could make the inductive definition conditional on
    \<^term>\<open>next \<in> increasing(S)\<close>
    but instead we make this a side-condition of an introduction rule.  Thus
    the induction rule lets us assume that condition!  Many inductive proofs
    are therefore unconditional.\<close>
consts
  "TFin" :: "[i,i]\<Rightarrow>i"

inductive
  domains       "TFin(S,next)" \<subseteq> "Pow(S)"
  intros
    nextI:       "\<lbrakk>x \<in> TFin(S,next);  next \<in> increasing(S)\<rbrakk>
                  \<Longrightarrow> next`x \<in> TFin(S,next)"

    Pow_UnionI: "Y \<in> Pow(TFin(S,next)) \<Longrightarrow> \<Union>(Y) \<in> TFin(S,next)"

  monos         Pow_mono
  con_defs      increasing_def
  type_intros   CollectD1 [THEN apply_funtype] Union_in_Pow


subsection\<open>Mathematical Preamble\<close>

lemma Union_lemma0: "(\<forall>x\<in>C. x<=A | B<=x) \<Longrightarrow> \<Union>(C)<=A | B<=\<Union>(C)"
by blast

lemma Inter_lemma0:
     "\<lbrakk>c \<in> C; \<forall>x\<in>C. A<=x | x<=B\<rbrakk> \<Longrightarrow> A \<subseteq> \<Inter>(C) | \<Inter>(C) \<subseteq> B"
by blast


subsection\<open>The Transfinite Construction\<close>

lemma increasingD1: "f \<in> increasing(A) \<Longrightarrow> f \<in> Pow(A)->Pow(A)"
  unfolding increasing_def
apply (erule CollectD1)
done

lemma increasingD2: "\<lbrakk>f \<in> increasing(A); x<=A\<rbrakk> \<Longrightarrow> x \<subseteq> f`x"
by (unfold increasing_def, blast)

lemmas TFin_UnionI = PowI [THEN TFin.Pow_UnionI]

lemmas TFin_is_subset = TFin.dom_subset [THEN subsetD, THEN PowD]


text\<open>Structural induction on \<^term>\<open>TFin(S,next)\<close>\<close>
lemma TFin_induct:
  "\<lbrakk>n \<in> TFin(S,next);
      \<And>x. \<lbrakk>x \<in> TFin(S,next);  P(x);  next \<in> increasing(S)\<rbrakk> \<Longrightarrow> P(next`x);
      \<And>Y. \<lbrakk>Y \<subseteq> TFin(S,next);  \<forall>y\<in>Y. P(y)\<rbrakk> \<Longrightarrow> P(\<Union>(Y))
\<rbrakk> \<Longrightarrow> P(n)"
by (erule TFin.induct, blast+)


subsection\<open>Some Properties of the Transfinite Construction\<close>

lemmas increasing_trans = subset_trans [OF _ increasingD2,
                                        OF _ _ TFin_is_subset]

text\<open>Lemma 1 of section 3.1\<close>
lemma TFin_linear_lemma1:
     "\<lbrakk>n \<in> TFin(S,next);  m \<in> TFin(S,next);
         \<forall>x \<in> TFin(S,next) . x<=m \<longrightarrow> x=m | next`x<=m\<rbrakk>
      \<Longrightarrow> n<=m | next`m<=n"
apply (erule TFin_induct)
apply (erule_tac [2] Union_lemma0) (*or just Blast_tac*)
(*downgrade subsetI from intro! to intro*)
apply (blast dest: increasing_trans)
done

text\<open>Lemma 2 of section 3.2.  Interesting in its own right!
  Requires \<^term>\<open>next \<in> increasing(S)\<close> in the second induction step.\<close>
lemma TFin_linear_lemma2:
    "\<lbrakk>m \<in> TFin(S,next);  next \<in> increasing(S)\<rbrakk>
     \<Longrightarrow> \<forall>n \<in> TFin(S,next). n<=m \<longrightarrow> n=m | next`n \<subseteq> m"
apply (erule TFin_induct)
apply (rule impI [THEN ballI])
txt\<open>case split using \<open>TFin_linear_lemma1\<close>\<close>
apply (rule_tac n1 = n and m1 = x in TFin_linear_lemma1 [THEN disjE],
       assumption+)
apply (blast del: subsetI
             intro: increasing_trans subsetI, blast)
txt\<open>second induction step\<close>
apply (rule impI [THEN ballI])
apply (rule Union_lemma0 [THEN disjE])
apply (erule_tac [3] disjI2)
prefer 2 apply blast
apply (rule ballI)
apply (drule bspec, assumption)
apply (drule subsetD, assumption)
apply (rule_tac n1 = n and m1 = x in TFin_linear_lemma1 [THEN disjE],
       assumption+, blast)
apply (erule increasingD2 [THEN subset_trans, THEN disjI1])
apply (blast dest: TFin_is_subset)+
done

text\<open>a more convenient form for Lemma 2\<close>
lemma TFin_subsetD:
     "\<lbrakk>n<=m;  m \<in> TFin(S,next);  n \<in> TFin(S,next);  next \<in> increasing(S)\<rbrakk>
      \<Longrightarrow> n=m | next`n \<subseteq> m"
by (blast dest: TFin_linear_lemma2 [rule_format])

text\<open>Consequences from section 3.3 -- Property 3.2, the ordering is total\<close>
lemma TFin_subset_linear:
     "\<lbrakk>m \<in> TFin(S,next);  n \<in> TFin(S,next);  next \<in> increasing(S)\<rbrakk>
      \<Longrightarrow> n \<subseteq> m | m<=n"
apply (rule disjE)
apply (rule TFin_linear_lemma1 [OF _ _TFin_linear_lemma2])
apply (assumption+, erule disjI2)
apply (blast del: subsetI
             intro: subsetI increasingD2 [THEN subset_trans] TFin_is_subset)
done


text\<open>Lemma 3 of section 3.3\<close>
lemma equal_next_upper:
     "\<lbrakk>n \<in> TFin(S,next);  m \<in> TFin(S,next);  m = next`m\<rbrakk> \<Longrightarrow> n \<subseteq> m"
apply (erule TFin_induct)
apply (drule TFin_subsetD)
apply (assumption+, force, blast)
done

text\<open>Property 3.3 of section 3.3\<close>
lemma equal_next_Union:
     "\<lbrakk>m \<in> TFin(S,next);  next \<in> increasing(S)\<rbrakk>
      \<Longrightarrow> m = next`m <-> m = \<Union>(TFin(S,next))"
apply (rule iffI)
apply (rule Union_upper [THEN equalityI])
apply (rule_tac [2] equal_next_upper [THEN Union_least])
apply (assumption+)
apply (erule ssubst)
apply (rule increasingD2 [THEN equalityI], assumption)
apply (blast del: subsetI
             intro: subsetI TFin_UnionI TFin.nextI TFin_is_subset)+
done


subsection\<open>Hausdorff's Theorem: Every Set Contains a Maximal Chain\<close>

text\<open>NOTE: We assume the partial ordering is \<open>\<subseteq>\<close>, the subset
relation!\<close>

text\<open>* Defining the "next" operation for Hausdorff's Theorem *\<close>

lemma chain_subset_Pow: "chain(A) \<subseteq> Pow(A)"
  unfolding chain_def
apply (rule Collect_subset)
done

lemma super_subset_chain: "super(A,c) \<subseteq> chain(A)"
  unfolding super_def
apply (rule Collect_subset)
done

lemma maxchain_subset_chain: "maxchain(A) \<subseteq> chain(A)"
  unfolding maxchain_def
apply (rule Collect_subset)
done

lemma choice_super:
     "\<lbrakk>ch \<in> (\<Prod>X \<in> Pow(chain(S)) - {0}. X); X \<in> chain(S);  X \<notin> maxchain(S)\<rbrakk>
      \<Longrightarrow> ch ` super(S,X) \<in> super(S,X)"
apply (erule apply_type)
apply (unfold super_def maxchain_def, blast)
done

lemma choice_not_equals:
     "\<lbrakk>ch \<in> (\<Prod>X \<in> Pow(chain(S)) - {0}. X); X \<in> chain(S);  X \<notin> maxchain(S)\<rbrakk>
      \<Longrightarrow> ch ` super(S,X) \<noteq> X"
apply (rule notI)
apply (drule choice_super, assumption, assumption)
apply (simp add: super_def)
done

text\<open>This justifies Definition 4.4\<close>
lemma Hausdorff_next_exists:
     "ch \<in> (\<Prod>X \<in> Pow(chain(S))-{0}. X) \<Longrightarrow>
      \<exists>next \<in> increasing(S). \<forall>X \<in> Pow(S).
                   next`X = if(X \<in> chain(S)-maxchain(S), ch`super(S,X), X)"
apply (rule_tac x="\<lambda>X\<in>Pow(S).
                   if X \<in> chain(S) - maxchain(S) then ch ` super(S, X) else X"
       in bexI)
apply force
  unfolding increasing_def
apply (rule CollectI)
apply (rule lam_type)
apply (simp (no_asm_simp))
apply (blast dest: super_subset_chain [THEN subsetD] 
                   chain_subset_Pow [THEN subsetD] choice_super)
txt\<open>Now, verify that it increases\<close>
apply (simp (no_asm_simp) add: Pow_iff subset_refl)
apply safe
apply (drule choice_super)
apply (assumption+)
apply (simp add: super_def, blast)
done

text\<open>Lemma 4\<close>
lemma TFin_chain_lemma4:
     "\<lbrakk>c \<in> TFin(S,next);
         ch \<in> (\<Prod>X \<in> Pow(chain(S))-{0}. X);
         next \<in> increasing(S);
         \<forall>X \<in> Pow(S). next`X =
                          if(X \<in> chain(S)-maxchain(S), ch`super(S,X), X)\<rbrakk>
     \<Longrightarrow> c \<in> chain(S)"
apply (erule TFin_induct)
apply (simp (no_asm_simp) add: chain_subset_Pow [THEN subsetD, THEN PowD]
            choice_super [THEN super_subset_chain [THEN subsetD]])
  unfolding chain_def
apply (rule CollectI, blast, safe)
apply (rule_tac m1=B and n1=Ba in TFin_subset_linear [THEN disjE], fast+)
      txt\<open>\<open>Blast_tac's\<close> slow\<close>
done

theorem Hausdorff: "\<exists>c. c \<in> maxchain(S)"
apply (rule AC_Pi_Pow [THEN exE])
apply (rule Hausdorff_next_exists [THEN bexE], assumption)
apply (rename_tac ch "next")
apply (subgoal_tac "\<Union>(TFin (S,next)) \<in> chain (S) ")
prefer 2
 apply (blast intro!: TFin_chain_lemma4 subset_refl [THEN TFin_UnionI])
apply (rule_tac x = "\<Union>(TFin (S,next))" in exI)
apply (rule classical)
apply (subgoal_tac "next ` Union(TFin (S,next)) = \<Union>(TFin (S,next))")
apply (rule_tac [2] equal_next_Union [THEN iffD2, symmetric])
apply (rule_tac [2] subset_refl [THEN TFin_UnionI])
prefer 2 apply assumption
apply (rule_tac [2] refl)
apply (simp add: subset_refl [THEN TFin_UnionI,
                              THEN TFin.dom_subset [THEN subsetD, THEN PowD]])
apply (erule choice_not_equals [THEN notE])
apply (assumption+)
done


subsection\<open>Zorn's Lemma: If All Chains in S Have Upper Bounds In S,
       then S contains a Maximal Element\<close>

text\<open>Used in the proof of Zorn's Lemma\<close>
lemma chain_extend:
    "\<lbrakk>c \<in> chain(A);  z \<in> A;  \<forall>x \<in> c. x<=z\<rbrakk> \<Longrightarrow> cons(z,c) \<in> chain(A)"
by (unfold chain_def, blast)

lemma Zorn: "\<forall>c \<in> chain(S). \<Union>(c) \<in> S \<Longrightarrow> \<exists>y \<in> S. \<forall>z \<in> S. y<=z \<longrightarrow> y=z"
apply (rule Hausdorff [THEN exE])
apply (simp add: maxchain_def)
apply (rename_tac c)
apply (rule_tac x = "\<Union>(c)" in bexI)
prefer 2 apply blast
apply safe
apply (rename_tac z)
apply (rule classical)
apply (subgoal_tac "cons (z,c) \<in> super (S,c) ")
apply (blast elim: equalityE)
apply (unfold super_def, safe)
apply (fast elim: chain_extend)
apply (fast elim: equalityE)
done

text \<open>Alternative version of Zorn's Lemma\<close>

theorem Zorn2:
  "\<forall>c \<in> chain(S). \<exists>y \<in> S. \<forall>x \<in> c. x \<subseteq> y \<Longrightarrow> \<exists>y \<in> S. \<forall>z \<in> S. y<=z \<longrightarrow> y=z"
apply (cut_tac Hausdorff maxchain_subset_chain)
apply (erule exE)
apply (drule subsetD, assumption)
apply (drule bspec, assumption, erule bexE)
apply (rule_tac x = y in bexI)
  prefer 2 apply assumption
apply clarify
apply rule apply assumption
apply rule
apply (rule ccontr)
apply (frule_tac z=z in chain_extend)
  apply (assumption, blast)
  unfolding maxchain_def super_def
apply (blast elim!: equalityCE)
done


subsection\<open>Zermelo's Theorem: Every Set can be Well-Ordered\<close>

text\<open>Lemma 5\<close>
lemma TFin_well_lemma5:
     "\<lbrakk>n \<in> TFin(S,next);  Z \<subseteq> TFin(S,next);  z:Z;  \<not> \<Inter>(Z) \<in> Z\<rbrakk>
      \<Longrightarrow> \<forall>m \<in> Z. n \<subseteq> m"
apply (erule TFin_induct)
prefer 2 apply blast txt\<open>second induction step is easy\<close>
apply (rule ballI)
apply (rule bspec [THEN TFin_subsetD, THEN disjE], auto)
apply (subgoal_tac "m = \<Inter>(Z) ")
apply blast+
done

text\<open>Well-ordering of \<^term>\<open>TFin(S,next)\<close>\<close>
lemma well_ord_TFin_lemma: "\<lbrakk>Z \<subseteq> TFin(S,next);  z \<in> Z\<rbrakk> \<Longrightarrow> \<Inter>(Z) \<in> Z"
apply (rule classical)
apply (subgoal_tac "Z = {\<Union>(TFin (S,next))}")
apply (simp (no_asm_simp) add: Inter_singleton)
apply (erule equal_singleton)
apply (rule Union_upper [THEN equalityI])
apply (rule_tac [2] subset_refl [THEN TFin_UnionI, THEN TFin_well_lemma5, THEN bspec], blast+)
done

text\<open>This theorem just packages the previous result\<close>
lemma well_ord_TFin:
     "next \<in> increasing(S) 
      \<Longrightarrow> well_ord(TFin(S,next), Subset_rel(TFin(S,next)))"
apply (rule well_ordI)
  unfolding Subset_rel_def linear_def
txt\<open>Prove the well-foundedness goal\<close>
apply (rule wf_onI)
apply (frule well_ord_TFin_lemma, assumption)
apply (drule_tac x = "\<Inter>(Z) " in bspec, assumption)
apply blast
txt\<open>Now prove the linearity goal\<close>
apply (intro ballI)
apply (case_tac "x=y")
 apply blast
txt\<open>The \<^term>\<open>x\<noteq>y\<close> case remains\<close>
apply (rule_tac n1=x and m1=y in TFin_subset_linear [THEN disjE],
       assumption+, blast+)
done

text\<open>* Defining the "next" operation for Zermelo's Theorem *\<close>

lemma choice_Diff:
     "\<lbrakk>ch \<in> (\<Prod>X \<in> Pow(S) - {0}. X);  X \<subseteq> S;  X\<noteq>S\<rbrakk> \<Longrightarrow> ch ` (S-X) \<in> S-X"
apply (erule apply_type)
apply (blast elim!: equalityE)
done

text\<open>This justifies Definition 6.1\<close>
lemma Zermelo_next_exists:
     "ch \<in> (\<Prod>X \<in> Pow(S)-{0}. X) \<Longrightarrow>
           \<exists>next \<in> increasing(S). \<forall>X \<in> Pow(S).
                      next`X = (if X=S then S else cons(ch`(S-X), X))"
apply (rule_tac x="\<lambda>X\<in>Pow(S). if X=S then S else cons(ch`(S-X), X)"
       in bexI)
apply force
  unfolding increasing_def
apply (rule CollectI)
apply (rule lam_type)
txt\<open>Type checking is surprisingly hard!\<close>
apply (simp (no_asm_simp) add: Pow_iff cons_subset_iff subset_refl)
apply (blast intro!: choice_Diff [THEN DiffD1])
txt\<open>Verify that it increases\<close>
apply (intro allI impI)
apply (simp add: Pow_iff subset_consI subset_refl)
done


text\<open>The construction of the injection\<close>
lemma choice_imp_injection:
     "\<lbrakk>ch \<in> (\<Prod>X \<in> Pow(S)-{0}. X);
         next \<in> increasing(S);
         \<forall>X \<in> Pow(S). next`X = if(X=S, S, cons(ch`(S-X), X))\<rbrakk>
      \<Longrightarrow> (\<lambda> x \<in> S. \<Union>({y \<in> TFin(S,next). x \<notin> y}))
               \<in> inj(S, TFin(S,next) - {S})"
apply (rule_tac d = "\<lambda>y. ch` (S-y) " in lam_injective)
apply (rule DiffI)
apply (rule Collect_subset [THEN TFin_UnionI])
apply (blast intro!: Collect_subset [THEN TFin_UnionI] elim: equalityE)
apply (subgoal_tac "x \<notin> \<Union>({y \<in> TFin (S,next) . x \<notin> y}) ")
prefer 2 apply (blast elim: equalityE)
apply (subgoal_tac "\<Union>({y \<in> TFin (S,next) . x \<notin> y}) \<noteq> S")
prefer 2 apply (blast elim: equalityE)
txt\<open>For proving \<open>x \<in> next`\<Union>(...)\<close>.
  Abrial and Laffitte's justification appears to be faulty.\<close>
apply (subgoal_tac "\<not> next ` Union({y \<in> TFin (S,next) . x \<notin> y}) 
                    \<subseteq> \<Union>({y \<in> TFin (S,next) . x \<notin> y}) ")
 prefer 2
 apply (simp del: Union_iff
             add: Collect_subset [THEN TFin_UnionI, THEN TFin_is_subset]
             Pow_iff cons_subset_iff subset_refl choice_Diff [THEN DiffD2])
apply (subgoal_tac "x \<in> next ` Union({y \<in> TFin (S,next) . x \<notin> y}) ")
 prefer 2
 apply (blast intro!: Collect_subset [THEN TFin_UnionI] TFin.nextI)
txt\<open>End of the lemmas!\<close>
apply (simp add: Collect_subset [THEN TFin_UnionI, THEN TFin_is_subset])
done

text\<open>The wellordering theorem\<close>
theorem AC_well_ord: "\<exists>r. well_ord(S,r)"
apply (rule AC_Pi_Pow [THEN exE])
apply (rule Zermelo_next_exists [THEN bexE], assumption)
apply (rule exI)
apply (rule well_ord_rvimage)
apply (erule_tac [2] well_ord_TFin)
apply (rule choice_imp_injection [THEN inj_weaken_type], blast+)
done


subsection \<open>Zorn's Lemma for Partial Orders\<close>

text \<open>Reimported from HOL by Clemens Ballarin.\<close>


definition Chain :: "i \<Rightarrow> i" where
  "Chain(r) = {A \<in> Pow(field(r)). \<forall>a\<in>A. \<forall>b\<in>A. \<langle>a, b\<rangle> \<in> r | \<langle>b, a\<rangle> \<in> r}"

lemma mono_Chain:
  "r \<subseteq> s \<Longrightarrow> Chain(r) \<subseteq> Chain(s)"
  unfolding Chain_def
  by blast

theorem Zorn_po:
  assumes po: "Partial_order(r)"
    and u: "\<forall>C\<in>Chain(r). \<exists>u\<in>field(r). \<forall>a\<in>C. \<langle>a, u\<rangle> \<in> r"
  shows "\<exists>m\<in>field(r). \<forall>a\<in>field(r). \<langle>m, a\<rangle> \<in> r \<longrightarrow> a = m"
proof -
  have "Preorder(r)" using po by (simp add: partial_order_on_def)
  \<comment> \<open>Mirror r in the set of subsets below (wrt r) elements of A (?).\<close>
  let ?B = "\<lambda>x\<in>field(r). r -`` {x}" let ?S = "?B `` field(r)"
  have "\<forall>C\<in>chain(?S). \<exists>U\<in>?S. \<forall>A\<in>C. A \<subseteq> U"
  proof (clarsimp simp: chain_def Subset_rel_def bex_image_simp)
    fix C
    assume 1: "C \<subseteq> ?S" and 2: "\<forall>A\<in>C. \<forall>B\<in>C. A \<subseteq> B | B \<subseteq> A"
    let ?A = "{x \<in> field(r). \<exists>M\<in>C. M = ?B`x}"
    have "C = ?B `` ?A" using 1
      apply (auto simp: image_def)
      apply rule
      apply rule
      apply (drule subsetD) apply assumption
      apply (erule CollectE)
      apply rule apply assumption
      apply (erule bexE)
      apply rule prefer 2 apply assumption
      apply rule
      apply (erule lamE) apply simp
      apply assumption

      apply (thin_tac "C \<subseteq> X" for X)
      apply (fast elim: lamE)
      done
    have "?A \<in> Chain(r)"
    proof (simp add: Chain_def subsetI, intro conjI ballI impI)
      fix a b
      assume "a \<in> field(r)" "r -`` {a} \<in> C" "b \<in> field(r)" "r -`` {b} \<in> C"
      hence "r -`` {a} \<subseteq> r -`` {b} | r -`` {b} \<subseteq> r -`` {a}" using 2 by auto
      then show "\<langle>a, b\<rangle> \<in> r | \<langle>b, a\<rangle> \<in> r"
        using \<open>Preorder(r)\<close> \<open>a \<in> field(r)\<close> \<open>b \<in> field(r)\<close>
        by (simp add: subset_vimage1_vimage1_iff)
    qed
    then obtain u where uA: "u \<in> field(r)" "\<forall>a\<in>?A. \<langle>a, u\<rangle> \<in> r"
      using u
      apply auto
      apply (drule bspec) apply assumption
      apply auto
      done
    have "\<forall>A\<in>C. A \<subseteq> r -`` {u}"
    proof (auto intro!: vimageI)
      fix a B
      assume aB: "B \<in> C" "a \<in> B"
      with 1 obtain x where "x \<in> field(r)" "B = r -`` {x}"
        apply -
        apply (drule subsetD) apply assumption
        apply (erule imageE)
        apply (erule lamE)
        apply simp
        done
      then show "\<langle>a, u\<rangle> \<in> r" using uA aB \<open>Preorder(r)\<close>
        by (auto simp: preorder_on_def refl_def) (blast dest: trans_onD)+
    qed
    then show "\<exists>U\<in>field(r). \<forall>A\<in>C. A \<subseteq> r -`` {U}"
      using \<open>u \<in> field(r)\<close> ..
  qed
  from Zorn2 [OF this]
  obtain m B where "m \<in> field(r)" "B = r -`` {m}"
    "\<forall>x\<in>field(r). B \<subseteq> r -`` {x} \<longrightarrow> B = r -`` {x}"
    by (auto elim!: lamE simp: ball_image_simp)
  then have "\<forall>a\<in>field(r). \<langle>m, a\<rangle> \<in> r \<longrightarrow> a = m"
    using po \<open>Preorder(r)\<close> \<open>m \<in> field(r)\<close>
    by (auto simp: subset_vimage1_vimage1_iff Partial_order_eq_vimage1_vimage1_iff)
  then show ?thesis using \<open>m \<in> field(r)\<close> by blast
qed

end
