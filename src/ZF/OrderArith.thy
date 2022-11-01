(*  Title:      ZF/OrderArith.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section\<open>Combining Orderings: Foundations of Ordinal Arithmetic\<close>

theory OrderArith imports Order Sum Ordinal begin

definition
  (*disjoint sum of two relations; underlies ordinal addition*)
  radd    :: "[i,i,i,i]\<Rightarrow>i"  where
    "radd(A,r,B,s) \<equiv>
                {z: (A+B) * (A+B).
                    (\<exists>x y. z = \<langle>Inl(x), Inr(y)\<rangle>)   |
                    (\<exists>x' x. z = \<langle>Inl(x'), Inl(x)\<rangle> \<and> \<langle>x',x\<rangle>:r)   |
                    (\<exists>y' y. z = \<langle>Inr(y'), Inr(y)\<rangle> \<and> \<langle>y',y\<rangle>:s)}"

definition
  (*lexicographic product of two relations; underlies ordinal multiplication*)
  rmult   :: "[i,i,i,i]\<Rightarrow>i"  where
    "rmult(A,r,B,s) \<equiv>
                {z: (A*B) * (A*B).
                    \<exists>x' y' x y. z = \<langle>\<langle>x',y'\<rangle>, \<langle>x,y\<rangle>\<rangle> \<and>
                       (\<langle>x',x\<rangle>: r | (x'=x \<and> \<langle>y',y\<rangle>: s))}"

definition
  (*inverse image of a relation*)
  rvimage :: "[i,i,i]\<Rightarrow>i"  where
    "rvimage(A,f,r) \<equiv> {z \<in> A*A. \<exists>x y. z = \<langle>x,y\<rangle> \<and> \<langle>f`x,f`y\<rangle>: r}"

definition
  measure :: "[i, i\<Rightarrow>i] \<Rightarrow> i"  where
    "measure(A,f) \<equiv> {\<langle>x,y\<rangle>: A*A. f(x) < f(y)}"


subsection\<open>Addition of Relations -- Disjoint Sum\<close>

subsubsection\<open>Rewrite rules.  Can be used to obtain introduction rules\<close>

lemma radd_Inl_Inr_iff [iff]:
    "\<langle>Inl(a), Inr(b)\<rangle> \<in> radd(A,r,B,s)  \<longleftrightarrow>  a \<in> A \<and> b \<in> B"
by (unfold radd_def, blast)

lemma radd_Inl_iff [iff]:
    "\<langle>Inl(a'), Inl(a)\<rangle> \<in> radd(A,r,B,s)  \<longleftrightarrow>  a':A \<and> a \<in> A \<and> \<langle>a',a\<rangle>:r"
by (unfold radd_def, blast)

lemma radd_Inr_iff [iff]:
    "\<langle>Inr(b'), Inr(b)\<rangle> \<in> radd(A,r,B,s) \<longleftrightarrow>  b':B \<and> b \<in> B \<and> \<langle>b',b\<rangle>:s"
by (unfold radd_def, blast)

lemma radd_Inr_Inl_iff [simp]:
    "\<langle>Inr(b), Inl(a)\<rangle> \<in> radd(A,r,B,s) \<longleftrightarrow> False"
by (unfold radd_def, blast)

declare radd_Inr_Inl_iff [THEN iffD1, dest!]

subsubsection\<open>Elimination Rule\<close>

lemma raddE:
    "\<lbrakk>\<langle>p',p\<rangle> \<in> radd(A,r,B,s);
        \<And>x y. \<lbrakk>p'=Inl(x); x \<in> A; p=Inr(y); y \<in> B\<rbrakk> \<Longrightarrow> Q;
        \<And>x' x. \<lbrakk>p'=Inl(x'); p=Inl(x); \<langle>x',x\<rangle>: r; x':A; x \<in> A\<rbrakk> \<Longrightarrow> Q;
        \<And>y' y. \<lbrakk>p'=Inr(y'); p=Inr(y); \<langle>y',y\<rangle>: s; y':B; y \<in> B\<rbrakk> \<Longrightarrow> Q
\<rbrakk> \<Longrightarrow> Q"
by (unfold radd_def, blast)

subsubsection\<open>Type checking\<close>

lemma radd_type: "radd(A,r,B,s) \<subseteq> (A+B) * (A+B)"
  unfolding radd_def
apply (rule Collect_subset)
done

lemmas field_radd = radd_type [THEN field_rel_subset]

subsubsection\<open>Linearity\<close>

lemma linear_radd:
    "\<lbrakk>linear(A,r);  linear(B,s)\<rbrakk> \<Longrightarrow> linear(A+B,radd(A,r,B,s))"
by (unfold linear_def, blast)


subsubsection\<open>Well-foundedness\<close>

lemma wf_on_radd: "\<lbrakk>wf[A](r);  wf[B](s)\<rbrakk> \<Longrightarrow> wf[A+B](radd(A,r,B,s))"
apply (rule wf_onI2)
apply (subgoal_tac "\<forall>x\<in>A. Inl (x) \<in> Ba")
 \<comment> \<open>Proving the lemma, which is needed twice!\<close>
 prefer 2
 apply (erule_tac V = "y \<in> A + B" in thin_rl)
 apply (rule_tac ballI)
 apply (erule_tac r = r and a = x in wf_on_induct, assumption)
 apply blast
txt\<open>Returning to main part of proof\<close>
apply safe
apply blast
apply (erule_tac r = s and a = ya in wf_on_induct, assumption, blast)
done

lemma wf_radd: "\<lbrakk>wf(r);  wf(s)\<rbrakk> \<Longrightarrow> wf(radd(field(r),r,field(s),s))"
apply (simp add: wf_iff_wf_on_field)
apply (rule wf_on_subset_A [OF _ field_radd])
apply (blast intro: wf_on_radd)
done

lemma well_ord_radd:
     "\<lbrakk>well_ord(A,r);  well_ord(B,s)\<rbrakk> \<Longrightarrow> well_ord(A+B, radd(A,r,B,s))"
apply (rule well_ordI)
apply (simp add: well_ord_def wf_on_radd)
apply (simp add: well_ord_def tot_ord_def linear_radd)
done

subsubsection\<open>An \<^term>\<open>ord_iso\<close> congruence law\<close>

lemma sum_bij:
     "\<lbrakk>f \<in> bij(A,C);  g \<in> bij(B,D)\<rbrakk>
      \<Longrightarrow> (\<lambda>z\<in>A+B. case(\<lambda>x. Inl(f`x), \<lambda>y. Inr(g`y), z)) \<in> bij(A+B, C+D)"
apply (rule_tac d = "case (\<lambda>x. Inl (converse(f)`x), \<lambda>y. Inr(converse(g)`y))"
       in lam_bijective)
apply (typecheck add: bij_is_inj inj_is_fun)
apply (auto simp add: left_inverse_bij right_inverse_bij)
done

lemma sum_ord_iso_cong:
    "\<lbrakk>f \<in> ord_iso(A,r,A',r');  g \<in> ord_iso(B,s,B',s')\<rbrakk> \<Longrightarrow>
            (\<lambda>z\<in>A+B. case(\<lambda>x. Inl(f`x), \<lambda>y. Inr(g`y), z))
            \<in> ord_iso(A+B, radd(A,r,B,s), A'+B', radd(A',r',B',s'))"
  unfolding ord_iso_def
apply (safe intro!: sum_bij)
(*Do the beta-reductions now*)
apply (auto cong add: conj_cong simp add: bij_is_fun [THEN apply_type])
done

(*Could we prove an ord_iso result?  Perhaps
     ord_iso(A+B, radd(A,r,B,s), A \<union> B, r \<union> s) *)
lemma sum_disjoint_bij: "A \<inter> B = 0 \<Longrightarrow>
            (\<lambda>z\<in>A+B. case(\<lambda>x. x, \<lambda>y. y, z)) \<in> bij(A+B, A \<union> B)"
apply (rule_tac d = "\<lambda>z. if z \<in> A then Inl (z) else Inr (z) " in lam_bijective)
apply auto
done

subsubsection\<open>Associativity\<close>

lemma sum_assoc_bij:
     "(\<lambda>z\<in>(A+B)+C. case(case(Inl, \<lambda>y. Inr(Inl(y))), \<lambda>y. Inr(Inr(y)), z))
      \<in> bij((A+B)+C, A+(B+C))"
apply (rule_tac d = "case (\<lambda>x. Inl (Inl (x)), case (\<lambda>x. Inl (Inr (x)), Inr))"
       in lam_bijective)
apply auto
done

lemma sum_assoc_ord_iso:
     "(\<lambda>z\<in>(A+B)+C. case(case(Inl, \<lambda>y. Inr(Inl(y))), \<lambda>y. Inr(Inr(y)), z))
      \<in> ord_iso((A+B)+C, radd(A+B, radd(A,r,B,s), C, t),
                A+(B+C), radd(A, r, B+C, radd(B,s,C,t)))"
by (rule sum_assoc_bij [THEN ord_isoI], auto)


subsection\<open>Multiplication of Relations -- Lexicographic Product\<close>

subsubsection\<open>Rewrite rule.  Can be used to obtain introduction rules\<close>

lemma  rmult_iff [iff]:
    "\<langle>\<langle>a',b'\<rangle>, \<langle>a,b\<rangle>\<rangle> \<in> rmult(A,r,B,s) \<longleftrightarrow>
            (\<langle>a',a\<rangle>: r  \<and> a':A \<and> a \<in> A \<and> b': B \<and> b \<in> B) |
            (\<langle>b',b\<rangle>: s  \<and> a'=a \<and> a \<in> A \<and> b': B \<and> b \<in> B)"

by (unfold rmult_def, blast)

lemma rmultE:
    "\<lbrakk>\<langle>\<langle>a',b'\<rangle>, \<langle>a,b\<rangle>\<rangle> \<in> rmult(A,r,B,s);
        \<lbrakk>\<langle>a',a\<rangle>: r;  a':A;  a \<in> A;  b':B;  b \<in> B\<rbrakk> \<Longrightarrow> Q;
        \<lbrakk>\<langle>b',b\<rangle>: s;  a \<in> A;  a'=a;  b':B;  b \<in> B\<rbrakk> \<Longrightarrow> Q
\<rbrakk> \<Longrightarrow> Q"
by blast

subsubsection\<open>Type checking\<close>

lemma rmult_type: "rmult(A,r,B,s) \<subseteq> (A*B) * (A*B)"
by (unfold rmult_def, rule Collect_subset)

lemmas field_rmult = rmult_type [THEN field_rel_subset]

subsubsection\<open>Linearity\<close>

lemma linear_rmult:
    "\<lbrakk>linear(A,r);  linear(B,s)\<rbrakk> \<Longrightarrow> linear(A*B,rmult(A,r,B,s))"
by (simp add: linear_def, blast)

subsubsection\<open>Well-foundedness\<close>

lemma wf_on_rmult: "\<lbrakk>wf[A](r);  wf[B](s)\<rbrakk> \<Longrightarrow> wf[A*B](rmult(A,r,B,s))"
apply (rule wf_onI2)
apply (erule SigmaE)
apply (erule ssubst)
apply (subgoal_tac "\<forall>b\<in>B. \<langle>x,b\<rangle>: Ba", blast)
apply (erule_tac a = x in wf_on_induct, assumption)
apply (rule ballI)
apply (erule_tac a = b in wf_on_induct, assumption)
apply (best elim!: rmultE bspec [THEN mp])
done


lemma wf_rmult: "\<lbrakk>wf(r);  wf(s)\<rbrakk> \<Longrightarrow> wf(rmult(field(r),r,field(s),s))"
apply (simp add: wf_iff_wf_on_field)
apply (rule wf_on_subset_A [OF _ field_rmult])
apply (blast intro: wf_on_rmult)
done

lemma well_ord_rmult:
     "\<lbrakk>well_ord(A,r);  well_ord(B,s)\<rbrakk> \<Longrightarrow> well_ord(A*B, rmult(A,r,B,s))"
apply (rule well_ordI)
apply (simp add: well_ord_def wf_on_rmult)
apply (simp add: well_ord_def tot_ord_def linear_rmult)
done


subsubsection\<open>An \<^term>\<open>ord_iso\<close> congruence law\<close>

lemma prod_bij:
     "\<lbrakk>f \<in> bij(A,C);  g \<in> bij(B,D)\<rbrakk>
      \<Longrightarrow> (lam \<langle>x,y\<rangle>:A*B. \<langle>f`x, g`y\<rangle>) \<in> bij(A*B, C*D)"
apply (rule_tac d = "\<lambda>\<langle>x,y\<rangle>. \<langle>converse (f) `x, converse (g) `y\<rangle>"
       in lam_bijective)
apply (typecheck add: bij_is_inj inj_is_fun)
apply (auto simp add: left_inverse_bij right_inverse_bij)
done

lemma prod_ord_iso_cong:
    "\<lbrakk>f \<in> ord_iso(A,r,A',r');  g \<in> ord_iso(B,s,B',s')\<rbrakk>
     \<Longrightarrow> (lam \<langle>x,y\<rangle>:A*B. \<langle>f`x, g`y\<rangle>)
         \<in> ord_iso(A*B, rmult(A,r,B,s), A'*B', rmult(A',r',B',s'))"
  unfolding ord_iso_def
apply (safe intro!: prod_bij)
apply (simp_all add: bij_is_fun [THEN apply_type])
apply (blast intro: bij_is_inj [THEN inj_apply_equality])
done

lemma singleton_prod_bij: "(\<lambda>z\<in>A. \<langle>x,z\<rangle>) \<in> bij(A, {x}*A)"
by (rule_tac d = snd in lam_bijective, auto)

(*Used??*)
lemma singleton_prod_ord_iso:
     "well_ord({x},xr) \<Longrightarrow>
          (\<lambda>z\<in>A. \<langle>x,z\<rangle>) \<in> ord_iso(A, r, {x}*A, rmult({x}, xr, A, r))"
apply (rule singleton_prod_bij [THEN ord_isoI])
apply (simp (no_asm_simp))
apply (blast dest: well_ord_is_wf [THEN wf_on_not_refl])
done

(*Here we build a complicated function term, then simplify it using
  case_cong, id_conv, comp_lam, case_case.*)
lemma prod_sum_singleton_bij:
     "a\<notin>C \<Longrightarrow>
       (\<lambda>x\<in>C*B + D. case(\<lambda>x. x, \<lambda>y.\<langle>a,y\<rangle>, x))
       \<in> bij(C*B + D, C*B \<union> {a}*D)"
apply (rule subst_elem)
apply (rule id_bij [THEN sum_bij, THEN comp_bij])
apply (rule singleton_prod_bij)
apply (rule sum_disjoint_bij, blast)
apply (simp (no_asm_simp) cong add: case_cong)
apply (rule comp_lam [THEN trans, symmetric])
apply (fast elim!: case_type)
apply (simp (no_asm_simp) add: case_case)
done

lemma prod_sum_singleton_ord_iso:
 "\<lbrakk>a \<in> A;  well_ord(A,r)\<rbrakk> \<Longrightarrow>
    (\<lambda>x\<in>pred(A,a,r)*B + pred(B,b,s). case(\<lambda>x. x, \<lambda>y.\<langle>a,y\<rangle>, x))
    \<in> ord_iso(pred(A,a,r)*B + pred(B,b,s),
                  radd(A*B, rmult(A,r,B,s), B, s),
              pred(A,a,r)*B \<union> {a}*pred(B,b,s), rmult(A,r,B,s))"
apply (rule prod_sum_singleton_bij [THEN ord_isoI])
apply (simp (no_asm_simp) add: pred_iff well_ord_is_wf [THEN wf_on_not_refl])
apply (auto elim!: well_ord_is_wf [THEN wf_on_asym] predE)
done

subsubsection\<open>Distributive law\<close>

lemma sum_prod_distrib_bij:
     "(lam \<langle>x,z\<rangle>:(A+B)*C. case(\<lambda>y. Inl(\<langle>y,z\<rangle>), \<lambda>y. Inr(\<langle>y,z\<rangle>), x))
      \<in> bij((A+B)*C, (A*C)+(B*C))"
by (rule_tac d = "case (\<lambda>\<langle>x,y\<rangle>.\<langle>Inl (x),y\<rangle>, \<lambda>\<langle>x,y\<rangle>.\<langle>Inr (x),y\<rangle>) "
    in lam_bijective, auto)

lemma sum_prod_distrib_ord_iso:
 "(lam \<langle>x,z\<rangle>:(A+B)*C. case(\<lambda>y. Inl(\<langle>y,z\<rangle>), \<lambda>y. Inr(\<langle>y,z\<rangle>), x))
  \<in> ord_iso((A+B)*C, rmult(A+B, radd(A,r,B,s), C, t),
            (A*C)+(B*C), radd(A*C, rmult(A,r,C,t), B*C, rmult(B,s,C,t)))"
by (rule sum_prod_distrib_bij [THEN ord_isoI], auto)

subsubsection\<open>Associativity\<close>

lemma prod_assoc_bij:
     "(lam \<langle>\<langle>x,y\<rangle>, z\<rangle>:(A*B)*C. \<langle>x,\<langle>y,z\<rangle>\<rangle>) \<in> bij((A*B)*C, A*(B*C))"
by (rule_tac d = "\<lambda>\<langle>x, \<langle>y,z\<rangle>\<rangle>. \<langle>\<langle>x,y\<rangle>, z\<rangle>" in lam_bijective, auto)

lemma prod_assoc_ord_iso:
 "(lam \<langle>\<langle>x,y\<rangle>, z\<rangle>:(A*B)*C. \<langle>x,\<langle>y,z\<rangle>\<rangle>)
  \<in> ord_iso((A*B)*C, rmult(A*B, rmult(A,r,B,s), C, t),
            A*(B*C), rmult(A, r, B*C, rmult(B,s,C,t)))"
by (rule prod_assoc_bij [THEN ord_isoI], auto)

subsection\<open>Inverse Image of a Relation\<close>

subsubsection\<open>Rewrite rule\<close>

lemma rvimage_iff: "\<langle>a,b\<rangle> \<in> rvimage(A,f,r)  \<longleftrightarrow>  \<langle>f`a,f`b\<rangle>: r \<and> a \<in> A \<and> b \<in> A"
by (unfold rvimage_def, blast)

subsubsection\<open>Type checking\<close>

lemma rvimage_type: "rvimage(A,f,r) \<subseteq> A*A"
by (unfold rvimage_def, rule Collect_subset)

lemmas field_rvimage = rvimage_type [THEN field_rel_subset]

lemma rvimage_converse: "rvimage(A,f, converse(r)) = converse(rvimage(A,f,r))"
by (unfold rvimage_def, blast)


subsubsection\<open>Partial Ordering Properties\<close>

lemma irrefl_rvimage:
    "\<lbrakk>f \<in> inj(A,B);  irrefl(B,r)\<rbrakk> \<Longrightarrow> irrefl(A, rvimage(A,f,r))"
  unfolding irrefl_def rvimage_def
apply (blast intro: inj_is_fun [THEN apply_type])
done

lemma trans_on_rvimage:
    "\<lbrakk>f \<in> inj(A,B);  trans[B](r)\<rbrakk> \<Longrightarrow> trans[A](rvimage(A,f,r))"
  unfolding trans_on_def rvimage_def
apply (blast intro: inj_is_fun [THEN apply_type])
done

lemma part_ord_rvimage:
    "\<lbrakk>f \<in> inj(A,B);  part_ord(B,r)\<rbrakk> \<Longrightarrow> part_ord(A, rvimage(A,f,r))"
  unfolding part_ord_def
apply (blast intro!: irrefl_rvimage trans_on_rvimage)
done

subsubsection\<open>Linearity\<close>

lemma linear_rvimage:
    "\<lbrakk>f \<in> inj(A,B);  linear(B,r)\<rbrakk> \<Longrightarrow> linear(A,rvimage(A,f,r))"
apply (simp add: inj_def linear_def rvimage_iff)
apply (blast intro: apply_funtype)
done

lemma tot_ord_rvimage:
    "\<lbrakk>f \<in> inj(A,B);  tot_ord(B,r)\<rbrakk> \<Longrightarrow> tot_ord(A, rvimage(A,f,r))"
  unfolding tot_ord_def
apply (blast intro!: part_ord_rvimage linear_rvimage)
done


subsubsection\<open>Well-foundedness\<close>

lemma wf_rvimage [intro!]: "wf(r) \<Longrightarrow> wf(rvimage(A,f,r))"
apply (simp (no_asm_use) add: rvimage_def wf_eq_minimal)
apply clarify
apply (subgoal_tac "\<exists>w. w \<in> {w: {f`x. x \<in> Q}. \<exists>x. x \<in> Q \<and> (f`x = w) }")
 apply (erule allE)
 apply (erule impE)
 apply assumption
 apply blast
apply blast
done

text\<open>But note that the combination of \<open>wf_imp_wf_on\<close> and
 \<open>wf_rvimage\<close> gives \<^prop>\<open>wf(r) \<Longrightarrow> wf[C](rvimage(A,f,r))\<close>\<close>
lemma wf_on_rvimage: "\<lbrakk>f \<in> A\<rightarrow>B;  wf[B](r)\<rbrakk> \<Longrightarrow> wf[A](rvimage(A,f,r))"
apply (rule wf_onI2)
apply (subgoal_tac "\<forall>z\<in>A. f`z=f`y \<longrightarrow> z \<in> Ba")
 apply blast
apply (erule_tac a = "f`y" in wf_on_induct)
 apply (blast intro!: apply_funtype)
apply (blast intro!: apply_funtype dest!: rvimage_iff [THEN iffD1])
done

(*Note that we need only wf[A](...) and linear(A,...) to get the result!*)
lemma well_ord_rvimage:
     "\<lbrakk>f \<in> inj(A,B);  well_ord(B,r)\<rbrakk> \<Longrightarrow> well_ord(A, rvimage(A,f,r))"
apply (rule well_ordI)
  unfolding well_ord_def tot_ord_def
apply (blast intro!: wf_on_rvimage inj_is_fun)
apply (blast intro!: linear_rvimage)
done

lemma ord_iso_rvimage:
    "f \<in> bij(A,B) \<Longrightarrow> f \<in> ord_iso(A, rvimage(A,f,s), B, s)"
  unfolding ord_iso_def
apply (simp add: rvimage_iff)
done

lemma ord_iso_rvimage_eq:
    "f \<in> ord_iso(A,r, B,s) \<Longrightarrow> rvimage(A,f,s) = r \<inter> A*A"
by (unfold ord_iso_def rvimage_def, blast)


subsection\<open>Every well-founded relation is a subset of some inverse image of
      an ordinal\<close>

lemma wf_rvimage_Ord: "Ord(i) \<Longrightarrow> wf(rvimage(A, f, Memrel(i)))"
by (blast intro: wf_rvimage wf_Memrel)


definition
  wfrank :: "[i,i]\<Rightarrow>i"  where
    "wfrank(r,a) \<equiv> wfrec(r, a, \<lambda>x f. \<Union>y \<in> r-``{x}. succ(f`y))"

definition
  wftype :: "i\<Rightarrow>i"  where
    "wftype(r) \<equiv> \<Union>y \<in> range(r). succ(wfrank(r,y))"

lemma wfrank: "wf(r) \<Longrightarrow> wfrank(r,a) = (\<Union>y \<in> r-``{a}. succ(wfrank(r,y)))"
by (subst wfrank_def [THEN def_wfrec], simp_all)

lemma Ord_wfrank: "wf(r) \<Longrightarrow> Ord(wfrank(r,a))"
apply (rule_tac a=a in wf_induct, assumption)
apply (subst wfrank, assumption)
apply (rule Ord_succ [THEN Ord_UN], blast)
done

lemma wfrank_lt: "\<lbrakk>wf(r); \<langle>a,b\<rangle> \<in> r\<rbrakk> \<Longrightarrow> wfrank(r,a) < wfrank(r,b)"
apply (rule_tac a1 = b in wfrank [THEN ssubst], assumption)
apply (rule UN_I [THEN ltI])
apply (simp add: Ord_wfrank vimage_iff)+
done

lemma Ord_wftype: "wf(r) \<Longrightarrow> Ord(wftype(r))"
by (simp add: wftype_def Ord_wfrank)

lemma wftypeI: "\<lbrakk>wf(r);  x \<in> field(r)\<rbrakk> \<Longrightarrow> wfrank(r,x) \<in> wftype(r)"
apply (simp add: wftype_def)
apply (blast intro: wfrank_lt [THEN ltD])
done


lemma wf_imp_subset_rvimage:
     "\<lbrakk>wf(r); r \<subseteq> A*A\<rbrakk> \<Longrightarrow> \<exists>i f. Ord(i) \<and> r \<subseteq> rvimage(A, f, Memrel(i))"
apply (rule_tac x="wftype(r)" in exI)
apply (rule_tac x="\<lambda>x\<in>A. wfrank(r,x)" in exI)
apply (simp add: Ord_wftype, clarify)
apply (frule subsetD, assumption, clarify)
apply (simp add: rvimage_iff wfrank_lt [THEN ltD])
apply (blast intro: wftypeI)
done

theorem wf_iff_subset_rvimage:
  "relation(r) \<Longrightarrow> wf(r) \<longleftrightarrow> (\<exists>i f A. Ord(i) \<and> r \<subseteq> rvimage(A, f, Memrel(i)))"
by (blast dest!: relation_field_times_field wf_imp_subset_rvimage
          intro: wf_rvimage_Ord [THEN wf_subset])


subsection\<open>Other Results\<close>

lemma wf_times: "A \<inter> B = 0 \<Longrightarrow> wf(A*B)"
by (simp add: wf_def, blast)

text\<open>Could also be used to prove \<open>wf_radd\<close>\<close>
lemma wf_Un:
     "\<lbrakk>range(r) \<inter> domain(s) = 0; wf(r);  wf(s)\<rbrakk> \<Longrightarrow> wf(r \<union> s)"
apply (simp add: wf_def, clarify)
apply (rule equalityI)
 prefer 2 apply blast
apply clarify
apply (drule_tac x=Z in spec)
apply (drule_tac x="Z \<inter> domain(s)" in spec)
apply simp
apply (blast intro: elim: equalityE)
done

subsubsection\<open>The Empty Relation\<close>

lemma wf0: "wf(0)"
by (simp add: wf_def, blast)

lemma linear0: "linear(0,0)"
by (simp add: linear_def)

lemma well_ord0: "well_ord(0,0)"
by (blast intro: wf_imp_wf_on well_ordI wf0 linear0)

subsubsection\<open>The "measure" relation is useful with wfrec\<close>

lemma measure_eq_rvimage_Memrel:
     "measure(A,f) = rvimage(A,Lambda(A,f),Memrel(Collect(RepFun(A,f),Ord)))"
apply (simp (no_asm) add: measure_def rvimage_def Memrel_iff)
apply (rule equalityI, auto)
apply (auto intro: Ord_in_Ord simp add: lt_def)
done

lemma wf_measure [iff]: "wf(measure(A,f))"
by (simp (no_asm) add: measure_eq_rvimage_Memrel wf_Memrel wf_rvimage)

lemma measure_iff [iff]: "\<langle>x,y\<rangle> \<in> measure(A,f) \<longleftrightarrow> x \<in> A \<and> y \<in> A \<and> f(x)<f(y)"
by (simp (no_asm) add: measure_def)

lemma linear_measure:
 assumes Ordf: "\<And>x. x \<in> A \<Longrightarrow> Ord(f(x))"
     and inj:  "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; f(x) = f(y)\<rbrakk> \<Longrightarrow> x=y"
 shows "linear(A, measure(A,f))"
apply (auto simp add: linear_def)
apply (rule_tac i="f(x)" and j="f(y)" in Ord_linear_lt)
    apply (simp_all add: Ordf)
apply (blast intro: inj)
done

lemma wf_on_measure: "wf[B](measure(A,f))"
by (rule wf_imp_wf_on [OF wf_measure])

lemma well_ord_measure:
 assumes Ordf: "\<And>x. x \<in> A \<Longrightarrow> Ord(f(x))"
     and inj:  "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; f(x) = f(y)\<rbrakk> \<Longrightarrow> x=y"
 shows "well_ord(A, measure(A,f))"
apply (rule well_ordI)
apply (rule wf_on_measure)
apply (blast intro: linear_measure Ordf inj)
done

lemma measure_type: "measure(A,f) \<subseteq> A*A"
by (auto simp add: measure_def)

subsubsection\<open>Well-foundedness of Unions\<close>

lemma wf_on_Union:
 assumes wfA: "wf[A](r)"
     and wfB: "\<And>a. a\<in>A \<Longrightarrow> wf[B(a)](s)"
     and ok: "\<And>a u v. \<lbrakk>\<langle>u,v\<rangle> \<in> s; v \<in> B(a); a \<in> A\<rbrakk>
                       \<Longrightarrow> (\<exists>a'\<in>A. \<langle>a',a\<rangle> \<in> r \<and> u \<in> B(a')) | u \<in> B(a)"
 shows "wf[\<Union>a\<in>A. B(a)](s)"
apply (rule wf_onI2)
apply (erule UN_E)
apply (subgoal_tac "\<forall>z \<in> B(a). z \<in> Ba", blast)
apply (rule_tac a = a in wf_on_induct [OF wfA], assumption)
apply (rule ballI)
apply (rule_tac a = z in wf_on_induct [OF wfB], assumption, assumption)
apply (rename_tac u)
apply (drule_tac x=u in bspec, blast)
apply (erule mp, clarify)
apply (frule ok, assumption+, blast)
done

subsubsection\<open>Bijections involving Powersets\<close>

lemma Pow_sum_bij:
    "(\<lambda>Z \<in> Pow(A+B). \<langle>{x \<in> A. Inl(x) \<in> Z}, {y \<in> B. Inr(y) \<in> Z}\<rangle>)
     \<in> bij(Pow(A+B), Pow(A)*Pow(B))"
apply (rule_tac d = "\<lambda>\<langle>X,Y\<rangle>. {Inl (x). x \<in> X} \<union> {Inr (y). y \<in> Y}"
       in lam_bijective)
apply force+
done

text\<open>As a special case, we have \<^term>\<open>bij(Pow(A*B), A \<rightarrow> Pow(B))\<close>\<close>
lemma Pow_Sigma_bij:
    "(\<lambda>r \<in> Pow(Sigma(A,B)). \<lambda>x \<in> A. r``{x})
     \<in> bij(Pow(Sigma(A,B)), \<Prod>x \<in> A. Pow(B(x)))"
apply (rule_tac d = "\<lambda>f. \<Union>x \<in> A. \<Union>y \<in> f`x. {\<langle>x,y\<rangle>}" in lam_bijective)
apply (blast intro: lam_type)
apply (blast dest: apply_type, simp_all)
apply fast (*strange, but blast can't do it*)
apply (rule fun_extension, auto)
by blast

end
