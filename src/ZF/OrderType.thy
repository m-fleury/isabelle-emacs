(*  Title:      ZF/OrderType.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section\<open>Order Types and Ordinal Arithmetic\<close>

theory OrderType imports OrderArith OrdQuant Nat begin

text\<open>The order type of a well-ordering is the least ordinal isomorphic to it.
Ordinal arithmetic is traditionally defined in terms of order types, as it is
here.  But a definition by transfinite recursion would be much simpler!\<close>

definition
  ordermap  :: "[i,i]\<Rightarrow>i"  where
   "ordermap(A,r) \<equiv> \<lambda>x\<in>A. wfrec[A](r, x, \<lambda>x f. f `` pred(A,x,r))"

definition
  ordertype :: "[i,i]\<Rightarrow>i"  where
   "ordertype(A,r) \<equiv> ordermap(A,r)``A"

definition
  (*alternative definition of ordinal numbers*)
  Ord_alt   :: "i \<Rightarrow> o"  where
   "Ord_alt(X) \<equiv> well_ord(X, Memrel(X)) \<and> (\<forall>u\<in>X. u=pred(X, u, Memrel(X)))"

definition
  (*coercion to ordinal: if not, just 0*)
  ordify    :: "i\<Rightarrow>i"  where
    "ordify(x) \<equiv> if Ord(x) then x else 0"

definition
  (*ordinal multiplication*)
  omult      :: "[i,i]\<Rightarrow>i"           (infixl \<open>**\<close> 70)  where
   "i ** j \<equiv> ordertype(j*i, rmult(j,Memrel(j),i,Memrel(i)))"

definition
  (*ordinal addition*)
  raw_oadd   :: "[i,i]\<Rightarrow>i"  where
    "raw_oadd(i,j) \<equiv> ordertype(i+j, radd(i,Memrel(i),j,Memrel(j)))"

definition
  oadd      :: "[i,i]\<Rightarrow>i"           (infixl \<open>++\<close> 65)  where
    "i ++ j \<equiv> raw_oadd(ordify(i),ordify(j))"

definition
  (*ordinal subtraction*)
  odiff      :: "[i,i]\<Rightarrow>i"           (infixl \<open>--\<close> 65)  where
    "i -- j \<equiv> ordertype(i-j, Memrel(i))"


subsection\<open>Proofs needing the combination of Ordinal.thy and Order.thy\<close>

lemma le_well_ord_Memrel: "j \<le> i \<Longrightarrow> well_ord(j, Memrel(i))"
apply (rule well_ordI)
apply (rule wf_Memrel [THEN wf_imp_wf_on])
apply (simp add: ltD lt_Ord linear_def
                 ltI [THEN lt_trans2 [of _ j i]])
apply (intro ballI Ord_linear)
apply (blast intro: Ord_in_Ord lt_Ord)+
done

(*"Ord(i) \<Longrightarrow> well_ord(i, Memrel(i))"*)
lemmas well_ord_Memrel = le_refl [THEN le_well_ord_Memrel]

(*Kunen's Theorem 7.3 (i), page 16;  see also Ordinal/Ord_in_Ord
  The smaller ordinal is an initial segment of the larger *)
lemma lt_pred_Memrel:
    "j<i \<Longrightarrow> pred(i, j, Memrel(i)) = j"
apply (simp add: pred_def lt_def)
apply (blast intro: Ord_trans)
done

lemma pred_Memrel:
      "x \<in> A \<Longrightarrow> pred(A, x, Memrel(A)) = A \<inter> x"
by (unfold pred_def Memrel_def, blast)

lemma Ord_iso_implies_eq_lemma:
     "\<lbrakk>j<i;  f \<in> ord_iso(i,Memrel(i),j,Memrel(j))\<rbrakk> \<Longrightarrow> R"
apply (frule lt_pred_Memrel)
apply (erule ltE)
apply (rule well_ord_Memrel [THEN well_ord_iso_predE, of i f j], auto)
  unfolding ord_iso_def
(*Combining the two simplifications causes looping*)
apply (simp (no_asm_simp))
apply (blast intro: bij_is_fun [THEN apply_type] Ord_trans)
done

(*Kunen's Theorem 7.3 (ii), page 16.  Isomorphic ordinals are equal*)
lemma Ord_iso_implies_eq:
     "\<lbrakk>Ord(i);  Ord(j);  f \<in> ord_iso(i,Memrel(i),j,Memrel(j))\<rbrakk>
      \<Longrightarrow> i=j"
apply (rule_tac i = i and j = j in Ord_linear_lt)
apply (blast intro: ord_iso_sym Ord_iso_implies_eq_lemma)+
done


subsection\<open>Ordermap and ordertype\<close>

lemma ordermap_type:
    "ordermap(A,r) \<in> A -> ordertype(A,r)"
  unfolding ordermap_def ordertype_def
apply (rule lam_type)
apply (rule lamI [THEN imageI], assumption+)
done

subsubsection\<open>Unfolding of ordermap\<close>

(*Useful for cardinality reasoning; see CardinalArith.ML*)
lemma ordermap_eq_image:
    "\<lbrakk>wf[A](r);  x \<in> A\<rbrakk>
     \<Longrightarrow> ordermap(A,r) ` x = ordermap(A,r) `` pred(A,x,r)"
  unfolding ordermap_def pred_def
apply (simp (no_asm_simp))
apply (erule wfrec_on [THEN trans], assumption)
apply (simp (no_asm_simp) add: subset_iff image_lam vimage_singleton_iff)
done

(*Useful for rewriting PROVIDED pred is not unfolded until later!*)
lemma ordermap_pred_unfold:
     "\<lbrakk>wf[A](r);  x \<in> A\<rbrakk>
      \<Longrightarrow> ordermap(A,r) ` x = {ordermap(A,r)`y . y \<in> pred(A,x,r)}"
by (simp add: ordermap_eq_image pred_subset ordermap_type [THEN image_fun])

(*pred-unfolded version.  NOT suitable for rewriting -- loops!*)
lemmas ordermap_unfold = ordermap_pred_unfold [simplified pred_def]

(*The theorem above is

\<lbrakk>wf[A](r); x \<in> A\<rbrakk>
\<Longrightarrow> ordermap(A,r) ` x = {ordermap(A,r) ` y . y: {y \<in> A . \<langle>y,x\<rangle> \<in> r}}

NOTE: the definition of ordermap used here delivers ordinals only if r is
transitive.  If r is the predecessor relation on the naturals then
ordermap(nat,predr) ` n equals {n-1} and not n.  A more complicated definition,
like

  ordermap(A,r) ` x = Union{succ(ordermap(A,r) ` y) . y: {y \<in> A . \<langle>y,x\<rangle> \<in> r}},

might eliminate the need for r to be transitive.
*)


subsubsection\<open>Showing that ordermap, ordertype yield ordinals\<close>

lemma Ord_ordermap:
    "\<lbrakk>well_ord(A,r);  x \<in> A\<rbrakk> \<Longrightarrow> Ord(ordermap(A,r) ` x)"
apply (unfold well_ord_def tot_ord_def part_ord_def, safe)
apply (rule_tac a=x in wf_on_induct, assumption+)
apply (simp (no_asm_simp) add: ordermap_pred_unfold)
apply (rule OrdI [OF _ Ord_is_Transset])
  unfolding pred_def Transset_def
apply (blast intro: trans_onD
             dest!: ordermap_unfold [THEN equalityD1])+
done

lemma Ord_ordertype:
    "well_ord(A,r) \<Longrightarrow> Ord(ordertype(A,r))"
  unfolding ordertype_def
apply (subst image_fun [OF ordermap_type subset_refl])
apply (rule OrdI [OF _ Ord_is_Transset])
prefer 2 apply (blast intro: Ord_ordermap)
  unfolding Transset_def well_ord_def
apply (blast intro: trans_onD
             dest!: ordermap_unfold [THEN equalityD1])
done


subsubsection\<open>ordermap preserves the orderings in both directions\<close>

lemma ordermap_mono:
     "\<lbrakk>\<langle>w,x\<rangle>: r;  wf[A](r);  w \<in> A; x \<in> A\<rbrakk>
      \<Longrightarrow> ordermap(A,r)`w \<in> ordermap(A,r)`x"
apply (erule_tac x1 = x in ordermap_unfold [THEN ssubst], assumption, blast)
done

(*linearity of r is crucial here*)
lemma converse_ordermap_mono:
    "\<lbrakk>ordermap(A,r)`w \<in> ordermap(A,r)`x;  well_ord(A,r); w \<in> A; x \<in> A\<rbrakk>
     \<Longrightarrow> \<langle>w,x\<rangle>: r"
apply (unfold well_ord_def tot_ord_def, safe)
apply (erule_tac x=w and y=x in linearE, assumption+)
apply (blast elim!: mem_not_refl [THEN notE])
apply (blast dest: ordermap_mono intro: mem_asym)
done

lemma ordermap_surj: "ordermap(A, r) \<in> surj(A, ordertype(A, r))"
  unfolding ordertype_def
  by (rule surj_image) (rule ordermap_type)

lemma ordermap_bij:
    "well_ord(A,r) \<Longrightarrow> ordermap(A,r) \<in> bij(A, ordertype(A,r))"
  unfolding well_ord_def tot_ord_def bij_def inj_def
apply (force intro!: ordermap_type ordermap_surj
             elim: linearE dest: ordermap_mono
             simp add: mem_not_refl)
done

subsubsection\<open>Isomorphisms involving ordertype\<close>

lemma ordertype_ord_iso:
 "well_ord(A,r)
  \<Longrightarrow> ordermap(A,r) \<in> ord_iso(A,r, ordertype(A,r), Memrel(ordertype(A,r)))"
  unfolding ord_iso_def
apply (safe elim!: well_ord_is_wf
            intro!: ordermap_type [THEN apply_type] ordermap_mono ordermap_bij)
apply (blast dest!: converse_ordermap_mono)
done

lemma ordertype_eq:
     "\<lbrakk>f \<in> ord_iso(A,r,B,s);  well_ord(B,s)\<rbrakk>
      \<Longrightarrow> ordertype(A,r) = ordertype(B,s)"
apply (frule well_ord_ord_iso, assumption)
apply (rule Ord_iso_implies_eq, (erule Ord_ordertype)+)
apply (blast intro: ord_iso_trans ord_iso_sym ordertype_ord_iso)
done

lemma ordertype_eq_imp_ord_iso:
     "\<lbrakk>ordertype(A,r) = ordertype(B,s); well_ord(A,r);  well_ord(B,s)\<rbrakk>
      \<Longrightarrow> \<exists>f. f \<in> ord_iso(A,r,B,s)"
apply (rule exI)
apply (rule ordertype_ord_iso [THEN ord_iso_trans], assumption)
apply (erule ssubst)
apply (erule ordertype_ord_iso [THEN ord_iso_sym])
done

subsubsection\<open>Basic equalities for ordertype\<close>

(*Ordertype of Memrel*)
lemma le_ordertype_Memrel: "j \<le> i \<Longrightarrow> ordertype(j,Memrel(i)) = j"
apply (rule Ord_iso_implies_eq [symmetric])
apply (erule ltE, assumption)
apply (blast intro: le_well_ord_Memrel Ord_ordertype)
apply (rule ord_iso_trans)
apply (erule_tac [2] le_well_ord_Memrel [THEN ordertype_ord_iso])
apply (rule id_bij [THEN ord_isoI])
apply (simp (no_asm_simp))
apply (fast elim: ltE Ord_in_Ord Ord_trans)
done

(*"Ord(i) \<Longrightarrow> ordertype(i, Memrel(i)) = i"*)
lemmas ordertype_Memrel = le_refl [THEN le_ordertype_Memrel]

lemma ordertype_0 [simp]: "ordertype(0,r) = 0"
apply (rule id_bij [THEN ord_isoI, THEN ordertype_eq, THEN trans])
apply (erule emptyE)
apply (rule well_ord_0)
apply (rule Ord_0 [THEN ordertype_Memrel])
done

(*Ordertype of rvimage:  \<lbrakk>f \<in> bij(A,B);  well_ord(B,s)\<rbrakk> \<Longrightarrow>
                         ordertype(A, rvimage(A,f,s)) = ordertype(B,s) *)
lemmas bij_ordertype_vimage = ord_iso_rvimage [THEN ordertype_eq]

subsubsection\<open>A fundamental unfolding law for ordertype.\<close>

(*Ordermap returns the same result if applied to an initial segment*)
lemma ordermap_pred_eq_ordermap:
     "\<lbrakk>well_ord(A,r);  y \<in> A;  z \<in> pred(A,y,r)\<rbrakk>
      \<Longrightarrow> ordermap(pred(A,y,r), r) ` z = ordermap(A, r) ` z"
apply (frule wf_on_subset_A [OF well_ord_is_wf pred_subset])
apply (rule_tac a=z in wf_on_induct, assumption+)
apply (safe elim!: predE)
apply (simp (no_asm_simp) add: ordermap_pred_unfold well_ord_is_wf pred_iff)
(*combining these two simplifications LOOPS! *)
apply (simp (no_asm_simp) add: pred_pred_eq)
apply (simp add: pred_def)
apply (rule RepFun_cong [OF _ refl])
apply (drule well_ord_is_trans_on)
apply (fast elim!: trans_onD)
done

lemma ordertype_unfold:
    "ordertype(A,r) = {ordermap(A,r)`y . y \<in> A}"
  unfolding ordertype_def
apply (rule image_fun [OF ordermap_type subset_refl])
done

text\<open>Theorems by Krzysztof Grabczewski; proofs simplified by lcp\<close>

lemma ordertype_pred_subset: "\<lbrakk>well_ord(A,r);  x \<in> A\<rbrakk> \<Longrightarrow>
          ordertype(pred(A,x,r),r) \<subseteq> ordertype(A,r)"
apply (simp add: ordertype_unfold well_ord_subset [OF _ pred_subset])
apply (fast intro: ordermap_pred_eq_ordermap elim: predE)
done

lemma ordertype_pred_lt:
     "\<lbrakk>well_ord(A,r);  x \<in> A\<rbrakk>
      \<Longrightarrow> ordertype(pred(A,x,r),r) < ordertype(A,r)"
apply (rule ordertype_pred_subset [THEN subset_imp_le, THEN leE])
apply (simp_all add: Ord_ordertype well_ord_subset [OF _ pred_subset])
apply (erule sym [THEN ordertype_eq_imp_ord_iso, THEN exE])
apply (erule_tac [3] well_ord_iso_predE)
apply (simp_all add: well_ord_subset [OF _ pred_subset])
done

(*May rewrite with this -- provided no rules are supplied for proving that
        well_ord(pred(A,x,r), r) *)
lemma ordertype_pred_unfold:
     "well_ord(A,r)
      \<Longrightarrow> ordertype(A,r) = {ordertype(pred(A,x,r),r). x \<in> A}"
apply (rule equalityI)
apply (safe intro!: ordertype_pred_lt [THEN ltD])
apply (auto simp add: ordertype_def well_ord_is_wf [THEN ordermap_eq_image]
                      ordermap_type [THEN image_fun]
                      ordermap_pred_eq_ordermap pred_subset)
done


subsection\<open>Alternative definition of ordinal\<close>

(*proof by Krzysztof Grabczewski*)
lemma Ord_is_Ord_alt: "Ord(i) \<Longrightarrow> Ord_alt(i)"
  unfolding Ord_alt_def
apply (rule conjI)
apply (erule well_ord_Memrel)
apply (unfold Ord_def Transset_def pred_def Memrel_def, blast)
done

(*proof by lcp*)
lemma Ord_alt_is_Ord:
    "Ord_alt(i) \<Longrightarrow> Ord(i)"
apply (unfold Ord_alt_def Ord_def Transset_def well_ord_def
                     tot_ord_def part_ord_def trans_on_def)
apply (simp add: pred_Memrel)
apply (blast elim!: equalityE)
done


subsection\<open>Ordinal Addition\<close>

subsubsection\<open>Order Type calculations for radd\<close>

text\<open>Addition with 0\<close>

lemma bij_sum_0: "(\<lambda>z\<in>A+0. case(\<lambda>x. x, \<lambda>y. y, z)) \<in> bij(A+0, A)"
apply (rule_tac d = Inl in lam_bijective, safe)
apply (simp_all (no_asm_simp))
done

lemma ordertype_sum_0_eq:
     "well_ord(A,r) \<Longrightarrow> ordertype(A+0, radd(A,r,0,s)) = ordertype(A,r)"
apply (rule bij_sum_0 [THEN ord_isoI, THEN ordertype_eq])
prefer 2 apply assumption
apply force
done

lemma bij_0_sum: "(\<lambda>z\<in>0+A. case(\<lambda>x. x, \<lambda>y. y, z)) \<in> bij(0+A, A)"
apply (rule_tac d = Inr in lam_bijective, safe)
apply (simp_all (no_asm_simp))
done

lemma ordertype_0_sum_eq:
     "well_ord(A,r) \<Longrightarrow> ordertype(0+A, radd(0,s,A,r)) = ordertype(A,r)"
apply (rule bij_0_sum [THEN ord_isoI, THEN ordertype_eq])
prefer 2 apply assumption
apply force
done

text\<open>Initial segments of radd.  Statements by Grabczewski\<close>

(*In fact, pred(A+B, Inl(a), radd(A,r,B,s)) = pred(A,a,r)+0 *)
lemma pred_Inl_bij:
 "a \<in> A \<Longrightarrow> (\<lambda>x\<in>pred(A,a,r). Inl(x))
          \<in> bij(pred(A,a,r), pred(A+B, Inl(a), radd(A,r,B,s)))"
  unfolding pred_def
apply (rule_tac d = "case (\<lambda>x. x, \<lambda>y. y) " in lam_bijective)
apply auto
done

lemma ordertype_pred_Inl_eq:
     "\<lbrakk>a \<in> A;  well_ord(A,r)\<rbrakk>
      \<Longrightarrow> ordertype(pred(A+B, Inl(a), radd(A,r,B,s)), radd(A,r,B,s)) =
          ordertype(pred(A,a,r), r)"
apply (rule pred_Inl_bij [THEN ord_isoI, THEN ord_iso_sym, THEN ordertype_eq])
apply (simp_all add: well_ord_subset [OF _ pred_subset])
apply (simp add: pred_def)
done

lemma pred_Inr_bij:
 "b \<in> B \<Longrightarrow>
         id(A+pred(B,b,s))
         \<in> bij(A+pred(B,b,s), pred(A+B, Inr(b), radd(A,r,B,s)))"
  unfolding pred_def id_def
apply (rule_tac d = "\<lambda>z. z" in lam_bijective, auto)
done

lemma ordertype_pred_Inr_eq:
     "\<lbrakk>b \<in> B;  well_ord(A,r);  well_ord(B,s)\<rbrakk>
      \<Longrightarrow> ordertype(pred(A+B, Inr(b), radd(A,r,B,s)), radd(A,r,B,s)) =
          ordertype(A+pred(B,b,s), radd(A,r,pred(B,b,s),s))"
apply (rule pred_Inr_bij [THEN ord_isoI, THEN ord_iso_sym, THEN ordertype_eq])
prefer 2 apply (force simp add: pred_def id_def, assumption)
apply (blast intro: well_ord_radd well_ord_subset [OF _ pred_subset])
done


subsubsection\<open>ordify: trivial coercion to an ordinal\<close>

lemma Ord_ordify [iff, TC]: "Ord(ordify(x))"
by (simp add: ordify_def)

(*Collapsing*)
lemma ordify_idem [simp]: "ordify(ordify(x)) = ordify(x)"
by (simp add: ordify_def)


subsubsection\<open>Basic laws for ordinal addition\<close>

lemma Ord_raw_oadd: "\<lbrakk>Ord(i); Ord(j)\<rbrakk> \<Longrightarrow> Ord(raw_oadd(i,j))"
by (simp add: raw_oadd_def ordify_def Ord_ordertype well_ord_radd
              well_ord_Memrel)

lemma Ord_oadd [iff,TC]: "Ord(i++j)"
by (simp add: oadd_def Ord_raw_oadd)


text\<open>Ordinal addition with zero\<close>

lemma raw_oadd_0: "Ord(i) \<Longrightarrow> raw_oadd(i,0) = i"
by (simp add: raw_oadd_def ordify_def ordertype_sum_0_eq
              ordertype_Memrel well_ord_Memrel)

lemma oadd_0 [simp]: "Ord(i) \<Longrightarrow> i++0 = i"
apply (simp (no_asm_simp) add: oadd_def raw_oadd_0 ordify_def)
done

lemma raw_oadd_0_left: "Ord(i) \<Longrightarrow> raw_oadd(0,i) = i"
by (simp add: raw_oadd_def ordify_def ordertype_0_sum_eq ordertype_Memrel
              well_ord_Memrel)

lemma oadd_0_left [simp]: "Ord(i) \<Longrightarrow> 0++i = i"
by (simp add: oadd_def raw_oadd_0_left ordify_def)


lemma oadd_eq_if_raw_oadd:
     "i++j = (if Ord(i) then (if Ord(j) then raw_oadd(i,j) else i)
              else (if Ord(j) then j else 0))"
by (simp add: oadd_def ordify_def raw_oadd_0_left raw_oadd_0)

lemma raw_oadd_eq_oadd: "\<lbrakk>Ord(i); Ord(j)\<rbrakk> \<Longrightarrow> raw_oadd(i,j) = i++j"
by (simp add: oadd_def ordify_def)

(*** Further properties of ordinal addition.  Statements by Grabczewski,
    proofs by lcp. ***)

(*Surely also provable by transfinite induction on j?*)
lemma lt_oadd1: "k<i \<Longrightarrow> k < i++j"
apply (simp add: oadd_def ordify_def lt_Ord2 raw_oadd_0, clarify)
apply (simp add: raw_oadd_def)
apply (rule ltE, assumption)
apply (rule ltI)
apply (force simp add: ordertype_pred_unfold well_ord_radd well_ord_Memrel
          ordertype_pred_Inl_eq lt_pred_Memrel leI [THEN le_ordertype_Memrel])
apply (blast intro: Ord_ordertype well_ord_radd well_ord_Memrel)
done

(*Thus also we obtain the rule  @{term"i++j = k \<Longrightarrow> i \<le> k"} *)
lemma oadd_le_self: "Ord(i) \<Longrightarrow> i \<le> i++j"
apply (rule all_lt_imp_le)
apply (auto simp add: Ord_oadd lt_oadd1)
done

text\<open>Various other results\<close>

lemma id_ord_iso_Memrel: "A<=B \<Longrightarrow> id(A) \<in> ord_iso(A, Memrel(A), A, Memrel(B))"
apply (rule id_bij [THEN ord_isoI])
apply (simp (no_asm_simp))
apply blast
done

lemma subset_ord_iso_Memrel:
     "\<lbrakk>f \<in> ord_iso(A,Memrel(B),C,r); A<=B\<rbrakk> \<Longrightarrow> f \<in> ord_iso(A,Memrel(A),C,r)"
apply (frule ord_iso_is_bij [THEN bij_is_fun, THEN fun_is_rel])
apply (frule ord_iso_trans [OF id_ord_iso_Memrel], assumption)
apply (simp add: right_comp_id)
done

lemma restrict_ord_iso:
     "\<lbrakk>f \<in> ord_iso(i, Memrel(i), Order.pred(A,a,r), r);  a \<in> A; j < i;
       trans[A](r)\<rbrakk>
      \<Longrightarrow> restrict(f,j) \<in> ord_iso(j, Memrel(j), Order.pred(A,f`j,r), r)"
apply (frule ltD)
apply (frule ord_iso_is_bij [THEN bij_is_fun, THEN apply_type], assumption)
apply (frule ord_iso_restrict_pred, assumption)
apply (simp add: pred_iff trans_pred_pred_eq lt_pred_Memrel)
apply (blast intro!: subset_ord_iso_Memrel le_imp_subset [OF leI])
done

lemma restrict_ord_iso2:
     "\<lbrakk>f \<in> ord_iso(Order.pred(A,a,r), r, i, Memrel(i));  a \<in> A;
       j < i; trans[A](r)\<rbrakk>
      \<Longrightarrow> converse(restrict(converse(f), j))
          \<in> ord_iso(Order.pred(A, converse(f)`j, r), r, j, Memrel(j))"
by (blast intro: restrict_ord_iso ord_iso_sym ltI)

lemma ordertype_sum_Memrel:
     "\<lbrakk>well_ord(A,r);  k<j\<rbrakk>
      \<Longrightarrow> ordertype(A+k, radd(A, r, k, Memrel(j))) =
          ordertype(A+k, radd(A, r, k, Memrel(k)))"
apply (erule ltE)
apply (rule ord_iso_refl [THEN sum_ord_iso_cong, THEN ordertype_eq])
apply (erule OrdmemD [THEN id_ord_iso_Memrel, THEN ord_iso_sym])
apply (simp_all add: well_ord_radd well_ord_Memrel)
done

lemma oadd_lt_mono2: "k<j \<Longrightarrow> i++k < i++j"
apply (simp add: oadd_def ordify_def raw_oadd_0_left lt_Ord lt_Ord2, clarify)
apply (simp add: raw_oadd_def)
apply (rule ltE, assumption)
apply (rule ordertype_pred_unfold [THEN equalityD2, THEN subsetD, THEN ltI])
apply (simp_all add: Ord_ordertype well_ord_radd well_ord_Memrel)
apply (rule bexI)
apply (erule_tac [2] InrI)
apply (simp add: ordertype_pred_Inr_eq well_ord_Memrel lt_pred_Memrel
                 leI [THEN le_ordertype_Memrel] ordertype_sum_Memrel)
done

lemma oadd_lt_cancel2: "\<lbrakk>i++j < i++k;  Ord(j)\<rbrakk> \<Longrightarrow> j<k"
apply (simp (asm_lr) add: oadd_eq_if_raw_oadd split: split_if_asm)
 prefer 2
 apply (frule_tac i = i and j = j in oadd_le_self)
 apply (simp (asm_lr) add: oadd_def ordify_def lt_Ord not_lt_iff_le [THEN iff_sym])
apply (rule Ord_linear_lt, auto)
apply (simp_all add: raw_oadd_eq_oadd)
apply (blast dest: oadd_lt_mono2 elim: lt_irrefl lt_asym)+
done

lemma oadd_lt_iff2: "Ord(j) \<Longrightarrow> i++j < i++k \<longleftrightarrow> j<k"
by (blast intro!: oadd_lt_mono2 dest!: oadd_lt_cancel2)

lemma oadd_inject: "\<lbrakk>i++j = i++k;  Ord(j); Ord(k)\<rbrakk> \<Longrightarrow> j=k"
apply (simp add: oadd_eq_if_raw_oadd split: split_if_asm)
apply (simp add: raw_oadd_eq_oadd)
apply (rule Ord_linear_lt, auto)
apply (force dest: oadd_lt_mono2 [of concl: i] simp add: lt_not_refl)+
done

lemma lt_oadd_disj: "k < i++j \<Longrightarrow> k<i | (\<exists>l\<in>j. k = i++l )"
apply (simp add: Ord_in_Ord' [of _ j] oadd_eq_if_raw_oadd
            split: split_if_asm)
 prefer 2
 apply (simp add: Ord_in_Ord' [of _ j] lt_def)
apply (simp add: ordertype_pred_unfold well_ord_radd well_ord_Memrel raw_oadd_def)
apply (erule ltD [THEN RepFunE])
apply (force simp add: ordertype_pred_Inl_eq well_ord_Memrel ltI
                       lt_pred_Memrel le_ordertype_Memrel leI
                       ordertype_pred_Inr_eq ordertype_sum_Memrel)
done


subsubsection\<open>Ordinal addition with successor -- via associativity!\<close>

lemma oadd_assoc: "(i++j)++k = i++(j++k)"
apply (simp add: oadd_eq_if_raw_oadd Ord_raw_oadd raw_oadd_0 raw_oadd_0_left, clarify)
apply (simp add: raw_oadd_def)
apply (rule ordertype_eq [THEN trans])
apply (rule sum_ord_iso_cong [OF ordertype_ord_iso [THEN ord_iso_sym]
                                 ord_iso_refl])
apply (simp_all add: Ord_ordertype well_ord_radd well_ord_Memrel)
apply (rule sum_assoc_ord_iso [THEN ordertype_eq, THEN trans])
apply (rule_tac [2] ordertype_eq)
apply (rule_tac [2] sum_ord_iso_cong [OF ord_iso_refl ordertype_ord_iso])
apply (blast intro: Ord_ordertype well_ord_radd well_ord_Memrel)+
done

lemma oadd_unfold: "\<lbrakk>Ord(i);  Ord(j)\<rbrakk> \<Longrightarrow> i++j = i \<union> (\<Union>k\<in>j. {i++k})"
apply (rule subsetI [THEN equalityI])
apply (erule ltI [THEN lt_oadd_disj, THEN disjE])
apply (blast intro: Ord_oadd)
apply (blast elim!: ltE, blast)
apply (force intro: lt_oadd1 oadd_lt_mono2 simp add: Ord_mem_iff_lt)
done

lemma oadd_1: "Ord(i) \<Longrightarrow> i++1 = succ(i)"
apply (simp (no_asm_simp) add: oadd_unfold Ord_1 oadd_0)
apply blast
done

lemma oadd_succ [simp]: "Ord(j) \<Longrightarrow> i++succ(j) = succ(i++j)"
apply (simp add: oadd_eq_if_raw_oadd, clarify)
apply (simp add: raw_oadd_eq_oadd)
apply (simp add: oadd_1 [of j, symmetric] oadd_1 [of "i++j", symmetric]
                 oadd_assoc)
done


text\<open>Ordinal addition with limit ordinals\<close>

lemma oadd_UN:
     "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> Ord(j(x));  a \<in> A\<rbrakk>
      \<Longrightarrow> i ++ (\<Union>x\<in>A. j(x)) = (\<Union>x\<in>A. i++j(x))"
by (blast intro: ltI Ord_UN Ord_oadd lt_oadd1 [THEN ltD]
                 oadd_lt_mono2 [THEN ltD]
          elim!: ltE dest!: ltI [THEN lt_oadd_disj])

lemma oadd_Limit: "Limit(j) \<Longrightarrow> i++j = (\<Union>k\<in>j. i++k)"
apply (frule Limit_has_0 [THEN ltD])
apply (simp add: Limit_is_Ord [THEN Ord_in_Ord] oadd_UN [symmetric]
                 Union_eq_UN [symmetric] Limit_Union_eq)
done

lemma oadd_eq_0_iff: "\<lbrakk>Ord(i); Ord(j)\<rbrakk> \<Longrightarrow> (i ++ j) = 0 \<longleftrightarrow> i=0 \<and> j=0"
apply (erule trans_induct3 [of j])
apply (simp_all add: oadd_Limit)
apply (simp add: Union_empty_iff Limit_def lt_def, blast)
done

lemma oadd_eq_lt_iff: "\<lbrakk>Ord(i); Ord(j)\<rbrakk> \<Longrightarrow> 0 < (i ++ j) \<longleftrightarrow> 0<i | 0<j"
by (simp add: Ord_0_lt_iff [symmetric] oadd_eq_0_iff)

lemma oadd_LimitI: "\<lbrakk>Ord(i); Limit(j)\<rbrakk> \<Longrightarrow> Limit(i ++ j)"
apply (simp add: oadd_Limit)
apply (frule Limit_has_1 [THEN ltD])
apply (rule increasing_LimitI)
 apply (rule Ord_0_lt)
  apply (blast intro: Ord_in_Ord [OF Limit_is_Ord])
 apply (force simp add: Union_empty_iff oadd_eq_0_iff
                        Limit_is_Ord [of j, THEN Ord_in_Ord], auto)
apply (rule_tac x="succ(y)" in bexI)
 apply (simp add: ltI Limit_is_Ord [of j, THEN Ord_in_Ord])
apply (simp add: Limit_def lt_def)
done

text\<open>Order/monotonicity properties of ordinal addition\<close>

lemma oadd_le_self2: "Ord(i) \<Longrightarrow> i \<le> j++i"
proof (induct i rule: trans_induct3)
  case 0 thus ?case by (simp add: Ord_0_le)
next
  case (succ i) thus ?case by (simp add: oadd_succ succ_leI)
next
  case (limit l)
  hence "l = (\<Union>x\<in>l. x)"
    by (simp add: Union_eq_UN [symmetric] Limit_Union_eq)
  also have "... \<le> (\<Union>x\<in>l. j++x)"
    by (rule le_implies_UN_le_UN) (rule limit.hyps)
  finally have "l \<le> (\<Union>x\<in>l. j++x)" .
  thus ?case using limit.hyps by (simp add: oadd_Limit)
qed

lemma oadd_le_mono1: "k \<le> j \<Longrightarrow> k++i \<le> j++i"
apply (frule lt_Ord)
apply (frule le_Ord2)
apply (simp add: oadd_eq_if_raw_oadd, clarify)
apply (simp add: raw_oadd_eq_oadd)
apply (erule_tac i = i in trans_induct3)
apply (simp (no_asm_simp))
apply (simp (no_asm_simp) add: oadd_succ succ_le_iff)
apply (simp (no_asm_simp) add: oadd_Limit)
apply (rule le_implies_UN_le_UN, blast)
done

lemma oadd_lt_mono: "\<lbrakk>i' \<le> i;  j'<j\<rbrakk> \<Longrightarrow> i'++j' < i++j"
by (blast intro: lt_trans1 oadd_le_mono1 oadd_lt_mono2 Ord_succD elim: ltE)

lemma oadd_le_mono: "\<lbrakk>i' \<le> i;  j' \<le> j\<rbrakk> \<Longrightarrow> i'++j' \<le> i++j"
by (simp del: oadd_succ add: oadd_succ [symmetric] le_Ord2 oadd_lt_mono)

lemma oadd_le_iff2: "\<lbrakk>Ord(j); Ord(k)\<rbrakk> \<Longrightarrow> i++j \<le> i++k \<longleftrightarrow> j \<le> k"
by (simp del: oadd_succ add: oadd_lt_iff2 oadd_succ [symmetric] Ord_succ)

lemma oadd_lt_self: "\<lbrakk>Ord(i);  0<j\<rbrakk> \<Longrightarrow> i < i++j"
apply (rule lt_trans2)
apply (erule le_refl)
apply (simp only: lt_Ord2  oadd_1 [of i, symmetric])
apply (blast intro: succ_leI oadd_le_mono)
done

text\<open>Every ordinal is exceeded by some limit ordinal.\<close>
lemma Ord_imp_greater_Limit: "Ord(i) \<Longrightarrow> \<exists>k. i<k \<and> Limit(k)"
apply (rule_tac x="i ++ nat" in exI)
apply (blast intro: oadd_LimitI  oadd_lt_self  Limit_nat [THEN Limit_has_0])
done

lemma Ord2_imp_greater_Limit: "\<lbrakk>Ord(i); Ord(j)\<rbrakk> \<Longrightarrow> \<exists>k. i<k \<and> j<k \<and> Limit(k)"
apply (insert Ord_Un [of i j, THEN Ord_imp_greater_Limit])
apply (simp add: Un_least_lt_iff)
done


subsection\<open>Ordinal Subtraction\<close>

text\<open>The difference is \<^term>\<open>ordertype(j-i, Memrel(j))\<close>.
    It's probably simpler to define the difference recursively!\<close>

lemma bij_sum_Diff:
     "A<=B \<Longrightarrow> (\<lambda>y\<in>B. if(y \<in> A, Inl(y), Inr(y))) \<in> bij(B, A+(B-A))"
apply (rule_tac d = "case (\<lambda>x. x, \<lambda>y. y) " in lam_bijective)
apply (blast intro!: if_type)
apply (fast intro!: case_type)
apply (erule_tac [2] sumE)
apply (simp_all (no_asm_simp))
done

lemma ordertype_sum_Diff:
     "i \<le> j \<Longrightarrow>
            ordertype(i+(j-i), radd(i,Memrel(j),j-i,Memrel(j))) =
            ordertype(j, Memrel(j))"
apply (safe dest!: le_subset_iff [THEN iffD1])
apply (rule bij_sum_Diff [THEN ord_isoI, THEN ord_iso_sym, THEN ordertype_eq])
apply (erule_tac [3] well_ord_Memrel, assumption)
apply (simp (no_asm_simp))
apply (frule_tac j = y in Ord_in_Ord, assumption)
apply (frule_tac j = x in Ord_in_Ord, assumption)
apply (simp (no_asm_simp) add: Ord_mem_iff_lt lt_Ord not_lt_iff_le)
apply (blast intro: lt_trans2 lt_trans)
done

lemma Ord_odiff [simp,TC]:
    "\<lbrakk>Ord(i);  Ord(j)\<rbrakk> \<Longrightarrow> Ord(i--j)"
  unfolding odiff_def
apply (blast intro: Ord_ordertype Diff_subset well_ord_subset well_ord_Memrel)
done


lemma raw_oadd_ordertype_Diff:
   "i \<le> j
    \<Longrightarrow> raw_oadd(i,j--i) = ordertype(i+(j-i), radd(i,Memrel(j),j-i,Memrel(j)))"
apply (simp add: raw_oadd_def odiff_def)
apply (safe dest!: le_subset_iff [THEN iffD1])
apply (rule sum_ord_iso_cong [THEN ordertype_eq])
apply (erule id_ord_iso_Memrel)
apply (rule ordertype_ord_iso [THEN ord_iso_sym])
apply (blast intro: well_ord_radd Diff_subset well_ord_subset well_ord_Memrel)+
done

lemma oadd_odiff_inverse: "i \<le> j \<Longrightarrow> i ++ (j--i) = j"
by (simp add: lt_Ord le_Ord2 oadd_def ordify_def raw_oadd_ordertype_Diff
              ordertype_sum_Diff ordertype_Memrel lt_Ord2 [THEN Ord_succD])

(*By oadd_inject, the difference between i and j is unique.  Note that we get
  i++j = k  \<Longrightarrow>  j = k--i.  *)
lemma odiff_oadd_inverse: "\<lbrakk>Ord(i); Ord(j)\<rbrakk> \<Longrightarrow> (i++j) -- i = j"
apply (rule oadd_inject)
apply (blast intro: oadd_odiff_inverse oadd_le_self)
apply (blast intro: Ord_ordertype Ord_oadd Ord_odiff)+
done

lemma odiff_lt_mono2: "\<lbrakk>i<j;  k \<le> i\<rbrakk> \<Longrightarrow> i--k < j--k"
apply (rule_tac i = k in oadd_lt_cancel2)
apply (simp add: oadd_odiff_inverse)
apply (subst oadd_odiff_inverse)
apply (blast intro: le_trans leI, assumption)
apply (simp (no_asm_simp) add: lt_Ord le_Ord2)
done


subsection\<open>Ordinal Multiplication\<close>

lemma Ord_omult [simp,TC]:
    "\<lbrakk>Ord(i);  Ord(j)\<rbrakk> \<Longrightarrow> Ord(i**j)"
  unfolding omult_def
apply (blast intro: Ord_ordertype well_ord_rmult well_ord_Memrel)
done

subsubsection\<open>A useful unfolding law\<close>

lemma pred_Pair_eq:
 "\<lbrakk>a \<in> A;  b \<in> B\<rbrakk> \<Longrightarrow> pred(A*B, \<langle>a,b\<rangle>, rmult(A,r,B,s)) =
                      pred(A,a,r)*B \<union> ({a} * pred(B,b,s))"
apply (unfold pred_def, blast)
done

lemma ordertype_pred_Pair_eq:
     "\<lbrakk>a \<in> A;  b \<in> B;  well_ord(A,r);  well_ord(B,s)\<rbrakk> \<Longrightarrow>
         ordertype(pred(A*B, \<langle>a,b\<rangle>, rmult(A,r,B,s)), rmult(A,r,B,s)) =
         ordertype(pred(A,a,r)*B + pred(B,b,s),
                  radd(A*B, rmult(A,r,B,s), B, s))"
apply (simp (no_asm_simp) add: pred_Pair_eq)
apply (rule ordertype_eq [symmetric])
apply (rule prod_sum_singleton_ord_iso)
apply (simp_all add: pred_subset well_ord_rmult [THEN well_ord_subset])
apply (blast intro: pred_subset well_ord_rmult [THEN well_ord_subset]
             elim!: predE)
done

lemma ordertype_pred_Pair_lemma:
    "\<lbrakk>i'<i;  j'<j\<rbrakk>
     \<Longrightarrow> ordertype(pred(i*j, <i',j'>, rmult(i,Memrel(i),j,Memrel(j))),
                   rmult(i,Memrel(i),j,Memrel(j))) =
         raw_oadd (j**i', j')"
  unfolding raw_oadd_def omult_def
apply (simp add: ordertype_pred_Pair_eq lt_pred_Memrel ltD lt_Ord2
                 well_ord_Memrel)
apply (rule trans)
 apply (rule_tac [2] ordertype_ord_iso
                      [THEN sum_ord_iso_cong, THEN ordertype_eq])
  apply (rule_tac [3] ord_iso_refl)
apply (rule id_bij [THEN ord_isoI, THEN ordertype_eq])
apply (elim SigmaE sumE ltE ssubst)
apply (simp_all add: well_ord_rmult well_ord_radd well_ord_Memrel
                     Ord_ordertype lt_Ord lt_Ord2)
apply (blast intro: Ord_trans)+
done

lemma lt_omult:
 "\<lbrakk>Ord(i);  Ord(j);  k<j**i\<rbrakk>
  \<Longrightarrow> \<exists>j' i'. k = j**i' ++ j' \<and> j'<j \<and> i'<i"
  unfolding omult_def
apply (simp add: ordertype_pred_unfold well_ord_rmult well_ord_Memrel)
apply (safe elim!: ltE)
apply (simp add: ordertype_pred_Pair_lemma ltI raw_oadd_eq_oadd
            omult_def [symmetric] Ord_in_Ord' [of _ i] Ord_in_Ord' [of _ j])
apply (blast intro: ltI)
done

lemma omult_oadd_lt:
     "\<lbrakk>j'<j;  i'<i\<rbrakk> \<Longrightarrow> j**i' ++ j'  <  j**i"
  unfolding omult_def
apply (rule ltI)
 prefer 2
 apply (simp add: Ord_ordertype well_ord_rmult well_ord_Memrel lt_Ord2)
apply (simp add: ordertype_pred_unfold well_ord_rmult well_ord_Memrel lt_Ord2)
apply (rule bexI [of _ i'])
apply (rule bexI [of _ j'])
apply (simp add: ordertype_pred_Pair_lemma ltI omult_def [symmetric])
apply (simp add: lt_Ord lt_Ord2 raw_oadd_eq_oadd)
apply (simp_all add: lt_def)
done

lemma omult_unfold:
     "\<lbrakk>Ord(i);  Ord(j)\<rbrakk> \<Longrightarrow> j**i = (\<Union>j'\<in>j. \<Union>i'\<in>i. {j**i' ++ j'})"
apply (rule subsetI [THEN equalityI])
apply (rule lt_omult [THEN exE])
apply (erule_tac [3] ltI)
apply (simp_all add: Ord_omult)
apply (blast elim!: ltE)
apply (blast intro: omult_oadd_lt [THEN ltD] ltI)
done

subsubsection\<open>Basic laws for ordinal multiplication\<close>

text\<open>Ordinal multiplication by zero\<close>

lemma omult_0 [simp]: "i**0 = 0"
  unfolding omult_def
apply (simp (no_asm_simp))
done

lemma omult_0_left [simp]: "0**i = 0"
  unfolding omult_def
apply (simp (no_asm_simp))
done

text\<open>Ordinal multiplication by 1\<close>

lemma omult_1 [simp]: "Ord(i) \<Longrightarrow> i**1 = i"
  unfolding omult_def
apply (rule_tac s1="Memrel(i)"
       in ord_isoI [THEN ordertype_eq, THEN trans])
apply (rule_tac c = snd and d = "\<lambda>z.\<langle>0,z\<rangle>"  in lam_bijective)
apply (auto elim!: snd_type well_ord_Memrel ordertype_Memrel)
done

lemma omult_1_left [simp]: "Ord(i) \<Longrightarrow> 1**i = i"
  unfolding omult_def
apply (rule_tac s1="Memrel(i)"
       in ord_isoI [THEN ordertype_eq, THEN trans])
apply (rule_tac c = fst and d = "\<lambda>z.\<langle>z,0\<rangle>" in lam_bijective)
apply (auto elim!: fst_type well_ord_Memrel ordertype_Memrel)
done

text\<open>Distributive law for ordinal multiplication and addition\<close>

lemma oadd_omult_distrib:
     "\<lbrakk>Ord(i);  Ord(j);  Ord(k)\<rbrakk> \<Longrightarrow> i**(j++k) = (i**j)++(i**k)"
apply (simp add: oadd_eq_if_raw_oadd)
apply (simp add: omult_def raw_oadd_def)
apply (rule ordertype_eq [THEN trans])
apply (rule prod_ord_iso_cong [OF ordertype_ord_iso [THEN ord_iso_sym]
                                  ord_iso_refl])
apply (simp_all add: well_ord_rmult well_ord_radd well_ord_Memrel
                     Ord_ordertype)
apply (rule sum_prod_distrib_ord_iso [THEN ordertype_eq, THEN trans])
apply (rule_tac [2] ordertype_eq)
apply (rule_tac [2] sum_ord_iso_cong [OF ordertype_ord_iso ordertype_ord_iso])
apply (simp_all add: well_ord_rmult well_ord_radd well_ord_Memrel
                     Ord_ordertype)
done

lemma omult_succ: "\<lbrakk>Ord(i);  Ord(j)\<rbrakk> \<Longrightarrow> i**succ(j) = (i**j)++i"
by (simp del: oadd_succ add: oadd_1 [of j, symmetric] oadd_omult_distrib)

text\<open>Associative law\<close>

lemma omult_assoc:
    "\<lbrakk>Ord(i);  Ord(j);  Ord(k)\<rbrakk> \<Longrightarrow> (i**j)**k = i**(j**k)"
  unfolding omult_def
apply (rule ordertype_eq [THEN trans])
apply (rule prod_ord_iso_cong [OF ord_iso_refl
                                  ordertype_ord_iso [THEN ord_iso_sym]])
apply (blast intro: well_ord_rmult well_ord_Memrel)+
apply (rule prod_assoc_ord_iso
             [THEN ord_iso_sym, THEN ordertype_eq, THEN trans])
apply (rule_tac [2] ordertype_eq)
apply (rule_tac [2] prod_ord_iso_cong [OF ordertype_ord_iso ord_iso_refl])
apply (blast intro: well_ord_rmult well_ord_Memrel Ord_ordertype)+
done


text\<open>Ordinal multiplication with limit ordinals\<close>

lemma omult_UN:
     "\<lbrakk>Ord(i);  \<And>x. x \<in> A \<Longrightarrow> Ord(j(x))\<rbrakk>
      \<Longrightarrow> i ** (\<Union>x\<in>A. j(x)) = (\<Union>x\<in>A. i**j(x))"
by (simp (no_asm_simp) add: Ord_UN omult_unfold, blast)

lemma omult_Limit: "\<lbrakk>Ord(i);  Limit(j)\<rbrakk> \<Longrightarrow> i**j = (\<Union>k\<in>j. i**k)"
by (simp add: Limit_is_Ord [THEN Ord_in_Ord] omult_UN [symmetric]
              Union_eq_UN [symmetric] Limit_Union_eq)


subsubsection\<open>Ordering/monotonicity properties of ordinal multiplication\<close>

(*As a special case we have "\<lbrakk>0<i;  0<j\<rbrakk> \<Longrightarrow> 0 < i**j" *)
lemma lt_omult1: "\<lbrakk>k<i;  0<j\<rbrakk> \<Longrightarrow> k < i**j"
apply (safe elim!: ltE intro!: ltI Ord_omult)
apply (force simp add: omult_unfold)
done

lemma omult_le_self: "\<lbrakk>Ord(i);  0<j\<rbrakk> \<Longrightarrow> i \<le> i**j"
by (blast intro: all_lt_imp_le Ord_omult lt_omult1 lt_Ord2)

lemma omult_le_mono1:
  assumes kj: "k \<le> j" and i: "Ord(i)" shows "k**i \<le> j**i"
proof -
  have o: "Ord(k)" "Ord(j)" by (rule lt_Ord [OF kj] le_Ord2 [OF kj])+
  show ?thesis using i
  proof (induct i rule: trans_induct3)
    case 0 thus ?case
      by simp
  next
    case (succ i) thus ?case
      by (simp add: o kj omult_succ oadd_le_mono)
  next
    case (limit l)
    thus ?case
      by (auto simp add: o kj omult_Limit le_implies_UN_le_UN)
  qed
qed

lemma omult_lt_mono2: "\<lbrakk>k<j;  0<i\<rbrakk> \<Longrightarrow> i**k < i**j"
apply (rule ltI)
apply (simp (no_asm_simp) add: omult_unfold lt_Ord2)
apply (safe elim!: ltE intro!: Ord_omult)
apply (force simp add: Ord_omult)
done

lemma omult_le_mono2: "\<lbrakk>k \<le> j;  Ord(i)\<rbrakk> \<Longrightarrow> i**k \<le> i**j"
apply (rule subset_imp_le)
apply (safe elim!: ltE dest!: Ord_succD intro!: Ord_omult)
apply (simp add: omult_unfold)
apply (blast intro: Ord_trans)
done

lemma omult_le_mono: "\<lbrakk>i' \<le> i;  j' \<le> j\<rbrakk> \<Longrightarrow> i'**j' \<le> i**j"
by (blast intro: le_trans omult_le_mono1 omult_le_mono2 Ord_succD elim: ltE)

lemma omult_lt_mono: "\<lbrakk>i' \<le> i;  j'<j;  0<i\<rbrakk> \<Longrightarrow> i'**j' < i**j"
by (blast intro: lt_trans1 omult_le_mono1 omult_lt_mono2 Ord_succD elim: ltE)

lemma omult_le_self2:
  assumes i: "Ord(i)" and j: "0<j" shows "i \<le> j**i"
proof -
  have oj: "Ord(j)" by (rule lt_Ord2 [OF j])
  show ?thesis using i
  proof (induct i rule: trans_induct3)
    case 0 thus ?case
      by simp
  next
    case (succ i)
    have "j ** i ++ 0 < j ** i ++ j"
      by (rule oadd_lt_mono2 [OF j])
    with succ.hyps show ?case
      by (simp add: oj j omult_succ ) (rule lt_trans1)
  next
    case (limit l)
    hence "l = (\<Union>x\<in>l. x)"
      by (simp add: Union_eq_UN [symmetric] Limit_Union_eq)
    also have "... \<le> (\<Union>x\<in>l. j**x)"
      by (rule le_implies_UN_le_UN) (rule limit.hyps)
    finally have "l \<le> (\<Union>x\<in>l. j**x)" .
    thus ?case using limit.hyps by (simp add: oj omult_Limit)
  qed
qed


text\<open>Further properties of ordinal multiplication\<close>

lemma omult_inject: "\<lbrakk>i**j = i**k;  0<i;  Ord(j);  Ord(k)\<rbrakk> \<Longrightarrow> j=k"
apply (rule Ord_linear_lt)
prefer 4 apply assumption
apply auto
apply (force dest: omult_lt_mono2 simp add: lt_not_refl)+
done

subsection\<open>The Relation \<^term>\<open>Lt\<close>\<close>

lemma wf_Lt: "wf(Lt)"
apply (rule wf_subset)
apply (rule wf_Memrel)
apply (auto simp add: Lt_def Memrel_def lt_def)
done

lemma irrefl_Lt: "irrefl(A,Lt)"
by (auto simp add: Lt_def irrefl_def)

lemma trans_Lt: "trans[A](Lt)"
apply (simp add: Lt_def trans_on_def)
apply (blast intro: lt_trans)
done

lemma part_ord_Lt: "part_ord(A,Lt)"
by (simp add: part_ord_def irrefl_Lt trans_Lt)

lemma linear_Lt: "linear(nat,Lt)"
apply (auto dest!: not_lt_imp_le simp add: Lt_def linear_def le_iff)
apply (drule lt_asym, auto)
done

lemma tot_ord_Lt: "tot_ord(nat,Lt)"
by (simp add: tot_ord_def linear_Lt part_ord_Lt)

lemma well_ord_Lt: "well_ord(nat,Lt)"
by (simp add: well_ord_def wf_Lt wf_imp_wf_on tot_ord_Lt)

end
