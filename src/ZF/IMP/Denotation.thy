(*  Title:      ZF/IMP/Denotation.thy
    Author:     Heiko Loetzbeyer and Robert Sandner, TU München
*)

section \<open>Denotational semantics of expressions and commands\<close>

theory Denotation imports Com begin

subsection \<open>Definitions\<close>

consts
  A     :: "i \<Rightarrow> i \<Rightarrow> i"
  B     :: "i \<Rightarrow> i \<Rightarrow> i"
  C     :: "i \<Rightarrow> i"

definition
  Gamma :: "[i,i,i] \<Rightarrow> i"  (\<open>\<Gamma>\<close>) where
  "\<Gamma>(b,cden) \<equiv>
    (\<lambda>phi. {io \<in> (phi O cden). B(b,fst(io))=1} \<union>
           {io \<in> id(loc->nat). B(b,fst(io))=0})"

primrec
  "A(N(n), sigma) = n"
  "A(X(x), sigma) = sigma`x"
  "A(Op1(f,a), sigma) = f`A(a,sigma)"
  "A(Op2(f,a0,a1), sigma) = f`<A(a0,sigma),A(a1,sigma)>"

primrec
  "B(true, sigma) = 1"
  "B(false, sigma) = 0"
  "B(ROp(f,a0,a1), sigma) = f`<A(a0,sigma),A(a1,sigma)>"
  "B(noti(b), sigma) = not(B(b,sigma))"
  "B(b0 andi b1, sigma) = B(b0,sigma) and B(b1,sigma)"
  "B(b0 ori b1, sigma) = B(b0,sigma) or B(b1,sigma)"

primrec
  "C(\<SKIP>) = id(loc->nat)"
  "C(x \<ASSN> a) =
    {io \<in> (loc->nat) \<times> (loc->nat). snd(io) = fst(io)(x := A(a,fst(io)))}"
  "C(c0\<SEQ> c1) = C(c1) O C(c0)"
  "C(\<IF> b \<THEN> c0 \<ELSE> c1) =
    {io \<in> C(c0). B(b,fst(io)) = 1} \<union> {io \<in> C(c1). B(b,fst(io)) = 0}"
  "C(\<WHILE> b \<DO> c) = lfp((loc->nat) \<times> (loc->nat), \<Gamma>(b,C(c)))"


subsection \<open>Misc lemmas\<close>

lemma A_type [TC]: "\<lbrakk>a \<in> aexp; sigma \<in> loc->nat\<rbrakk> \<Longrightarrow> A(a,sigma) \<in> nat"
  by (erule aexp.induct) simp_all

lemma B_type [TC]: "\<lbrakk>b \<in> bexp; sigma \<in> loc->nat\<rbrakk> \<Longrightarrow> B(b,sigma) \<in> bool"
by (erule bexp.induct, simp_all)

lemma C_subset: "c \<in> com \<Longrightarrow> C(c) \<subseteq> (loc->nat) \<times> (loc->nat)"
  apply (erule com.induct)
      apply simp_all
      apply (blast dest: lfp_subset [THEN subsetD])+
  done

lemma C_type_D [dest]:
    "\<lbrakk>\<langle>x,y\<rangle> \<in> C(c); c \<in> com\<rbrakk> \<Longrightarrow> x \<in> loc->nat \<and> y \<in> loc->nat"
  by (blast dest: C_subset [THEN subsetD])

lemma C_type_fst [dest]: "\<lbrakk>x \<in> C(c); c \<in> com\<rbrakk> \<Longrightarrow> fst(x) \<in> loc->nat"
  by (auto dest!: C_subset [THEN subsetD])

lemma Gamma_bnd_mono:
  "cden \<subseteq> (loc->nat) \<times> (loc->nat)
    \<Longrightarrow> bnd_mono ((loc->nat) \<times> (loc->nat), \<Gamma>(b,cden))"
  by (unfold bnd_mono_def Gamma_def) blast

end
