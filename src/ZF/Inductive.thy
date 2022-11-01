(*  Title:      ZF/Inductive.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Inductive definitions use least fixedpoints with standard products and sums
Coinductive definitions use greatest fixedpoints with Quine products and sums

Sums are used only for mutual recursion;
Products are used only to derive "streamlined" induction rules for relations
*)

section\<open>Inductive and Coinductive Definitions\<close>

theory Inductive
imports Fixedpt QPair Nat
keywords
  "inductive" "coinductive" "inductive_cases" "rep_datatype" "primrec" :: thy_decl and
  "domains" "intros" "monos" "con_defs" "type_intros" "type_elims"
    "elimination" "induction" "case_eqns" "recursor_eqns" :: quasi_command
begin

lemma def_swap_iff: "a \<equiv> b \<Longrightarrow> a = c \<longleftrightarrow> c = b"
  by blast

lemma def_trans: "f \<equiv> g \<Longrightarrow> g(a) = b \<Longrightarrow> f(a) = b"
  by simp

lemma refl_thin: "\<And>P. a = a \<Longrightarrow> P \<Longrightarrow> P" .

ML_file \<open>ind_syntax.ML\<close>
ML_file \<open>Tools/ind_cases.ML\<close>
ML_file \<open>Tools/cartprod.ML\<close>
ML_file \<open>Tools/inductive_package.ML\<close>
ML_file \<open>Tools/induct_tacs.ML\<close>
ML_file \<open>Tools/primrec_package.ML\<close>

ML \<open>
structure Lfp =
  struct
  val oper      = \<^Const>\<open>lfp\<close>
  val bnd_mono  = \<^Const>\<open>bnd_mono\<close>
  val bnd_monoI = @{thm bnd_monoI}
  val subs      = @{thm def_lfp_subset}
  val Tarski    = @{thm def_lfp_unfold}
  val induct    = @{thm def_induct}
  end;

structure Standard_Prod =
  struct
  val sigma     = \<^Const>\<open>Sigma\<close>
  val pair      = \<^Const>\<open>Pair\<close>
  val split_name = \<^const_name>\<open>split\<close>
  val pair_iff  = @{thm Pair_iff}
  val split_eq  = @{thm split}
  val fsplitI   = @{thm splitI}
  val fsplitD   = @{thm splitD}
  val fsplitE   = @{thm splitE}
  end;

structure Standard_CP = CartProd_Fun (Standard_Prod);

structure Standard_Sum =
  struct
  val sum       = \<^Const>\<open>sum\<close>
  val inl       = \<^Const>\<open>Inl\<close>
  val inr       = \<^Const>\<open>Inr\<close>
  val elim      = \<^Const>\<open>case\<close>
  val case_inl  = @{thm case_Inl}
  val case_inr  = @{thm case_Inr}
  val inl_iff   = @{thm Inl_iff}
  val inr_iff   = @{thm Inr_iff}
  val distinct  = @{thm Inl_Inr_iff}
  val distinct' = @{thm Inr_Inl_iff}
  val free_SEs  = Ind_Syntax.mk_free_SEs
            [distinct, distinct', inl_iff, inr_iff, Standard_Prod.pair_iff]
  end;


structure Ind_Package =
    Add_inductive_def_Fun
      (structure Fp=Lfp and Pr=Standard_Prod and CP=Standard_CP
       and Su=Standard_Sum val coind = false);


structure Gfp =
  struct
  val oper      = \<^Const>\<open>gfp\<close>
  val bnd_mono  = \<^Const>\<open>bnd_mono\<close>
  val bnd_monoI = @{thm bnd_monoI}
  val subs      = @{thm def_gfp_subset}
  val Tarski    = @{thm def_gfp_unfold}
  val induct    = @{thm def_Collect_coinduct}
  end;

structure Quine_Prod =
  struct
  val sigma     = \<^Const>\<open>QSigma\<close>
  val pair      = \<^Const>\<open>QPair\<close>
  val split_name = \<^const_name>\<open>qsplit\<close>
  val pair_iff  = @{thm QPair_iff}
  val split_eq  = @{thm qsplit}
  val fsplitI   = @{thm qsplitI}
  val fsplitD   = @{thm qsplitD}
  val fsplitE   = @{thm qsplitE}
  end;

structure Quine_CP = CartProd_Fun (Quine_Prod);

structure Quine_Sum =
  struct
  val sum       = \<^Const>\<open>qsum\<close>
  val inl       = \<^Const>\<open>QInl\<close>
  val inr       = \<^Const>\<open>QInr\<close>
  val elim      = \<^Const>\<open>qcase\<close>
  val case_inl  = @{thm qcase_QInl}
  val case_inr  = @{thm qcase_QInr}
  val inl_iff   = @{thm QInl_iff}
  val inr_iff   = @{thm QInr_iff}
  val distinct  = @{thm QInl_QInr_iff}
  val distinct' = @{thm QInr_QInl_iff}
  val free_SEs  = Ind_Syntax.mk_free_SEs
            [distinct, distinct', inl_iff, inr_iff, Quine_Prod.pair_iff]
  end;


structure CoInd_Package =
  Add_inductive_def_Fun(structure Fp=Gfp and Pr=Quine_Prod and CP=Quine_CP
    and Su=Quine_Sum val coind = true);

\<close>

end
