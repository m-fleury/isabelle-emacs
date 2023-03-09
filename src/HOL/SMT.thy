(*  Title:      HOL/SMT.thy
    Author:     Sascha Boehme, TU Muenchen
    Author:     Jasmin Blanchette, VU Amsterdam
*)

section \<open>Bindings to Satisfiability Modulo Theories (SMT) solvers based on SMT-LIB 2\<close>

theory SMT
  imports Divides Numeral_Simprocs "HOL-Library.Word" "HOL.Real" "Tools/SMT/cvc5_dsl_rewrites/Rare_Interface"
"HOL-Library.Sublist"
  keywords "smt_status" "parse_rare_file" "parse_rare" :: diag
begin

subsection \<open>A skolemization tactic and proof method\<close>

lemma choices:
  "\<And>Q. \<forall>x. \<exists>y ya. Q x y ya \<Longrightarrow> \<exists>f fa. \<forall>x. Q x (f x) (fa x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb. Q x y ya yb \<Longrightarrow> \<exists>f fa fb. \<forall>x. Q x (f x) (fa x) (fb x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc. Q x y ya yb yc \<Longrightarrow> \<exists>f fa fb fc. \<forall>x. Q x (f x) (fa x) (fb x) (fc x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc yd. Q x y ya yb yc yd \<Longrightarrow>
     \<exists>f fa fb fc fd. \<forall>x. Q x (f x) (fa x) (fb x) (fc x) (fd x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc yd ye. Q x y ya yb yc yd ye \<Longrightarrow>
     \<exists>f fa fb fc fd fe. \<forall>x. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc yd ye yf. Q x y ya yb yc yd ye yf \<Longrightarrow>
     \<exists>f fa fb fc fd fe ff. \<forall>x. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x) (ff x)"
  "\<And>Q. \<forall>x. \<exists>y ya yb yc yd ye yf yg. Q x y ya yb yc yd ye yf yg \<Longrightarrow>
     \<exists>f fa fb fc fd fe ff fg. \<forall>x. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x) (ff x) (fg x)"
  by metis+

lemma bchoices:
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya. Q x y ya \<Longrightarrow> \<exists>f fa. \<forall>x \<in> S. Q x (f x) (fa x)"
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya yb. Q x y ya yb \<Longrightarrow> \<exists>f fa fb. \<forall>x \<in> S. Q x (f x) (fa x) (fb x)"
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya yb yc. Q x y ya yb yc \<Longrightarrow> \<exists>f fa fb fc. \<forall>x \<in> S. Q x (f x) (fa x) (fb x) (fc x)"
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya yb yc yd. Q x y ya yb yc yd \<Longrightarrow>
    \<exists>f fa fb fc fd. \<forall>x \<in> S. Q x (f x) (fa x) (fb x) (fc x) (fd x)"
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya yb yc yd ye. Q x y ya yb yc yd ye \<Longrightarrow>
    \<exists>f fa fb fc fd fe. \<forall>x \<in> S. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x)"
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya yb yc yd ye yf. Q x y ya yb yc yd ye yf \<Longrightarrow>
    \<exists>f fa fb fc fd fe ff. \<forall>x \<in> S. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x) (ff x)"
  "\<And>Q. \<forall>x \<in> S. \<exists>y ya yb yc yd ye yf yg. Q x y ya yb yc yd ye yf yg \<Longrightarrow>
    \<exists>f fa fb fc fd fe ff fg. \<forall>x \<in> S. Q x (f x) (fa x) (fb x) (fc x) (fd x) (fe x) (ff x) (fg x)"
  by metis+

ML \<open>
fun moura_tac ctxt =
  Atomize_Elim.atomize_elim_tac ctxt THEN'
  SELECT_GOAL (Clasimp.auto_tac (ctxt addSIs @{thms choice choices bchoice bchoices}) THEN
    ALLGOALS (Metis_Tactic.metis_tac (take 1 ATP_Proof_Reconstruct.partial_type_encs)
        ATP_Proof_Reconstruct.default_metis_lam_trans ctxt [] ORELSE'
      blast_tac ctxt))
\<close>

method_setup moura = \<open>
  Scan.succeed (SIMPLE_METHOD' o moura_tac)
\<close> "solve skolemization goals, especially those arising from Z3 proofs"

hide_fact (open) choices bchoices


subsection \<open>Triggers for quantifier instantiation\<close>

text \<open>
Some SMT solvers support patterns as a quantifier instantiation
heuristics. Patterns may either be positive terms (tagged by "pat")
triggering quantifier instantiations -- when the solver finds a
term matching a positive pattern, it instantiates the corresponding
quantifier accordingly -- or negative terms (tagged by "nopat")
inhibiting quantifier instantiations. A list of patterns
of the same kind is called a multipattern, and all patterns in a
multipattern are considered conjunctively for quantifier instantiation.
A list of multipatterns is called a trigger, and their multipatterns
act disjunctively during quantifier instantiation. Each multipattern
should mention at least all quantified variables of the preceding
quantifier block.
\<close>

typedecl 'a symb_list

consts
  Symb_Nil :: "'a symb_list"
  Symb_Cons :: "'a \<Rightarrow> 'a symb_list \<Rightarrow> 'a symb_list"

typedecl pattern

consts
  pat :: "'a \<Rightarrow> pattern"
  nopat :: "'a \<Rightarrow> pattern"

definition trigger :: "pattern symb_list symb_list \<Rightarrow> bool \<Rightarrow> bool" where
  "trigger _ P = P"


subsection \<open>Higher-order encoding\<close>

text \<open>
Application is made explicit for constants occurring with varying
numbers of arguments. This is achieved by the introduction of the
following constant.
\<close>

definition fun_app :: "'a \<Rightarrow> 'a" where "fun_app f = f"

text \<open>
Some solvers support a theory of arrays which can be used to encode
higher-order functions. The following set of lemmas specifies the
properties of such (extensional) arrays.
\<close>

lemmas array_rules = ext fun_upd_apply fun_upd_same fun_upd_other  fun_upd_upd fun_app_def


subsection \<open>Normalization\<close>

lemma case_bool_if[abs_def]: "case_bool x y P = (if P then x else y)"
  by simp

lemmas Ex1_def_raw = Ex1_def[abs_def]
lemmas Ball_def_raw = Ball_def[abs_def]
lemmas Bex_def_raw = Bex_def[abs_def]
lemmas abs_if_raw = abs_if[abs_def]
lemmas min_def_raw = min_def[abs_def]
lemmas max_def_raw = max_def[abs_def]

lemma nat_zero_as_int:
  "0 = nat 0"
  by simp

lemma nat_one_as_int:
  "1 = nat 1"
  by simp

lemma nat_numeral_as_int: "numeral = (\<lambda>i. nat (numeral i))" by simp
lemma nat_less_as_int: "(<) = (\<lambda>a b. int a < int b)" by simp
lemma nat_leq_as_int: "(\<le>) = (\<lambda>a b. int a \<le> int b)" by simp
lemma Suc_as_int: "Suc = (\<lambda>a. nat (int a + 1))" by (rule ext) simp
lemma nat_plus_as_int: "(+) = (\<lambda>a b. nat (int a + int b))" by (rule ext)+ simp
lemma nat_minus_as_int: "(-) = (\<lambda>a b. nat (int a - int b))" by (rule ext)+ simp
lemma nat_times_as_int: "(*) = (\<lambda>a b. nat (int a * int b))" by (simp add: nat_mult_distrib)
lemma nat_div_as_int: "(div) = (\<lambda>a b. nat (int a div int b))" by (simp add: nat_div_distrib)
lemma nat_mod_as_int: "(mod) = (\<lambda>a b. nat (int a mod int b))" by (simp add: nat_mod_distrib)

lemma int_Suc: "int (Suc n) = int n + 1" by simp
lemma int_plus: "int (n + m) = int n + int m" by (rule of_nat_add)
lemma int_minus: "int (n - m) = int (nat (int n - int m))" by auto

lemma nat_int_comparison:
  fixes a b :: nat     
  shows "(a = b) = (int a = int b)"
    and "(a < b) = (int a < int b)"
    and "(a \<le> b) = (int a \<le> int b)"
  by simp_all

lemma int_ops:
  fixes a b :: nat
  shows "int 0 = 0"
    and "int 1 = 1"
    and "int (numeral n) = numeral n"
    and "int (Suc a) = int a + 1"
    and "int (a + b) = int a + int b"
    and "int (a - b) = (if int a < int b then 0 else int a - int b)"
    and "int (a * b) = int a * int b"
    and "int (a div b) = int a div int b"
    and "int (a mod b) = int a mod int b"
  by (auto intro: zdiv_int zmod_int)

lemma int_if:
  fixes a b :: nat
  shows "int (if P then a else b) = (if P then int a else int b)"
  by simp


subsection \<open>Integer division and modulo for Z3\<close>

text \<open>
The following Z3-inspired definitions are overspecified for the case where \<open>l = 0\<close>. This
Schönheitsfehler is corrected in the \<open>div_as_z3div\<close> and \<open>mod_as_z3mod\<close> theorems.
\<close>

definition z3div :: "int \<Rightarrow> int \<Rightarrow> int" where
  "z3div k l = (if l \<ge> 0 then k div l else - (k div - l))"

definition z3mod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "z3mod k l = k mod (if l \<ge> 0 then l else - l)"

lemma div_as_z3div:
  "\<forall>k l. k div l = (if l = 0 then 0 else if l > 0 then z3div k l else z3div (- k) (- l))"
  by (simp add: z3div_def)

lemma mod_as_z3mod:
  "\<forall>k l. k mod l = (if l = 0 then k else if l > 0 then z3mod k l else - z3mod (- k) (- l))"
  by (simp add: z3mod_def)


subsection \<open>Extra theorems for veriT reconstruction\<close>

lemma verit_sko_forall: \<open>(\<forall>x. P x) \<longleftrightarrow> P (SOME x. \<not>P x)\<close>
  using someI[of \<open>\<lambda>x. \<not>P x\<close>]
  by auto

lemma verit_sko_forall': \<open>P (SOME x. \<not>P x) = A \<Longrightarrow> (\<forall>x. P x) = A\<close>
  by (subst verit_sko_forall)

lemma verit_sko_forall'': \<open>B = A \<Longrightarrow> (SOME x. P x) = A \<equiv> (SOME x. P x) = B\<close>
  by auto

lemma verit_sko_forall_indirect: \<open>x = (SOME x. \<not>P x) \<Longrightarrow> (\<forall>x. P x) \<longleftrightarrow> P x\<close>
  using someI[of \<open>\<lambda>x. \<not>P x\<close>]
  by auto

lemma verit_sko_forall_indirect2:
    \<open>x = (SOME x. \<not>P x) \<Longrightarrow> (\<And>x :: 'a. (P x = P' x)) \<Longrightarrow>(\<forall>x. P' x) \<longleftrightarrow> P x\<close>
  using someI[of \<open>\<lambda>x. \<not>P x\<close>]
  by auto

lemma verit_sko_ex: \<open>(\<exists>x. P x) \<longleftrightarrow> P (SOME x. P x)\<close>
  using someI[of \<open>\<lambda>x. P x\<close>]
  by auto

lemma verit_sko_ex': \<open>P (SOME x. P x) = A \<Longrightarrow> (\<exists>x. P x) = A\<close>
  by (subst verit_sko_ex)

lemma verit_sko_ex_indirect: \<open>x = (SOME x. P x) \<Longrightarrow> (\<exists>x. P x) \<longleftrightarrow> P x\<close>
  using someI[of \<open>\<lambda>x. P x\<close>]
  by auto

lemma verit_sko_ex_indirect2: \<open>x = (SOME x. P x) \<Longrightarrow> (\<And>x. P x = P' x) \<Longrightarrow> (\<exists>x. P' x) \<longleftrightarrow> P x\<close>
  using someI[of \<open>\<lambda>x. P x\<close>]
  by auto

lemma verit_Pure_trans:
  \<open>P \<equiv> Q \<Longrightarrow> Q \<Longrightarrow> P\<close>
  by auto

lemma verit_if_cong:
  assumes \<open>b \<equiv> c\<close>
    and \<open>c \<Longrightarrow> x \<equiv> u\<close>
    and \<open>\<not> c \<Longrightarrow> y \<equiv> v\<close>
  shows \<open>(if b then x else y) \<equiv> (if c then u else v)\<close>
  using assms if_cong[of b c x u] by auto

lemma verit_if_weak_cong':
  \<open>b \<equiv> c \<Longrightarrow> (if b then x else y) \<equiv> (if c then x else y)\<close>
  by auto

lemma verit_or_neg:
   \<open>(A \<Longrightarrow> B) \<Longrightarrow> B \<or> \<not>A\<close>
   \<open>(\<not>A \<Longrightarrow> B) \<Longrightarrow> B \<or> A\<close>
  by auto

lemma verit_subst_bool: \<open>P \<Longrightarrow> f True \<Longrightarrow> f P\<close>
  by auto

lemma verit_and_pos:
  \<open>(a \<Longrightarrow> \<not>(b \<and> c) \<or> A) \<Longrightarrow> \<not>(a \<and> b \<and> c) \<or> A\<close>
  \<open>(a \<Longrightarrow> b \<Longrightarrow> A) \<Longrightarrow> \<not>(a \<and> b) \<or> A\<close>
  \<open>(a \<Longrightarrow> A) \<Longrightarrow> \<not>a \<or> A\<close>
  \<open>(\<not>a \<Longrightarrow> A) \<Longrightarrow> a \<or> A\<close>
  by blast+

lemma verit_or_pos:
   \<open>A \<and> A' \<Longrightarrow> (c \<and> A) \<or> (\<not>c \<and> A')\<close>
   \<open>A \<and> A' \<Longrightarrow> (\<not>c \<and> A) \<or> (c \<and> A')\<close>
  by blast+


lemma verit_la_generic:
  \<open>(a::int) \<le> x \<or> a = x \<or> a \<ge> x\<close>
  by linarith

lemma verit_bfun_elim:
  \<open>(if b then P True else P False) = P b\<close>
  \<open>(\<forall>b. P' b) = (P' False \<and> P' True)\<close>
  \<open>(\<exists>b. P' b) = (P' False \<or> P' True)\<close>
  by (cases b) (auto simp: all_bool_eq ex_bool_eq)

lemma verit_eq_true_simplify:
  \<open>(P = True) \<equiv> P\<close>
  by auto

lemma verit_and_neg:
  \<open>(a \<Longrightarrow> \<not>b \<or> A) \<Longrightarrow> \<not>(a \<and> b) \<or> A\<close>
  \<open>(a \<Longrightarrow> A) \<Longrightarrow> \<not>a \<or> A\<close>
  \<open>(\<not>a \<Longrightarrow> A) \<Longrightarrow> a \<or> A\<close>
  by blast+

lemma verit_forall_inst:
  \<open>A \<longleftrightarrow> B \<Longrightarrow> \<not>A \<or> B\<close>
  \<open>\<not>A \<longleftrightarrow> B \<Longrightarrow> A \<or> B\<close>
  \<open>A \<longleftrightarrow> B \<Longrightarrow> \<not>B \<or> A\<close>
  \<open>A \<longleftrightarrow> \<not>B \<Longrightarrow> B \<or> A\<close>
  \<open>A \<longrightarrow> B \<Longrightarrow> \<not>A \<or> B\<close>
  \<open>\<not>A \<longrightarrow> B \<Longrightarrow> A \<or> B\<close>
  by blast+

lemma verit_eq_transitive:
  \<open>A = B \<Longrightarrow> B = C \<Longrightarrow> A = C\<close>
  \<open>A = B \<Longrightarrow> C = B \<Longrightarrow> A = C\<close>
  \<open>B = A \<Longrightarrow> B = C \<Longrightarrow> A = C\<close>
  \<open>B = A \<Longrightarrow> C = B \<Longrightarrow> A = C\<close>
  by auto

lemma verit_bool_simplify:
  \<open>\<not>(P \<longrightarrow> Q) \<longleftrightarrow> P \<and> \<not>Q\<close>
  \<open>\<not>(P \<or> Q) \<longleftrightarrow> \<not>P \<and> \<not>Q\<close>
  \<open>\<not>(P \<and> Q) \<longleftrightarrow> \<not>P \<or> \<not>Q\<close>
  \<open>(P \<longrightarrow> (Q \<longrightarrow> R)) \<longleftrightarrow> ((P \<and> Q) \<longrightarrow> R)\<close>
  \<open>((P \<longrightarrow> Q) \<longrightarrow> Q) \<longleftrightarrow> P \<or> Q\<close>
  \<open>(Q \<longleftrightarrow> (P \<or> Q)) \<longleftrightarrow> (P \<longrightarrow> Q)\<close> \<comment> \<open>This rule was inverted\<close>
  \<open>P \<and> (P \<longrightarrow> Q) \<longleftrightarrow> P \<and> Q\<close>
  \<open>(P \<longrightarrow> Q) \<and> P \<longleftrightarrow> P \<and> Q\<close>
 (* \<comment>\<open>Additional rules:\<close>
  *  \<open>((P \<longrightarrow> Q) \<longrightarrow> P) \<longleftrightarrow> P\<close>
  *  \<open>((P \<longrightarrow> Q) \<longrightarrow> Q) \<longleftrightarrow> P \<or> Q\<close>
  *  \<open>(P \<longrightarrow> Q) \<or> P\<close> *)
  unfolding not_imp imp_conjL
  by auto

text \<open>We need the last equation for \<^term>\<open>\<not>(\<forall>a b. \<not>P a b)\<close>\<close>
lemma verit_connective_def: \<comment> \<open>the definition of XOR is missing
  as the operator is not generated by Isabelle\<close>
  \<open>(A = B) \<longleftrightarrow> ((A \<longrightarrow> B) \<and> (B \<longrightarrow> A))\<close>
  \<open>(If A B C) = ((A \<longrightarrow> B) \<and> (\<not>A \<longrightarrow> C))\<close>
  \<open>(\<exists>x. P x) \<longleftrightarrow> \<not>(\<forall>x. \<not>P x)\<close>
  \<open>\<not>(\<exists>x. P x) \<longleftrightarrow> (\<forall>x. \<not>P x)\<close>
  by auto

lemma verit_ite_simplify:
  \<open>(If True B C) = B\<close>
  \<open>(If False B C) = C\<close>
  \<open>(If A' B B) = B\<close>
  \<open>(If (\<not>A') B C) = (If A' C B)\<close>
  \<open>(If c (If c A B) C) = (If c A C)\<close>
  \<open>(If c C (If c A B)) = (If c C B)\<close>
  \<open>(If A' True False) = A'\<close>
  \<open>(If A' False True) \<longleftrightarrow> \<not>A'\<close>
  \<open>(If A' True B') \<longleftrightarrow> A'\<or>B'\<close>
  \<open>(If A' B' False) \<longleftrightarrow> A'\<and>B'\<close>
  \<open>(If A' False B') \<longleftrightarrow> \<not>A'\<and>B'\<close>
  \<open>(If A' B' True) \<longleftrightarrow> \<not>A'\<or>B'\<close>
  \<open>x \<and> True \<longleftrightarrow> x\<close>
  \<open>x \<or> False \<longleftrightarrow> x\<close>
  for B C :: 'a and A' B' C' :: bool
  by auto

lemma verit_and_simplify1:
  \<open>True \<and> b \<longleftrightarrow> b\<close> \<open>b \<and> True \<longleftrightarrow> b\<close>
  \<open>False \<and> b \<longleftrightarrow> False\<close> \<open>b \<and> False \<longleftrightarrow> False\<close>
  \<open>(c \<and> \<not>c) \<longleftrightarrow> False\<close> \<open>(\<not>c \<and> c) \<longleftrightarrow> False\<close>
  \<open>\<not>\<not>a = a\<close>
  by auto

lemmas verit_and_simplify = conj_ac de_Morgan_conj disj_not1


lemma verit_or_simplify_1:
  \<open>False \<or> b \<longleftrightarrow> b\<close> \<open>b \<or> False \<longleftrightarrow> b\<close>
  \<open>b \<or> \<not>b\<close>
  \<open>\<not>b \<or> b\<close>
  by auto

lemmas verit_or_simplify = disj_ac

lemma verit_not_simplify:
  \<open>\<not> \<not>b \<longleftrightarrow> b\<close> \<open>\<not>True \<longleftrightarrow> False\<close> \<open>\<not>False \<longleftrightarrow> True\<close>
  by auto


lemma verit_implies_simplify:
  \<open>(\<not>a \<longrightarrow> \<not>b) \<longleftrightarrow> (b \<longrightarrow> a)\<close>
  \<open>(False \<longrightarrow> a) \<longleftrightarrow> True\<close>
  \<open>(a \<longrightarrow> True) \<longleftrightarrow> True\<close>
  \<open>(True \<longrightarrow> a) \<longleftrightarrow> a\<close>
  \<open>(a \<longrightarrow> False) \<longleftrightarrow> \<not>a\<close>
  \<open>(a \<longrightarrow> a) \<longleftrightarrow> True\<close>
  \<open>(\<not>a \<longrightarrow> a) \<longleftrightarrow> a\<close>
  \<open>(a \<longrightarrow> \<not>a) \<longleftrightarrow> \<not>a\<close>
  \<open>((a \<longrightarrow> b) \<longrightarrow> b) \<longleftrightarrow> a \<or> b\<close>
  by auto

lemma verit_equiv_simplify:
  \<open>((\<not>a) = (\<not>b)) \<longleftrightarrow> (a = b)\<close>
  \<open>(a = a) \<longleftrightarrow> True\<close>
  \<open>(a = (\<not>a)) \<longleftrightarrow> False\<close>
  \<open>((\<not>a) = a) \<longleftrightarrow> False\<close>
  \<open>(True = a) \<longleftrightarrow> a\<close>
  \<open>(a = True) \<longleftrightarrow> a\<close>
  \<open>(False = a) \<longleftrightarrow> \<not>a\<close>
  \<open>(a = False) \<longleftrightarrow> \<not>a\<close>
  \<open>\<not>\<not>a \<longleftrightarrow> a\<close>
  \<open>(\<not> False) = True\<close>
  for a b :: bool
  by auto

lemmas verit_eq_simplify =
  semiring_char_0_class.eq_numeral_simps eq_refl zero_neq_one num.simps
  neg_equal_zero equal_neg_zero one_neq_zero neg_equal_iff_equal

lemma verit_minus_simplify:
  \<open>(a :: 'a :: cancel_comm_monoid_add) - a = 0\<close>
  \<open>(a :: 'a :: cancel_comm_monoid_add) - 0 = a\<close>
  \<open>0 - (b :: 'b :: {group_add}) = -b\<close>
  \<open>- (- (b :: 'b :: group_add)) = b\<close>
  by auto

lemma verit_sum_simplify:
  \<open>(a :: 'a :: cancel_comm_monoid_add) + 0 = a\<close>
  by auto

lemmas verit_prod_simplify =
(* already included:
   mult_zero_class.mult_zero_right
   mult_zero_class.mult_zero_left *)
   mult_1
   mult_1_right

lemma verit_comp_simplify1:
  \<open>(a :: 'a ::order) < a \<longleftrightarrow> False\<close>
  \<open>a \<le> a\<close>
  \<open>\<not>(b' \<le> a') \<longleftrightarrow> (a' :: 'b :: linorder) < b'\<close>
  by auto

lemmas verit_comp_simplify =
  verit_comp_simplify1
  le_numeral_simps
  le_num_simps
  less_numeral_simps
  less_num_simps
  zero_less_one
  zero_le_one
  less_neg_numeral_simps

lemma verit_la_disequality:
  \<open>(a :: 'a ::linorder) = b \<or> \<not>a \<le> b \<or> \<not>b \<le> a\<close>
  by auto

context
begin

text \<open>For the reconstruction, we need to keep the order of the arguments.\<close>

named_theorems smt_arith_multiplication \<open>Theorems to reconstruct arithmetic theorems.\<close>

named_theorems smt_arith_combine \<open>Theorems to reconstruct arithmetic theorems.\<close>

named_theorems smt_arith_simplify \<open>Theorems to combine theorems in the LA procedure\<close>

lemmas [smt_arith_simplify] =
    div_add dvd_numeral_simp divmod_steps less_num_simps le_num_simps if_True if_False divmod_cancel
    dvd_mult dvd_mult2 less_irrefl prod.case numeral_plus_one divmod_step_def order.refl le_zero_eq
    le_numeral_simps less_numeral_simps mult.right_neutral simp_thms divides_aux_eq
    mult_nonneg_nonneg dvd_imp_mod_0 dvd_add zero_less_one mod_mult_self4 numeral_mod_numeral
    divmod_trivial prod.sel mult.left_neutral div_pos_pos_trivial arith_simps div_add div_mult_self1
    add_le_cancel_left add_le_same_cancel2 not_one_le_zero le_numeral_simps add_le_same_cancel1
    zero_neq_one zero_le_one le_num_simps add_Suc mod_div_trivial nat.distinct mult_minus_right
    add.inverse_inverse distrib_left_numeral mult_num_simps numeral_times_numeral add_num_simps
    divmod_steps rel_simps if_True if_False numeral_div_numeral divmod_cancel prod.case
    add_num_simps one_plus_numeral fst_conv arith_simps sub_num_simps dbl_inc_simps
    dbl_simps mult_1 add_le_cancel_right left_diff_distrib_numeral add_uminus_conv_diff zero_neq_one
    zero_le_one One_nat_def add_Suc mod_div_trivial nat.distinct of_int_1 numerals numeral_One
    of_int_numeral add_uminus_conv_diff zle_diff1_eq add_less_same_cancel2 minus_add_distrib
    add_uminus_conv_diff mult.left_neutral semiring_class.distrib_right
    add_diff_cancel_left' add_diff_eq ring_distribs mult_minus_left minus_diff_eq

lemma [smt_arith_simplify]:
  \<open>\<not> (a' :: 'a :: linorder) < b' \<longleftrightarrow> b' \<le> a'\<close>
  \<open>\<not> (a' :: 'a :: linorder) \<le> b' \<longleftrightarrow> b' < a'\<close>
  \<open>(c::int) mod Numeral1 = 0\<close>
  \<open>(a::nat) mod Numeral1 = 0\<close>
  \<open>(c::int) div Numeral1 = c\<close>
  \<open>a div Numeral1 = a\<close>
  \<open>(c::int) mod 1 = 0\<close>
  \<open>a mod 1 = 0\<close>
  \<open>(c::int) div 1 = c\<close>
  \<open>a div 1 = a\<close>
  \<open>\<not>(a' \<noteq> b') \<longleftrightarrow> a' = b'\<close>
  by auto


lemma div_mod_decomp: "A = (A div n) * n + (A mod n)" for A :: nat
  by auto

lemma div_less_mono:
  fixes A B :: nat
  assumes "A < B" "0 < n" and
    mod: "A mod n = 0""B mod n = 0"
  shows "(A div n) < (B div n)"
proof -
  show ?thesis
    using assms(1)
    apply (subst (asm) div_mod_decomp[of "A" n])
    apply (subst (asm) div_mod_decomp[of "B" n])
    unfolding mod
    by (use assms(2,3) in \<open>auto simp: ac_simps\<close>)
qed

lemma verit_le_mono_div:
  fixes A B :: nat
  assumes "A < B" "0 < n"
  shows "(A div n) + (if B mod n = 0 then 1 else 0) \<le> (B div n)"
  by (auto simp: ac_simps Suc_leI assms less_mult_imp_div_less div_le_mono less_imp_le_nat)

lemmas [smt_arith_multiplication] =
  verit_le_mono_div[THEN mult_le_mono1, unfolded add_mult_distrib]
  div_le_mono[THEN mult_le_mono2, unfolded add_mult_distrib]

lemma div_mod_decomp_int: "A = (A div n) * n + (A mod n)" for A :: int
  by auto

lemma zdiv_mono_strict:
  fixes A B :: int
  assumes "A < B" "0 < n" and
    mod: "A mod n = 0""B mod n = 0"
  shows "(A div n) < (B div n)"
proof -
  show ?thesis
    using assms(1)
    apply (subst (asm) div_mod_decomp_int[of A n])
    apply (subst (asm) div_mod_decomp_int[of B n])
    unfolding mod
    by (use assms(2,3) in \<open>auto simp: ac_simps\<close>)
qed

lemma verit_le_mono_div_int:
  \<open>A div n + (if B mod n = 0 then 1 else 0) \<le> B div n\<close>
    if \<open>A < B\<close> \<open>0 < n\<close>
    for A B n :: int
proof -
  from \<open>A < B\<close> \<open>0 < n\<close> have \<open>A div n \<le> B div n\<close>
    by (auto intro: zdiv_mono1)
  show ?thesis
  proof (cases \<open>n dvd B\<close>)
    case False
    with \<open>A div n \<le> B div n\<close> show ?thesis
      by auto
  next
    case True
    then obtain C where \<open>B = n * C\<close> ..
    then have \<open>B div n = C\<close>
      using \<open>0 < n\<close> by simp
    from \<open>0 < n\<close> have \<open>A mod n \<ge> 0\<close>
      by simp
    have \<open>A div n < C\<close>
    proof (rule ccontr)
      assume \<open>\<not> A div n < C\<close>
      then have \<open>C \<le> A div n\<close>
        by simp
      with \<open>B div n = C\<close> \<open>A div n \<le> B div n\<close>
      have \<open>A div n = C\<close>
        by simp
      moreover from \<open>A < B\<close> have \<open>n * (A div n) + A mod n < B\<close>
        by simp
      ultimately have \<open>n * C + A mod n < n * C\<close>
        using \<open>B = n * C\<close> by simp
      moreover have \<open>A mod n \<ge> 0\<close>
        using \<open>0 < n\<close> by simp
      ultimately show False
        by simp
    qed
    with \<open>n dvd B\<close> \<open>B div n = C\<close> show ?thesis
      by simp
  qed
qed

lemma verit_less_mono_div_int2:
  fixes A B :: int
  assumes "A \<le> B" "0 < -n"
  shows "(A div n) \<ge> (B div n)"
  using assms(1) assms(2) zdiv_mono1_neg by auto

lemmas [smt_arith_multiplication] =
  verit_le_mono_div_int[THEN mult_left_mono, unfolded int_distrib]
  zdiv_mono1[THEN mult_left_mono, unfolded int_distrib]

lemmas [smt_arith_multiplication] =
  arg_cong[of _ _ \<open>\<lambda>a :: nat. a div n * p\<close> for n p :: nat, THEN sym]
  arg_cong[of _ _ \<open>\<lambda>a :: int. a div n * p\<close> for n p :: int, THEN sym]

lemma [smt_arith_combine]:
  "a < b \<Longrightarrow> c < d \<Longrightarrow> a + c + 2 \<le> b + d"
  "a < b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c + 1 \<le> b + d"
  "a \<le> b \<Longrightarrow> c < d \<Longrightarrow> a + c + 1 \<le> b + d" for a b c :: int
  by auto

lemma [smt_arith_combine]:
  "a < b \<Longrightarrow> c < d \<Longrightarrow> a + c + 2 \<le> b + d"
  "a < b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c + 1 \<le> b + d"
  "a \<le> b \<Longrightarrow> c < d \<Longrightarrow> a + c + 1 \<le> b + d" for a b c :: nat
  by auto

lemmas [smt_arith_combine] =
  add_strict_mono
  add_less_le_mono
  add_mono
  add_le_less_mono

lemma [smt_arith_combine]:
  \<open>m < n \<Longrightarrow> c = d \<Longrightarrow> m + c < n + d\<close>
  \<open>m \<le> n \<Longrightarrow> c = d \<Longrightarrow> m + c \<le> n + d\<close>
  \<open>c = d \<Longrightarrow> m < n \<Longrightarrow> m + c < n + d\<close>
  \<open>c = d \<Longrightarrow> m \<le> n \<Longrightarrow> m + c \<le> n + d\<close>
  for m :: \<open>'a :: ordered_cancel_ab_semigroup_add\<close>
  by (auto intro: ordered_cancel_ab_semigroup_add_class.add_strict_right_mono
    ordered_ab_semigroup_add_class.add_right_mono)

lemma verit_negate_coefficient:
  \<open>a \<le> (b :: 'a :: {ordered_ab_group_add}) \<Longrightarrow> -a \<ge> -b\<close>
  \<open>a < b \<Longrightarrow> -a > -b\<close>
  \<open>a = b \<Longrightarrow> -a = -b\<close>
  by auto

end

lemma verit_ite_intro:
  \<open>(if a then P (if a then a' else b') else Q) \<longleftrightarrow> (if a then P a' else Q)\<close>
  \<open>(if a then P' else Q' (if a then a' else b')) \<longleftrightarrow> (if a then P' else Q' b')\<close>
  \<open>A = f (if a then R else S) \<longleftrightarrow> (if a then A = f R else A = f S)\<close>
  by auto

lemma verit_ite_if_cong:
  fixes x y :: bool
  assumes "b=c"
    and "c \<equiv> True \<Longrightarrow> x = u"
    and "c \<equiv> False \<Longrightarrow> y = v"
  shows "(if b then x else y) \<equiv> (if c then u else v)"
proof -
  have H: "(if b then x else y) = (if c then u else v)"
    using assms by (auto split: if_splits)

  show "(if b then x else y) \<equiv> (if c then u else v)"
    by (subst H) auto
qed


(*Bitvector*)
named_theorems arith_simp_cvc5 \<open>Might be temp and integrated into smt_arith_simplify \<close>

lemmas [arith_simp_cvc5] = Groups.monoid_mult_class.mult_1_right Nat.mult_Suc_right
                     Nat.mult_0_right Nat.add_Suc_right Groups.monoid_add_class.add.right_neutral
                     Num.numeral_2_eq_2 Nat.One_nat_def Num.numeral_2_eq_2 Nat.One_nat_def
                     Nat.Suc_less_eq Nat.zero_less_Suc minus_nat.diff_0 Nat.diff_Suc_Suc Nat.le0

named_theorems arith_poly_norm \<open>Theorems normalize polynoms.\<close>
lemmas [arith_poly_norm] = ac_simps realrel_def of_int_mult of_int_add

named_theorems word_var_rbl_list \<open>Theorems to reconstruct bitblasting of a variable.\<close>

named_theorems bv_reconstruction_const \<open>Theorems to reconstruct bitblasting of a constant.\<close>
named_theorems bv_reconstruction_const_test \<open>Theorems to reconstruct bitblasting of a constant.\<close>

named_theorems word_and_rbl_bvand \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_or_rbl_bvor \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_xor_rbl_bvxor \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_notxor_rbl_bvxnor \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_not_rbl_bvnot \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>

named_theorems word_plus_rbl_bvadd \<open>Theorems to reconstruct bitblasting of a bvadd term.\<close>
named_theorems word_plus_rbl_bvadd_fun \<open>Theorems to reconstruct bitblasting of a bvadd term.\<close>
named_theorems word_plus_rbl_bvadd_fun2 \<open>Theorems to reconstruct bitblasting of a bvadd term.\<close>

named_theorems word_minus_rbl_bvneg \<open>Theorems to reconstruct bitblasting of a bvneg term.\<close>
named_theorems word_minus_rbl_bvneg_fun \<open>Theorems to reconstruct bitblasting of a bvneg term.\<close> (*temp?*)

named_theorems word_mult_rbl_bvmult \<open>Theorems to reconstruct bitblasting of a bvmult term.\<close>
named_theorems word_mult_rbl_bvmult_fun \<open>Theorems to reconstruct bitblasting of a bvmult term.\<close>

named_theorems rbl_bvult_fun \<open>Theorems to reconstruct bitblasting of a bvult term.\<close>
named_theorems word_less_rbl_bvult \<open>Theorems to reconstruct bitblasting of a bvult term.\<close>

named_theorems rbl_bvequal_fun \<open>Theorems to reconstruct bitblasting of a bvequal term.\<close>
named_theorems word_equal_rbl_bvequal \<open>Theorems to reconstruct bitblasting of a bvequal term.\<close>

named_theorems rbl_extract_fun \<open>Theorems to reconstruct bitblasting of a extract term.\<close>
named_theorems rbl_extract \<open>Theorems to reconstruct bitblasting of a extract term.\<close>

named_theorems rbl_concat \<open>Theorems to reconstruct bitblasting of a contract term.\<close>

named_theorems bv_reconstruction_length \<open>Theorems evaluate LENGTH('a) for a concrete length.\<close>
named_theorems bv_reconstruction_lists \<open>Theorems to reconstruct bitvector theorems concerning lists.\<close>
named_theorems bv_reconstruction_list_funs \<open>Theorems to reconstruct bitvector theorems concerning list function, e.g. take.\<close>

named_theorems rbl_xor_temp \<open>xor_def.\<close>

named_theorems all_simplify_temp \<open>Theorems to reconstruct bitvector theorems concerning list function, e.g. take.\<close>

subsection \<open>Setup\<close>

ML_file \<open>Tools/SMT/smt_util.ML\<close>
ML_file \<open>Tools/SMT/smt_failure.ML\<close>
ML_file \<open>Tools/SMT/smt_config.ML\<close>
ML_file \<open>Tools/SMT/smt_builtin.ML\<close>
ML_file \<open>Tools/SMT/smt_datatypes.ML\<close>
ML_file \<open>Tools/SMT/smt_normalize.ML\<close>
ML_file \<open>Tools/SMT/smt_translate.ML\<close>
ML_file \<open>Tools/SMT/smtlib.ML\<close>
ML_file \<open>Tools/SMT/smtlib_interface.ML\<close>
ML_file \<open>Tools/SMT/SMT_string.ML\<close>
ML_file \<open>Tools/SMT/smtlib_proof.ML\<close>
ML_file \<open>Tools/SMT/smtlib_isar.ML\<close>
ML_file \<open>Tools/SMT/z3_proof.ML\<close>
ML_file \<open>Tools/SMT/z3_isar.ML\<close>
ML_file \<open>Tools/SMT/smt_solver.ML\<close>
ML_file \<open>Tools/SMT/cvc_interface.ML\<close>
ML_file \<open>Tools/SMT/lethe_proof.ML\<close>
ML_file \<open>Tools/SMT/lethe_isar.ML\<close>
ML_file \<open>Tools/SMT/lethe_proof_parse.ML\<close>
ML_file \<open>Tools/SMT/cvc_proof_parse.ML\<close>
ML_file \<open>Tools/SMT/conj_disj_perm.ML\<close>
ML_file \<open>Tools/SMT/smt_replay_methods.ML\<close>
ML_file \<open>Tools/SMT/smt_replay.ML\<close>
ML_file \<open>Tools/SMT/smt_replay_arith.ML\<close>
ML_file \<open>Tools/SMT/z3_interface.ML\<close>
ML_file \<open>Tools/SMT/z3_replay_rules.ML\<close>
ML_file \<open>Tools/SMT/z3_replay_methods.ML\<close>
ML_file \<open>Tools/SMT/z3_replay.ML\<close>
ML_file \<open>Tools/SMT/lethe_replay_methods.ML\<close>
ML_file \<open>Tools/SMT/verit_replay_methods.ML\<close>
ML_file \<open>Tools/SMT/cvc4_replay_methods.ML\<close>
ML_file \<open>Tools/SMT/verit_strategies.ML\<close>
ML_file \<open>Tools/SMT/verit_replay.ML\<close>
ML_file \<open>Tools/SMT/cvc4_replay.ML\<close>
ML_file \<open>Tools/SMT/smt_systems.ML\<close>



subsection \<open>Configuration\<close>

text \<open>
The current configuration can be printed by the command
\<open>smt_status\<close>, which shows the values of most options.
\<close>


subsection \<open>General configuration options\<close>

text \<open>
The option \<open>smt_solver\<close> can be used to change the target SMT
solver. The possible values can be obtained from the \<open>smt_status\<close>
command.
\<close>

declare [[smt_solver = z3]]

text \<open>
Since SMT solvers are potentially nonterminating, there is a timeout
(given in seconds) to restrict their runtime.
\<close>

declare [[smt_timeout = 0]]

text \<open>
SMT solvers apply randomized heuristics. In case a problem is not
solvable by an SMT solver, changing the following option might help.
\<close>

declare [[smt_random_seed = 1]]

text \<open>
In general, the binding to SMT solvers runs as an oracle, i.e, the SMT
solvers are fully trusted without additional checks. The following
option can cause the SMT solver to run in proof-producing mode, giving
a checkable certificate. This is currently only implemented for Z3.
\<close>

declare [[smt_oracle = false]]

text \<open>
CVC5 is able to generate Lethe. Support for it is currently experimental
and hence not activate by default (in particular CVC5 is not yet bundled
with Isabelle).
\<close>

declare [[smt_cvc_lethe = false]]

text \<open>
Each SMT solver provides several commandline options to tweak its

Each SMT solver provides several commandline options to tweak its
behaviour. They can be passed to the solver by setting the following
options.
\<close>


declare [[cvc4_options = "--full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --multi-trigger-linear"]]
declare [[cvc5_options = ""]]
declare [[verit_options = ""]]
declare [[z3_options = ""]]

text \<open>
The SMT method provides an inference mechanism to detect simple triggers
in quantified formulas, which might increase the number of problems
solvable by SMT solvers (note: triggers guide quantifier instantiations
in the SMT solver). To turn it on, set the following option.
\<close>

declare [[smt_infer_triggers = false]]

text \<open>
Enable the following option to use built-in support for datatypes,
codatatypes, and records in CVC4 and cvc5. Currently, this is implemented
only in oracle mode.
\<close>

declare [[cvc_extensions = false]]

text \<open>
Enable the following option to use built-in support for div/mod, datatypes,
and records in Z3. Currently, this is implemented only in oracle mode.
\<close>

declare [[z3_extensions = false]]


subsection \<open>Certificates\<close>

text \<open>
By setting the option \<open>smt_certificates\<close> to the name of a file,
all following applications of an SMT solver a cached in that file.
Any further application of the same SMT solver (using the very same
configuration) re-uses the cached certificate instead of invoking the
solver. An empty string disables caching certificates.

The filename should be given as an explicit path. It is good
practice to use the name of the current theory (with ending
\<open>.certs\<close> instead of \<open>.thy\<close>) as the certificates file.
Certificate files should be used at most once in a certain theory context,
to avoid race conditions with other concurrent accesses.
\<close>

declare [[smt_certificates = ""]]

text \<open>
The option \<open>smt_read_only_certificates\<close> controls whether only
stored certificates should be used or invocation of an SMT solver
is allowed. When set to \<open>true\<close>, no SMT solver will ever be
invoked and only the existing certificates found in the configured
cache are used;  when set to \<open>false\<close> and there is no cached
certificate for some proposition, then the configured SMT solver is
invoked.
\<close>

declare [[smt_read_only_certificates = false]]


subsection \<open>Tracing\<close>

text \<open>
The SMT method, when applied, traces important information. To
make it entirely silent, set the following option to \<open>false\<close>.
\<close>

declare [[smt_verbose = true]]

text \<open>
For tracing the generated problem file given to the SMT solver as
well as the returned result of the solver, the option
\<open>smt_trace\<close> should be set to \<open>true\<close>.
\<close>

declare [[smt_trace = false]]


subsection \<open>Schematic rules for Z3 proof reconstruction\<close>

text \<open>
Several prof rules of Z3 are not very well documented. There are two
lemma groups which can turn failing Z3 proof reconstruction attempts
into succeeding ones: the facts in \<open>z3_rule\<close> are tried prior to
any implemented reconstruction procedure for all uncertain Z3 proof
rules;  the facts in \<open>z3_simp\<close> are only fed to invocations of
the simplifier when reconstructing theory-specific proof steps.
\<close>

lemmas [z3_rule] =
  refl eq_commute conj_commute disj_commute simp_thms nnf_simps
  ring_distribs field_simps times_divide_eq_right times_divide_eq_left
  if_True if_False not_not
  NO_MATCH_def

lemma [z3_rule]:
  "(P \<and> Q) = (\<not> (\<not> P \<or> \<not> Q))"
  "(P \<and> Q) = (\<not> (\<not> Q \<or> \<not> P))"
  "(\<not> P \<and> Q) = (\<not> (P \<or> \<not> Q))"
  "(\<not> P \<and> Q) = (\<not> (\<not> Q \<or> P))"
  "(P \<and> \<not> Q) = (\<not> (\<not> P \<or> Q))"
  "(P \<and> \<not> Q) = (\<not> (Q \<or> \<not> P))"
  "(\<not> P \<and> \<not> Q) = (\<not> (P \<or> Q))"
  "(\<not> P \<and> \<not> Q) = (\<not> (Q \<or> P))"
  by auto

lemma [z3_rule]:
  "(P \<longrightarrow> Q) = (Q \<or> \<not> P)"
  "(\<not> P \<longrightarrow> Q) = (P \<or> Q)"
  "(\<not> P \<longrightarrow> Q) = (Q \<or> P)"
  "(True \<longrightarrow> P) = P"
  "(P \<longrightarrow> True) = True"
  "(False \<longrightarrow> P) = True"
  "(P \<longrightarrow> P) = True"
  "(\<not> (A \<longleftrightarrow> \<not> B)) \<longleftrightarrow> (A \<longleftrightarrow> B)"
  by auto

lemma [z3_rule]:
  "((P = Q) \<longrightarrow> R) = (R \<or> (Q = (\<not> P)))"
  by auto

lemma [z3_rule]:
  "(\<not> True) = False"
  "(\<not> False) = True"
  "(x = x) = True"
  "(P = True) = P"
  "(True = P) = P"
  "(P = False) = (\<not> P)"
  "(False = P) = (\<not> P)"
  "((\<not> P) = P) = False"
  "(P = (\<not> P)) = False"
  "((\<not> P) = (\<not> Q)) = (P = Q)"
  "\<not> (P = (\<not> Q)) = (P = Q)"
  "\<not> ((\<not> P) = Q) = (P = Q)"
  "(P \<noteq> Q) = (Q = (\<not> P))"
  "(P = Q) = ((\<not> P \<or> Q) \<and> (P \<or> \<not> Q))"
  "(P \<noteq> Q) = ((\<not> P \<or> \<not> Q) \<and> (P \<or> Q))"
  by auto

lemma [z3_rule]:
  "(if P then P else \<not> P) = True"
  "(if \<not> P then \<not> P else P) = True"
  "(if P then True else False) = P"
  "(if P then False else True) = (\<not> P)"
  "(if P then Q else True) = ((\<not> P) \<or> Q)"
  "(if P then Q else True) = (Q \<or> (\<not> P))"
  "(if P then Q else \<not> Q) = (P = Q)"
  "(if P then Q else \<not> Q) = (Q = P)"
  "(if P then \<not> Q else Q) = (P = (\<not> Q))"
  "(if P then \<not> Q else Q) = ((\<not> Q) = P)"
  "(if \<not> P then x else y) = (if P then y else x)"
  "(if P then (if Q then x else y) else x) = (if P \<and> (\<not> Q) then y else x)"
  "(if P then (if Q then x else y) else x) = (if (\<not> Q) \<and> P then y else x)"
  "(if P then (if Q then x else y) else y) = (if P \<and> Q then x else y)"
  "(if P then (if Q then x else y) else y) = (if Q \<and> P then x else y)"
  "(if P then x else if P then y else z) = (if P then x else z)"
  "(if P then x else if Q then x else y) = (if P \<or> Q then x else y)"
  "(if P then x else if Q then x else y) = (if Q \<or> P then x else y)"
  "(if P then x = y else x = z) = (x = (if P then y else z))"
  "(if P then x = y else y = z) = (y = (if P then x else z))"
  "(if P then x = y else z = y) = (y = (if P then x else z))"
  by auto

lemma [z3_rule]:
  "0 + (x::int) = x"
  "x + 0 = x"
  "x + x = 2 * x"
  "0 * x = 0"
  "1 * x = x"
  "x + y = y + x"
  by auto

lemma [z3_rule]:  (* for def-axiom *)
  "P = Q \<or> P \<or> Q"
  "P = Q \<or> \<not> P \<or> \<not> Q"
  "(\<not> P) = Q \<or> \<not> P \<or> Q"
  "(\<not> P) = Q \<or> P \<or> \<not> Q"
  "P = (\<not> Q) \<or> \<not> P \<or> Q"
  "P = (\<not> Q) \<or> P \<or> \<not> Q"
  "P \<noteq> Q \<or> P \<or> \<not> Q"
  "P \<noteq> Q \<or> \<not> P \<or> Q"
  "P \<noteq> (\<not> Q) \<or> P \<or> Q"
  "(\<not> P) \<noteq> Q \<or> P \<or> Q"
  "P \<or> Q \<or> P \<noteq> (\<not> Q)"
  "P \<or> Q \<or> (\<not> P) \<noteq> Q"
  "P \<or> \<not> Q \<or> P \<noteq> Q"
  "\<not> P \<or> Q \<or> P \<noteq> Q"
  "P \<or> y = (if P then x else y)"
  "P \<or> (if P then x else y) = y"
  "\<not> P \<or> x = (if P then x else y)"
  "\<not> P \<or> (if P then x else y) = x"
  "P \<or> R \<or> \<not> (if P then Q else R)"
  "\<not> P \<or> Q \<or> \<not> (if P then Q else R)"
  "\<not> (if P then Q else R) \<or> \<not> P \<or> Q"
  "\<not> (if P then Q else R) \<or> P \<or> R"
  "(if P then Q else R) \<or> \<not> P \<or> \<not> Q"
  "(if P then Q else R) \<or> P \<or> \<not> R"
  "(if P then \<not> Q else R) \<or> \<not> P \<or> Q"
  "(if P then Q else \<not> R) \<or> P \<or> R"
  by auto

hide_type (open) symb_list pattern
hide_const (open) Symb_Nil Symb_Cons trigger pat nopat fun_app z3div z3mod


subsection \<open>Setup for SMT\<close>

ML_file \<open>Tools/SMT/smt_real.ML\<close>
ML_file \<open>Tools/SMT/SMT_real.ML\<close>

lemma [z3_rule]:
  "0 + x = x"
  "x + 0 = x"
  "0 * x = 0"
  "1 * x = x"
  "-x = -1 * x"
  "x + y = y + x"
  for x y :: real
  by auto

lemma [smt_arith_multiplication]:
  fixes A B :: real and p n :: real
  assumes "A \<le> B" "0 < n" "p > 0"
  shows "(A / n) * p \<le> (B / n) * p"
  using assms by (auto simp: field_simps)

lemma [smt_arith_multiplication]:
  fixes A B :: real and p n :: real
  assumes "A < B" "0 < n" "p > 0"
  shows "(A / n) * p < (B / n) * p"
  using assms by (auto simp: field_simps)

lemma [smt_arith_multiplication]:
  fixes A B :: real and p n :: int
  assumes "A \<le> B" "0 < n" "p > 0"
  shows "(A / n) * p \<le> (B / n) * p"
  using assms by (auto simp: field_simps)

lemma [smt_arith_multiplication]:
  fixes A B :: real and p n :: int
  assumes "A < B" "0 < n" "p > 0"
  shows "(A / n) * p < (B / n) * p"
  using assms by (auto simp: field_simps)

lemmas [smt_arith_multiplication] =
  verit_le_mono_div[THEN mult_left_mono, unfolded int_distrib, of _ _ \<open>nat (floor (_ :: real))\<close>  \<open>nat (floor (_ :: real))\<close>]
  div_le_mono[THEN mult_left_mono, unfolded int_distrib, of _ _ \<open>nat (floor (_ :: real))\<close>  \<open>nat (floor (_ :: real))\<close>]
  verit_le_mono_div_int[THEN mult_left_mono, unfolded int_distrib, of _ _ \<open>floor (_ :: real)\<close>  \<open>floor (_ :: real)\<close>]
  zdiv_mono1[THEN mult_left_mono, unfolded int_distrib, of _ _ \<open>floor (_ :: real)\<close>  \<open>floor (_ :: real)\<close>]
  arg_cong[of _ _ \<open>\<lambda>a :: real. a / real (n::nat) * real (p::nat)\<close> for n p :: nat, THEN sym]
  arg_cong[of _ _ \<open>\<lambda>a :: real. a / real_of_int n * real_of_int p\<close> for n p :: int, THEN sym]
  arg_cong[of _ _ \<open>\<lambda>a :: real. a / n * p\<close> for n p :: real, THEN sym]

lemmas [smt_arith_simplify] =
   floor_one floor_numeral div_by_1 times_divide_eq_right
   nonzero_mult_div_cancel_left division_ring_divide_zero div_0
  divide_minus_left zero_less_divide_iff



subsection \<open>Tool support\<close>

context
begin
qualified definition smt_extract where
  \<open>smt_extract j i w = slice i (take_bit j w)\<close>
end

ML_file \<open>~~/src/HOL/Library/Tools/smt_word.ML\<close> (*TODO: Mathias*)

ML \<open>
local

  val nat_as_int_bv = Attrib.setup_config_bool \<^binding>\<open>smt_nat_as_int_bv\<close> (K false)
  val simple_nat_ops = [
    @{const HOL.eq (nat)}, @{const less (nat)}, @{const less_eq (nat)},
    \<^const>\<open>Suc\<close>, @{const plus (nat)}, @{const minus (nat)}]

  val nat_consts = simple_nat_ops @
    [@{const numeral (nat)}, @{const zero_class.zero (nat)}, @{const one_class.one (nat)}] @
    [@{const times (nat)}, @{const divide (nat)}, @{const modulo (nat)}] @
    [@{term \<open>unsigned :: 'a :: len word \<Rightarrow> nat\<close>}, @{const of_nat (nat)} ] @
    [@{term \<open>unat :: 'a :: len word \<Rightarrow> nat\<close>}]

  fun is_nat_const x = if member (Term.aconv_untyped) nat_consts x then (@{print} x; true) else false
  val bv_thms = @{lemma "int (unat v) = uint v"
 by simp_all} |> single
  val nat_int_thm = map (Thm.symmetric o mk_meta_eq) (bv_thms @ @{thms nat_int})
|> @{print}
  val nat_int_comp_thms = map mk_meta_eq (@{thms nat_int_comparison})
  val int_ops_thms = map mk_meta_eq @{thms int_ops}
  val int_if_thm = mk_meta_eq @{thm int_if}

  fun if_conv cv1 cv2 = Conv.combination_conv (Conv.combination_conv (Conv.arg_conv cv1) cv2) cv2

  fun int_ops_conv cv ctxt ct =
    (case Thm.term_of ct of
      @{const of_nat (int)} $ (Const (\<^const_name>\<open>If\<close>, _) $ _ $ _ $ _) =>
        Conv.rewr_conv int_if_thm then_conv
        if_conv (cv ctxt) (int_ops_conv cv ctxt)
    | @{const of_nat (int)} $ _ =>
        (Conv.rewrs_conv int_ops_thms then_conv
          Conv.top_sweep_conv (int_ops_conv cv) ctxt) else_conv
        Conv.arg_conv (Conv.sub_conv cv ctxt)
    | _ => Conv.no_conv) ct

  val unfold_nat_let_conv = Conv.rewr_conv @{lemma "Let (n::nat) f \<equiv> f n" by (rule Let_def)}
  val drop_nat_int_conv = Conv.rewrs_conv (map Thm.symmetric nat_int_thm |> @{print})


  fun nat_to_int_conv ctxt ct = (
    Conv.top_conv (K (Conv.try_conv unfold_nat_let_conv)) ctxt then_conv
    (Conv.top_conv nat_conv ctxt else_conv Conv.all_conv) then_conv
    Conv.top_conv (K (Conv.try_conv drop_nat_int_conv)) ctxt) (@{print}ct)
|> tap (@{print} o Thm.cprop_of)

  and nat_conv ctxt ct = (
      (Conv.rewrs_conv (nat_int_thm @ nat_int_comp_thms) then_conv
      Conv.top_conv (int_ops_conv nat_to_int_conv) ctxt)
      else_conv Conv.all_conv) (@{print}ct)
|> tap (@{print} o Thm.cprop_of)

  fun add_int_of_nat vs ct cu (q, cts) =
    (case Thm.term_of ct of
      @{const of_nat(int)} =>
        if Term.exists_subterm (member (op aconv) vs) (Thm.term_of cu) then (true, cts)
        else (q, insert (op aconvc) cu cts)
    | _ => (q, cts))

  fun add_apps f vs ct = 
    (case Thm.term_of ct of
      _ $ _ =>
        let val (cu1, cu2) = Thm.dest_comb ct
        in f vs cu1 cu2 #> add_apps f vs cu1 #> add_apps f vs cu2 end
    | Abs _ =>
        let val (cv, cu) = Thm.dest_abs_global ct
        in add_apps f (Thm.term_of cv :: vs) cu end
    | _ => I)

  val int_thm = @{lemma "(0::int) <= int (n::nat)" by simp}
  val nat_int_thms = @{lemma
    "\<forall>n::nat. (0::int) <= int n"
    "\<forall>n::nat. nat (int n) = n"
    "\<forall>i::int. int (nat i) = (if 0 <= i then i else 0)"
    by simp_all}
  val var = Term.dest_Var (Thm.term_of (funpow 3 Thm.dest_arg (Thm.cprop_of int_thm)))
in

fun nat_as_int_conv ctxt = SMT_Util.if_exists_conv is_nat_const (nat_to_int_conv ctxt)

fun add_int_of_nat_constraints thms =
  let
 val (q, cts) = fold (add_apps add_int_of_nat [] o Thm.cprop_of) thms (false, [])
  in
    if q then (thms, nat_int_thms)
    else (thms, map (fn ct => Thm.instantiate (TVars.empty, Vars.add (var, ct) Vars.empty) int_thm) cts)
  end

  val setup_nat_as_int =
    fold (SMT_Builtin.add_builtin_fun_ext' o Term.dest_Const) simple_nat_ops
  val _ = Theory.setup (Context.theory_map (setup_nat_as_int))
  val _ = SMT_Normalize.add_normalization "nat_as_int_bv" (nat_as_int_bv, nat_as_int_conv, add_int_of_nat_constraints)
   |> Theory.setup o Context.theory_map 
end
\<close>

type_synonym w32 = "32 word"

declare [[show_types=true]]
declare [[cvc4_options = "--proof-format-mode=alethe --produce-proofs --simplification=none --dag-thres=0 --lang=smt2 --full-saturate-quant"]]

declare [[smt_nat_as_int_bv=true,smt_nat_as_int]]

(*
definition bound :: nat where
  [simplified, simp]: "bound = unat (2^11 :: w32)"

definition bseg :: "w32 \<Rightarrow> w32 \<Rightarrow> bool" where
  [simp]: "bseg x s \<longleftrightarrow> unat x < bound \<and> unat x + unat s \<le> bound"

lemma \<open>LENGTH(32) = 32\<close>
  supply [[smt_trace]]
  apply (smt (cvc4))
  oops

ML \<open>@{term \<open>LENGTH(32) = 32\<close>}\<close>
term len_of

declare [[cvc4_options = "--proof-format-mode=alethe --produce-proofs --simplification=none --dag-thres=0 --lang=smt2 --full-saturate-quant"]]

lemma b2:
  assumes
  "bseg x s"
   "i < unat s"
 shows "unat x + i < bound"
  supply [[smt_trace,smt_nat_as_int=true,smt_nat_as_int_bv=true]]
using assms unfolding bound_def bseg_def
  apply (smt (cvc4) )
  using assms by auto

lemma b2:
  fixes a :: nat
  assumes
  "bseg x s"
   "i < unat s" and
   "a < 2"
 shows "unat x + i < bound"
  supply [[smt_trace,smt_nat_as_int=true,smt_nat_as_int_bv=true]]
using assms unfolding bound_def bseg_def
  apply (smt (cvc4) )
  using assms by auto

ML \<open>@{term "unat :: w32 \<Rightarrow> nat"} aconv @{term "unat :: 'a :: len word \<Rightarrow> nat"}\<close>
ML \<open>
SMT_Config.solver_class_of @{context}
\<close>

definition bound :: int where
  [simplified, simp]: "bound = uint (2^11 :: w32)"

definition bseg :: "w32 \<Rightarrow> w32 \<Rightarrow> bool" where
  [simp]: "bseg x s \<longleftrightarrow> uint x < bound \<and> uint x + uint s \<le> bound"

(* bv2nat *)
lemma b2:
  assumes
  "bseg x s"
   "i < uint s"
 shows "uint x + i < bound"
  supply [[smt_trace,smt_nat_as_int=false]]
using assms unfolding bound_def bseg_def
  apply (smt (cvc4) )
  using assms by auto

ML \<open>

open Word_Lib;
let
  fun if_fixed pred m n T ts =
    let val (Us, U) = Term.strip_type T
    in
      if pred (U, Us) then SOME (n, length Us, ts, Term.list_comb o pair (Const (m, T))) else NONE
    end

  fun is_conv [(Type (\<^type_name>\<open>Int.int\<close>, [])), a] = can dest_wordT a
    | is_conv x = (@{print} x; false)

  fun if_fixed_all m = if_fixed (is_conv o (op ::)) m
in
if_fixed_all "string" "t" @{typ "w32 \<Rightarrow> int"} "e"
end
\<close>
*)

ML \<open> 
val x =
SMT_Word.bv_type_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "BitVec", SMTLIB.Num 3], [])

val y =
SMT_Word.bv_term_parser (SMTLIB.Sym "bvneg",  [Free ("x", \<^typ>\<open>32 word\<close>)])

val z =
SMT_Word.bv_term_parser (SMTLIB.Sym "bvneg",  [Free ("x", \<^typ>\<open>'a word\<close>)])


\<close>

ML_file \<open>Tools/SMT/cvc5_dsl_rewrites/parse_rewrites.ML\<close>
ML_file \<open>Tools/SMT/cvc5_dsl_rewrites/rewrites_to_lemma.ML\<close>

ML \<open>
open PARSE_REWRITE
open WRITE_LEMMA

fun print_item string_of (modes, arg) = Toplevel.keep (fn state =>
  Print_Mode.with_modes modes (fn () => writeln (string_of state (hd arg))) ())

fun string_of_rewrite ctxt s
= foldr1 (op^) (List.concat (WRITE_LEMMA.write_lemmas (PARSE_REWRITE.parse_rewrites [s]) "THEORY_NAME" "IMPORTING_THEORIES" ctxt))

fun print_rewrite (cs:string) (t:Toplevel.transition) :  Toplevel.transition =
Toplevel.keep (fn toplevel => (fn state =>
  Print_Mode.with_modes [] (fn () => writeln (string_of_rewrite state cs)) ()) (Toplevel.context_of toplevel)) t

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>parse_rare\<close> "parse a single rule in rare format (provided as a string) and output lemma"
    ( Parse.string >> print_rewrite);



val semi = Scan.option \<^keyword>\<open>;\<close>; (*TODO: Do not need?*)

val _ =  Outer_Syntax.local_theory \<^command_keyword>\<open>parse_rare_file\<close> "parse file in rare format and output lemmas. <rare_file, import theories, target_theory>"
    (((Parse.string -- Parse.string)  -- Parse.string)
    >> (fn ((file_name,theory_imports),theory_name) => fn lthy =>
  let
          (*Built new path*)
          val file_path = Path.explode file_name
          val new_theory_name = theory_name ^ ".thy"
          val ctxt = Local_Theory.target_of lthy
          val res_path = Path.append (Path.dir file_path) (Path.basic new_theory_name)

          (*Calculate result*)
          val lines = (Bytes.split_lines (Bytes.read file_path)) ;
          val res = foldr1 (op^) (List.concat (WRITE_LEMMA.write_lemmas (PARSE_REWRITE.parse_rewrites lines) theory_name theory_imports ctxt))
          val _ = (Output.writeln res)

          val _ =
           Bytes.write
            res_path (Bytes.string res)
          val _ = @{print} ("done writing to file", res_path)
in  lthy
end))
\<close>
end