(*  Title:      HOL/Hoare/Hoare_Logic.thy
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Copyright   1998 TUM

Sugared semantic embedding of Hoare logic.
Strictly speaking a shallow embedding (as implemented by Norbert Galm
following Mike Gordon) would suffice. Maybe the datatype com comes in useful
later.
*)

theory Hoare_Logic
imports Main
begin

type_synonym 'a bexp = "'a set"
type_synonym 'a assn = "'a set"

datatype 'a com =
  Basic "'a \<Rightarrow> 'a"
| Seq "'a com" "'a com"               ("(_;/ _)"      [61,60] 60)
| Cond "'a bexp" "'a com" "'a com"    ("(1IF _/ THEN _ / ELSE _/ FI)"  [0,0,0] 61)
| While "'a bexp" "'a assn" "'a com"  ("(1WHILE _/ INV {_} //DO _ /OD)"  [0,0,0] 61)

abbreviation annskip ("SKIP") where "SKIP == Basic id"

type_synonym 'a sem = "'a => 'a => bool"

inductive Sem :: "'a com \<Rightarrow> 'a sem"
where
  "Sem (Basic f) s (f s)"
| "Sem c1 s s'' \<Longrightarrow> Sem c2 s'' s' \<Longrightarrow> Sem (c1;c2) s s'"
| "s \<in> b \<Longrightarrow> Sem c1 s s' \<Longrightarrow> Sem (IF b THEN c1 ELSE c2 FI) s s'"
| "s \<notin> b \<Longrightarrow> Sem c2 s s' \<Longrightarrow> Sem (IF b THEN c1 ELSE c2 FI) s s'"
| "s \<notin> b \<Longrightarrow> Sem (While b x c) s s"
| "s \<in> b \<Longrightarrow> Sem c s s'' \<Longrightarrow> Sem (While b x c) s'' s' \<Longrightarrow>
   Sem (While b x c) s s'"

inductive_cases [elim!]:
  "Sem (Basic f) s s'" "Sem (c1;c2) s s'"
  "Sem (IF b THEN c1 ELSE c2 FI) s s'"

definition Valid :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a bexp \<Rightarrow> bool"
  where "Valid p c q \<longleftrightarrow> (\<forall>s s'. Sem c s s' \<longrightarrow> s \<in> p \<longrightarrow> s' \<in> q)"


syntax
  "_assign" :: "idt => 'b => 'a com"  ("(2_ :=/ _)" [70, 65] 61)

syntax
 "_hoare_vars" :: "[idts, 'a assn,'a com,'a assn] => bool"
                 ("VARS _// {_} // _ // {_}" [0,0,55,0] 50)
syntax ("" output)
 "_hoare"      :: "['a assn,'a com,'a assn] => bool"
                 ("{_} // _ // {_}" [0,55,0] 50)

ML_file \<open>hoare_syntax.ML\<close>
parse_translation \<open>[(\<^syntax_const>\<open>_hoare_vars\<close>, K Hoare_Syntax.hoare_vars_tr)]\<close>
print_translation \<open>[(\<^const_syntax>\<open>Valid\<close>, K (Hoare_Syntax.spec_tr' \<^syntax_const>\<open>_hoare\<close>))]\<close>


lemma SkipRule: "p \<subseteq> q \<Longrightarrow> Valid p (Basic id) q"
by (auto simp:Valid_def)

lemma BasicRule: "p \<subseteq> {s. f s \<in> q} \<Longrightarrow> Valid p (Basic f) q"
by (auto simp:Valid_def)

lemma SeqRule: "Valid P c1 Q \<Longrightarrow> Valid Q c2 R \<Longrightarrow> Valid P (c1;c2) R"
by (auto simp:Valid_def)

lemma CondRule:
 "p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}
  \<Longrightarrow> Valid w c1 q \<Longrightarrow> Valid w' c2 q \<Longrightarrow> Valid p (Cond b c1 c2) q"
by (auto simp:Valid_def)

lemma While_aux:
  assumes "Sem (WHILE b INV {i} DO c OD) s s'"
  shows "\<forall>s s'. Sem c s s' \<longrightarrow> s \<in> I \<and> s \<in> b \<longrightarrow> s' \<in> I \<Longrightarrow>
    s \<in> I \<Longrightarrow> s' \<in> I \<and> s' \<notin> b"
  using assms
  by (induct "WHILE b INV {i} DO c OD" s s') auto

lemma WhileRule:
 "p \<subseteq> i \<Longrightarrow> Valid (i \<inter> b) c i \<Longrightarrow> i \<inter> (-b) \<subseteq> q \<Longrightarrow> Valid p (While b i c) q"
apply (clarsimp simp:Valid_def)
apply(drule While_aux)
  apply assumption
 apply blast
apply blast
done


lemma Compl_Collect: "-(Collect b) = {x. ~(b x)}"
  by blast

lemmas AbortRule = SkipRule  \<comment> \<open>dummy version\<close>
ML_file \<open>hoare_tac.ML\<close>

method_setup vcg = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD' (Hoare.hoare_tac ctxt (K all_tac)))\<close>
  "verification condition generator"

method_setup vcg_simp = \<open>
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (Hoare.hoare_tac ctxt (asm_full_simp_tac ctxt)))\<close>
  "verification condition generator plus simplification"

end
