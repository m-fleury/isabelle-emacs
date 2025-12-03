section \<open>Regression test for the extended embedding of natural numbers into integers\<close>

theory SMT_Global_Normalize_Examples
  imports "HOL.SMT" Main (*HOL.SMT_CVC HOL.String*)
begin

(*None of the goals should contain any nats after encoding unless explicitly stated.*)

declare[[smt_expert_debug_alethe_files="all"]]
declare[[smt_expert_debug_alethe_level=3]]
declare[[smt_nat_as_int=true,smt_trace]]

lemma variable_only:
  shows "(x::nat) = (x::nat)" 
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (= lift_x$ lift_x$))) :named a0))
\<close>)
  by (smt (cvc5))

lemma constant_only:
  shows "(42::nat) = (42::nat)"
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (= 42 42)) :named a0))
\<close>)
  by (smt (cvc5))

lemma neg_constant:
  shows "3 - (4::nat) = 0"
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (= (ite (< 3 4) 0 (- 3 4)) 0)) :named a0))
\<close>)
  by (smt (cvc5))

lemma variable_and_constant:
  assumes "(x::nat) = 3"
  shows "True"
  using assms
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (= lift_x$ 3)) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma two_variables:
  assumes "(x::nat) = (y::nat)" 
  shows "True"
  using assms
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (and (<= 0 lift_x$) (<= 0 lift_y$)) (= lift_x$ lift_y$)) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma constant_and_native_fun:
  shows "(4::nat) + 5 = 9" 
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (= (+ 4 5) 9)) :named a0))
\<close>)
  by (smt (cvc5))

lemma variables_and_native_fun:
  assumes "(x::nat) + y = z" 
  shows "True"
  using assms
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(declare-fun lift_y$ () Int)
(declare-fun lift_z$ () Int)
(assert (! (and (and (<= 0 lift_x$) (and (<= 0 lift_y$) (<= 0 lift_z$))) (= (+ lift_x$ lift_y$) lift_z$)) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma two_variables_mult_occ:
  shows "(x::nat) = 3 \<Longrightarrow> (y::nat) = 3 \<Longrightarrow> (x::nat) = (y::nat)"
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (and (<= 0 lift_x$) (<= 0 lift_y$)) (not (=> (and (= lift_x$ 3) (= lift_y$ 3)) (= lift_x$ lift_y$)))) :named a0))
\<close>)
  by (smt (cvc5))

lemma fun_native:
  shows "(x::nat) \<ge> 0"
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (<= 0 lift_x$))) :named a0))
\<close>)
  by (smt (cvc5))

lemma fun_constant1:
  fixes f::"int \<Rightarrow> int"
  assumes "f 3 = 5"
  shows "True"
  using assms
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun f$ (Int) Int)
(assert (! (= (f$ 3) 5) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma fun_constant2:
  fixes f::"nat \<Rightarrow> int"
  assumes "f 3 = 5"
  shows "True"
  using assms
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_f$ (Int) Int)
(assert (! (= (lift_f$ 3) 5) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma fun_constant2b:
  fixes f::"nat \<Rightarrow> nat \<Rightarrow> int"
  assumes "f 3 4 = 5"
  shows "True"
  using assms
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_f$ (Int Int) Int)
(assert (! (= (lift_f$ 3 4) 5) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma fun_constant3:
  fixes f::"int \<Rightarrow> nat"
  assumes "f 3 = 5"
  shows "True"
  using assms
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_f$ (Int) Int)
(assert (! (and (<= 0 (lift_f$ 3)) (= (lift_f$ 3) 5)) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma fun_variable1:
  fixes f::"nat \<Rightarrow> int"
  assumes "f x = 5"
  shows "True"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_f$ (Int) Int)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (= (lift_f$ lift_x$) 5)) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma fun_variable2:
  fixes f::"int \<Rightarrow> nat"
  assumes "f x = 5"
  shows "True"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun x$ () Int)
(declare-fun lift_f$ (Int) Int)
(assert (! (and (<= 0 (lift_f$ x$)) (= (lift_f$ x$) 5)) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma fun_variable3:
  fixes f::"nat \<Rightarrow> int"
  assumes "f 6 = x"
  shows "True"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun x$ () Int)
(declare-fun lift_f$ (Int) Int)
(assert (! (= (lift_f$ 6) x$) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma fun_variable4:
  fixes f::"nat \<Rightarrow> nat"
  assumes "f x = y"
  shows "True"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_f$ (Int) Int)
(declare-fun lift_x$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (and (<= 0 lift_x$) (and (<= 0 (lift_f$ lift_x$)) (<= 0 lift_y$))) (= (lift_f$ lift_x$) lift_y$)) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma fun_variable5:
  fixes f::"int \<Rightarrow> nat"
  assumes "f 6 = x"
  shows "True"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_f$ (Int) Int)
(declare-fun lift_x$ () Int)
(assert (! (and (and (<= 0 (lift_f$ 6)) (<= 0 lift_x$)) (= (lift_f$ 6) lift_x$)) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma fun_variable_constant_twice:
  fixes f::"int \<Rightarrow> nat"
  assumes "f 6 = f x"
  shows "True"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun x$ () Int)
(declare-fun lift_f$ (Int) Int)
(assert (! (and (and (<= 0 (lift_f$ 6)) (<= 0 (lift_f$ x$))) (= (lift_f$ 6) (lift_f$ x$))) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma native_inside_uninterpreted:
  fixes f::"int \<Rightarrow> nat"
  assumes "f (6 + 1) = f x"
  shows "True"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun x$ () Int)
(declare-fun lift_f$ (Int) Int)
(assert (! (and (and (<= 0 (lift_f$ (+ 6 1))) (<= 0 (lift_f$ x$))) (= (lift_f$ (+ 6 1)) (lift_f$ x$))) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma fun_trans:
  fixes f::"nat\<Rightarrow>int"
  shows "f y = 5 \<Longrightarrow> f x = 5 \<Longrightarrow> f y = f x"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_f$ (Int) Int)
(declare-fun lift_x$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (and (<= 0 lift_y$) (<= 0 lift_x$)) (not (=> (and (= (lift_f$ lift_y$) 5) (= (lift_f$ lift_x$) 5)) (= (lift_f$ lift_y$) (lift_f$ lift_x$))))) :named a0))
\<close>)
  by (smt (cvc5))

lemma fun_trans2:
  fixes f::"nat\<Rightarrow>int"
  shows "f 3 = 5 \<Longrightarrow> f x = 5 \<Longrightarrow> f 3 = f x" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_f$ (Int) Int)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (=> (and (= (lift_f$ 3) 5) (= (lift_f$ lift_x$) 5)) (= (lift_f$ 3) (lift_f$ lift_x$))))) :named a0))
\<close>)
  by (smt (cvc5))

lemma fun_trans3:
  fixes f::"nat\<Rightarrow>nat"
  shows "f y = 5 \<Longrightarrow> f x = 5 \<Longrightarrow> f y = f x"
  supply[[ML_print_depth=1000]]
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_f$ (Int) Int)
(declare-fun lift_x$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (and (<= 0 lift_y$) (and (<= 0 (lift_f$ lift_y$)) (and (<= 0 lift_x$) (<= 0 (lift_f$ lift_x$))))) (not (=> (and (= (lift_f$ lift_y$) 5) (= (lift_f$ lift_x$) 5)) (= (lift_f$ lift_y$) (lift_f$ lift_x$))))) :named a0))
\<close>)
  by (smt (cvc5))

lemma quant0:
  shows "\<forall>x. (x::int) = x" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (forall ((?v0 Int)) (= ?v0 ?v0))) :named a0))
\<close>)
  by (smt (cvc5))

lemma quant1:
  shows "\<forall>x. (x::nat) = x" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (forall ((?v0 Int)) (=> (<= 0 ?v0) (= ?v0 ?v0)))) :named a0))
\<close>)
  by (smt (cvc5))

lemma quant2:
  shows "\<exists>x. (x::nat) = x"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (exists ((?v0 Int)) (and (<= 0 ?v0) (= ?v0 ?v0)))) :named a0))
\<close>)
  by (smt (cvc5))

lemma quant3:
  fixes f::"nat\<Rightarrow>int" and a::"nat"
  assumes "(\<forall> x. f a = f x) \<and> (\<forall> x. f a = f x)"
  shows "True"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_a$ () Int)
(declare-fun lift_f$ (Int) Int)
(assert (! (and (forall ((?v0 Int)) (=> (<= 0 ?v0) (and (<= 0 lift_a$) (= (lift_f$ lift_a$) (lift_f$ ?v0))))) (forall ((?v0 Int)) (=> (<= 0 ?v0) (and (<= 0 lift_a$) (= (lift_f$ lift_a$) (lift_f$ ?v0)))))) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma quant4:
 fixes y::"nat"
 shows "(\<exists> x::int. (x = 3 \<and> y = y))"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_y$ () Int)
(assert (! (not (exists ((?v0 Int)) (=> (<= 0 lift_y$) (and (= ?v0 3) (= lift_y$ lift_y$))))) :named a0))
\<close>)
  by (smt (cvc5))

lemma quant4b:
 fixes f::"int \<Rightarrow> nat"
 shows "(\<exists> x::int. (x = 3 \<and> f x = f x))"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_f$ (Int) Int)
(assert (! (not (exists ((?v0 Int)) (=> (<= 0 (lift_f$ ?v0)) (and (= ?v0 3) (= (lift_f$ ?v0) (lift_f$ ?v0)))))) :named a0))
\<close>)
  by (smt (cvc5))

lemma quant5:
 fixes y::"nat"
  shows "(\<exists> x::nat. (x = 3 \<and> y = y))" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_y$ () Int)
(assert (! (not (exists ((?v0 Int)) (and (<= 0 ?v0) (=> (<= 0 lift_y$) (and (= ?v0 3) (= lift_y$ lift_y$)))))) :named a0))
\<close>)
  by (smt (cvc5))


lemma quant6:
 fixes y::"nat"
  shows "(\<exists> x. x = y)" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_y$ () Int)
(assert (! (not (exists ((?v0 Int)) (and (<= 0 ?v0) (=> (<= 0 lift_y$) (= ?v0 lift_y$))))) :named a0))
\<close>)
  oops

lemma nat_const:
  shows "nat (0::int) \<noteq> 1"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (not (= 0 1))) :named a0))
\<close>)
  by (smt (cvc5))

lemma int_const:
  shows "int (4::nat) \<noteq> 5" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (not (= 4 5))) :named a0))
\<close>)
  by (smt (cvc5))

lemma nat_var2:
  shows "nat (x::int) = 4 \<Longrightarrow> nat (x::int) \<noteq> 5"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun x$ () Int)
(assert (! (not (=> (= (ite (<= 0 x$) x$ 0) 4) (not (= (ite (<= 0 x$) x$ 0) 5)))) :named a0))
\<close>)
  by (smt (cvc5))

(*Definitions*)

definition foo ::"nat \<Rightarrow> nat" where
"foo (x::nat) = x + 1"

lemma def_quant1:
  shows "foo 0 = 1"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_foo$ (Int) Int)
(assert (! (and (<= 0 (lift_foo$ 0)) (not (= (lift_foo$ 0) 1))) :named a0))
\<close>)
  oops

lemma def_quant2:
  shows "foo 0 = 1"
  using foo_def
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_foo$ (Int) Int)
(assert (! (forall ((?v0 Int)) (=> (<= 0 ?v0) (and (<= 0 (lift_foo$ ?v0)) (= (lift_foo$ ?v0) (+ ?v0 1))))) :named a0))
(assert (! (and (<= 0 (lift_foo$ 0)) (not (= (lift_foo$ 0) 1))) :named a1))
\<close>)
  using foo_def
  by (smt (cvc5))

(*We don't translate in this case*)
lemma def_quant_not_trans:
  shows "foo = foo"
  using foo_def
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-sort Nat$ 0)
(declare-sort Nat_nat_fun$ 0)
(declare-fun foo$ () Nat_nat_fun$)
(declare-fun of_nat$ (Nat$) Int)
(declare-fun fun_app$ (Nat_nat_fun$ Nat$) Nat$)
(assert (! (forall ((?v0 Nat$)) (= (of_nat$ (fun_app$ foo$ ?v0)) (+ (of_nat$ ?v0) 1))) :named a0))
(assert (! (not (= foo$ foo$)) :named a1))
\<close>)
  sorry

definition foo2 :: "nat \<Rightarrow> int" where
"foo2 (x::nat) = (1::int)"

lemma def_quant3:
  shows "foo2 0 = 1"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_foo2$ (Int) Int)
(assert (! (not (= (lift_foo2$ 0) 1)) :named a0))
\<close>)
  oops

lemma def_quant4:
  shows "foo2 0 = 1"
  using foo2_def
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_foo2$ (Int) Int)
(assert (! (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (lift_foo2$ ?v0) 1))) :named a0))
(assert (! (not (= (lift_foo2$ 0) 1)) :named a1))
\<close>)
  using foo2_def
  by (smt (cvc5))

definition boo:: "nat \<Rightarrow> int \<Rightarrow> bool" where
"boo (x::nat) (y::int) \<equiv> (x = 2) \<and> (y = 3)"

lemma def_quant5:
  shows "boo (x::nat) 3"
  using boo_def
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(declare-fun lift_boo$ (Int Int) Bool)
(assert (! (forall ((?v0 Int)) (=> (<= 0 ?v0) (forall ((?v1 Int)) (= (lift_boo$ ?v0 ?v1) (and (= ?v0 2) (= ?v1 3)))))) :named a0))
(assert (! (and (<= 0 lift_x$) (not (lift_boo$ lift_x$ 3))) :named a1))
\<close>)
  oops

(*Lets
Some lets (where the let term has type nat)
already get deleted during preprocessing so they are not an issue*)

lemma let1:
  "let (x::nat) = y + 3 in x = 1 + 2 + y"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_y$ () Int)
(assert (! (and (<= 0 lift_y$) (not (= (+ lift_y$ 3) (+ (+ 1 2) lift_y$)))) :named a0))
\<close>)
  by (smt (cvc5))

lemma let2:
"let P = (if ((1::nat) + y) > 0 then True else False) in
   False \<or> P = (((1::nat) + y) - 1 = y) \<or> (\<not>P \<longrightarrow> False)"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_y$ () Int)
(assert (! (and (<= 0 lift_y$) (not (or false (or (= (ite (< 0 (+ 1 lift_y$)) true false) (= (ite (< (+ 1 lift_y$) 1) 0 (- (+ 1 lift_y$) 1)) lift_y$)) (=> (not (ite (< 0 (+ 1 lift_y$)) true false)) false))))) :named a0))
\<close>)
  oops


(*Conversions*)

lemma
  shows "nat x = y \<Longrightarrow> of_nat y = z \<Longrightarrow> x \<le> z"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun x$ () Int)
(declare-fun z$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (<= 0 lift_y$) (not (=> (and (= (ite (<= 0 x$) x$ 0) lift_y$) (= lift_y$ z$)) (<= x$ z$)))) :named a0))
\<close>)
  by (smt (cvc5))

(*There is nothing to be done here but adding an ite*)
lemma
  fixes x::int
  assumes "nat x = 4"
  shows "True"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun x$ () Int)
(assert (! (= (ite (<= 0 x$) x$ 0) 4) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

(*Here x is a nat though and can be lifted*)
lemma
  fixes x::nat
  assumes "int x = 4"
  shows "True"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (= lift_x$ 4)) :named a0))
(assert (! (not true) :named a1))
\<close>)
  by (smt (cvc5))

lemma
  shows "int 4 = 4"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (= 4 4)) :named a0))
\<close>)
  by (smt (cvc5))

lemma
  shows "nat 4 = 4"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (= 4 4)) :named a0))
\<close>)
  by (smt (cvc5))

lemma
  shows "int x = int y"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (and (<= 0 lift_x$) (<= 0 lift_y$)) (not (= lift_x$ lift_y$))) :named a0))
\<close>)
  oops

lemma
  shows "(x::nat) <= x - 1 \<Longrightarrow> x = 0"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (=> (<= lift_x$ (ite (< lift_x$ 1) 0 (- lift_x$ 1))) (= lift_x$ 0)))) :named a0))
\<close>)
  supply[[smt_trace=false]]
  by (smt (cvc5))

lemma
  shows "(x::nat) - y + y < x \<Longrightarrow> x < y"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (and (<= 0 lift_x$) (<= 0 lift_y$)) (not (=> (< (+ (ite (< lift_x$ lift_y$) 0 (- lift_x$ lift_y$)) lift_y$) lift_x$) (< lift_x$ lift_y$)))) :named a0))
\<close>)
  by (smt (cvc5))

lemma
  shows "0 \<le> (x::int) \<Longrightarrow> y = nat x \<Longrightarrow> of_nat y = x"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun x$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (<= 0 lift_y$) (not (=> (and (<= 0 x$) (= lift_y$ (ite (<= 0 x$) x$ 0))) (= lift_y$ x$)))) :named a0))
\<close>)
  by (smt (cvc5))

lemma
  shows "0 > (x::int) \<Longrightarrow> y = nat x \<Longrightarrow> of_nat y = (0::int)"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun x$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (<= 0 lift_y$) (not (=> (and (< x$ 0) (= lift_y$ (ite (<= 0 x$) x$ 0))) (= lift_y$ 0)))) :named a0))
\<close>)
  by (smt (cvc5))

lemma
  shows "0 > (x::int) \<Longrightarrow> y = nat x \<Longrightarrow> of_nat y = 0"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-sort A$ 0)
(declare-fun x$ () Int)
(declare-fun zero$ () A$)
(declare-fun lift_y$ () Int)
(declare-fun lift_of_nat$ (Int) A$)
(assert (! (and (<= 0 lift_y$) (not (=> (and (< x$ 0) (= lift_y$ (ite (<= 0 x$) x$ 0))) (= (lift_of_nat$ lift_y$) zero$)))) :named a0))
\<close>)
  oops

lemma "nat (int (x::nat)) = x" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (= lift_x$ lift_x$))) :named a0))
\<close>)
  by (smt (cvc5))

lemma "(int (x::nat)) = y \<Longrightarrow> nat y = x" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun y$ () Int)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (=> (= lift_x$ y$) (= (ite (<= 0 y$) y$ 0) lift_x$)))) :named a0))
\<close>)
  by (smt (cvc5))


lemma "int x = y \<Longrightarrow> nat y = x"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun y$ () Int)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (=> (= lift_x$ y$) (= (ite (<= 0 y$) y$ 0) lift_x$)))) :named a0))
\<close>)
  by (smt (cvc5))

lemma "(x::nat) = 3 + 4 \<Longrightarrow> x = 7" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (=> (= lift_x$ (+ 3 4)) (= lift_x$ 7)))) :named a0))
\<close>)
  by (smt (cvc5))

lemma "(x::int) = 3 + 4 \<Longrightarrow> x = 7" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun x$ () Int)
(assert (! (not (=> (= x$ (+ 3 4)) (= x$ 7))) :named a0))
\<close>)
  by (smt (cvc5))

(*Misc*)

definition g1 where "g1 (x::nat) (y::int) = y + 1"

lemma "\<exists>(x :: nat).((g1 :: nat \<Rightarrow> int \<Rightarrow> int) x (2 :: int)) = 3"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_g1$ (Int Int) Int)
(assert (! (not (exists ((?v0 Int)) (and (<= 0 ?v0) (= (lift_g1$ ?v0 2) 3)))) :named a0))
\<close>)
  oops

lemma "\<forall>(x :: nat).((g1 :: nat \<Rightarrow> int \<Rightarrow> int) x (2 :: int)) = 3"
  using g1_def
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_g1$ (Int Int) Int)
(assert (! (forall ((?v0 Int)) (=> (<= 0 ?v0) (forall ((?v1 Int)) (= (lift_g1$ ?v0 ?v1) (+ ?v1 1))))) :named a0))
(assert (! (not (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (lift_g1$ ?v0 2) 3)))) :named a1))
\<close>)
  using g1_def
  by (smt (cvc5))

lemma "(if (\<forall>x::int. x < 0 \<or> x > 0) then -1 else 3) > (0::int)"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (< 0 (ite (forall ((?v0 Int)) (or (< ?v0 0) (< 0 ?v0))) (- 1) 3))) :named a0))
\<close>)
  by (smt (cvc5))

lemma "(2::nat) ^ 3 = 8"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (= (int.pow2 3) 8)) :named a0))
\<close>)
  oops

definition bound :: nat where
  "bound = 4"

lemma "bound = 3 + 1"
  using bound_def
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_bound$ () Int)
(assert (! (and (<= 0 lift_bound$) (= lift_bound$ 4)) :named a0))
(assert (! (and (<= 0 lift_bound$) (not (= lift_bound$ (+ 3 1)))) :named a1))
\<close>)
  using bound_def
  by (smt (cvc5))


definition prime_nat :: "nat \<Rightarrow> bool" where
  "prime_nat p = (1 < p \<and> (\<forall>m. m dvd p --> m = 1 \<or> m = p))"

lemma "prime_nat (4*m + 1) \<Longrightarrow> m \<ge> (1::nat)"
  using prime_nat_def
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_m$ () Int)
(declare-fun lift_dvd$ (Int Int) Bool)
(declare-fun lift_prime_nat$ (Int) Bool)
(assert (! (forall ((?v0 Int)) (=> (<= 0 ?v0) (= (lift_prime_nat$ ?v0) (and (< 1 ?v0) (forall ((?v1 Int)) (=> (<= 0 ?v1) (=> (lift_dvd$ ?v1 ?v0) (or (= ?v1 1) (= ?v1 ?v0))))))))) :named a0))
(assert (! (and (<= 0 lift_m$) (not (=> (lift_prime_nat$ (+ (* 4 lift_m$) 1)) (<= 1 lift_m$)))) :named a1))
\<close>)
  using dvd_def
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun dvd$ (Int Int) Bool)
(declare-fun times$ (Int Int) Int)
(declare-fun lift_m$ () Int)
(declare-fun lift_prime_nat$ (Int) Bool)
(assert (! (forall ((?v0 Int) (?v1 Int)) (= (dvd$ ?v0 ?v1) (exists ((?v2 Int)) (= ?v1 (times$ ?v0 ?v2))))) :named a0))
(assert (! (and (<= 0 lift_m$) (not (=> (lift_prime_nat$ (+ (* 4 lift_m$) 1)) (<= 1 lift_m$)))) :named a1))
\<close>)
  oops


experiment
begin

declare[[smt_expert_debug_alethe_files="smt_global_normalize"]]
declare[[smt_expert_debug_alethe_level=3]]
lemma (in complete_lattice)
  assumes "Sup {a | i::bool.  True} \<le> Sup {b | i::bool. True}"
  and "Sup {b | i::bool. True} \<le> Sup {a | i::bool. True}"
  shows "Sup {a | i::bool. True} \<le> Sup {a | i::bool. True}"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-sort A$ 0)
(declare-sort A_set$ 0)
(declare-sort A_bool_fun$ 0)
(declare-fun a$ () A$)
(declare-fun b$ () A$)
(declare-fun sup$ (A_set$) A$)
(declare-fun uul$ () A_bool_fun$)
(declare-fun uum$ () A_bool_fun$)
(declare-fun collect$ (A_bool_fun$) A_set$)
(declare-fun fun_app$ (A_bool_fun$ A$) Bool)
(declare-fun less_eq$ (A$ A$) Bool)
(assert (! (forall ((?v0 A$)) (! (= (fun_app$ uum$ ?v0) (exists ((?v1 Bool)) (and (= ?v0 b$) true))) :pattern ((fun_app$ uum$ ?v0)))) :named a0))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$ uul$ ?v0) (exists ((?v1 Bool)) (and (= ?v0 a$) true))) :pattern ((fun_app$ uul$ ?v0)))) :named a1))
(assert (! (less_eq$ (sup$ (collect$ uul$)) (sup$ (collect$ uum$))) :named a2))
(assert (! (less_eq$ (sup$ (collect$ uum$)) (sup$ (collect$ uul$))) :named a3))
(assert (! (not (less_eq$ (sup$ (collect$ uul$)) (sup$ (collect$ uul$)))) :named a4))
\<close>)
 using assms by (smt (cvc5) order_trans)

lemma (in complete_lattice)
  assumes "Sup {a | i::bool.  (3::nat) = (3::nat)} \<le> Sup {b | i::bool. True}"
  and "Sup {b | i::bool. True} \<le> Sup {a | i::bool. True}"
  shows "Sup {a | i::bool. True} \<le> Sup {a | i::bool. True}"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-sort A$ 0)
(declare-sort A_set$ 0)
(declare-sort A_bool_fun$ 0)
(declare-fun a$ () A$)
(declare-fun b$ () A$)
(declare-fun sup$ (A_set$) A$)
(declare-fun uul$ () A_bool_fun$)
(declare-fun uum$ () A_bool_fun$)
(declare-fun uun$ () A_bool_fun$)
(declare-fun collect$ (A_bool_fun$) A_set$)
(declare-fun fun_app$ (A_bool_fun$ A$) Bool)
(declare-fun less_eq$ (A$ A$) Bool)
(assert (! (forall ((?v0 A$)) (! (= (fun_app$ uul$ ?v0) (exists ((?v1 Bool)) (and (= ?v0 a$) (= 3 3)))) :pattern ((fun_app$ uul$ ?v0)))) :named a0))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$ uum$ ?v0) (exists ((?v1 Bool)) (and (= ?v0 b$) true))) :pattern ((fun_app$ uum$ ?v0)))) :named a1))
(assert (! (forall ((?v0 A$)) (! (= (fun_app$ uun$ ?v0) (exists ((?v1 Bool)) (and (= ?v0 a$) true))) :pattern ((fun_app$ uun$ ?v0)))) :named a2))
(assert (! (less_eq$ (sup$ (collect$ uul$)) (sup$ (collect$ uum$))) :named a3))
(assert (! (less_eq$ (sup$ (collect$ uum$)) (sup$ (collect$ uun$))) :named a4))
(assert (! (not (less_eq$ (sup$ (collect$ uun$)) (sup$ (collect$ uun$)))) :named a5))
\<close>)
  sorry
end


end