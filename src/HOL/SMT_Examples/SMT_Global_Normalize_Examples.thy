section \<open>Regression test for the extended embedding of natural numbers into integers\<close>

theory SMT_Global_Normalize_Examples
  imports "HOL.SMT"  (*HOL.SMT_CVC HOL.String*)
begin

(*None of the goals should contain any nats after encoding unless explicitly stated.*)
(*Note: I have not finished filling in the expected outcomes and some might not be the 
correct ones yet*)


declare[[smt_expert_debug_alethe_files="smt_global_normalize"]]
declare[[smt_expert_debug_alethe_level=3]]
declare[[smt_nat_as_int=true,smt_trace]]
declare[[show_hyps]]

definition prime_nat :: "nat \<Rightarrow> bool" where
  "prime_nat p = (1 < p \<and> (\<forall>m. m dvd p --> m = 1 \<or> m = p))"

lemma "prime_nat (4*m + 1) \<Longrightarrow> m \<ge> (1::nat)" by (smt (cvc5) ) (*ERROR nat embedding*)


thm SMT.int_ops(3)[symmetric]
thm of_nat_numeral
thm SMT.H1(1)

lemma variable_only:
  shows "(x::nat) = (x::nat)" 
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (= lift_x$ lift_x$))) :named a0))
\<close>)
  sorry


lemma constant_only:
  shows "(42::nat) = (42::nat)"
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (= 42 42)) :named a0))
\<close>)
  sorry

lemma neg_constant:
  shows "3 - (4::nat) = 0"
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (= (ite (< 3 4) 0 (- 3 4)) 0)) :named a0))
\<close>)
  sorry

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
  sorry

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
  sorry

lemma constant_and_native_fun:
  shows "(4::nat) + 5 = 9" 
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (= (+ 4 5) 9)) :named a0))
\<close>)
  sorry

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
  sorry

lemma two_variables_mult_occ:
  shows "(x::nat) = 3 \<Longrightarrow> (y::nat) = 3 \<Longrightarrow> (x::nat) = (y::nat)"
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (and (<= 0 lift_x$) (<= 0 lift_y$)) (not (=> (and (= lift_x$ 3) (= lift_y$ 3)) (= lift_x$ lift_y$)))) :named a0))
\<close>)
  sorry

lemma fun_native:
  shows "(x::nat) \<ge> 0"
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (<= 0 lift_x$))) :named a0))
\<close>)
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

lemma quant0:
  shows "\<forall>x. (x::int) = x" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (forall ((?v0 Int)) (= ?v0 ?v0))) :named a0))
\<close>)
  sorry

lemma quant1:
  shows "\<forall>x. (x::nat) = x" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (forall ((?v0 Int)) (=> (<= 0 ?v0) (= ?v0 ?v0)))) :named a0))
\<close>)
  sorry

lemma quant2:
  shows "\<exists>x. (x::nat) = x"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (exists ((?v0 Int)) (and (<= 0 ?v0) (= ?v0 ?v0)))) :named a0))
\<close>)
  sorry

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
  sorry

lemma quant4:
 fixes y::"nat"
 shows "(\<exists> x::int. (x = 3 \<and> y = y))"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_y$ () Int)
(assert (! (not (exists ((?v0 Int)) (=> (<= 0 lift_y$) (and (= ?v0 3) (= lift_y$ lift_y$))))) :named a0))
\<close>)
  sorry

lemma quant4b:
 fixes f::"int \<Rightarrow> nat"
 shows "(\<exists> x::int. (x = 3 \<and> f x = f x))"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_f$ (Int) Int)
(assert (! (not (exists ((?v0 Int)) (=> (<= 0 (lift_f$ ?v0)) (and (= ?v0 3) (= (lift_f$ ?v0) (lift_f$ ?v0)))))) :named a0))
\<close>)
  sorry

lemma quant5:
 fixes y::"nat"
  shows "(\<exists> x::nat. (x = 3 \<and> y = y))" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_y$ () Int)
(assert (! (not (exists ((?v0 Int)) (and (<= 0 ?v0) (=> (<= 0 lift_y$) (and (= ?v0 3) (= lift_y$ lift_y$)))))) :named a0))
\<close>)
  sorry


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
  sorry

lemma int_const:
  shows "int (4::nat) \<noteq> 5" 
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (not (= 4 5))) :named a0))
\<close>)
  sorry

lemma nat_var2:
  shows "nat (x::int) = 4 \<Longrightarrow> nat (x::int) \<noteq> 5"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun x$ () Int)
(assert (! (not (=> (= (ite (<= 0 x$) x$ 0) 4) (not (= (ite (<= 0 x$) x$ 0) 5)))) :named a0))
\<close>)
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

(*Lets*)

lemma let1: (*TODO*)
  "let (x::nat) = y + 3  in
  x = 1 + 2 + y"
  supply[[smt_nat_as_int,smt_trace]]
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_y$ () Int)
(assert (! (and (<= 0 lift_y$) (not (= (+ lift_y$ 3) (+ (+ 1 2) lift_y$)))) :named a0))
\<close>)
sorry

lemma let2:
  "let (x::int) = y + 3  in
  x = 1 + 2 + y"
  supply[[smt_nat_as_int,smt_trace]]
  by (smt (cvc5_proof))

lemma
"   let P = (if ((1::nat) + y) > 0 then True else False) in
   False \<or> P = (((1::nat) + y) - 1 = y) \<or> (\<not>P \<longrightarrow> False)"
  supply[[smt_nat_as_int]]
  by (smt (cvc5_proof)) (*ERROR nat embedding*)

lemma
  "let x = (1::nat) + y in
   let P = (if x > 0 then True else False) in
   False \<or> P = (x - 1 = y) \<or> (\<not>P \<longrightarrow> False)"
  supply[[smt_nat_as_int]]
  by (smt (cvc5_proof)) (*ERROR nat embedding*)




(*Conversions*)

lemma
  shows "nat x = y \<Longrightarrow> of_nat y = z \<Longrightarrow> x \<le> z"
  sorry



declare[[smt_expert_debug_alethe_files="smt_global_normalize"]]
declare[[smt_expert_debug_alethe_level=3]]

(*There is nothing to be done here*)
lemma
  fixes x::int
  assumes "nat x = 4"
  shows "True"
  using assms
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun x$ () Int)
(assert (! (= x$ 4) :named a0))
(assert (! (not true) :named a1))
\<close>)
  sorry

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
  sorry
lemma
  shows "int 4 = 4"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (= 4 4)) :named a0))
\<close>)
  sorry
lemma
  shows "nat 4 = 4"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (= 4 4)) :named a0))
\<close>)
  sorry
lemma
  shows "int x = int y"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (and (<= 0 lift_x$) (<= 0 lift_y$)) (not (= lift_x$ lift_y$))) :named a0))
\<close>)
  sorry


lemma
  shows "(x::nat) <= x - 1 \<Longrightarrow> x = 0"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (=> (<= lift_x$ (ite (< lift_x$ 1) 0 (- lift_x$ 1))) (= lift_x$ 0)))) :named a0))
\<close>)
  sorry

lemma
  shows "(x::nat) - y + y < x \<Longrightarrow> x < y"
 apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(declare-fun lift_x$ () Int)
(declare-fun lift_y$ () Int)
(assert (! (and (and (<= 0 lift_x$) (<= 0 lift_y$)) (not (=> (< (+ (ite (< lift_x$ lift_y$) 0 (- lift_x$ lift_y$)) lift_y$) lift_x$) (< lift_x$ lift_y$)))) :named a0))
\<close>)
  sorry
lemma
  shows "0 \<le> (x::int) \<Longrightarrow> y = nat x \<Longrightarrow> of_nat y = x"
 apply (test_smt_translate 
\<open>
\<close>)
    apply (smt (cvc5) int_nat_eq)
  done

lemma
  shows "0 > (x::int) \<Longrightarrow> y = nat x \<Longrightarrow> of_nat y = 0"
 apply (test_smt_translate 
\<open>
\<close>)
    apply (smt (cvc5) int_nat_eq)
  done

lemma "nat (int (x::nat)) = x" 
  apply (smt (cvc5))
  done

lemma "int x = y \<Longrightarrow> nat y = x"
  apply (smt (cvc5))
  done


lemma "(x::nat) = 3 + 4 \<Longrightarrow> x = 7" 
  apply (smt (cvc5))
  done

lemma "(x::int) = 3 + 4 \<Longrightarrow> x = 7" 

  apply (smt (cvc5))
  done


definition g1 where
"g1 (x::nat) (y::int) = y + 1"

lemma "\<exists>(x :: nat).((g :: nat \<Rightarrow> int \<Rightarrow> int) x (2 :: int)) = 3"
  sorry
lemma "\<forall>(x :: nat).((g :: nat \<Rightarrow> int \<Rightarrow> int) x (2 :: int)) = 3"
  sorry
lemma "(if (\<forall>x::int. x < 0 \<or> x > 0) then -1 else 3) > (0::int)"
  supply [[smt_trace]] by (smt (cvc5))

lemma "(2::nat) ^ 3 = 8"
  sorry
definition bound :: nat where
  "bound = 4"

lemma "bound = 3 + 1"
  using bound_def
  sorry

(*
  "(f::nat \<Rightarrow> int) (nat (3::int)) = (5::int)"



  introduce free variable (f_lift::int \<Rightarrow> int)

  transform this to a thm by Thm.assume (adds the same thing as a meta assumption):
    "\<And>v0. (f::nat \<Rightarrow> int) (v0::nat) = (lift_f__::int \<Rightarrow> int) (int v0) \<and> int v0 \<ge> 0"

  Create two lemmas from this:
    "\<And>v0. (f::nat \<Rightarrow> int) (v0::nat) = (lift_f__::int \<Rightarrow> int) (int v0)"
    "\<And>v0. int v0 \<ge> 0"

  Use those for conversion:


*)

(*

Before global normalization:
 "\<forall>(x::nat) y::int. boo x y = (int x = (2::int) \<and> y = (3::int))"
After preproc:
\<forall>x\<ge>0. \<forall>y::int. boo (nat x) y = (x = (2::int) \<and> y = (3::int)) 
Term to show after:
 "\<forall>x\<ge>0. \<forall>y::int. lift_boo x y = (x = (2::int) \<and> y = (3::int))"

Algo should have proven:
boo (nat x) y = lift_boo x y



\<forall>x\<ge>0. \<forall>y::int. boo (nat x) y = (int (nat x) = (2::int) \<and> y = (3::int)) \<Longrightarrow>
(\<And>(lb0::nat) lb1::int. boo lb0 lb1 = lift_boo (int lb0) lb1)
  \<Longrightarrow> \<forall>x\<ge>0. \<forall>y::int. lift_boo x y = (x = (2::int) \<and> y = (3::int))

*)
(*
(declare-fun lift_f$ (Int) Int)
(assert (! (and (<= 0 (lift_f$ 3)) (= (lift_f$ 3) 5)) :named a0))
(assert (! (not true) :named a1))
*)


(*
  original: "int((f::int \<Rightarrow> nat) (3::int)) = (5::int)"

  introduce free variable (f_lift::int \<Rightarrow> int)

  transform this to a thm by Thm.assume (adds the same thing as a meta assumption):
    "\<And>v0. (f::int \<Rightarrow> nat) (v0::int) = (lift_f__::int \<Rightarrow> int) v0 \<and> lift_f__ v0 \<ge> 0"

  Create two lemmas from this: NOTE: We can create these directly
    1 "\<And>v0. (lift_f__::int \<Rightarrow> int) v0 = (f::int \<Rightarrow> nat) (v0::int)"
    2 "\<And>v0. lift_f__ v0 \<ge> 0"

  Make new lemma:
  Int.nat_0_le: 0 \<le> (?z::int) \<Longrightarrow> int (nat ?z) = ?z
  Instantiate: 0 \<le> lift_f__ 3 \<Longrightarrow> int (nat (lift_f__ 3)) = (lift_f__ 3)
  3 Use above with 2: int (nat (lift_f__ 3)) = (lift_f__ 3)


  Create new :
  Use 1: "int(nat (lift_f__ (3::int))) = (5::int)"
  Have a new conversion using 3:  "lift_f__ (3::int) = (5::int)" hyps 0 \<le> lift_f__ 3 
  Use Thm.implies to pull meta hyp up to get "lift_f__ 3 \<ge> 0 \<longrightarrow> lift_f__ 3 = 5"
  


  end result:
     lift_f__ 3 \<ge> 0 \<longrightarrow> lift_f__ 3 = 5
*)
































end