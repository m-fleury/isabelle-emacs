(*  Title:      HOL/SMT_Examples/SMT_Examples_CVC.thy
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University of Freiburg


   41 rules in total
   14 rules with test
   27 without test
*)

theory Arith_Rewrites
  imports HOL.SMT_CVC
begin

declare[[smt_trace=false,smt_verbose=false]]

(*(define-rule arith-div-total-zero-real ((t ?)) (/_total t 0/1) 0/1)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-div-total-zero-real.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-div-total-zero-real.alethe"


(*(define-rule arith-div-total-zero-int ((t ?)) (/_total t 0) 0/1)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-div-total-zero-int.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-div-total-zero-int.alethe"

(*(define-cond-rule arith-int-div-total ((t Int) (s Int)) (not (= s 0)) (div t s) (div_total t s))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-div-total.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-div-total.alethe"

(*(define-rule arith-int-div-total-one ((t Int)) (div_total t 1) t)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-div-total-one.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-div-total-one.alethe"

(*(define-rule arith-int-div-total-zero ((t Int)) (div_total t 0) 0)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-div-total-zero.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-div-total-zero.alethe"


(*(define-cond-rule arith-int-div-total-neg ((t Int) (s Int)) (< s 0) (div_total t s) (- (div_total t (- s))))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-div-total-neg.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-div-total-neg.alethe"


(*(define-cond-rule arith-int-mod-total ((t Int) (s Int)) (not (= s 0)) (mod t s) (mod_total t s))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-mod-total.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-mod-total.alethe"

(*(define-rule arith-int-mod-total-one ((t Int)) (mod_total t 1) 0)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-mod-total-one.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-mod-total-one.alethe"

(*(define-rule arith-int-mod-total-zero ((t Int)) (mod_total t 0) t)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-mod-total-zero.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-mod-total-zero.alethe"


(*(define-cond-rule arith-int-mod-total-neg ((t Int) (s Int)) (< s 0) (mod_total t s) (mod_total t (- s)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-mod-total-neg.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-mod-total-neg.alethe"


(*(define-rule arith-elim-gt ((t ?) (s ?)) (> t s) (not (>= s t)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-elim-gt.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-elim-gt.alethe"

(*(define-rule arith-elim-lt ((t ?) (s ?)) (< t s) (not (>= t s)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-elim-lt.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-elim-lt.alethe"

(*(define-rule arith-elim-int-gt ((t Int) (s Int)) (> t s) (>= t (+ s 1)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-elim-int-gt.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-elim-int-gt.alethe"

(*(define-rule arith-elim-int-lt ((t Int) (s Int)) (< t s) (>= s (+ t 1)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-elim-int-lt.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-elim-int-lt.alethe"

(*(define-rule arith-elim-leq ((t ?) (s ?)) (<= t s) (>= s t))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-elim-leq.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-elim-leq.alethe"


(*(define-rule arith-leq-norm ((t Int) (s Int)) (<= t s) (not (>= t (+ s 1))))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-leq-norm.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-leq-norm.alethe"


(*(define-rule arith-geq-tighten ((t Int) (s Int)) (not (>= t s)) (>= s (+ t 1)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-geq-tighten.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-geq-tighten.alethe"


(*(define-rule arith-geq-norm1-int ((t Int) (s Int)) (>= t s) (>= (- t s) 0))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-geq-norm1-int.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-geq-norm1-int.alethe"

(*(define-rule arith-geq-norm1-real ((t Real) (s Real)) (>= t s) (>= (- t s) 0/1))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-geq-norm1-real.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-geq-norm1-real.alethe"


(*(define-rule arith-eq-elim-real ((t Real) (s Real)) (= t s) (and (>= t s) (<= t s)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-eq-elim-real.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-eq-elim-real.alethe"

(*(define-rule arith-eq-elim-int ((t Int) (s Int)) (= t s) (and (>= t s) (<= t s)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-eq-elim-in.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-eq-elim-in.alethe"


(*(define-rule* arith-plus-flatten ((xs ? :list) (w1 ?) (w2 ?) (ys ? :list) (zs ? :list))
  (+ xs (+ w1 w2 ys) zs)
  (+ xs w1 w2 ys zs))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-plus-flatten.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-plus-flatten.alethe"


(*(define-rule arith-to-int-elim ((x Int)) (to_int x) x)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-to-int-elim.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-to-int-elim.alethe"

(*(define-rule arith-to-int-elim-to-real ((x ?)) (to_int (to_real x)) (to_int x))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-to-int-elim-to-real.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-to-int-elim-to-real.alethe"

(*(define-rule arith-div-elim-to-real1 ((x ?) (y ?)) (/ (to_real x) y) (/ x y))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-div-elim-to-real1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-div-elim-to-real1.alethe"

(*(define-rule arith-div-elim-to-real2 ((x ?) (y ?)) (/ x (to_real y)) (/ x y))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-div-elim-to-real2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-div-elim-to-real2.alethe"


(*(define-cond-rule arith-mod-over-mod ((c Int) (ts Int :list) (r Int) (ss Int :list))
  (not (= c 0))
  (mod_total (+ ts (mod_total r c) ss) c)
  (mod_total (+ ts r ss) c))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-mod-over-mod.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-mod-over-mod.alethe"

(*(define-cond-rule arith-int-eq-conflict ((t Int) (c Real))
  (not (= (to_real (to_int c)) c))
  (= (to_real t) c)
  false)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-eq-conflict.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-eq-conflict.alethe"


(*(define-cond-rule arith-int-geq-tighten ((t Int) (c Real) (cc Int))
  (and (not (= (to_real (to_int c)) c)) (= cc (+ (to_int c) 1)))
  (>= (to_real t) c)
  (>= t cc))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-geq-tighten.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-int-geq-tighten.alethe"


(*(define-cond-rule arith-divisible-elim ((n Int) (t Int))
  (not (= n 0))
  (divisible n t)
  (= (mod_total t n) 0))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-divisible-elim.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-divisible-elim.alethe"



(*(define-rule arith-abs-eq ((x ?) (y ?))
  (= (abs x) (abs y))
  (or (= x y) (= x (- y))))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-abs-eq.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-abs-eq.alethe"


(*(define-rule arith-abs-int-gt ((x Int) (y Int))
  (> (abs x) (abs y))
  (ite (>= x 0)
    (ite (>= y 0)
      (> x y)
      (> x (- y)))
    (ite (>= y 0)
      (> (- x) y)
      (> (- x) (- y)))))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-abs-int-gt.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-abs-int-gt.alethe"


(*(define-rule arith-abs-real-gt ((x Real) (y Real))
  (> (abs x) (abs y))
  (ite (>= x 0/1)
    (ite (>= y 0/1)
      (> x y)
      (> x (- y)))
    (ite (>= y 0/1)
      (> (- x) y)
      (> (- x) (- y)))))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-abs-real-gt.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-abs-real-gt.alethe"



(*(define-rule arith-geq-ite-lift ((C Bool) (t ?) (s ?) (r ?))
  (>= (ite C t s) r)
  (ite C (>= t r) (>= s r)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-geq-ite-lift.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-geq-ite-lift.alethe"


(*(define-rule arith-gt-ite-lift ((C Bool) (t ?) (s ?) (r ?))
  (> (ite C t s) r)
  (ite C (> t r) (> s r)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-gt-ite-lift.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-gt-ite-lift.alethe"


(*(define-rule arith-leq-ite-lift ((C Bool) (t ?) (s ?) (r ?))
  (<= (ite C t s) r)
  (ite C (<= t r) (<= s r)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-leq-ite-lift.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-leq-ite-lift.alethe"


(*(define-rule arith-lt-ite-lift ((C Bool) (t ?) (s ?) (r ?))
  (< (ite C t s) r)
  (ite C (< t r) (< s r)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-lt-ite-lift.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-lt-ite-lift.alethe"




(*(define-rule arith-min-lt1 ((t ?) (s ?))
  (<= (ite (< t s) t s) t)
  true)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-min-lt1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-min-lt1.alethe"


(*(define-rule arith-min-lt2 ((t ?) (s ?))
  (<= (ite (< t s) t s) s)
  true)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-min-lt2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-min-lt2.alethe"


(*(define-rule arith-max-geq1 ((t ?) (s ?))
  (>= (ite (>= t s) t s) t)
  true)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-max-geq1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-max-geq1.alethe"


(*(define-rule arith-max-geq2 ((t ?) (s ?))
  (>= (ite (>= t s) t s) s)
  true)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-max-geq2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Arith_Rewrites/arith-max-geq2.alethe"




end