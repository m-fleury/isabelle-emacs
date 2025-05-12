(*  Title:      HOL/SMT_Examples/SMT_Examples_CVC.thy
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University of Freiburg


    13 rules in total
    5 rules with test
    8 without test
*)

theory UF_Rewrites
  imports HOL.SMT_CVC
begin

declare[[smt_trace=false,smt_verbose=false]]


(*(define-rule eq-refl ((t ?)) (= t t) true)*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/eq-refl.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/eq-refl.alethe"



(*(define-rule eq-symm ((t ?) (s ?)) (= t s) (= s t))*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/eq-symm.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/eq-symm.alethe"


(*(define-cond-rule eq-cond-deq ((t ?) (s ?) (r ?))
  (= (= s r) false)
  (= (= t s) (= t r))
  (and (not (= t s)) (not (= t r))))*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/eq-cond-deq.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/eq-cond-deq.alethe"

(*(define-rule eq-ite-lift ((C Bool) (t ?) (s ?) (r ?))
  (= (ite C t s) r)
  (ite C (= t r) (= s r)))*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/eq-ite-lift.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/eq-ite-lift.alethe"

(*(define-rule distinct-binary-elim ((t ?) (s ?)) (distinct t s) (not (= t s)))*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/distinct-binary-elim.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/distinct-binary-elim.alethe"

(*(define-cond-rule uf-bv2nat-int2bv ((w Int) (t ?BitVec))
  (= (@bvsize t) w)
  (int_to_bv w (ubv_to_int t))
  t)*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-bv2nat-int2bv.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-bv2nat-int2bv.alethe"

(*(define-cond-rule uf-bv2nat-int2bv-extend ((w Int) (t ?BitVec) (n Int))
  (and (> w (@bvsize t)) (= n (- w (@bvsize t))))
  (int_to_bv w (ubv_to_int t))
  (concat (@bv 0 n) t))*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-bv2nat-int2bv-extend.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-bv2nat-int2bv-extend.alethe"

(*(define-cond-rule uf-bv2nat-int2bv-extract ((w Int) (t ?BitVec) (wm1 Int))
  (and (< w (@bvsize t)) (= wm1 (- w 1)))
  (int_to_bv w (ubv_to_int t))
  (extract wm1 0 t))*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-bv2nat-int2bv-extract.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-bv2nat-int2bv-extract.alethe"

(*(define-rule uf-int2bv-bv2nat ((w Int) (t Int))
  (ubv_to_int (int_to_bv w t))
  (mod_total t (int.pow2 w)))*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-int2bv-bv2nat.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-int2bv-bv2nat.alethe"

(*(define-cond-rule uf-bv2nat-geq-elim ((x ?BitVec) (n Int) (w Int))
  (= w (@bvsize x))
  (>= (ubv_to_int x) n)
  (ite (>= n w) false (ite (< n 0) true (bvuge x (int_to_bv w n)))))*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-bv2nat-geq-elim.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-bv2nat-geq-elim.alethe"

(*(define-rule uf-int2bv-bvult-equiv ((t ?BitVec) (s ?BitVec))
  (bvult t s)
  (< (ubv_to_int t) (ubv_to_int s)))*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-int2bv-bvult-equiv.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-int2bv-bvult-equiv.alethe"

(*(define-rule uf-int2bv-bvule-equiv ((t ?BitVec) (s ?BitVec))
  (bvule t s)
  (<= (ubv_to_int t) (ubv_to_int s)))*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-int2bv-bvule-equiv.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-int2bv-bvule-equiv.alethe"

(*(define-cond-rule uf-sbv-to-int-elim ((t ?BitVec) (wm1 Int) (n Int))
  (and (= wm1 (- (@bvsize t) 1)) (= n (int.pow2 (@bvsize t))))
  (sbv_to_int t)
  (ite (= (extract wm1 wm1 t) (@bv 0 1)) (ubv_to_int t) (- (ubv_to_int t) n)))*)

check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-sbv-to-int-elim.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/uf-sbv-to-int-elim.alethe"

end