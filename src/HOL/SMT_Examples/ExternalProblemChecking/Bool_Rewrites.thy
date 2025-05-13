(*  Title:      HOL/SMT_Examples/SMT_Examples_CVC.thy
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University of Freiburg


   43 rules in total
   37 rules with test
   6 without test
*)

theory Bool_Rewrites
  imports HOL.SMT_CVC
begin

declare[[smt_trace=false,smt_verbose=false]]

(*(define-rule bool-double-not-elim ((t Bool)) (not (not t)) t))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-double-not-elim.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-double-not-elim.alethe"

(*(define-cond-rule bool-not-true ((t Bool))
  (= t false) (not t) true)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-not-true.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-not-true.alethe"

(*(define-cond-rule bool-not-false ((t Bool))
  (= t true) (not t) false)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-not-false.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-not-false.alethe"

(*(define-rule bool-eq-true ((t Bool)) (= t true) t)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-eq-true.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-eq-true.alethe"

(*(define-rule bool-eq-false ((t Bool)) (= t false) (not t))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-eq-false.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-eq-false.alethe"

declare[[smt_trace,smt_verbose,smt_expert_debug_alethe_files="all",smt_expert_debug_alethe_level=3]]
(*(define-rule bool-eq-nrefl ((x Bool)) (= x (not x)) false)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-eq-nrefl.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-eq-nrefl.alethe"


(*(define-rule bool-impl-false1 ((t Bool)) (=> t false) (not t))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-impl-false1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-impl-false1.alethe"

(*(define-rule bool-impl-false2 ((t Bool)) (=> false t) true)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-impl-false2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-impl-false2.alethe"

(*(define-rule bool-impl-true1 ((t Bool)) (=> t true) true)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-impl-true1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-impl-true1.alethe"

(*(define-rule bool-impl-true2 ((t Bool)) (=> true t) t)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-impl-true2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-impl-true2.alethe"

(*(define-rule bool-impl-elim ((t Bool) (s Bool)) (=> t s) (or (not t) s))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-impl-elim.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-impl-elim.alethe"


(*(define-rule bool-dual-impl-eq ((t Bool) (s Bool)) (and (=> t s) (=> s t)) (= t s))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-dual-impl-eq .smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-dual-impl-eq .alethe"


(*(define-rule* bool-or-flatten ((xs Bool :list) (b1 Bool) (b2 Bool) (ys Bool :list) (zs Bool :list)) (or xs (or b1 b2 ys) zs) (or xs b1 b2 ys zs))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-or-flatten.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-or-flatten.alethe"


(*(define-rule* bool-and-flatten ((xs Bool :list) (b1 Bool) (b2 Bool) (ys Bool :list) (zs Bool :list)) (and xs (and b1 b2 ys) zs) (and xs b1 b2 ys zs))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-and-flatten.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-and-flatten.alethe"


(*(define-rule bool-and-conf ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list)) (and xs w ys (not w) zs) false)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-and-conf.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-and-conf.alethe"

(*(define-rule bool-and-conf2 ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list)) (and xs (not w) ys w zs) false)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-and-conf2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-and-conf2.alethe"

(*(define-rule bool-or-taut ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list)) (or xs w ys (not w) zs) true)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-or-taut.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-or-taut.alethe"

(*(define-rule bool-or-taut2 ((xs Bool :list) (w Bool) (ys Bool :list) (zs Bool :list)) (or xs (not w) ys w zs) true)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-or-taut2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-or-taut2.alethe"


(*(define-rule* bool-or-de-morgan ((x Bool) (y Bool) (zs Bool :list)) 
  (not (or x y zs))
  (not (or y zs))
  (and (not x) _))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-or-de-morgan.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-or-de-morgan.alethe"

(*(define-rule bool-implies-de-morgan ((x Bool) (y Bool))
  (not (=> x y))
  (and x (not y)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-implies-de-morgan.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-implies-de-morgan.alethe"

(*(define-rule* bool-and-de-morgan ((x Bool) (y Bool) (zs Bool :list)) 
  (not (and x y zs))
  (not (and y zs))
  (or (not x) _))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-and-de-morgan.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-and-de-morgan.alethe"


(*(define-rule* bool-or-and-distrib ((y1 Bool) (y2 Bool) (ys Bool :list) (z1 Bool) (zs Bool :list))
  (or (and y1 y2 ys) z1 zs)
  (or (and y2 ys) z1 zs)
  (and (or y1 z1 zs) _))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-or-and-distrib.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-or-and-distrib.alethe"


(*(define-rule* bool-implies-or-distrib ((y1 Bool) (y2 Bool) (ys Bool :list) (z Bool))
  (=> (or y1 y2 ys) z)
  (=> (or y2 ys) z)
  (and (=> y1 z) _))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-implies-or-distrib.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-implies-or-distrib.alethe"


(*(define-rule bool-xor-refl ((x Bool)) (xor x x) false)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-xor-refl.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-xor-refl.alethe"

(*(define-rule bool-xor-nrefl ((x Bool)) (xor x (not x)) true)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-xor-nrefl.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-xor-nrefl.alethe"

(*(define-rule bool-xor-false ((x Bool)) (xor x false) x)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-xor-false.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-xor-false.alethe"

(*(define-rule bool-xor-true ((x Bool)) (xor x true) (not x))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-xor-true.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-xor-true.alethe"

(*(define-rule bool-xor-comm ((x Bool) (y Bool)) (xor x y) (xor y x))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-xor-comm.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-xor-comm.alethe"

(*(define-rule bool-xor-elim ((x Bool) (y Bool)) (xor x y) (= (not x) y))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-xor-elim.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-xor-elim.alethe"

(*(define-rule bool-not-xor-elim ((x Bool) (y Bool)) (not (xor x y)) (= x y))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-not-xor-elim.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-not-xor-elim.alethe"


(*(define-rule bool-not-eq-elim1 ((x Bool) (y Bool)) (not (= x y)) (= (not x) y))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-not-eq-elim1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-not-eq-elim1.alethe"

(*(define-rule bool-not-eq-elim2 ((x Bool) (y Bool)) (not (= x y)) (= x (not y)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-not-eq-elim2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-not-eq-elim2.alethe"


(*(define-cond-rule ite-neg-branch ((c Bool) (x Bool) (y Bool)) (= (not y) x) (ite c x y) (= c x))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-neg-branch.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-neg-branch.alethe"


(*(define-rule ite-then-true ((c Bool) (x Bool)) (ite c true x) (or c x))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-then-true.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-then-true.alethe"

(*(define-rule ite-else-false ((c Bool) (x Bool)) (ite c x false) (and c x))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-else-false.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-else-false.alethe"

(*(define-rule ite-then-false ((c Bool) (x Bool)) (ite c false x) (and (not c) x))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-then-false.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-then-false.alethe"

(*(define-rule ite-else-true ((c Bool) (x Bool)) (ite c x true) (or (not c) x))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-else-true.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-else-true.alethe"


(*(define-rule ite-then-lookahead-self ((c Bool) (x Bool)) (ite c c x) (ite c true x))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-then-lookahead-self.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-then-lookahead-self.alethe"

(*(define-rule ite-else-lookahead-self ((c Bool) (x Bool)) (ite c x c) (ite c x false))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-else-lookahead-self.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-else-lookahead-self.alethe"


(*(define-rule ite-then-lookahead-not-self ((c Bool) (x Bool)) (ite c (not c) x) (ite c false x))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-then-lookahead-not-self.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-then-lookahead-not-self.alethe"

(*(define-rule ite-else-lookahead-not-self ((c Bool) (x Bool)) (ite c x (not c)) (ite c x true))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-else-lookahead-not-self.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-else-lookahead-not-self.alethe"


(*(define-rule ite-expand ((c Bool) (x Bool) (y Bool)) (ite c x y) (and (or (not c) x) (or c y)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-expand.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/ite-expand.alethe"


(*(define-rule bool-not-ite-elim ((c Bool) (x Bool) (y Bool)) (not (ite c x y)) (ite c (not x) (not y)))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-not-ite-elim.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Bool_Rewrites/bool-not-ite-elim.alethe"



end