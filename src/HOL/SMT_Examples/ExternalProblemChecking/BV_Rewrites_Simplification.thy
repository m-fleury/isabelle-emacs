(*  Title:      HOL/SMT_Examples/BV_Rewrites_Simplification.thy
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University of Freiburg


*)

theory BV_Rewrites_Simplification
  imports HOL.SMT_CVC HOL.SMT_CVC_Word
begin

declare[[smt_trace=true,smt_verbose=true]]

declare[[smt_expert_debug_alethe_level=1]]
declare[[smt_expert_debug_alethe_files="alethe_replay_rare"]]
declare[[rare_rec_mode=1]]

(*bv-ite-equal-children*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-equal-children.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-equal-children.alethe"

(*bv-ite-const-children-1*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-const-children-1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-const-children-1.alethe"

(*bv-ite-const-children-2*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-const-children-2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-const-children-2.alethe"

(*bv-ite-equal-cond-1*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-equal-cond-1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-equal-cond-1.alethe"

(*bv-ite-equal-cond-2*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-equal-cond-2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-equal-cond-2.alethe"

(*bv-ite-equal-cond-3*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-equal-cond-3.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-equal-cond-3.alethe"

(*bv-ite-merge-then-if*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-merge-then-if.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-merge-then-if.alethe"

(*bv-ite-merge-else-if*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-merge-then-if.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-merge-then-if.alethe"

(*bv-ite-merge-then-else*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-merge-then-else.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-merge-then-else.alethe"

(*bv-ite-merge-else-else*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-merge-else-else.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ite-merge-else-else.alethe"

(*bv-shl-by-const-0*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-shl-by-const-0.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-shl-by-const-0.alethe"

(*bv-shl-by-const-1*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-shl-by-const-1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-shl-by-const-1.alethe"

(*bv-shl-by-const-2*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-shl-by-const-2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-shl-by-const-2.alethe"

(*bv-lshr-by-const-0*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-lshr-by-const-0.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-lshr-by-const-0.alethe"

(*bv-lshr-by-const-1*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-lshr-by-const-1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-lshr-by-const-1.alethe"

(*bv-lshr-by-const-2*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-lshr-by-const-2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-lshr-by-const-2.alethe"

(*bv-ashr-by-const-0*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ashr-by-const-0.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ashr-by-const-0.alethe"

(*bv-ashr-by-const-1*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ashr-by-const-1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ashr-by-const-1.alethe"

(*bv-ashr-by-const-2*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ashr-by-const-2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ashr-by-const-2.alethe"

(*bv-and-concat-pullup*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-and-concat-pullup.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-and-concat-pullup.alethe"

(*bv-or-concat-pullup*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-or-concat-pullup.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-or-concat-pullup.alethe"

(*bv-xor-concat-pullup*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-xor-concat-pullup.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-xor-concat-pullup.alethe"

(*bv-and-concat-pullup2*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-and-concat-pullup2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-and-concat-pullup2.alethe"

(*bv-or-concat-pullup2*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-or-concat-pullup2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-or-concat-pullup2.alethe"

(*bv-xor-concat-pullup2*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-xor-concat-pullup2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-xor-concat-pullup2.alethe"

(*bv-and-concat-pullup3*)

(*bv-or-concat-pullup3*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-or-concat-pullup3.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-or-concat-pullup3.alethe"

(*bv-xor-concat-pullup3*)

(*bv-xor-duplicate*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-xor-duplicate.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-xor-duplicate.alethe"

(*bv-xor-ones*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-xor-ones.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-xor-ones.alethe"

(*bv-xor-not*)

(*bv-not-idemp*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-not-idemp.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-not-idemp.alethe"

(*bv-ult-zero-1*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ult-zero-1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ult-zero-1.alethe"

(*bv-ult-zero-2*)

(*bv-ult-self*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ult-self.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ult-self.alethe"

(*bv-lt-self*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-lt-self.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-lt-self.alethe"

(*bv-ule-self*)

(*bv-ule-zero*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ule-zero.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ule-zero.alethe"

(*bv-zero-ule*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ule-max.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ule-max.alethe"

(*bv-sle-self*)

(*bv-ule-max*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ule-max.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ule-max.alethe"

(*bv-not-ult*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-not-ult.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-not-ult.alethe"

(*bv-mult-pow2-1*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-mult-pow2-1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-mult-pow2-1.alethe"

(*bv-mult-pow2-2*)

(*bv-mult-pow2-2b*)

(*bv-extract-mult-leading-bit*)

(*bv-udiv-pow2-not-one*)

(*bv-udiv-zero*)

(*bv-udiv-one*)

(*bv-urem-pow2-not-one*)

(*bv-urem-one*)

(*bv-urem-self*)

(*bv-shl-zero*)

(*bv-lshr-zero*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-lshr-zero.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-lshr-zero.alethe"

(*bv-ashr-zero*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ashr-zero.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ashr-zero.alethe"

(*bv-ugt-urem*)

(*bv-ult-one*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ult-one.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-ult-one.alethe"

(*bv-merge-sign-extend-1*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-merge-sign-extend-1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-merge-sign-extend-1.alethe"

(*bv-merge-sign-extend-2*)

(*bv-sign-extend-eq-const-1*)

(*bv-sign-extend-eq-const-2*)

(*bv-zero-extend-eq-const-1*)

(*bv-zero-extend-eq-const-2*)

(*bv-zero-extend-ult-const-1*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-zero-extend-ult-const-1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-zero-extend-ult-const-1.alethe"

(*bv-zero-extend-ult-const-2*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-zero-extend-ult-const-2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-zero-extend-ult-const-2.alethe"

(*bv-sign-extend-ult-const-1*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-sign-extend-ult-const-1.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-sign-extend-ult-const-1.alethe"

(*bv-sign-extend-ult-const-2*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-sign-extend-ult-const-2.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-sign-extend-ult-const-2.alethe"

(*bv-sign-extend-ult-const-3*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-sign-extend-ult-const-3.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-sign-extend-ult-const-3.alethe"

(*bv-sign-extend-ult-const-4*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-sign-extend-ult-const-4.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites_Simplification/bv-sign-extend-ult-const-4.alethe"



end
