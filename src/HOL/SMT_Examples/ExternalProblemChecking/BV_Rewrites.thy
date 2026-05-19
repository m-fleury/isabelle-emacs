(*  Title:      HOL/SMT_Examples/SMT_Examples_CVC.thy
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University of Freiburg

*)
theory BV_Rewrites
  imports HOL.SMT_CVC HOL.SMT_CVC_Word
begin


declare[[smt_trace=true,smt_verbose=true]]

declare[[smt_expert_debug_alethe_level=0]]
declare[[smt_expert_debug_alethe_files="alethe_replay_rare"]]
declare[[rare_rec_mode=1]]

(* bv-concat-extract-merge *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-concat-extract-merge.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-concat-extract-merge.alethe"

(* bv-extract-extract *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-extract.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-extract.alethe"

(* bv-extract-whole *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-whole.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-whole.alethe"

(* bv-extract-concat-1 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-concat-1.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-concat-1.alethe"

(* bv-extract-concat-2 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-concat-2.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-concat-2.alethe"

(* bv-extract-concat-3 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-concat-3.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-concat-3.alethe"

(* bv-extract-concat-4 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-concat-4.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-concat-4.alethe"

(* bv-eq-extract-elim1 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-eq-extract-elim1.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-eq-extract-elim1.alethe"

(* bv-eq-extract-elim2 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-eq-extract-elim2.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-eq-extract-elim2.alethe"

(* bv-eq-extract-elim3 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-eq-extract-elim3.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-eq-extract-elim3.alethe"

(* bv-extract-not *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-not.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-not.alethe"

(* bv-extract-sign-extend-1 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-sign-extend-1.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-sign-extend-1.alethe"

(* bv-extract-sign-extend-2 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-sign-extend-2.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-sign-extend-2.alethe"

(* bv-extract-sign-extend-3 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-sign-extend-3.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-extract-sign-extend-3.alethe"

(* bv-not-xor *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-not-xor.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-not-xor.alethe"

(* bv-and-simplify-1 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-and-simplify-1.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-and-simplify-1.alethe"

(* bv-and-simplify-2 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-and-simplify-2.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-and-simplify-2.alethe"

(* bv-or-simplify-1 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-or-simplify-1.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-or-simplify-1.alethe"

(* bv-or-simplify-2 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-or-simplify-2.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-or-simplify-2.alethe"

(* bv-xor-simplify-1 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-xor-simplify-1.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-xor-simplify-1.alethe"

(* bv-xor-simplify-2 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-xor-simplify-2.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-xor-simplify-2.alethe"

(* bv-xor-simplify-3 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-xor-simplify-3.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-xor-simplify-3.alethe"

(* bv-ult-add-one *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-ult-add-one.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-ult-add-one.alethe"

(* bv-mult-slt-mult-1 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-mult-slt-mult-1.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-mult-slt-mult-1.alethe"

(* bv-mult-slt-mult-2 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-mult-slt-mult-2.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-mult-slt-mult-2.alethe"

(* bv-commutative-xor *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-commutative-xor.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-commutative-xor.alethe"

(* bv-commutative-comp *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-commutative-comp.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-commutative-comp.alethe"

(* bv-zero-extend-eliminate-0 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-zero-extend-eliminate-0.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-zero-extend-eliminate-0.alethe"

(* bv-sign-extend-eliminate-0 *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-sign-extend-eliminate-0.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-sign-extend-eliminate-0.alethe"

(* bv-not-neq *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-not-neq.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-not-neq.alethe"

(* bv-ult-ones *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-ult-ones.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-ult-ones.alethe"

(* bv-concat-merge-const *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-concat-merge-const.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-concat-merge-const.alethe"

(* bv-commutative-add *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-commutative-add.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-commutative-add.alethe"

(* bv-sub-eliminate *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-sub-eliminate.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-sub-eliminate.alethe"

(* bv-ite-width-one *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-ite-width-one.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-ite-width-one.alethe"

(* bv-ite-width-one-not *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-ite-width-one-not.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-ite-width-one-not.alethe"

(* bv-eq-xor-solve *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-eq-xor-solve.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-eq-xor-solve.alethe"

(* bv-eq-not-solve *)
check_smt ("cvc5_proof")
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-eq-not-solve.smt2"
"~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/BV_Rewrites/bv-eq-not-solve.alethe"

end