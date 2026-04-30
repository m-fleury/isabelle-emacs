(*  Title:      HOL/SMT_Examples/SMT_Examples/ExternalProblemChecking/Builtin_Rewrites.thy
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University of Freiburg
*)

theory Builtin_Rewrites
    imports HOL.SMT_CVC HOL.Real
begin

declare[[rare_rec_mode=1]]

declare[[smt_trace=false,smt_verbose=false]]

check_smt_dir ("cvc5_proof") "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/"

declare[[smt_trace=true,smt_verbose=true]]

declare[[smt_expert_debug_alethe_level=3]]
declare[[smt_expert_debug_alethe_files="alethe_replay_rare"]]

(*(define-rule ite-true-cond ((x ?) (y ?)) (ite true x y) x)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-true-cond.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-true-cond.alethe"

(*(define-rule ite-false-cond ((x ?) (y ?)) (ite false x y) y)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-false-cond.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-false-cond.alethe"

(*(define-rule ite-not-cond ((c Bool) (x ?) (y ?)) (ite (not c) x y) (ite c y x))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-not-cond.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-not-cond.alethe"

(*(define-rule ite-eq-branch ((c Bool) (x ?)) (ite c x x) x)*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-eq-branch.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-eq-branch.alethe"

(*(define-rule ite-then-lookahead ((c Bool) (x ?) (y ?) (z ?)) (ite c (ite c x y) z) (ite c x z))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-then-lookahead.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-then-lookahead.alethe"

(*(define-rule ite-else-lookahead ((c Bool) (x ?) (y ?) (z ?)) (ite c x (ite c y z)) (ite c x z))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-else-lookahead.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-else-lookahead.alethe"

(*(define-rule ite-then-neg-lookahead ((c Bool) (x ?) (y ?) (z ?)) (ite c (ite (not c) x y) z) (ite c y z))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-then-neg-lookahead.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-then-neg-lookahead.alethe"

(*(define-rule ite-else-neg-lookahead ((c Bool) (x ?) (y ?) (z ?)) (ite c x (ite (not c) y z)) (ite c x y))*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-else-neg-lookahead.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Builtin_Rewrites/ite-else-neg-lookahead.alethe"



end