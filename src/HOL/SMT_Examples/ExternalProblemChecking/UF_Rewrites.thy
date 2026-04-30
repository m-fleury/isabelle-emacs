(*  Title:      HOL/SMT_Examples/SMT_Examples_CVC.thy
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University of Freiburg
*)

theory UF_Rewrites
    imports HOL.SMT_CVC HOL.Real
begin

declare[[rare_rec_mode=1]]

declare[[smt_trace=false,smt_verbose=false]]

check_smt_dir ("cvc5_proof") "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_Rewrites/"

declare[[smt_trace=true,smt_verbose=true]]

declare[[smt_expert_debug_alethe_level=3]]
declare[[smt_expert_debug_alethe_files="alethe_replay_rare"]]

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

end