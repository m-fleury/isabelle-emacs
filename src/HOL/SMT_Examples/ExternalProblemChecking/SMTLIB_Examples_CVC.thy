(*  Title:      HOL/SMT_Examples/SMT_Examples_CVC.thy
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University of Freiburg

Problems taken from the SMT-LIB release 2024 of non-incremental benchmarks from the theories
QF_UF, QF_LIA, and UF.

Proofs obtained by cvc5 with:

--proof-format-mode=alethe --dump-proofs --produce-proofs --proof-alethe-experimental --proof-alethe-define-skolems --proof-elim-subtypes --full-saturate-quant --no-stats --sat-random-seed=1 --lang=smt2

*)

section \<open>Examples for the (smt (cvc5)) binding\<close>

theory SMTLIB_Examples_CVC
  imports "HOL-CVC.SMT_CVC"
begin

declare[[smt_trace=false,smt_verbose=false]]

check_smt_dir ("cvc5_proof") "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/QF_UF/"

end