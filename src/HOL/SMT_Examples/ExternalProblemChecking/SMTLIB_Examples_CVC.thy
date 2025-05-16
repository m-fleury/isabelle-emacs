(*  Title:      HOL/SMT_Examples/SMT_Examples_CVC.thy
    Author:     Hanna Lachnitt, Stanford University
    Author:     Mathias Fleury, University of Freiburg

Problems taken from the SMT-LIB release 2024 of non-incremental benchmarks from the theories
QF_UF, QF_LIA, and UF.

Proofs obtained by cvc5 with:

--proof-format-mode=alethe --dump-proofs --produce-proofs --proof-alethe-define-skolems --proof-elim-subtypes --full-saturate-quant --no-stats --sat-random-seed=1 --lang=smt2

*)

section \<open>Examples for the (smt (cvc5)) binding\<close>

theory SMTLIB_Examples_CVC
  imports "HOL-CVC.SMT_CVC"
begin

(*
Bool_Rewrites:    			38/43
Builtin_Rewrites:			7/8
Arith_Rewrites:			        26/48
UF_Rewrites:				6/13
BV_Rewrites_Simplification:             18/70


*)



end
