section \<open>Examples for the SMT binding\<close>

theory SMT_Examples_Z3_New
imports HOL.SMT_CVC
begin

declare [[smt_trace]]
check_smt ("z3_new") "~~/src/HOL/SMT_Examples/test-proofs/z3/proof1.smt2"
"~~/src/HOL/SMT_Examples/test-proofs/z3/proof1-old.z3"

end