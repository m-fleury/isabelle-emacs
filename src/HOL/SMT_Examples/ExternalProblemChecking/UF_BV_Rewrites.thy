(*  Title:      HOL/SMT_Examples/ExternalProblemChecking/UF_BV_Rewrites.thy
    Author:     Hanna Lachnitt, Stanford University
*)

theory UF_BV_Rewrites
  imports HOL.SMT_CVC HOL.SMT_CVC_Word
begin

declare[[smt_trace=true,smt_verbose=true]]

declare[[smt_expert_debug_alethe_level=3]]
declare[[smt_expert_debug_alethe_files="alethe_replay_rare"]]
declare[[rare_rec_mode=1]]

(*uf-bv2nat-int2bv*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-bv2nat-int2bv.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-bv2nat-int2bv.alethe"

(*uf-bv2nat-int2bv-extend*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-bv2nat-int2bv-extend.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-bv2nat-int2bv-extend.alethe"

(*uf-bv2nat-int2bv-extract*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-bv2nat-int2bv-extract.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-bv2nat-int2bv-extract.alethe"

(*uf-int2bv-bv2nat*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-int2bv-bv2nat.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-int2bv-bv2nat.alethe"

(*uf-bv2nat-geq-elim*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-bv2nat-geq-elim.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-bv2nat-geq-elim.alethe"

(*uf-int2bv-bvult-equiv*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-int2bv-bvult-equiv.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-int2bv-bvult-equiv.alethe"

(*uf-int2bv-bvule-equiv*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-int2bv-bvule-equiv.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-int2bv-bvule-equiv.alethe"

(*uf-sbv-to-int-elim*)
check_smt ("cvc5_proof")
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-sbv-to-int-elim.smt2"
  "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/UF_BV_Rewrites/uf-sbv-to-int-elim.alethe"

end
