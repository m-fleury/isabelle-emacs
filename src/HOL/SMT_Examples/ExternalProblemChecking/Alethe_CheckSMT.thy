theory Alethe_CheckSMT
  imports Main

begin 

declare [[smt_trace=false,smt_verbose=false]]
(*declare [[smt_statistics]]*)

(*(* or_neg *)
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/or_neg/1776309183726509767.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/or_neg/1776309183726509767.alethe" 
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/or_neg/1776309184477962081.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/or_neg/1776309184477962081.alethe" 
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/or_neg/1776309184626455221.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/or_neg/1776309184626455221.alethe" 
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/or_neg/1776309184748737531.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/or_neg/1776309184748737531.alethe" 
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/or_neg/1776309184872995788.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/or_neg/1776309184872995788.alethe" 

(* and_pos *)
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/and_pos/1776309182721929989.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/and_pos/1776309182721929989.alethe" 
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/and_pos/1776309183192212150.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/and_pos/1776309183192212150.alethe" 
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/and_pos/1776309184319275756.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/and_pos/1776309184319275756.alethe" 
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/and_pos/1776309184396476070.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/and_pos/1776309184396476070.alethe" 
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/and_pos/1776309184542667460.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/and_pos/1776309184542667460.alethe" 

(* not_or *)
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/not_or/1776309182903737805.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/not_or/1776309182903737805.alethe" 
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/not_or/1776309185320626911.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/not_or/1776309185320626911.alethe" 
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/not_or/1776309185537445774.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/not_or/1776309185537445774.alethe" 
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/not_or/1776309186374601446.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/not_or/1776309186374601446.alethe" 
check_smt "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/not_or/1776309187381950718.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/not_or/1776309187381950718.alethe" 

(* bfun_elim *)
check_smt ("verit") "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/bfun_elim_verit/prob_00190_007175__15921318.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/bfun_elim_verit/prob_00190_007175__15921318.alethe" 
check_smt ("verit") "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/bfun_elim_verit/prob_00262_010473__20210062.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/bfun_elim_verit/prob_00262_010473__20210062.alethe" 
check_smt ("verit") "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/bfun_elim_verit/prob_00262_010473__20324706.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/bfun_elim_verit/prob_00262_010473__20324706.alethe" 
check_smt ("verit") "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/bfun_elim_verit/prob_00284_011539__22022436.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/bfun_elim_verit/prob_00284_011539__22022436.alethe" 
check_smt ("verit") "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/bfun_elim_verit/prob_00284_011539__22121740.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/bfun_elim_verit/prob_00284_011539__22121740.alethe" 
*)

declare [[smt_trace]]
(* declare [[smt_verbose]] *)
(* declare [[smt_debug_arith_verit = true]] *)
check_smt ("verit") "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/verit/errors/bind/prob_00125_005409__32891652.smt2" "~~/src/HOL/SMT_Examples/ExternalProblemChecking/Benchmarks/Alethe_Proof_Rules/verit/errors/bind/prob_00125_005409__32891652.alethe" 


end