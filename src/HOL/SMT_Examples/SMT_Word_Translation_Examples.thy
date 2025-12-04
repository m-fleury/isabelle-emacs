section \<open>Regression test for the encoding of Word Problems into SMT-LIB\<close>

theory SMT_Word_Translation_Examples
  imports "HOL-Library.Word" "HOL.SMT_CVC_Word"
begin

(*None of the goals should contain any nats after encoding unless explicitly stated.*)

declare[[smt_expert_debug_alethe_files="all"]]
declare[[smt_expert_debug_alethe_level=0]]
declare[[smt_nat_as_int=true,smt_trace]]


lemma "(27 :: 4 word) = -5"
  
  by (smt (cvc5))


lemma "Word.Word 0 = (0::5 word)"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= ((_ int_to_bv 5) 0) (_ bv0 5))) :named a0))
\<close>)
  by (smt (cvc5))



end
