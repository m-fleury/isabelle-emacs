(*
Should not be included in offical repo but contains regression tests until then
*)

theory SMT_Word_Translator_Parser_Test
  imports SMT_CVC_Word
begin

declare[[cvc5_options = "--proof-prune-input --proof-format-mode=alethe
  --lang=smt2 --dag-thres=0 --proof-granularity=dsl-rewrite"]]
declare [[smt_cvc_lethe,smt_verbose,smt_trace,smt_nat_as_int]]
declare[[show_types,show_sorts]]


(*

010 ++ 11 = 01011

Goal              word_cat (2::3 word) (3::2 word) \<noteq> (11::5 word)
SMT-LIB Problem:  (not (= (concat (_ bv2 3) (_ bv3 2)) (_ bv11 5)))
Alethe proof:      (not (= (concat #b010 #b11) #b01011))
Parsed in:        word_cat (2::3 word) (3::2 word) \<noteq> (11::5 word)

*)

lemma concat_test: "word_cat (2::3 word) (3::2 word) = (11::5 word)"
  by (smt (cvc5))
  




end