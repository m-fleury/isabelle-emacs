(*
Should not be included in offical repo but contains regression tests until then
*)

theory SMT_CVC_Word_Translator_Parser_Test
  imports SMT_CVC_Word
begin

declare[[cvc5_options = "--proof-prune-input --proof-format-mode=alethe
  --lang=smt2 --dag-thres=0 --proof-granularity=dsl-rewrite"]]
declare [[smt_cvc_lethe,smt_verbose,smt_trace,smt_nat_as_int]]
declare[[show_types,show_sorts]]


(*
----------------------------------------------------------------------
-------------------------------word_cat-------------------------------
----------------------------------------------------------------------
*)

(*

010 ++ 11 = 01011

Goal              word_cat (2::3 word) (3::2 word) \<noteq> (11::5 word)
SMT-LIB Problem:  (not (= (concat (_ bv2 3) (_ bv3 2)) (_ bv11 5)))
Alethe proof:     (not (= (concat #b010 #b11) #b01011))
Parsed in:        word_cat (2::3 word) (3::2 word) \<noteq> (11::5 word)

*)

lemma concat_test1: "word_cat (2::3 word) (3::2 word) = (11::5 word)"
  by (smt (cvc5))

(*

If bit-widths of the arguments don't sum up to the bit-width of the whole term we expect word_cat
to be uninterpreted for now:

*)


lemma concat_test_: "word_cat (2::3 word) (3::2 word) = (11::4 word)"
  apply (smt (cvc5))
  oops

lemma concat_test: "word_cat (2::3 word) (3::2 word) = (11::6 word)"
  apply (smt (cvc5))
  oops




(*

56 + 38 = 94
94 mod 2^

1011110
100110

Goal              word_cat (2::3 word) (3::2 word) \<noteq> (11::5 word)
SMT-LIB Problem:  (not (= (concat (_ bv2 3) (_ bv3 2)) (_ bv11 5)))
Alethe proof:      (not (= (concat #b010 #b11) #b01011))
Parsed in:        word_cat (2::3 word) (3::2 word) \<noteq> (11::5 word)


14 + 3 = 17 \<longrightarrow> 17 mod 2^4 = 1

   1110
+  0011
----------
   0001
*)
lemma plus_test: "(56::8 word) + (38::8 word) = 94"
  by (smt (cvc5))

lemma plus_test_overflow: "(14::4 word) + (3::4 word) = 1"
  by (smt (cvc5))











end