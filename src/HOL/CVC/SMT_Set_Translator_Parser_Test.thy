theory SMT_Set_Translator_Parser_Test
  imports SMT_CVC
begin

declare[[smt_nat_as_int=true,smt_trace=true,smt_verbose=true,smt_debug_verit]]
declare[[cvc5_options = "--proof-prune-input --proof-format-mode=alethe
  --lang=smt2 --dag-thres=0 --proof-granularity=dsl-rewrite"]]
declare[[native_set=true]]
declare[[show_types,show_sorts]]

(*Test set types, insert and bot*)

lemma "{True,False} = ({True,False}::bool set)"
  apply (smt (cvc5))

lemma "{True,False,True} = ({True,False,True}::bool set)"
  apply (smt (cvc5))

lemma "{1::int,4} = {4,1}"
  by (smt (cvc5))

(*Test card*)

lemma "card {1::int,4} = 2"
  apply (smt (cvc5))

lemma "card {True::bool,False,True} = 2"
  apply (smt (cvc5))

lemma "card ({}::int set) = 0"
  apply (smt (cvc5))

lemma "card ({}::'a set) = 0"
  apply (smt (cvc5))

(*Union*)

lemma "{1::int,4} \<union> {1,4} = {1,4}"
  apply (smt (cvc5))

(*Intersection*)


lemma "{1::int,4} \<inter> {1,4} = {1,4}"
  apply (smt (cvc5))

lemma "{1::int,4} \<inter> {2,3} = {}"
  apply (smt (cvc5))

lemma "{1::int,4} \<inter> {4} = {4}"
  apply (smt (cvc5))


(*Minus*)


lemma "{1::int,4} - {4} = {1}"
  apply (smt (cvc5))





end