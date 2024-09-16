(*
Should not be included in offical repo but contains regression tests until then
*)

theory SMT_Word_Translator_Parser_Test
  imports SMT_Word
begin

declare[[cvc5_options = "--proof-prune-input --proof-format-mode=alethe
  --lang=smt2 --dag-thres=0 "]] (*--proof-granularity=dsl-rewrite*)
declare [[smt_cvc_lethe,smt_verbose,smt_trace,smt_nat_as_int]]
declare[[show_types,show_sorts]]


(*
----------------------------------------------------------------------
-------------------------------constant-------------------------------
----------------------------------------------------------------------
*)

(*

100 \<noteq> 101 

Goal              \<not> (4::3 word) \<noteq> (5::3 word) 
SMT-LIB Problem:  (not (not (= (_ bv4 3) (_ bv5 3))))
Alethe proof:     (not (not (= #b100 #b101)))
Parsed in:        \<not> (4::3 word) \<noteq> (5::3 word)

*)

lemma constant_test_1: "(4::3 word) \<noteq> (5::3 word)"
  apply (smt (cvc5))
  oops

(*
TODO!
000 \<noteq> 000 

Goal               (8::3 word) \<noteq> (0::3 word) 
SMT-LIB Problem:   (not (= (_ bv0 3) (_ bv0 3)))
Alethe proof:      (not (= #b000 #b000))
Parsed in:         (0::3 word) \<noteq> (0::3 word)

*)

lemma constant_test_2: "(8::3 word) = (0::3 word)"
  apply (smt (cvc5))
  oops

(*
----------------------------------------------------------------------
-------------------------------uminus---------------------------------
----------------------------------------------------------------------
*)

(*
----------------------------------------------------------------------
-------------------------------plus-----------------------------------
----------------------------------------------------------------------
*)

(*
----------------------------------------------------------------------
-------------------------------minus----------------------------------
----------------------------------------------------------------------
*)

(*
----------------------------------------------------------------------
-------------------------------times----------------------------------
----------------------------------------------------------------------
*)

(*
----------------------------------------------------------------------
-------------------------------not----------------------------------
----------------------------------------------------------------------
*)

(*
----------------------------------------------------------------------
-------------------------------and----------------------------------
----------------------------------------------------------------------
*)
(*
----------------------------------------------------------------------
-------------------------------or----------------------------------
----------------------------------------------------------------------
*)
(*
----------------------------------------------------------------------
-------------------------------xor----------------------------------
----------------------------------------------------------------------
*)

(*
----------------------------------------------------------------------
-------------------------------push_bit-------------------------------
----------------------------------------------------------------------
*)

(*

0111 \<noteq> 1110 

Goal              push_bit (nat (3::int)) (7::4 word) \<noteq> (8::4 word)
SMT-LIB Problem:  (not (= (bvshl (_ bv7 4) (_ bv3 4)) (_ bv8 4))
Alethe proof:     (not (= (bvshl #b0111 #b0011) #b1000)) 
Parsed in: 

*)

lemma push_bit_test_1: "push_bit 3 (7::4 word) = 8"
  supply[[smt_nat_as_int=true]]
  apply (smt (cvc5))
  oops


(*
----------------------------------------------------------------------
---------------------------------slice----------------------------------
----------------------------------------------------------------------
*)

  value "slice 3 (11::4 word) :: 3 word" (* 1011 \<longrightarrow> 001 *)
  value "slice 3 (11::4 word) :: 2 word" (* 1011 \<longrightarrow> 01 *)
  value "slice 3 (11::4 word) :: 1 word" (* 1011 \<longrightarrow> 1 *)
 
  value "slice 1 (11::4 word) :: 3 word" (* 1011 \<longrightarrow> 101 *)
  value "slice 1 (11::4 word) :: 2 word" (* 1011 \<longrightarrow> 01 *)




(*native*)
lemma push_bit_test_1: "slice 1 (11::4 word) = (5::3 word)"
  supply[[smt_nat_as_int=true]]
  apply (smt (cvc5))
  oops

(*non-native*)
lemma push_bit_test_1: "slice 1 (11::4 word) = (5::2 word)"
  supply[[smt_nat_as_int=true]]
  apply (smt (cvc5))
  oops



(*
----------------------------------------------------------------------
---------------------------------bit----------------------------------
----------------------------------------------------------------------
*)

lemma bit_test_1: "bit (5::3 word) 0" (*101*)
  supply[[smt_nat_as_int=true]]
  apply (smt (cvc5))
  oops

lemma bit_test_1: "\<not>bit (5::3 word) 1" (*101*)
  supply[[smt_nat_as_int=true]]
  apply (smt (cvc5))
  oops

  value "smt_extract (1::nat) (1::nat) (7::3 word)::1 word"
lemma bit_test_1: "bit (7::3 word) 1" (*111*)
  supply[[smt_nat_as_int=true]]
  apply (smt (cvc5))
  oops

  value "take_bit 3 (7::3 word)"
  value "slice 2 (take_bit 3 (7::3 word))::1 word"


(*  

101 ! 0

take_bit yields 011 so it is correctly translated

slice should now 




\<open>lemma bit_smt_extract2': 
"k < size (x::'a::len word) \<Longrightarrow> bit x k = (slice k (take_bit (Suc k) x) = (1::1 word))" 


*)


(*

100 \<noteq> 101 

Goal              
SMT-LIB Problem:  
Alethe proof:     
Parsed in:        

*)

end