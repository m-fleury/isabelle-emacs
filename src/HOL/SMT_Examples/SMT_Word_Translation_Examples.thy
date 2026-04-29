section \<open>Regression test for the encoding of Word Problems into SMT-LIB\<close>

theory SMT_Word_Translation_Examples
  imports "HOL-Library.Word" "HOL.SMT_CVC_Word"
begin

(*None of the goals should contain any nats after encoding unless explicitly stated.*)
(*TODO: why is the logic AUFBVLIRAFS*)
declare[[smt_expert_debug_alethe_files="smt_normalize"]]
declare[[smt_expert_debug_alethe_level=3]]
declare[[smt_nat_as_int=true,smt_trace]]

section \<open>Bit-vector lengths\<close>

text \<open>LENGTH is evaluated during normalization if it is a concrete value.\<close>

lemma "LENGTH(64) = 64"
  apply (test_smt_translate 
\<open>
(set-logic AUFLIRA)
(assert (! (not (= 64 64)) :named a0))
\<close>)  
  by (smt (cvc5))


section \<open>Bit-vector numerals\<close>

text \<open>Words are normally encoded as Bit-vectors.\<close>

lemma "(169 :: 8 word) = 169"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (_ bv169 8) (_ bv169 8))) :named a0))
\<close>)  
  by (smt (cvc5))

text \<open>Overflows should be normalized before generating the SMT-LIB problem.\<close>

lemma "(1705 :: 8 word) = 169"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (_ bv169 8) (_ bv169 8))) :named a0))
\<close>)  
  by (smt (cvc5))

text \<open>Unary minus is translated into bvneg\<close>

lemma "(- 169 :: 8 word) = 87"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (bvneg (_ bv169 8)) (_ bv87 8))) :named a0))
\<close>)
  by (smt (cvc5))

text \<open>-- is translated to bvneg bvneg (this used to be broken)\<close>

lemma "-(- 2 :: 8 word) = 2"
  apply (test_smt_translate
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (bvneg (bvneg (_ bv2 8))) (_ bv2 8))) :named a0))
\<close>)
  by (smt (cvc5))


section \<open>Ordering\<close>

text \<open>\<le> is translated into bvule.\<close>

lemma "(42 :: 8 word) \<le> 43"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (bvule (_ bv42 8) (_ bv43 8))) :named a0))
\<close>)
  by (smt (cvc5))

text \<open>< is translated into bvult.\<close>

lemma "(42 :: 8 word) < 43"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (bvult (_ bv42 8) (_ bv43 8))) :named a0))
\<close>)
  by (smt (cvc5))

text \<open>\<le>s is translated into bvsle.\<close>

lemma "(42 :: 8 word) \<le>s 44"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (bvsle (_ bv42 8) (_ bv44 8))) :named a0))
\<close>)
  by (smt (cvc5))

text \<open><s is translated into bvslt.\<close>

lemma "(42 :: 8 word) <s 44"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (bvslt (_ bv42 8) (_ bv44 8))) :named a0))
\<close>)
  by (smt (cvc5))


section \<open>Bitwise operators\<close>

context
  includes bit_operations_syntax
begin

text \<open>NOT is translated into bvnot.\<close>

lemma "(NOT (- 42 :: 32 word)) = 41"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (bvnot (bvneg (_ bv42 32))) (_ bv41 32))) :named a0))
\<close>)
  by (smt (cvc5))

text \<open>AND is translated into bvand.\<close>

lemma "((41::32 word) AND (42 :: 32 word)) = 40"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (bvand (_ bv41 32) (_ bv42 32)) (_ bv40 32))) :named a0))
\<close>)
  by (smt (cvc5))

text \<open>OR is translated into bvor.\<close>

lemma "((41::32 word) OR (42 :: 32 word)) = 43"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (bvor (_ bv41 32) (_ bv42 32)) (_ bv43 32))) :named a0))
\<close>)
  by (smt (cvc5))

text \<open>XOR is translated into bvxor.\<close>

lemma "((41::32 word) XOR (42 :: 32 word)) = 3"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (bvxor (_ bv41 32) (_ bv42 32)) (_ bv3 32))) :named a0))
\<close>)
  by (smt (cvc5))

end

section \<open>Basic operators\<close>

text \<open>push_bit is translated into bvshl. If the amount of the shift is a constant it is directly
transformed into a bit-vector. \<close>

lemma "push_bit 3 (1705 :: 32 word) = 13640"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (bvshl (_ bv1705 32) (_ bv3 32)) (_ bv13640 32))) :named a0))
(assert (! (<= 0 3) :named a1))
\<close>)
  by (smt (cvc5))

lemma "push_bit (Suc 0) (1705 :: 32 word) = 3410"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (bvshl (_ bv1705 32) ((_ int_to_bv 32) (ite (<= 0 (+ 0 1)) (+ 0 1) 0))) (_ bv3410 32))) :named a0))
(assert (! (<= 0 (ite (<= 0 (+ 0 1)) (+ 0 1) 0)) :named a1))
\<close>)
  by (smt (cvc5))

lemma "push_bit x (1705 :: 32 word) = 13640"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (= (bvshl (_ bv1705 32) ((_ int_to_bv 32) lift_x$)) (_ bv13640 32)))) :named a0))
(assert (! (and (<= 0 lift_x$) (<= 0 lift_x$)) :named a1))
\<close>)
  by (smt (cvc5))


text \<open>drop_bit is translated into bvshr\<close>

lemma "drop_bit 3 (1705 :: 32 word) = 213"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (bvlshr (_ bv1705 32) (_ bv3 32)) (_ bv213 32))) :named a0))
(assert (! (<= 0 3) :named a1))
\<close>)
  by (smt (cvc5))

text \<open>take_bit is translated into a combination of left and right shifts\<close>

lemma "take_bit 3 (1705 :: 32 word) = 1"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (bvsub (_ bv1705 32) (bvshl (bvlshr (_ bv1705 32) (_ bv3 32)) (_ bv3 32))) (_ bv1 32))) :named a0))
(assert (! (<= 0 3) :named a1))
\<close>)
  by (smt (cvc5))

text \<open>+ is translated into bvadd.\<close>

lemma "1 + 3 = (4::5 word)"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (bvadd (_ bv1 5) (_ bv3 5)) (_ bv4 5))) :named a0))
\<close>)
  by (smt (cvc5))


section \<open>Casts\<close>

text \<open>Word.Word and word_of_int are translated into int_to_bv.\<close>

lemma "Word.Word 8 = (8::5 word)"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= ((_ int_to_bv 5) 8) (_ bv8 5))) :named a0))
\<close>)
  by (smt (cvc5))

text \<open>of_int is translated into int_to_bv as well if it returns a bit-vector.\<close>

lemma "of_int 8 = (8::5 word)"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= ((_ int_to_bv 5) 8) (_ bv8 5))) :named a0))
\<close>)
  by (smt (cvc5))



section \<open>Other operators\<close>

text \<open>smt_extract is not used by the users but internally very important so just in case\<close>

lemma "(smt_extract 2 0 (4::3 word) :: 3 word) = (4::3 word)"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= ((_ extract 2 0) (_ bv4 3)) (_ bv4 3))) :named a0))
(assert (! (<= 0 0) :named a1))
(assert (! (<= 0 2) :named a2))
\<close>)
  by (smt (cvc5))

























lemma eee: "k < size (x::'a::len word) \<Longrightarrow>  bit (x::'a word) k \<equiv> (smt_extract k k x = (1:: 1 word))"
  sorry


ML \<open>

val simplify_norm_table = [
  ("Bit_Operations.semiring_bits_class.bit",(NONE,([@{thm eee}],SOME[] )))

]


val _ = fold SMT_Normalize.add_simplify_ops_tab (simplify_norm_table)
    |> Theory.setup o  Context.theory_map
\<close>





(*
bit w n is translated into (= ((_ extract n n) w) #b1) if n < size w.

This translation is tricky because of the condition. We can lift bit to bit_lift during normalization.
Then, during translation we print extract but when parsing it in we cannot parse it back into bit_lift.
Thus, we don't translate to extract but 
*)
  
lemma "bit (1705 :: 16 word) 3"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= ((_ extract 3 3) (_ bv1705 16)) (_ bv1 1))) :named a0))
(assert (! (<= 0 3) :named a1))
\<close>) supply[[smt_trace]]
  by (smt (cvc5))






This goal is translated into the assertion:

0 \<le> (lift_x::int) \<and> push_bit_lift lift_x 0 \<noteq> 0

Before being encoded into the SMT-LIB problem shown below (which introduces the int_to_bv cast).

The important part for this examination being:  (bvshl (_ bv0 32) ((_ int_to_bv 32) lift_x$)) 

When it is parsed back in should it become
  \<not> push_bit (nat lift_x) 0 = 0
or
  \<not> push_bit (unat (nat2bv lift_x)) 0 = 0
?

What if it actually is (bvshl (_ bv0 32) ((_ int_to_bv 32) x$)) where x is an int (external proofs etc.), how do we distinguish.
















Then, we
can either transform that to push_bit_lift or transform push_bit_lift to it? I think there was something
wrong with the latter. Probably that when we don't want to do the nat lifting it then gives issues.
*)

lemma "push_bit (3::nat) (0 :: 32 word) = 0"
  supply[[smt_nat_as_int=false]]
  apply (smt (cvc5)) (*TODO This should not happen with the flag set to false*)



lemma "push_bit x (0 :: 32 word) = 0"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (= (bvshl (_ bv0 32) ((_ int_to_bv 32) lift_x$)) (_ bv0 32)))) :named a0))
(assert (! (and (<= 0 lift_x$) (<= 0 lift_x$)) :named a1))
\<close>)
  by (smt (cvc5))
(*SMT: Goal: "__normalized_input"
       assumptions:
         0 \<le> (lift_x::int) \<and> push_bit_lift lift_x 0 \<noteq> 0
       proposition:
         0 \<le> (lift_x::int) \<and> \<not> push_bit (nat (of_int lift_x)) 0 = 0 *)


(*
drop_bit is translated into bvshr
For a nat constant, the constant is transformed into a word
For a word variable with a nat cast the cast is removed  \<Longrightarrow> TODO
Otherwise, we add a cast
*)
lemma "drop_bit 3 (1705 :: 16 word) = 213"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= (bvlshr (_ bv1705 16) (_ bv3 16)) (_ bv213 16))) :named a0))
(assert (! (<= 0 3) :named a1))
\<close>)
  by (smt (cvc5))

lemma "drop_bit x (0 :: 16 word) = 0"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(declare-fun lift_x$ () Int)
(assert (! (and (<= 0 lift_x$) (not (= (bvlshr (_ bv0 16) ((_ int_to_bv 16) lift_x$)) (_ bv0 16)))) :named a0))
(assert (! (and (<= 0 lift_x$) (<= 0 lift_x$)) :named a1))
\<close>)
  by (smt (cvc5))



end












lemma "Word.Word 0 = (0::5 word)"
  apply (test_smt_translate 
\<open>
(set-logic AUFBVLIRAFS)
(assert (! (not (= ((_ int_to_bv 5) 0) (_ bv0 5))) :named a0))
\<close>)
  by (smt (cvc5))



end
