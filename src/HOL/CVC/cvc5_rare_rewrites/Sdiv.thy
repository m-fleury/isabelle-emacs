theory Sdiv
imports BV_Rewrites
begin

named_theorems rewrite_bv_sdiv_eliminate \<open>automatically_generated\<close>

lemma h1: "bit (smt_extract i i x) 0 = bit x i"
  by (metis add_0 bit_imp_le_length bit_smt_extract lessI test_bit_1)
declare[[show_types]]
declare[[show_sorts]]

lemma h2: "i < size x \<Longrightarrow> (smt_extract i i x = (1::1 word)) = bit x i"
  by (metis one_word_def smt_extract_bit zero_neq_one)



lemma h3a: "bit x (LENGTH('a)-1) \<Longrightarrow> uint (x ::'a::len word) = 2^(LENGTH('a)-1) + uint (take_bit (LENGTH('a)-1) x)"
  apply transfer
  apply simp           
  using take_bit_Suc_from_most[of "LENGTH('a)-1" ]
  by simp


lemma h3b: "\<not>bit x (LENGTH('a)-1) \<Longrightarrow> uint (x ::'a::len word) =  uint (take_bit (LENGTH('a)-1) x)"
  using take_bit_Suc_from_most[of "LENGTH('a)-1" ]
  by (metis (no_types, opaque_lifting) One_nat_def bits_ident cancel_comm_monoid_add_class.diff_cancel drop_bit_eq_zero_iff_not_bit_last take_bit_0 take_bit_length_eq take_bit_push_bit)

lemma h3c: "uint (x ::'a::len word) = 2^(LENGTH('a)-1) * of_bool (bit x (LENGTH('a::len) - (1::nat))) +  uint (take_bit (LENGTH('a)-1) x)"
  using take_bit_Suc_from_most[of "LENGTH('a)-1" ]
  by (simp add: h3a h3b)

value "word_of_int 1 :: 2 word"
   
lemma h4: "word_of_int (not (mask a)) = - (2 ^ a)"
  unfolding not_eq_complement mask_eq_exp_minus_1
  by simp

lemma h4b: "bit x (LENGTH('a)-1) \<Longrightarrow> uint (x ::'a::len word) = - (not (mask (LENGTH('a)-1))) + uint (take_bit (LENGTH('a)-1) x)"
  by (simp add: h3a mask_eq_exp_minus_1 minus_eq_not_plus_1)


lemma h5: " (not (mask (nat (int n - (1::int))))) =
     (- ((2::int) ^ (n - (1::nat))))"
  unfolding mask_eq_exp_minus_1 minus_eq_not_minus_1
  by simp



lemma h6: "a = c \<Longrightarrow> a div b = c div b"
  by simp



value "take_bit 3 (11::2 word)"
value "bit (11::4 word) 2"


lemma h7:
"take_bit (nat (int LENGTH('a::len) - (1::int))) (uint (x::'a::len word)) + - ((2::int) ^ nat (int LENGTH('a::len) - (1::int))) =
    or (take_bit (nat (int LENGTH('a::len) - (1::int))) (uint x)) (- ((2::int) ^ nat (int LENGTH('a::len) - (1::int))))"
proof-
  have "(\<And>n::nat.
        \<not> bit (take_bit (nat (int LENGTH('a::len) - (1::int))) (uint (x::'a::len word))) n \<or>
        \<not> bit (- ((2::int) ^ nat (int LENGTH('a::len) - (1::int)))) n)"
    by (metis bit_minus_1_iff bit_not_iff bit_take_bit_iff h5 take_bit_minus_one_eq_mask)
  then show ?thesis 
    using disjunctive_add by blast
qed



lemma h8: "(b::int) \<noteq> (0::int) \<Longrightarrow> a mod b = (0::int) \<Longrightarrow> - (a div b) = - (a::int) div b"
  using zdiv_zminus1_eq_if by presburger
 


(*
  (take_bit (nat (int LENGTH('a) - (1::int))) (uint x) - (2::int) ^ nat (int LENGTH('a) - (1::int))) div
    take_bit (nat (int LENGTH('a) - (1::int))) (uint y) =
    - (take_bit LENGTH('a) (- ((2::int) ^ nat (int LENGTH('a) - (1::int))) - take_bit (nat (int LENGTH('a) - (1::int))) (uint x)) div
       take_bit (nat (int LENGTH('a) - (1::int))) (uint y))


(take_bit (nat (int LENGTH('a) - (1::int))) (uint x) - (2::int) ^ nat (int LENGTH('a) - (1::int))) div
    take_bit (nat (int LENGTH('a) - (1::int))) (uint y) =
    - take_bit LENGTH('a) (- ((2::int) ^ nat (int LENGTH('a) - (1::int))) - take_bit (nat (int LENGTH('a) - (1::int))) (uint x)) div
    take_bit (nat (int LENGTH('a) - (1::int))) (uint y)
*)


(*  
   or m
      n
 div
    take_bit (nat (int LENGTH('a) - (1::int))) (uint y) 



   - (take_bit LENGTH('a) n - m)
 div
    take_bit (nat (int LENGTH('a) - (1::int))) (uint y))


*)

lemma h10: 
"\<not> bit y (nat (int (size y) - (1::int))) \<Longrightarrow> 
take_bit (LENGTH('a)) (uint (y::'a::len word)) 
= take_bit (LENGTH('a) - Suc (0::nat)) (uint (y::'a::len word)) 
"
  by (metis One_nat_def h3b nat_minus_as_int of_nat_1 signed_ucast_eq sint_uint uint_sint unsigned_take_bit_eq unsigned_ucast_eq word_size)

lemma h11: 
"\<not> bit y (nat (int (size y) - (1::int))) \<Longrightarrow> 
(uint (y::'a::len word)) 
= take_bit (LENGTH('a) - Suc (0::nat)) (uint (y::'a::len word)) 
"
  by (metis One_nat_def h3b nat_minus_as_int of_nat_1 signed_ucast_eq sint_uint uint_sint unsigned_take_bit_eq unsigned_ucast_eq word_size)

value "-(1::4 word)"

value "mask 4 :: 4 word"
value "- ((2::4 word) ^ 3)"
value "- ((2::5 word) ^ 4)"

lemma h123:
"not (mask (LENGTH('a))) = (0::'a::len word)"
  by fastforce

lemma h123b:
"LENGTH('a) > 0 \<longrightarrow> not (mask (LENGTH('a)-1)) = (2^(LENGTH('a)-1)::'a::len word)"
  unfolding mask_eq_exp_minus_1
  apply simp
  unfolding not_eq_complement
  apply simp
 using double_eq_zero_iff by blast

value "not (mask (2 - Suc (0::nat))::int)"
value "not (mask (4 - Suc (0::nat))::int)"
value "-(2^(2)::int)"
value "(-10::4 word)"

value "take_bit (LENGTH(Enum.finite_2) - Suc (0::nat)) (uint (2::Enum.finite_2 word)) + not (mask (LENGTH(Enum.finite_2) - Suc (0::nat)))"


lemma h123c:
"n > 0 \<Longrightarrow> not (mask (n-Suc (0::nat))::int) = -(2^(n-1))"
  by (simp add: minus_exp_eq_not_mask)


lemma h9: 
"bit y (nat (int (size y) - (1::int))) \<Longrightarrow> 
take_bit (LENGTH('a)) (uint (y::'a::len word)) 
= 2^(LENGTH('a)-1) + take_bit (LENGTH('a) - Suc (0::nat)) (uint (y::'a::len word)) 
"
  by (metis (no_types, opaque_lifting) One_nat_def h3a nat_minus_as_int of_nat_1 signed_ucast_eq sint_uint uint_sint unsigned_take_bit_eq unsigned_ucast_eq word_size)  

value "take_bit 2 (uint (2::2 word))"


lemma h9bc:
"bit y (nat (int (size y) - (1::int))) \<Longrightarrow>LENGTH('a) > 1 \<Longrightarrow> y > 0 \<Longrightarrow>
take_bit (LENGTH('a) - Suc (0::nat)) (uint (y::'a::len word))  - ((2::int) ^ (LENGTH('a)-1))
= ( ((take_bit (LENGTH('a)) (sint (-y::'a::len word))) + 1))"
  oops





lemma h9b:
"bit y (nat (int (size y) - (1::int))) \<Longrightarrow> 
(take_bit (LENGTH('a) - Suc (0::nat)) (uint y) + - ((2::int) ^ (LENGTH('a) - (1::nat)))) =
take_bit (LENGTH('a)) (uint (y::'a::len word)) - ((2::int) ^ LENGTH('a))"
proof-
  assume a0: "bit y (nat (int (size y) - (1::int)))" and a1: "size y > 0"
  have "(take_bit (LENGTH('a) - Suc (0::nat)) (uint y) + - ((2::int) ^ (LENGTH('a) - (1::nat)))) =
take_bit (LENGTH('a)) (uint (y::'a::len word)) - ((2::int) ^ LENGTH('a))"
    using a0
  apply (simp add: h9)
  by (metis One_nat_def Suc_pred' len_gt_0 power_Suc)
  then have "(take_bit (LENGTH('a) - Suc (0::nat)) (uint y) + - ((2::int) ^ (LENGTH('a) - (1::nat)))) =
take_bit (LENGTH('a)-1) (uint (y::'a::len word))"
    



    value "(-3::int) mod 4"
    value "(-4::int) mod 4"



(* x::'a::len word = \<guillemotleft>(3::int)\<guillemotright>
    y::'a::len word = \<guillemotleft>- (4::int)\<guillemotright>
"'a::len" = 9:
*)

    value "- (- (3::9 word) div (-4))"

    value "word_of_int (signed_take_bit (9 - Suc (0::nat)) (uint (3::9 word))
 div signed_take_bit (9 - Suc (0::nat)) (uint (-4::9 word)))::9 word"

    value "take_bit 9 (- uint (3::9 word)) mod uint (-4::9 word) "




    value
word_of_int (signed_take_bit (LENGTH('a) - Suc (0::nat)) (uint x) div signed_take_bit (LENGTH('a) - Suc (0::nat)) (uint y)) =
    - (- x div y)


(*(define-rule bv-sdiv-eliminate ((x ?BitVec) (y ?BitVec))
 (def (n (bvsize x)) (xLt0 (= (extract (- n 1) (- n 1) x) (bv 1 1))) (yLt0 (= (extract (- n 1) (- n 1) y) (bv 1 1))) 
(rUdiv (bvudiv (ite xLt0 (bvneg x) x) (ite yLt0 (bvneg y) y))) ) (bvsdiv x y) (ite (xor xLt0 yLt0) (bvneg rUdiv) rUdiv))
*)


declare [[show_types]]
declare [[show_sorts]]

lemma f0:
  assumes "a = b"
  shows "sint a = sint b"
  using assms by blast

lemma [rewrite_bv_sdiv_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  assumes "LENGTH('a) > 1" "int LENGTH('a) > 0"
  shows "x sdiv y =
   (if (smt_extract (nat (int (size x) - (1::int)))
         (nat (int (size x) - (1::int))) x =
        (Word.Word (1::int)::1 word)) [+]
       (smt_extract (nat (int (size x) - (1::int)))
         (nat (int (size x) - (1::int))) y =
        (Word.Word (1::int)::1 word))
    then - ((if smt_extract (nat (int (size x) - (1::int)))
                 (nat (int (size x) - (1::int))) x =
                (Word.Word (1::int)::1 word)
             then - x else x) div
            (if smt_extract (nat (int (size x) - (1::int)))
                 (nat (int (size x) - (1::int))) y =
                (Word.Word (1::int)::1 word)
             then - y else y))
    else (if smt_extract (nat (int (size x) - (1::int)))
              (nat (int (size x) - (1::int))) x =
             (Word.Word (1::int)::1 word)
          then - x else x) div
         (if smt_extract (nat (int (size x) - (1::int)))
              (nat (int (size x) - (1::int))) y =
             (Word.Word (1::int)::1 word)
          then - y else y))"
  apply (simp add: xor_simps)
  apply ((subst h2[of "(nat (int (size x) - (1::int)))" x]),
   (metis One_nat_def diff_less len_gt_0 nat_minus_as_int of_nat_1 word_size zero_less_Suc))+
  apply ((subst h2[of "(nat (int (size x) - (1::int)))" y]),
         (metis One_nat_def diff_less len_gt_0 nat_minus_as_int of_nat_1 word_size zero_less_Suc))+
  apply (cases "(bit y (nat (int (size x) - (1::int))))")
   apply simp_all
  apply (case_tac [!] "bit x (nat (int (size x) - (1::int)))")
     apply simp_all
     apply (simp add: sdiv_word_def)
  apply transfer  
  subgoal for x y
  using take_bit_int_eq_self[of x "LENGTH('a)" ]
  apply (simp add: take_bit_word_eq_self)


     prefer 4
  subgoal
     unfolding sint_uint
     apply (subst signed_take_bit_eq_if_positive[of "uint x" "(LENGTH('a) - Suc (0::nat))"])
     apply (simp add: nat_minus_as_int word_size word_test_bit_def)
     apply (subst signed_take_bit_eq_if_positive[of "uint y" "(LENGTH('a) - Suc (0::nat))"])
     apply (simp add: nat_minus_as_int word_size word_test_bit_def)
    apply (simp add: word_uint_eq_iff)
    apply (simp add: uint_div_distrib)
    apply (subst (2) h3b[of x])
    apply (simp add: nat_minus_as_int word_size)
    apply (subst (2) h3b[of y])
     apply (simp add: nat_minus_as_int size_word.rep_eq)
    apply (simp add: uint_word_of_int_eq)
    apply (simp add: uint_take_bit_eq[symmetric])
    apply (simp add: uint_div[symmetric])
    by (simp add: bintr_uint[of "LENGTH('a)"])
  subgoal
 unfolding sint_uint
     apply (subst signed_take_bit_eq_if_negative[of "uint x" "(LENGTH('a) - Suc (0::nat))"])
     apply (simp add: nat_minus_as_int word_size word_test_bit_def)
     apply (subst signed_take_bit_eq_if_negative[of "uint y" "(LENGTH('a) - Suc (0::nat))"])
     apply (simp add: nat_minus_as_int word_size word_test_bit_def)
    apply (simp add: word_uint_eq_iff)
    apply (simp add: uint_div_distrib)
    apply (subst (2) h3b[of x])
    apply (simp add: nat_minus_as_int word_size)
    apply (subst (2) h3b[of y])
     apply (simp add: nat_minus_as_int size_word.rep_eq)
    apply (simp add: uint_word_of_int_eq)
    apply (simp add: uint_take_bit_eq[symmetric])
    apply (simp add: uint_div[symmetric])
    by (simp add: bintr_uint[of "LENGTH('a)"])







  unfolding sint_uint
  subgoal
    sorry
  subgoal
    sorry
  subgoal

  proof-
    assume a0: "\<not> bit y (nat (int (size x) - (1::int)))"
    and a1: "bit x (nat (int (size x) - (1::int)))"

    have "take_bit LENGTH('a) (- uint x) =  - (uint x) mod (2::int) ^ LENGTH('a::len)"
      using take_bit_int_def[of "LENGTH('a)" "- uint x"]
      by simp
    have t2: " ((take_bit (LENGTH('a) - Suc (0::nat)) (uint x) - (2::int) ^ (LENGTH('a) - Suc (0::nat))) div uint y =
    - (take_bit LENGTH('a) (- uint x) div uint y))

= ((take_bit (LENGTH('a) - Suc (0::nat)) (uint x) + - ((2::int) ^ (LENGTH('a) - (1::nat)))) div uint y 
+ (take_bit LENGTH('a) (- uint x) div uint y)
  =
    0)"
      by fastforce

    have t3: "((2::int) ^ (LENGTH('a) - Suc (0::nat)) - (2::int) ^ (LENGTH('a) - Suc (0::nat)))
= 0"
      by auto

    have t4: "uint (x::'a::len word) mod (2::int) ^ (LENGTH('a::len) - Suc (0::nat)) \<noteq> (0::int)
\<Longrightarrow>  uint x mod (2::int) ^ (LENGTH('a::len) - Suc (0::nat)) - (2::int) ^ (LENGTH('a::len) - Suc (0::nat)) =
  uint x mod - ((2::int) ^ (LENGTH('a::len) - Suc (0::nat)))"
      using zmod_zminus2_eq_if by presburger


      show ?thesis
        using a0 a1

     apply (subst signed_take_bit_eq_if_negative[of "uint x" "(LENGTH('a) - Suc (0::nat))"])
     apply (simp add: nat_minus_as_int word_size word_test_bit_def)
     apply (subst signed_take_bit_eq_if_positive[of "uint y" "(LENGTH('a) - Suc (0::nat))"])
     apply (simp add: nat_minus_as_int word_size word_test_bit_def)
    apply (simp add: word_uint_eq_iff)
    apply (simp add: uint_div_distrib uint_word_arith_bintrs(4))
    apply (simp add: uint_word_of_int_eq)
    apply (subst arg_cong[of "(or (take_bit (LENGTH('a) - Suc (0::nat)) (uint x)) (not (mask (LENGTH('a) - Suc (0::nat)))) div
      take_bit (LENGTH('a) - Suc (0::nat)) (uint y))" "(- (take_bit LENGTH('a) (- uint x) div uint y))" "take_bit LENGTH('a)"])
     apply simp_all
    apply (subst h11[symmetric,of y])
     apply (simp add: word_size)
    apply (subst disjunctive_add[symmetric, of "(take_bit (LENGTH('a) - Suc (0::nat)) (uint x))" "(not (mask (LENGTH('a) - Suc (0::nat))))"])
    apply (metis bit.compl_one bit_int_code(1) bit_take_bit_iff mask_eq_take_bit_minus_one take_bit_not_take_bit)
    apply (subst h123c[of "LENGTH('a)"])
         apply blast
        apply simp
        unfolding take_bit_eq_mod[of "(LENGTH('a) - Suc (0::nat))"]
        apply (cases "uint (x::'a::len word) mod (2::int) ^ (LENGTH('a::len) - Suc (0::nat)) = (0::int) ")
         defer
         apply (simp add: t4)
        
        using zmod_zminus2_eq_if[symmetric, of "uint x" "(2::int) ^ (LENGTH('a) - Suc (0::nat))"]
         defer
        subgoal
          apply (simp add: t3)



    apply (subst h9b[of x])
     apply simp_all
    apply (simp add: bintr_uint[of "LENGTH('a)" x])
    apply (simp add: uint_word_arith_bintrs(4)[symmetric])
    using zdiv_zminus1_eq_if[]



    using disjunctive_add[of "(take_bit (nat (int LENGTH('a) - (1::int))) (uint x))" " (- ((2::int) ^ nat (int LENGTH('a) - (1::int))))"]
    apply simp
    apply (simp add: h7[symmetric])
    apply (cases "take_bit (nat (int LENGTH('a) - (1::int))) (uint y) = 0")
     apply simp_all
    apply (subst h8[of "take_bit (nat (int LENGTH('a) - (1::int))) (uint y)"
"take_bit LENGTH('a) (- ((2::int) ^ nat (int LENGTH('a) - (1::int))) - take_bit (nat (int LENGTH('a) - (1::int))) (uint x))"]
)
    apply blast
     
    



    using zdiv_zminus1_eq_if[of "take_bit (nat (int LENGTH('a) - (1::int))) (uint y)"
"take_bit LENGTH('a) (- ((2::int) ^ nat (int LENGTH('a) - (1::int))) - take_bit (nat (int LENGTH('a) - (1::int))) (uint x))"]
    using ceiling_divide_eq_div
    apply (simp add: )




    using minus_divide_left[of
"(take_bit LENGTH('a) (- ((2::int) ^ nat (int LENGTH('a) - (1::int))) - take_bit (nat (int LENGTH('a) - (1::int))) (uint x)))"
"take_bit (nat (int LENGTH('a) - (1::int))) (uint y)"]
    using h6[of "(or (take_bit (nat (int LENGTH('a) - (1::int))) (uint x)) (- ((2::int) ^ nat (int LENGTH('a) - (1::int)))))"
"- take_bit LENGTH('a::len)
     (- ((2::int) ^ nat (int LENGTH('a::len) - (1::int))) - take_bit (nat (int LENGTH('a::len) - (1::int))) (uint x))"
"take_bit (nat (int LENGTH('a) - (1::int))) (uint y)"]



    apply (simp add:  bwsimps(4)[symmetric, of "(take_bit (nat (int LENGTH('a) - (1::int))) (uint (x::'a::len word)))"
"(not (mask (nat (int LENGTH('a) - (1::int)))))"])
    apply (simp add: uint_word_of_int_eq)
    apply (simp add: uint_take_bit_eq[symmetric])
    apply (simp add: uint_or[symmetric])
    apply (simp add: uint_div[symmetric])
    by (simp add: bintr_uint[of "LENGTH('a)"])




    apply transfer
    apply simp

    apply (simp add: take_bit_or)
    sorry
  subgoal
     apply (subst signed_take_bit_eq_if_positive[of "uint x" "(LENGTH('a) - Suc (0::nat))"])
     apply (simp add: nat_minus_as_int word_size word_test_bit_def)
     apply (subst signed_take_bit_eq_if_positive[of "uint y" "(LENGTH('a) - Suc (0::nat))"])
     apply (simp add: nat_minus_as_int word_size word_test_bit_def)
    apply (simp add: word_uint_eq_iff)
    apply (simp add: uint_div_distrib)
    apply (subst (2) h3b[of x])
    apply (simp add: nat_minus_as_int word_size)
    apply (subst (2) h3b[of y])
     apply (simp add: nat_minus_as_int size_word.rep_eq)
    apply (simp add: uint_word_of_int_eq)
    apply (simp add: uint_take_bit_eq[symmetric])
    apply (simp add: uint_div[symmetric])
    by (simp add: bintr_uint[of "LENGTH('a)"])
 
  sorry
(*signed_take_bit_eq_if_negative*)

named_theorems rewrite_bv_sdiv_eliminate_fewer_bitwise_ops \<open>automatically_generated\<close>

lemma t0:
"LENGTH('a) = LENGTH('b) + 1 \<Longrightarrow> (word_cat (1::1 word) (0::'b::len word)::'a::len word) = 2^(LENGTH('b))"
  apply (simp add: word_unat_eq_iff)
  by (simp add: unat_word_cat)

lemma [rewrite_bv_sdiv_eliminate_fewer_bitwise_ops]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "LENGTH('a) = LENGTH('b) + 1 \<longrightarrow> 
x sdiv y =
   (if xor (word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> x) 
       (word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b word) \<le> y)
    then - ((if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b word) \<le> x
             then - x else x) div
            (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b word) \<le> y
             then - y else y))
    else (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b word) \<le> x
          then - x else x) div
         (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b word) \<le> y
          then - y else y))"
  apply (simp add: xor_simps)
  apply (cases "word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b word) \<le> y" )
   apply simp_all
  apply (case_tac[!] "word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b word) \<le> x" )
     apply simp_all
  sorry

lemma [rewrite_bv_mult_slt_mult_1]:
  fixes x::"'a ::len word" and t::"'a ::len word" and a::"'a ::len word" and n::"int" and m::"int"
  shows "nat n < LENGTH('a) \<Longrightarrow> LENGTH('a) > 1 \<Longrightarrow> 
    (signed_take_bit (nat n) (x + t) * signed_take_bit (nat m) a
    <s signed_take_bit (nat n) x * signed_take_bit (nat m) a) =
   (t \<noteq> (Word.Word 0::'a::len word) \<and>
    a \<noteq> (Word.Word 0::'a::len word) \<and>
   (x + t <s x) = (Word.Word 0 <s a))"
  apply (cases "t = (Word.Word 0::'a::len word)")
   apply simp
  apply (cases "a = (Word.Word 0::'a::len word)")
   apply simp
  apply (cases "(x + t <s x) = (Word.Word 0 <s a)")
   apply simp_all
proof-
  assume a00: "nat n < LENGTH('a)" and a01: " Suc (0::nat) < LENGTH('a)" and a0: "t \<noteq> (0::'a word)"
  and a1: "a \<noteq> (0::'a word)"
  and a2: "(x + t <s x) = ((0::'a word) <s a)"

have t0: "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x))
       (signed_take_bit (LENGTH('a) - 1) ((if (bit x (nat n)) then 1 else 0)
   * signed_take_bit LENGTH('a::len) (not (signed (mask (nat n)::'a::len word))))))"
proof-
  have "sint (signed_take_bit (nat n) x) =
   sint (or (take_bit (nat n) x) (of_bool (bit x (nat n)) * not (mask (nat n))))"
    using signed_take_bit_def[of "nat n" "x"] signed_or_eq
    by simp
  then have "sint (signed_take_bit (nat n) x) =
   (or (sint (take_bit (nat n) x::'a::len word)) (sint (of_bool (bit x (nat n)) * not (mask (nat n))::'a::len word)))"
    using signed_or_eq by simp
 then have "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x)) (sint (of_bool (bit x (nat n)) * not (mask (nat n))::'a::len word)))"
  using signed_take_bit_eq[of "nat n" "x"] a00 by simp
then have "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x)) (sint ((if (bit x (nat n)) then 1 else 0) * not (mask (nat n))::'a::len word)))"
  using of_bool_def by simp
then have "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x))
       (signed_take_bit (LENGTH('a) - 1) (sint (if (bit x (nat n)) then 1 else 0::'a::len word) * sint (not (mask (nat n))::'a::len word))))"
  by (simp add: sint_word_ariths(3))
then have "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x))
       (signed_take_bit (LENGTH('a) - 1) ( (if (bit x (nat n)) then sint (1::'a::len word) else sint (0::'a::len word)) * sint (not (mask (nat n))::'a::len word))))"
  by simp
  moreover have "sint (1::'a::len word) = (1::int)"
    using a01 by fastforce
  moreover have "sint (0::'a::len word) = (0::int)"
    by simp
  ultimately have "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x))
       (signed_take_bit (LENGTH('a) - 1) ((if (bit x (nat n)) then 1 else 0) * sint (not (mask (nat n))::'a::len word))))"
    by presburger
then have "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x))
       (signed_take_bit (LENGTH('a) - 1) ((if (bit x (nat n)) then 1 else 0)
   * signed_take_bit LENGTH('a::len) (not (signed (mask (nat n)::'a::len word))))))"
  using signed_not_eq[of "mask (nat n)"] by metis
  then show ?thesis 
    by blast
qed

 have t1: "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t)))
       (signed_take_bit (LENGTH('a) - 1) ((if (bit (x + t) (nat n)) then 1 else 0)
   * signed_take_bit LENGTH('a::len) (not (signed (mask (nat n)::'a::len word))))))"
proof-
  have "sint (signed_take_bit (nat n) (x + t) * signed_take_bit (nat m) a) =
   signed_take_bit (LENGTH('a::len) - (1::nat)) (sint (signed_take_bit (nat n) (x + t)) * sint (signed_take_bit (nat m) a))"
    using sint_word_ariths(3) by simp
  have "sint (signed_take_bit (nat n) (x + t)) =
   sint (or (take_bit (nat n) (x + t)) (of_bool (bit (x + t) (nat n)) * not (mask (nat n))))"
    using signed_take_bit_def[of "nat n" "x+t"] signed_or_eq
    by simp
  then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (sint (take_bit (nat n) (x + t)::'a::len word)) (sint (of_bool (bit (x + t) (nat n)) * not (mask (nat n))::'a::len word)))"
    using signed_or_eq by simp
 then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (sint (x + t))) (sint (of_bool (bit (x + t) (nat n)) * not (mask (nat n))::'a::len word)))"
  using signed_take_bit_eq[of "nat n" "x+t"] a00 by simp
then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t))) (sint (of_bool (bit (x + t) (nat n)) * not (mask (nat n))::'a::len word)))"
  using sint_word_ariths(1) by metis
then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t))) (sint ((if (bit (x + t) (nat n)) then 1 else 0) * not (mask (nat n))::'a::len word)))"
  using of_bool_def by simp
then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t)))
       (signed_take_bit (LENGTH('a) - 1) (sint (if (bit (x + t) (nat n)) then 1 else 0::'a::len word) * sint (not (mask (nat n))::'a::len word))))"
  by (simp add: sint_word_ariths(3))
then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t)))
       (signed_take_bit (LENGTH('a) - 1) ( (if (bit (x + t) (nat n)) then sint (1::'a::len word) else sint (0::'a::len word)) * sint (not (mask (nat n))::'a::len word))))"
  by simp
  moreover have "sint (1::'a::len word) = (1::int)"
    using a01 by fastforce
  moreover have "sint (0::'a::len word) = (0::int)"
    by simp
  ultimately have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t)))
       (signed_take_bit (LENGTH('a) - 1) ((if (bit (x + t) (nat n)) then 1 else 0) * sint (not (mask (nat n))::'a::len word))))"
    by presburger
then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t)))
       (signed_take_bit (LENGTH('a) - 1) ((if (bit (x + t) (nat n)) then 1 else 0)
   * signed_take_bit LENGTH('a::len) (not (signed (mask (nat n)::'a::len word))))))"
  using signed_not_eq[of "mask (nat n)"] by metis
  then show ?thesis 
    by blast
qed

  show " signed_take_bit (nat n) (x + t) * signed_take_bit (nat m) a <s signed_take_bit (nat n) x * signed_take_bit (nat m) a"
    apply (simp add: word_sless_alt)
    apply (simp add: sint_word_ariths(3))
    apply (simp add: t0 t1)
    apply (cases "bit (x + t) (nat n)")
    apply (case_tac "bit x (nat n)")
      apply simp_all
    unfolding take_bit_eq_mod bit_or_iff
    apply simp
qed



end