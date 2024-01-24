theory BV_Rewrites1_2
  imports Dsl_Nary_Ops BV_Rewrites_Lemmas
begin

(* This is a theory automatically created from a rare file! All that remains to do is to prove
any lemma whose provided proof fails and to to import this file in thy. 
If your rare statements use nary operators over lists that would be binarised by Isabelle 
you have to add it in Dsl_Nary_Ops.thy. Currently already supported are the operators:
and,
or,
plus,
times,
append,
re_concat,
str_concat,
*)

named_theorems rewrite_bv_concat_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_concat_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "cvc_list_right word_cat
    (cvc_list_left word_cat xs (cvc_list_right word_cat s ys)) zs =
   cvc_list_right word_cat
    (cvc_list_right word_cat (cvc_list_left word_cat xs s) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction zss arbitrary: zs)
     apply simp_all
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (induction xss arbitrary: xs)
     apply simp_all
     apply (metis word_cat_id)
    by (simp add: word_cat_id)
  done

(*This cannot be added as a lemma, has to be implemented as a tactic*)
named_theorems rewrite_bv_concat_extract_merge \<open>automatically_generated\<close>

lemma [rewrite_bv_concat_extract_merge]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'b::len word" and ys::"'a::len word cvc_ListVar" and i::"int" and j::"int" and j1::"int" and k::"int"
  shows "j1 = j + (1::int) \<longrightarrow>
   cvc_list_right word_cat
    (word_cat
      (cvc_list_left word_cat xs (smt_extract (nat k) (nat j1) s))
      (smt_extract (nat j) (nat i) s))
    ys =
   cvc_list_right word_cat
    (cvc_list_left word_cat xs (smt_extract (nat k) (nat i) s)) ys"
  oops

named_theorems rewrite_bv_extract_extract \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_extract]:
  fixes x::"'a::len word" and i::"int" and j::"int" and k::"int" and l::"int"
  assumes "i \<ge> 0" "i \<le> j" "j < size x" "LENGTH('b) = j + 1 - i"
   "k \<ge> 0" "k \<le> l" "l < size (smt_extract (nat j) (nat i) x::'b::len word)" "LENGTH('c) = l + 1 - k"
   "(i+k) \<ge> 0" "(i+k) \<le> (i+l)" "(i+l) < size x" "LENGTH('c) = (i+l) + 1 - (i+k)"
  shows "
   (smt_extract (nat l) (nat k) (smt_extract (nat j) (nat i) x::'b::len word)::'c::len word) =
   smt_extract (nat (i + l)) (nat (i + k)) x"
proof-
  have t0: "nat (k::int) \<le> nat (l::int)"
           "nat l < size (smt_extract (nat (j::int)) (nat (i::int)) (x::'a::len word)::'b::len word)"
           "LENGTH('c::len) = nat l + (1::nat) - nat k"
    using assms(5-8) by simp_all
  have t1: "nat (i::int) \<le> nat (j::int)"
           "nat j < size (x::'a::len word)"
           "LENGTH('b::len) = nat j + (1::nat) - nat i"
    using assms(1-4) by simp_all
  have t2: "nat ((i::int) + (k::int)) \<le> nat (i + (l::int))"
           "nat (i + l) < size (x::'a::len word)"
           "LENGTH('c::len) = nat (i + l) + (1::nat) - nat (i + k)"
    using assms(9-12) by simp_all
  have t3: "(Suc (min (nat l + nat i) (nat j))) = Suc (nat l + nat i)"
    by (metis Nat.le_diff_conv2 Suc_diff_le Suc_eq_plus1 Suc_le_mono discrete min_absorb1 t0(2) t1(1) t1(3) word_size)
  have t4: " (nat l + nat i) = nat (l+i)"
    using assms(1) assms(5) assms(6) nat_add_distrib by auto

  show ?thesis
    apply (simp add: word_unat_eq_iff)
    apply (simp add: unat_smt_extract[of "nat k" "nat l" "(smt_extract (nat j) (nat i) x::'b::len word)", where 'b="'c"] t0)
    apply (simp add: unat_smt_extract[of "nat i" "nat j" x, where 'b="'b"] t1)
    apply (simp add: unat_smt_extract[of "nat (i+k)" "nat (i+l)" x, where 'b="'c"] t2)
    apply (simp add: take_bit_drop_bit)
    apply (simp add: assms(1) assms(5) nat_add_distrib)
    apply (simp add: t3 )
    apply (simp add: t4)
    by (simp add: add.commute)
qed


named_theorems rewrite_bv_extract_whole \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_whole]:
  fixes x::"'a::len word" and n::"int"
  shows "int (size x) - (1::int) \<le> n \<longrightarrow>
   smt_extract (nat n) (nat (0::int)) x = x"
  apply (cases "n = int (size x)")
  apply (simp add: size_word.rep_eq slice_id smt_extract_def take_bit_word_eq_self)
  by (simp add: size_word.rep_eq slice_id smt_extract_def take_bit_word_eq_self)


(*This cannot be added as a lemma, has to be implemented as a tactic*)
named_theorems rewrite_bv_extract_concat_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_concat_1]:
  fixes x::"'a::len word" and xs::"'b::len word cvc_ListVar" and y::"'b::len word" and i::"int" and j::"int"
  shows "j \<le> int (size x) \<longrightarrow>
   smt_extract (nat j) (nat i)
    (word_cat (cvc_list_left word_cat xs y) x) =
   smt_extract (nat j) (nat i) x"
  oops

(*This cannot be added as a lemma, has to be implemented as a tactic*)
named_theorems rewrite_bv_extract_concat_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_concat_2]:
  fixes x::"'a::len word" and xs::"'b::len word cvc_ListVar" and y::"'b::len word" and i::"int" and j::"int"
  shows "i < int (size x) \<and> int (size x) \<le> j \<longrightarrow>
   smt_extract (nat j) (nat i)
    (word_cat (cvc_list_left word_cat xs y) x) =
   word_cat
    (smt_extract (nat (j - int (size x))) (nat (0::int))
      (cvc_list_left word_cat xs y))
    (smt_extract (nat (int (size x) - (1::int))) (nat i) x)"
  oops

named_theorems rewrite_bv_extract_concat_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_concat_3]:
  fixes x::"'a::len word" and y::"'b::len word" and xs::"'b::len word cvc_ListVar" and i::"int" and j::"int"
  shows "int (size x) \<le> i \<longrightarrow>
   smt_extract (nat j) (nat i)
    (word_cat (cvc_list_left word_cat xs y) x) =
   smt_extract (nat (j - int (size x))) (nat (i - int (size x)))
    (cvc_list_left word_cat xs y)"
  apply (cases xs)
  subgoal for xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_extract_concat_3_lemma)
  done

named_theorems rewrite_bv_extract_concat_4 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_concat_4]:
  fixes x::"'a::len word" and y::"'a::len word" and xs::"'a::len word cvc_ListVar" and i::"int" and j::"int"
  shows "j < int (size (word_cat (cvc_list_right word_cat x xs) y)) -
       int (size x) \<longrightarrow>
   smt_extract (nat j) (nat i)
    (word_cat (cvc_list_right word_cat x xs) y) =
   smt_extract (nat j) (nat i) (cvc_list_left word_cat xs y)"
  apply (cases xs)
  subgoal for xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_extract_concat_4_lemma)
  done

named_theorems rewrite_bv_ugt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "(y < x) = (y < x)"
  by auto

named_theorems rewrite_bv_uge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_uge_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "(y \<le> x) = (y \<le> x)"
  by auto

named_theorems rewrite_bv_sgt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sgt_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "(y <s x) = (y <s x)"
  by auto

named_theorems rewrite_bv_sge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sge_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "(y \<le>s x) = (y \<le>s x)"
  by auto

named_theorems rewrite_bv_slt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_slt_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "(x <s y) =
   (x +
    push_bit (unat (Word.Word (int (size x) - (1::int))))
     (Word.Word (1::int))
    < y +
      push_bit (unat (Word.Word (int (size x) - (1::int))))
       (Word.Word (1::int)))"
  by auto

named_theorems rewrite_bv_sle_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "(x \<le>s y) = (\<not> y <s x)"
  by auto

named_theorems rewrite_bv_redor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redor_eliminate]:
  fixes x::"'a::len word"
  shows "smt_redor x = not (smt_comp x (Word.Word (0::int)))"
  by auto

named_theorems rewrite_bv_redand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redand_eliminate]:
  fixes x::"'a::len word"
  shows "smt_redand x = not (smt_comp x (not (Word.Word (0::int))))"
  by auto

named_theorems rewrite_bv_sub_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sub_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "x - y = x + - y"
  by auto

named_theorems rewrite_bv_ule_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "(x \<le> y) = (\<not> y < x)"
  by auto

named_theorems rewrite_bv_comp_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_comp_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "smt_comp x y = (if x = y then Word.Word (1::int) else Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_repeat_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_1]:
  fixes x::"'a::len word" and n::"int"
  shows "(1::int) < n \<longrightarrow>
   smt_repeat (nat n) x = word_cat x (smt_repeat (nat (n - (1::int))) x)"
  unfolding smt_repeat_def
  by (metis One_nat_def Suc_diff_Suc Suc_lessD Suc_pred' linorder_linear nat_1 nat_diff_distrib not_one_le_zero one_less_nat_eq order_less_imp_le repeat.simps(2))

named_theorems rewrite_bv_repeat_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_2]:
  fixes x::"'a::len word"
  shows "smt_repeat (nat (1::int)) x = x"
  unfolding smt_repeat_def
  by auto

named_theorems rewrite_bv_rotate_left_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_1]:
  fixes x::"'a::len word" and amount::"int"
  assumes "amount \<ge> 0"
  "0 \<ge> 0" "0 \<le> size x - (1 + z3mod amount (int (size x)))"
  "size x - (1 + z3mod amount (int (size x))) < size x"
  shows "z3mod amount (int (size x)) \<noteq> (0::int) \<longrightarrow>
   word_rotl (nat amount) x =
   word_cat
    (smt_extract
      (nat (int (size x) - ((1::int) + z3mod amount (int (size x)))))
      (nat (0::int)) x::'b::len word)
    (smt_extract (nat (int (size x) - (1::int)))
      (nat (int (size x) - z3mod amount (int (size x)))) x::'c::len word)"
  by auto

named_theorems rewrite_bv_rotate_left_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_2]:
  fixes x::"'a::len word" and amount::"int"
  shows "z3mod amount (int (size x)) = (0::int) \<longrightarrow>
   word_rotl (nat amount) x = x"
  by auto

named_theorems rewrite_bv_rotate_right_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_1]:
  fixes x::"'a::len word" and amount::"int"
  shows "z3mod amount (int (size x)) \<noteq> (0::int) \<longrightarrow>
   word_rotr (nat amount) x =
   word_cat
    (smt_extract (nat (z3mod amount (int (size x)) - (1::int)))
      (nat (0::int)) x)
    (smt_extract (nat (int (size x) - (1::int)))
      (nat (z3mod amount (int (size x)))) x)"
  by auto

named_theorems rewrite_bv_rotate_right_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_2]:
  fixes x::"'a::len word" and amount::"int"
  shows "z3mod amount (int (size x)) = (0::int) \<longrightarrow>
   word_rotr (nat amount) x = x"
  by auto

named_theorems rewrite_bv_nand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_nand_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "not (and x y) = not (and x y)"
  by auto

named_theorems rewrite_bv_nor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_nor_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "not (or x y) = not (or x y)"
  by auto

named_theorems rewrite_bv_xnor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_xnor_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "not (semiring_bit_operations_class.xor x y) =
   not (semiring_bit_operations_class.xor x y)"
  by auto

named_theorems rewrite_bv_sdiv_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sdiv_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "x div y =
   (if (smt_extract (nat (int (size x) - (1::int)))
         (nat (int (size x) - (1::int))) x =
        Word.Word (1::int)) [+]
       (smt_extract (nat (int (size x) - (1::int)))
         (nat (int (size x) - (1::int))) y =
        Word.Word (1::int))
    then - ((if smt_extract (nat (int (size x) - (1::int)))
                 (nat (int (size x) - (1::int))) x =
                Word.Word (1::int)
             then - x else x) div
            (if smt_extract (nat (int (size x) - (1::int)))
                 (nat (int (size x) - (1::int))) y =
                Word.Word (1::int)
             then - y else y))
    else (if smt_extract (nat (int (size x) - (1::int)))
              (nat (int (size x) - (1::int))) x =
             Word.Word (1::int)
          then - x else x) div
         (if smt_extract (nat (int (size x) - (1::int)))
              (nat (int (size x) - (1::int))) y =
             Word.Word (1::int)
          then - y else y))"
  by auto

named_theorems rewrite_bv_sdiv_eliminate_fewer_bitwise_ops \<open>automatically_generated\<close>

lemma [rewrite_bv_sdiv_eliminate_fewer_bitwise_ops]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "x div y =
   (if (word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> x) [+]
       (word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> y)
    then - ((if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> x
             then - x else x) div
            (if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> y
             then - y else y))
    else (if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> x
          then - x else x) div
         (if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> y
          then - y else y))"
  by auto

named_theorems rewrite_bv_zero_extend_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eliminate]:
  fixes x::"'a::len word" and n::"int"
  shows "Word.cast x = word_cat (Word.Word (0::int)) x"
  by auto

named_theorems rewrite_bv_sign_extend_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eliminate]:
  fixes x::"'a::len word" and n::"int"
  shows "Word.signed_cast x =
   word_cat
    (smt_repeat (nat n)
      (smt_extract (nat (int (size x) - (1::int)))
        (nat (int (size x) - (1::int))) x))
    x"
  by auto

named_theorems rewrite_bv_uaddo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_uaddo_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "smt_uaddo (itself::'b::len itself) x y =
   (smt_extract (nat (int (size x))) (nat (int (size x)))
     (word_cat (Word.Word (0::int)) x + word_cat (Word.Word (0::int)) y) =
    Word.Word (1::int))"
  by auto

named_theorems rewrite_bv_saddo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_saddo_eliminate]:
  fixes x::"'a::len word" and y::"'b::len word"
  shows "smt_saddo (itself::'c::len itself) x y =
   (smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int)))
     (word_cat (Word.Word (0::int)) x + word_cat (Word.Word (0::int)) y) =
    Word.Word (1::int))"
  by auto

named_theorems rewrite_bv_sdivo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sdivo_eliminate]:
  fixes x::"'a::len word" and y::"'b::len word"
  shows "smt_sdivo (itself::'c::len itself) x y =
   (x = word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<and>
    y = not (Word.Word (0::int)))"
  by auto

named_theorems rewrite_bv_smod_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_smod_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "smt_smod x y =
   (if smt_urem
        (if smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) x =
            Word.Word (1::int)
         then - x else x)
        (if smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) y =
            Word.Word (1::int)
         then - y else y) =
       Word.Word (0::int)
    then smt_urem
          (if smt_extract (nat (int (size x) - (1::int)))
               (nat (int (size x) - (1::int))) x =
              Word.Word (1::int)
           then - x else x)
          (if smt_extract (nat (int (size x) - (1::int)))
               (nat (int (size x) - (1::int))) y =
              Word.Word (1::int)
           then - y else y)
    else if smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) x \<noteq>
            Word.Word (1::int) \<and>
            smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) y \<noteq>
            Word.Word (1::int)
         then smt_urem
               (if smt_extract (nat (int (size x) - (1::int)))
                    (nat (int (size x) - (1::int))) x =
                   Word.Word (1::int)
                then - x else x)
               (if smt_extract (nat (int (size x) - (1::int)))
                    (nat (int (size x) - (1::int))) y =
                   Word.Word (1::int)
                then - y else y)
         else if smt_extract (nat (int (size x) - (1::int)))
                  (nat (int (size x) - (1::int))) x =
                 Word.Word (1::int) \<and>
                 smt_extract (nat (int (size x) - (1::int)))
                  (nat (int (size x) - (1::int))) y \<noteq>
                 Word.Word (1::int)
              then - smt_urem
                      (if smt_extract (nat (int (size x) - (1::int)))
                           (nat (int (size x) - (1::int))) x =
                          Word.Word (1::int)
                       then - x else x)
                      (if smt_extract (nat (int (size x) - (1::int)))
                           (nat (int (size x) - (1::int))) y =
                          Word.Word (1::int)
                       then - y else y) +
                   y
              else if smt_extract (nat (int (size x) - (1::int)))
                       (nat (int (size x) - (1::int))) x \<noteq>
                      Word.Word (1::int) \<and>
                      smt_extract (nat (int (size x) - (1::int)))
                       (nat (int (size x) - (1::int))) y =
                      Word.Word (1::int)
                   then smt_urem
                         (if smt_extract (nat (int (size x) - (1::int)))
                              (nat (int (size x) - (1::int))) x =
                             Word.Word (1::int)
                          then - x else x)
                         (if smt_extract (nat (int (size x) - (1::int)))
                              (nat (int (size x) - (1::int))) y =
                             Word.Word (1::int)
                          then - y else y) +
                        y
                   else - smt_urem
                           (if smt_extract
                                (nat (int (size x) - (1::int)))
                                (nat (int (size x) - (1::int))) x =
                               Word.Word (1::int)
                            then - x else x)
                           (if smt_extract
                                (nat (int (size x) - (1::int)))
                                (nat (int (size x) - (1::int))) y =
                               Word.Word (1::int)
                            then - y else y))"
  by auto

named_theorems rewrite_bv_smod_eliminate_fewer_bitwise_ops \<open>automatically_generated\<close>

lemma [rewrite_bv_smod_eliminate_fewer_bitwise_ops]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "smt_smod x y =
   (if smt_urem
        (if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> x
         then - x else x)
        (if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> y
         then - y else y) =
       Word.Word (0::int)
    then smt_urem
          (if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> x
           then - x else x)
          (if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> y
           then - y else y)
    else if \<not> word_cat (Word.Word (1::int)) (Word.Word (0::int))
                   \<le> x \<and>
            \<not> word_cat (Word.Word (1::int)) (Word.Word (0::int))
                   \<le> y
         then smt_urem
               (if word_cat (Word.Word (1::int)) (Word.Word (0::int))
                   \<le> x
                then - x else x)
               (if word_cat (Word.Word (1::int)) (Word.Word (0::int))
                   \<le> y
                then - y else y)
         else if word_cat (Word.Word (1::int)) (Word.Word (0::int))
                 \<le> x \<and>
                 \<not> word_cat (Word.Word (1::int)) (Word.Word (0::int))
                        \<le> y
              then - smt_urem
                      (if word_cat (Word.Word (1::int)) (Word.Word (0::int))
                          \<le> x
                       then - x else x)
                      (if word_cat (Word.Word (1::int)) (Word.Word (0::int))
                          \<le> y
                       then - y else y) +
                   y
              else if \<not> word_cat (Word.Word (1::int))
                              (Word.Word (0::int))
                             \<le> x \<and>
                      word_cat (Word.Word (1::int)) (Word.Word (0::int))
                      \<le> y
                   then smt_urem
                         (if word_cat (Word.Word (1::int))
                              (Word.Word (0::int))
                             \<le> x
                          then - x else x)
                         (if word_cat (Word.Word (1::int))
                              (Word.Word (0::int))
                             \<le> y
                          then - y else y) +
                        y
                   else - smt_urem
                           (if word_cat (Word.Word (1::int))
                                (Word.Word (0::int))
                               \<le> x
                            then - x else x)
                           (if word_cat (Word.Word (1::int))
                                (Word.Word (0::int))
                               \<le> y
                            then - y else y))"
  by auto

named_theorems rewrite_bv_srem_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_srem_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "smt_srem x y =
   (if bit (smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) x)
        (0::nat)
    then - smt_urem
            (if bit (smt_extract (nat (int (size x) - (1::int)))
                      (nat (int (size x) - (1::int))) x)
                 (0::nat)
             then - x else x)
            (if bit (smt_extract (nat (int (size x) - (1::int)))
                      (nat (int (size x) - (1::int))) y)
                 (0::nat)
             then - y else y)
    else smt_urem
          (if bit (smt_extract (nat (int (size x) - (1::int)))
                    (nat (int (size x) - (1::int))) x)
               (0::nat)
           then - x else x)
          (if bit (smt_extract (nat (int (size x) - (1::int)))
                    (nat (int (size x) - (1::int))) y)
               (0::nat)
           then - y else y))"
  by auto

named_theorems rewrite_bv_srem_eliminate_fewer_bitwise_ops \<open>automatically_generated\<close>

lemma [rewrite_bv_srem_eliminate_fewer_bitwise_ops]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "smt_srem x y =
   (if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> x
    then - smt_urem
            (if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> x
             then - x else x)
            (if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> y
             then - y else y)
    else smt_urem
          (if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> x
           then - x else x)
          (if word_cat (Word.Word (1::int)) (Word.Word (0::int)) \<le> y
           then - y else y))"
  by auto

named_theorems rewrite_bv_usubo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_usubo_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "smt_usubo x y =
   (smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) (Word.cast x - Word.cast y) =
    Word.Word (1::int))"
  by auto

named_theorems rewrite_bv_ssubo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ssubo_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "smt_ssubo x y =
   (smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) x =
    Word.Word (1::int) \<and>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) y \<noteq>
    Word.Word (1::int) \<and>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) (x - y) \<noteq>
    Word.Word (1::int) \<or>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) x \<noteq>
    Word.Word (1::int) \<and>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) y =
    Word.Word (1::int) \<and>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) (x - y) =
    Word.Word (1::int))"
  by auto

named_theorems rewrite_bv_ite_equal_children \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_children]:
  fixes c::"1 ::len word" and x::"'a::type ::len word"
  shows "(if bit c (0::nat) then x else x) = x"
  by auto

named_theorems rewrite_bv_ite_const_children_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_1]:
  fixes c::"1 ::len word"
  shows "(if bit c (0::nat) then Word.Word (0::int) else Word.Word (1::int)) =
   not c"
  by auto

named_theorems rewrite_bv_ite_const_children_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_2]:
  fixes c::"1 ::len word"
  shows "(if bit c (0::nat) then Word.Word (1::int) else Word.Word (0::int)) = c"
  by auto

named_theorems rewrite_bv_ite_equal_cond_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_1]:
  fixes c0::"1 ::len word" and t0::"'a::type ::len word" and e0::"'a::type ::len word" and e1::"'a::type ::len word"
  shows "(if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto

named_theorems rewrite_bv_ite_equal_cond_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_2]:
  fixes c0::"1 ::len word" and t0::"'a::type ::len word" and t1::"'a::type ::len word" and e1::"'a::type ::len word"
  shows "(if bit c0 (0::nat) then t0 else if bit c0 (0::nat) then t1 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto

named_theorems rewrite_bv_ite_equal_cond_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_3]:
  fixes c0::"1 ::len word" and t0::"'a::type ::len word" and e0::"'a::type ::len word" and t1::"'a::type ::len word" and e1::"'a::type ::len word"
  shows "(if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0
    else if bit c0 (0::nat) then t1 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto

named_theorems rewrite_bv_ite_merge_then_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_if]:
  fixes c0::"1 ::len word" and c1::"1 ::len word" and t1::"'a::type ::len word" and e1::"'a::type ::len word"
  shows "(if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else t1) =
   (if bit (and c0 (not c1)) (0::nat) then e1 else t1)"
  by auto

named_theorems rewrite_bv_ite_merge_else_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_if]:
  fixes c0::"1 ::len word" and c1::"1 ::len word" and t1::"'a::type ::len word" and e1::"'a::type ::len word"
  shows "(if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else e1) =
   (if bit (and c0 c1) (0::nat) then t1 else e1)"
  by auto

named_theorems rewrite_bv_ite_merge_then_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_else]:
  fixes c0::"1 ::len word" and c1::"1 ::len word" and t0::"'a::type ::len word" and e1::"'a::type ::len word"
  shows "(if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t0 else e1) =
   (if bit (not (or c0 c1)) (0::nat) then e1 else t0)"
  by auto

named_theorems rewrite_bv_ite_merge_else_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_else]:
  fixes c0::"1 ::len word" and c1::"1 ::len word" and t1::"'a::type ::len word" and t0::"'a::type ::len word"
  shows "(if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t1 else t0) =
   (if bit (and (not c0) c1) (0::nat) then t1 else t0)"
  by auto

named_theorems rewrite_bv_shl_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_1]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
   push_bit (unat x) (Word.Word amount) =
   word_cat
    (smt_extract (nat (int (size x)))
      (nat (int (size x) - ((1::int) + amount))) x)
    (Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_shl_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_2]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow>
   push_bit (unat x) (Word.Word amount) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_lshr_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_1]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
   drop_bit (unat x) (Word.Word amount) =
   word_cat (Word.Word (0::int))
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x)"
  by auto

named_theorems rewrite_bv_lshr_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_2]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow>
   drop_bit (unat x) (Word.Word amount) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_ashr_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_by_const_1]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
   drop_bit (unat x) (Word.Word amount) =
   word_cat
    (smt_repeat (nat amount)
      (smt_extract (nat (int (size x) - (1::int)))
        (nat (int (size x) - (1::int))) x))
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x)"
  by auto

named_theorems rewrite_bv_ashr_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_by_const_2]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow>
   drop_bit (unat x) (Word.Word amount) =
   smt_repeat (nat (int (size x)))
    (smt_extract (nat (int (size x) - (1::int)))
      (nat (int (size x) - (1::int))) x)"
  by auto

named_theorems rewrite_bv_and_concat_pullup \<open>automatically_generated\<close>

lemma [rewrite_bv_and_concat_pullup]:
  fixes x::"'a::len word" and y::"'b::len word" and z::"'c::len word" and ys::"'c::len word cvc_ListVar"
  shows "and x (word_cat (cvc_list_left word_cat ys z) y) =
   word_cat
    (and (smt_extract (nat (int (size x) - (1::int)))
           (nat (int (size y))) x)
      (cvc_list_left word_cat ys z))
    (and (smt_extract (nat (int (size y) - (1::int))) (nat (0::int)) x)
      y)"
  apply (cases ys)
  subgoal for yss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_and_concat_pullup_lemma)
  done

named_theorems rewrite_bv_or_concat_pullup \<open>automatically_generated\<close>

lemma [rewrite_bv_or_concat_pullup]:
  fixes x::"'a::len word" and y::"'b::len word" and z::"'c::len word" and ys::"'c::len word cvc_ListVar"
  shows "or x (word_cat (cvc_list_left word_cat ys z) y) =
   word_cat
    (or (smt_extract (nat (int (size x) - (1::int)))
          (nat (int (size y))) x)
      (cvc_list_left word_cat ys z))
    (or (smt_extract (nat (int (size y) - (1::int))) (nat (0::int)) x)
      y)"
  apply (cases ys)
  subgoal for yss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_or_concat_pullup_lemma)
  done

named_theorems rewrite_bv_xor_concat_pullup \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_concat_pullup]:
  fixes x::"'a::len word" and y::"'b::len word" and z::"'c::len word" and ys::"'c::len word cvc_ListVar"
  shows "semiring_bit_operations_class.xor x
    (word_cat (cvc_list_left word_cat ys z) y) =
   word_cat
    (semiring_bit_operations_class.xor
      (smt_extract (nat (int (size x) - (1::int))) (nat (int (size y)))
        x)
      (cvc_list_left word_cat ys z))
    (semiring_bit_operations_class.xor
      (smt_extract (nat (int (size y) - (1::int))) (nat (0::int)) x) y)"
  apply (cases ys)
  subgoal for yss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_xor_concat_pullup_lemma)
  done

named_theorems rewrite_bv_bitwise_idemp_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_idemp_1]:
  fixes x::"'a::len word"
  shows "and x x = x"
  by auto

named_theorems rewrite_bv_bitwise_idemp_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_idemp_2]:
  fixes x::"'a::len word"
  shows "or x x = x"
  by auto

named_theorems rewrite_bv_and_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_and_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "and x (Word.Word (0::int)) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_and_one \<open>automatically_generated\<close>

lemma [rewrite_bv_and_one]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "y = not (Word.Word (0::int)) \<longrightarrow> and x y = x"
  by auto

named_theorems rewrite_bv_or_one \<open>automatically_generated\<close>

lemma [rewrite_bv_or_one]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "y = not (Word.Word (0::int)) \<longrightarrow>
   or x y = not (Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_xor_duplicate \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_duplicate]:
  fixes x::"'a::len word"
  shows "semiring_bit_operations_class.xor x x = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_xor_ones \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_ones]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "y = not (Word.Word (0::int)) \<longrightarrow>
   semiring_bit_operations_class.xor x y = not x"
  by auto

named_theorems rewrite_bv_xor_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "semiring_bit_operations_class.xor x (Word.Word (0::int)) = x"
  by auto

named_theorems rewrite_bv_bitwise_not_and \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_not_and]:
  fixes x::"'a::len word"
  shows "and x (not x) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_bitwise_not_or \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_not_or]:
  fixes x::"'a::len word"
  shows "or x (not x) = not (Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_xor_not \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_not]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "semiring_bit_operations_class.xor (not x) (not y) =
   semiring_bit_operations_class.xor x y"
  by auto

named_theorems rewrite_bv_not_idemp \<open>automatically_generated\<close>

lemma [rewrite_bv_not_idemp]:
  fixes x::"'a::len word"
  shows "not (not x) = x"
  by auto

named_theorems rewrite_bv_ult_zero_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_1]:
  fixes x::"'a::len word" and n::"int"
  shows "(Word.Word (0::int) < x) = (Word.Word (0::int) \<noteq> x)"
  by auto

named_theorems rewrite_bv_ult_zero_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_2]:
  fixes x::"'a::len word" and n::"int"
  shows "(x < Word.Word (0::int)) = False"
  by auto

named_theorems rewrite_bv_ult_self \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_self]:
  fixes x::"'a::len word"
  shows "(x < x) = False"
  by auto

named_theorems rewrite_bv_lt_self \<open>automatically_generated\<close>

lemma [rewrite_bv_lt_self]:
  fixes x::"'a::len word"
  shows "(x <s x) = False"
  by auto

named_theorems rewrite_bv_ule_self \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_self]:
  fixes x::"'a::len word"
  shows "(x \<le> x) = True"
  by auto

named_theorems rewrite_bv_ule_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "(x \<le> Word.Word (0::int)) = (x = Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_zero_ule \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ule]:
  fixes x::"'a::len word" and n::"int"
  shows "(Word.Word (0::int) \<le> x) = True"
  by auto

named_theorems rewrite_bv_sle_self \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_self]:
  fixes x::"'a::len word"
  shows "(x \<le>s x) = True"
  by auto

named_theorems rewrite_bv_ule_max \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_max]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "y = not (Word.Word (0::int)) \<longrightarrow> (x \<le> y) = True"
  by auto

named_theorems rewrite_bv_not_ult \<open>automatically_generated\<close>

lemma [rewrite_bv_not_ult]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "(\<not> x < y) = (y \<le> x)"
  by auto

named_theorems rewrite_bv_not_ule \<open>automatically_generated\<close>

lemma [rewrite_bv_not_ule]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "(\<not> x \<le> y) = (y < x)"
  by auto

named_theorems rewrite_bv_not_sle \<open>automatically_generated\<close>

lemma [rewrite_bv_not_sle]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "(\<not> x \<le>s y) = (y <s x)"
  by auto

named_theorems rewrite_bv_mult_pow2_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_pow2_1]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and z::"'a::len word" and size::"int" and n::"int"
  shows "is_pow2 n \<longrightarrow>
   cvc_list_right (*) (cvc_list_left (*) xs z * Word.Word n) ys =
   word_cat
    (smt_extract
      (nat (size - int (floorlog (nat n) (2::nat)) - (1::int)))
      (nat (0::int)) (cvc_list_right (*) (cvc_list_left (*) xs z) ys))
    (Word.Word (0::int))"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_mult_pow2_1_lemma)
  done

named_theorems rewrite_bv_mult_pow2_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_pow2_2]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and z::"'a::len word" and size::"int" and n::"int"
  shows "is_pow2 (- n) \<longrightarrow>
   cvc_list_right (*) (cvc_list_left (*) xs z * Word.Word n) ys =
   - word_cat
      (smt_extract
        (nat (size - int (floorlog (nat (- n)) (2::nat)) - (1::int)))
        (nat (0::int)) (cvc_list_right (*) (cvc_list_left (*) xs z) ys))
      (Word.Word (0::int))"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_mult_pow2_2_lemma)
  done

named_theorems rewrite_bv_extract_mult_leading_bit \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_mult_leading_bit]:
  fixes high::"int" and low::"int" and x1i::"int" and x1in::"int" and x2::"'a::len word" and y1i::"int" and y1in::"int" and y2::"'b::len word"
  shows "(64::int) < x1in + int (size x2) \<and>
   low
   < (2::int) * (x1in + int (size x2)) -
     ((if x1i = (0::int) then x1in
       else x1in - int (floorlog (nat x1i) (2::nat))) +
      (if y1i = (0::int) then y1in
       else y1in - int (floorlog (nat y1i) (2::nat)))) \<longrightarrow>
   smt_extract (nat high) (nat low)
    (word_cat (Word.Word x1i) x2 * word_cat (Word.Word y1i) y2) =
   Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_neg_idemp \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_idemp]:
  fixes x::"'a::len word"
  shows "- (- x) = x"
  by auto

named_theorems rewrite_bv_udiv_pow2_1p \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_1p]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "is_pow2 v \<and> (1::int) < v \<longrightarrow>
   x div Word.Word v =
   word_cat (Word.Word (0::int))
    (smt_extract (nat (n - (1::int)))
      (nat (int (floorlog (nat v) (2::nat)))) x)"
  by auto

named_theorems rewrite_bv_udiv_pow2_1n \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_1n]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "is_pow2 (- v) \<and> v < - (1::int) \<longrightarrow>
   x div Word.Word v =
   - word_cat (Word.Word (0::int))
      (smt_extract (nat (n - (1::int)))
        (nat (int (floorlog (nat (- v)) (2::nat)))) x)"
  by auto

named_theorems rewrite_bv_udiv_pow2_2p \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_2p]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "v = (1::int) \<longrightarrow> x div Word.Word v = x"
  by auto

named_theorems rewrite_bv_udiv_pow2_2n \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_2n]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "v = - (1::int) \<longrightarrow> x div Word.Word v = - x"
  by auto

named_theorems rewrite_bv_udiv_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "x div Word.Word (0::int) = not (Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_udiv_one \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_one]:
  fixes x::"'a::len word" and n::"int"
  shows "x div Word.Word (1::int) = x"
  by auto

named_theorems rewrite_bv_urem_pow2_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_pow2_1]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "is_pow2 v \<and> (1::int) < v \<longrightarrow>
   smt_urem x (Word.Word v) =
   word_cat (Word.Word (0::int))
    (smt_extract (nat (int (floorlog (nat v) (2::nat)) - (1::int)))
      (nat (0::int)) x)"
  by auto

named_theorems rewrite_bv_urem_pow2_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_pow2_2]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "is_pow2 (- v) \<and> v < - (1::int) \<longrightarrow>
   smt_urem x (Word.Word v) =
   word_cat (Word.Word (0::int))
    (smt_extract (nat (int (floorlog (nat (- v)) (2::nat)) - (1::int)))
      (nat (0::int)) x)"
  by auto

named_theorems rewrite_bv_urem_one_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_one_1]:
  fixes x::"'a::len word" and n::"int"
  shows "smt_urem x (Word.Word (1::int)) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_urem_one_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_one_2]:
  fixes x::"'a::len word" and v::"int" and n::"int"
  shows "v = - (1::int) \<longrightarrow>
   smt_urem x (Word.Word v) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_urem_self \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_self]:
  fixes x::"'a::len word"
  shows "smt_urem x x = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_shl_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_zero]:
  fixes a::"'a::len word" and n::"int"
  shows "push_bit (unat a) (Word.Word (0::int)) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_lshr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_zero]:
  fixes a::"'a::len word" and n::"int"
  shows "drop_bit (unat a) (Word.Word (0::int)) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_ashr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_zero]:
  fixes a::"'a::len word" and n::"int"
  shows "signed_drop_bit (unat a) (Word.Word (0::int)) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_ugt_urem \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_urem]:
  fixes y::"'a::len word" and x::"'a::len word"
  shows "(x < smt_urem y x) =
   (Word.Word (0::int) < y \<and> x = Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_ult_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_one]:
  fixes x::"'a::len word" and n::"int"
  shows "(x < Word.Word (1::int)) = (x = Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_slt_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_slt_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "(x <s Word.Word (0::int)) =
   (smt_extract (nat (n - (1::int))) (nat (n - (1::int))) x =
    Word.Word (1::int))"
  by auto

named_theorems rewrite_bv_zero_ult \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ult]:
  fixes x::"'a::len word" and n::"int"
  shows "(Word.Word (0::int) < x) = (x \<noteq> Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_merge_sign_extend_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_1]:
  fixes x::"'a::len word" and i::"int" and j::"int"
  shows "Word.signed_cast (Word.signed_cast x) = Word.signed_cast x"
  by auto

named_theorems rewrite_bv_merge_sign_extend_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_2]:
  fixes x::"'a::len word" and i::"int" and j::"int"
  shows "(1::int) < j \<longrightarrow>
   Word.signed_cast (Word.cast x) = Word.cast x"
  by auto

named_theorems rewrite_bv_merge_sign_extend_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_3]:
  fixes x::"'a::len word" and i::"int"
  shows "Word.signed_cast (Word.cast x) = Word.signed_cast x"
  by auto

named_theorems rewrite_bv_sign_extend_eq_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eq_const_1]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "(Word.signed_cast x = Word.Word c) =
   ((smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
      (Word.Word c) =
     Word.Word (0::int) \<or>
     smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
      (Word.Word c) =
     not (Word.Word (0::int))) \<and>
    x =
    smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
     (Word.Word c))"
  by auto

named_theorems rewrite_bv_sign_extend_eq_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eq_const_2]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "(Word.Word c = Word.signed_cast x) =
   ((smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
      (Word.Word c) =
     Word.Word (0::int) \<or>
     smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
      (Word.Word c) =
     not (Word.Word (0::int))) \<and>
    x =
    smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
     (Word.Word c))"
  by auto

named_theorems rewrite_bv_zero_extend_eq_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eq_const_1]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "(Word.cast x = Word.Word c) =
   (smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
     (Word.Word c) =
    Word.Word (0::int) \<and>
    x =
    smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
     (Word.Word c))"
  by auto

named_theorems rewrite_bv_zero_extend_eq_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eq_const_2]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "(Word.Word c = Word.cast x) =
   (smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
     (Word.Word c) =
    Word.Word (0::int) \<and>
    x =
    smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
     (Word.Word c))"
  by auto

named_theorems rewrite_bv_zero_extend_ult_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_ult_const_1]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "smt_extract (nat (nm - (1::int))) (nat (int (size x)))
    (Word.Word c) =
   Word.Word (0::int) \<longrightarrow>
   (Word.cast x < Word.Word c) =
   (x < smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
         (Word.Word c))"
  by auto

named_theorems rewrite_bv_zero_extend_ult_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_ult_const_2]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "smt_extract (nat (nm - (1::int))) (nat (int (size x)))
    (Word.Word c) =
   Word.Word (0::int) \<longrightarrow>
   (Word.Word c < Word.cast x) =
   (smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
     (Word.Word c)
    < x)"
  by auto

named_theorems rewrite_bv_sign_extend_ult_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_1]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "Word.Word c
   \<le> push_bit (unat (Word.Word (1::int)))
          (Word.Word (int (size x) - (1::int))) \<or>
   push_bit (unat (not (Word.Word (0::int))))
    (Word.Word (int (size x) - (1::int)))
   \<le> Word.Word c \<longrightarrow>
   (Word.signed_cast x < Word.Word c) =
   (x < smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
         (Word.Word c))"
  by auto

named_theorems rewrite_bv_sign_extend_ult_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_2]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "push_bit (unat (Word.Word (1::int)))
    (Word.Word (int (size x) - (1::int)))
   < Word.Word c \<and>
   Word.Word c
   \<le> push_bit (unat (not (Word.Word (0::int))))
          (Word.Word (int (size x) - (1::int))) \<longrightarrow>
   (Word.signed_cast x < Word.Word c) =
   (smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) x =
    Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_sign_extend_ult_const_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_3]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "Word.Word c
   < push_bit (unat (Word.Word (1::int)))
      (Word.Word (int (size x) - (1::int))) \<or>
   not (push_bit (unat (Word.Word (1::int)))
         (Word.Word (int (size x) - (1::int))))
   \<le> Word.Word c \<longrightarrow>
   (Word.Word c < Word.signed_cast x) =
   (smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
     (Word.Word c)
    < x)"
  by auto

named_theorems rewrite_bv_sign_extend_ult_const_4 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_4]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "not (push_bit (unat (not (Word.Word (0::int))))
         (Word.Word (int (size x) - (1::int))))
   \<le> Word.Word c \<and>
   Word.Word c
   \<le> not (push_bit (unat (Word.Word (1::int)))
               (Word.Word (int (size x) - (1::int)))) \<longrightarrow>
   (Word.Word c < Word.signed_cast x) =
   (smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) x =
    Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_extract_bitwise_and \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_and]:
  fixes x::"'a::len word" and y::"'a::len word" and i::"int" and j::"int"
  shows "smt_extract (nat j) (nat i) (and x y) =
   and (smt_extract (nat j) (nat i) x)
    (smt_extract (nat j) (nat i) y)"
  by auto

named_theorems rewrite_bv_extract_bitwise_or \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_or]:
  fixes x::"'a::len word" and y::"'a::len word" and i::"int" and j::"int"
  shows "smt_extract (nat j) (nat i) (or x y) =
   or (smt_extract (nat j) (nat i) x)
    (smt_extract (nat j) (nat i) y)"
  by auto

named_theorems rewrite_bv_extract_bitwise_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_xor]:
  fixes x::"'a::len word" and y::"'a::len word" and i::"int" and j::"int"
  shows "smt_extract (nat j) (nat i) (semiring_bit_operations_class.xor x y) =
   semiring_bit_operations_class.xor (smt_extract (nat j) (nat i) x)
    (smt_extract (nat j) (nat i) y)"
  by auto

named_theorems rewrite_bv_extract_not \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_not]:
  fixes x::"'a::len word" and i::"int" and j::"int"
  shows "smt_extract (nat j) (nat i) (not x) =
   not (smt_extract (nat j) (nat i) x)"
  by auto

named_theorems rewrite_bv_extract_sign_extend_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_1]:
  fixes x::"'a::len word" and low::"int" and high::"int" and k::"int"
  shows "high < int (size x) \<longrightarrow>
   smt_extract (nat high) (nat low) (Word.signed_cast x) =
   smt_extract (nat high) (nat low) x"
  by auto

named_theorems rewrite_bv_extract_sign_extend_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_2]:
  fixes x::"'a::len word" and low::"int" and high::"int" and k::"int"
  shows "low < int (size x) \<and> int (size x) \<le> high \<longrightarrow>
   smt_extract (nat high) (nat low) (Word.signed_cast x) =
   Word.signed_cast
    (smt_extract (nat (int (size x) - (1::int))) (nat low) x)"
  by auto

named_theorems rewrite_bv_extract_sign_extend_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_3]:
  fixes x::"'a::len word" and low::"int" and high::"int" and k::"int"
  shows "int (size x) \<le> low \<longrightarrow>
   smt_extract (nat high) (nat low) (Word.signed_cast x) =
   smt_repeat (nat ((1::int) + (high - low)))
    (smt_extract (nat (int (size x) - (1::int)))
      (nat (int (size x) - (1::int))) x)"
  by auto

named_theorems rewrite_bv_neg_mult \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_mult]:
  fixes xs::"'a::len word" and ys::"'a::len word" and n::"int" and m::"int"
  shows "- (xs * Word.Word n * ys) = xs * Word.Word (- n) * ys"
  by auto

named_theorems rewrite_bv_neg_sub \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_sub]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "- (x - y) = y - x"
  by auto

named_theorems rewrite_bv_neg_add \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_add]:
  fixes x::"'a::len word" and y::"'a::len word" and zs::"'a::len word cvc_ListVar"
  shows "- (x + cvc_list_right (+) y zs) = - x + - cvc_list_right (+) y zs"
  apply (cases zs)
  subgoal for zss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_neg_add_lemma)
  done

named_theorems rewrite_bv_mult_distrib_const_neg \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_neg]:
  fixes x::"'a::len word" and n::"int" and m::"int"
  shows "- x * Word.Word n = x * Word.Word (- n)"
  by auto

named_theorems rewrite_bv_mult_distrib_const_add \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_add]:
  fixes x::"'a::len word" and y::"'a::len word" and n::"int" and m::"int"
  shows "(x + y) * Word.Word n = x * Word.Word n + y * Word.Word n"
  by auto

named_theorems rewrite_bv_mult_distrib_const_sub \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_sub]:
  fixes x::"'a::len word" and y::"'a::len word" and n::"int" and m::"int"
  shows "(x - y) * Word.Word n = x * Word.Word n - y * Word.Word n"
  by auto

named_theorems rewrite_bv_mult_distrib_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_1]:
  fixes x1::"'a::len word" and x2::"'a::len word" and y::"'a::len word"
  shows "(x1 + x2) * y = x1 * y + x2 * y"
  by auto

named_theorems rewrite_bv_mult_distrib_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_2]:
  fixes x1::"'a::len word" and x2::"'a::len word" and y::"'a::len word"
  shows "y * (x1 + x2) = y * x1 + y * x2"
  by auto

named_theorems rewrite_bv_not_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_not_xor]:
  fixes x::"'a::len word" and xs::"'a::len word cvc_ListVar"
  shows "not (cvc_list_right semiring_bit_operations_class.xor x xs) =
   cvc_list_right semiring_bit_operations_class.xor (not x) xs"
  apply (cases xs)
  subgoal for xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_not_xor_lemma)
  done

named_theorems rewrite_bv_and_simplify_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_and_simplify_1]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "cvc_list_right and
    (and (cvc_list_right and (cvc_list_left and xs x) ys) x) zs =
   cvc_list_right and (cvc_list_right and (cvc_list_left and xs x) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_and_simplify_1_lemma)
  done

named_theorems rewrite_bv_and_simplify_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_and_simplify_2]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "cvc_list_right and
    (and (cvc_list_right and (cvc_list_left and xs x) ys) (not x)) zs =
   Word.Word (0::int)"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_and_simplify_2_lemma)
  done

named_theorems rewrite_bv_or_simplify_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_or_simplify_1]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "cvc_list_right or (or (cvc_list_right or (cvc_list_left or xs x) ys) x)
    zs =
   cvc_list_right or (cvc_list_right or (cvc_list_left or xs x) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_or_simplify_1_lemma)
  done

named_theorems rewrite_bv_or_simplify_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_or_simplify_2]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "cvc_list_right or
    (or (cvc_list_right or (cvc_list_left or xs x) ys) (not x)) zs =
   not (Word.Word (0::int))"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_or_simplify_2_lemma)
  done

named_theorems rewrite_bv_xor_simplify_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_simplify_1]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "cvc_list_right semiring_bit_operations_class.xor
    (semiring_bit_operations_class.xor
      (cvc_list_right semiring_bit_operations_class.xor
        (cvc_list_left semiring_bit_operations_class.xor xs x) ys)
      x)
    zs =
   cvc_list_right semiring_bit_operations_class.xor
    (cvc_list_both semiring_bit_operations_class.xor (0::'a::len word) xs
      ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_xor_simplify_1_lemma)
  done

named_theorems rewrite_bv_xor_simplify_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_simplify_2]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "cvc_list_right semiring_bit_operations_class.xor
    (semiring_bit_operations_class.xor
      (cvc_list_right semiring_bit_operations_class.xor
        (cvc_list_left semiring_bit_operations_class.xor xs x) ys)
      (not x))
    zs =
   not (cvc_list_right semiring_bit_operations_class.xor
         (cvc_list_both semiring_bit_operations_class.xor
           (0::'a::len word) xs ys)
         zs)"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_xor_simplify_2_lemma)
  done

named_theorems rewrite_bv_xor_simplify_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_simplify_3]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "cvc_list_right semiring_bit_operations_class.xor
    (semiring_bit_operations_class.xor
      (cvc_list_right semiring_bit_operations_class.xor
        (cvc_list_left semiring_bit_operations_class.xor xs (not x)) ys)
      x)
    zs =
   not (cvc_list_right semiring_bit_operations_class.xor
         (cvc_list_both semiring_bit_operations_class.xor
           (0::'a::len word) xs ys)
         zs)"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_xor_simplify_3_lemma)
  done

named_theorems rewrite_bv_ult_add_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_add_one]:
  fixes x::"'a::len word" and y::"'a::len word" and n::"int"
  shows "(x < y + Word.Word (1::int)) =
   (\<not> y < x \<and> y \<noteq> not (Word.Word (0::int)))"
  by auto

named_theorems rewrite_bv_concat_to_mult \<open>automatically_generated\<close>

lemma [rewrite_bv_concat_to_mult]:
  fixes x::"'a::len word" and i::"int" and m::"int"
  shows "(1::int) + i + m = int (size x) \<longrightarrow>
   word_cat (smt_extract (nat i) (nat (0::int)) x)
    (Word.Word (0::int)) =
   x * push_bit (unat (Word.Word m)) (Word.Word (1::int))"
  by auto

named_theorems rewrite_bv_mult_slt_mult_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_slt_mult_1]:
  fixes x::"'a::len word" and t::"'a::len word" and a::"'b::len word" and n::"int" and m::"int"
  shows "(Word.signed_cast (x + t) * Word.signed_cast a
    <s Word.signed_cast x * Word.signed_cast a) =
   (t \<noteq> Word.Word (0::int) \<and>
    a \<noteq> Word.Word (0::int) \<and>
    (x + t <s x) = (Word.Word (0::int) <s a))"
  by auto

named_theorems rewrite_bv_mult_slt_mult_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_slt_mult_2]:
  fixes x::"'a::len word" and t::"'a::len word" and a::"'b::len word" and n::"int" and m::"int"
  shows "(Word.cast (x + t) * Word.signed_cast a
    <s Word.cast x * Word.signed_cast a) =
   (t \<noteq> Word.Word (0::int) \<and>
    a \<noteq> Word.Word (0::int) \<and>
    (x + t < x) = (Word.Word (0::int) <s a))"
  by auto

named_theorems rewrite_bv_commutative_and \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_and]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "and x y = and y x"
  by auto

named_theorems rewrite_bv_commutative_or \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_or]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "or x y = or y x"
  by auto

named_theorems rewrite_bv_commutative_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_xor]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "semiring_bit_operations_class.xor x y =
   semiring_bit_operations_class.xor y x"
  by auto

named_theorems rewrite_bv_commutative_add \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_add]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "x + y = y + x"
  by auto

named_theorems rewrite_bv_commutative_mul \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_mul]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "x * y = y * x"
  by auto

named_theorems rewrite_bv_or_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_or_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "or x (Word.Word (0::int)) = x"
  by auto

named_theorems rewrite_bv_mul_one \<open>automatically_generated\<close>

lemma [rewrite_bv_mul_one]:
  fixes x::"'a::len word" and n::"int"
  shows "x * Word.Word (1::int) = x"
  by auto

named_theorems rewrite_bv_mul_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_mul_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "x * Word.Word (0::int) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_add_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_add_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "x + Word.Word (0::int) = x"
  by auto

named_theorems rewrite_bv_add_two \<open>automatically_generated\<close>

lemma [rewrite_bv_add_two]:
  fixes x::"'a::len word"
  shows "x + x = x * Word.Word (2::int)"
  by auto

named_theorems rewrite_bv_zero_extend_eliminate_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eliminate_0]:
  fixes x::"'a::len word"
  shows "Word.cast x = x"
  by auto

named_theorems rewrite_bv_sign_extend_eliminate_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eliminate_0]:
  fixes x::"'a::len word"
  shows "Word.signed_cast x = x"
  by auto

named_theorems rewrite_bv_not_neq \<open>automatically_generated\<close>

lemma [rewrite_bv_not_neq]:
  fixes x::"'a::len word"
  shows "(0::int) < int (size x) \<longrightarrow> (x = not x) = False"
  by auto

named_theorems rewrite_bv_ult_ones \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_ones]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "y = not (Word.Word (0::int)) \<longrightarrow> (x < y) = (x \<noteq> y)"
  by auto

named_theorems rewrite_bv_or_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_or_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "cvc_list_right or (cvc_list_left or xs (cvc_list_right or s ys)) zs =
   cvc_list_right or (cvc_list_right or (cvc_list_left or xs s) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_or_flatten_lemma)
  done

named_theorems rewrite_bv_xor_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "cvc_list_right semiring_bit_operations_class.xor
    (cvc_list_left semiring_bit_operations_class.xor xs
      (cvc_list_right semiring_bit_operations_class.xor s ys))
    zs =
   cvc_list_right semiring_bit_operations_class.xor
    (cvc_list_right semiring_bit_operations_class.xor
      (cvc_list_left semiring_bit_operations_class.xor xs s) ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_xor_flatten_lemma)
  done

named_theorems rewrite_bv_and_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_and_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "cvc_list_right and (cvc_list_left and xs (cvc_list_right and s ys)) zs =
   cvc_list_right and (cvc_list_right and (cvc_list_left and xs s) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_and_flatten_lemma)
  done

named_theorems rewrite_bv_mul_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_mul_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "cvc_list_right (*) (cvc_list_left (*) xs (cvc_list_right (*) s ys)) zs =
   cvc_list_right (*) (cvc_list_right (*) (cvc_list_left (*) xs s) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_mul_flatten_lemma)
  done

end