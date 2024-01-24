theory BV_Rewrites3
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

named_theorems rewrite_bv_concat_extract_merge \<open>automatically_generated\<close>

lemma [rewrite_bv_concat_extract_merge]:
  fixes xs::"'a ::len word cvc_ListVar" and s::"'b ::len word" and ys::"'a ::len word cvc_ListVar" and i::"int" and j::"int" and k::"int"
  shows "x_c4 = cvc_list_right word_cat (cvc_list_left word_cat xs x_c3) ys \<and>
   int (size x_c4) = int (size xs) + int (size x_c3) + int (size ys) \<and>
   x_c3 = smt_extract (nat k) (nat i) s \<and>
   x_c2 = cvc_list_right word_cat (word_cat (cvc_list_left word_cat xs x_c0) x_c1) ys \<and>
   x_c1 = smt_extract (nat j) (nat i) s \<and>
   x_c0 = smt_extract (nat k) (nat (j + 1)) s \<and>
   int (size x_c3) = 1 + (k - i) \<and>
   int (size x_c2) = int (size xs) + int (size x_c0) + int (size x_c1) + int (size ys) \<and>
   int (size x_c1) = 1 + (j - i) \<and>
   int (size x_c0) = 1 + (k - (j + 1)) \<and>
   i \<le> k \<and> j < int (size s) \<and>
   i \<le> j \<and> 0 \<le> i \<and> k < int (size s) \<and>
   j + 1 \<le> k \<and> 0 \<le> j + 1 \<longrightarrow>
   x_c2 = x_c4"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: word_size)
    by (simp add: bv_concat_extract_merge_lemma)
  done

named_theorems rewrite_test_conat \<open>automatically_generated\<close>

lemma [rewrite_test_conat]:
  fixes s::"'a ::len word" and i::"int" and j::"int" and k::"int"
  shows "x_c3 = smt_extract (nat k) (nat i) s \<and>
   int (size x_c3) = 1 + (k - i) \<and>
   i \<le> k \<and>
   x_c2 = word_cat x_c0 x_c1 \<and>
   int (size x_c2) = int (size x_c0) + int (size x_c1) \<and>
   j < int (size s) \<and>
   x_c1 = smt_extract (nat j) (nat i) s \<and>
   int (size x_c1) = 1 + (j - i) \<and>
   i \<le> j \<and>
   0 \<le> i \<and>
   k < int (size s) \<and>
   x_c0 = smt_extract (nat k) (nat (j + 1)) s \<and>
   int (size x_c0) = 1 + (k - (j + 1)) \<and>
   j + 1 \<le> k \<and> 0 \<le> j + 1 \<longrightarrow>
   x_c2 = x_c3"
  by auto

named_theorems rewrite_bv_extract_whole \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_whole]:
  fixes x::"'a ::len word" and n::"int"
  shows "n - 1 < int (size x) \<and>
   x_c0 = smt_extract (nat (n - 1)) (nat 0) x \<and>
   int (size x_c0) = 1 + (n - 1 - 0) \<and>
   0 \<le> n - 1  \<longrightarrow>
   n = int (size x) \<longrightarrow> x_c0 = x"
  unfolding smt_extract_def
  by (metis Suc_nat_eq_nat_zadd1 diff_zero nat_int nat_zero_as_int size_word.rep_eq slice_id take_bit_length_eq)

named_theorems rewrite_bv_extract_concat_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_concat_1]:
  fixes x::"'a ::len word" and xs::"'b ::len word cvc_ListVar" and y::"'b ::len word" and i::"int" and j::"int"
  shows "x_c3 = word_cat (cvc_list_left word_cat xs y) x_c2 \<and>
   int (size x_c3) = int (size xs) + int (size y) + int (size x_c2) \<and>
   j < int (size x) \<and>
   x_c2 = smt_extract (nat j) (nat i) x \<and>
   int (size x_c2) = 1 + (j - i) \<and>
   j < int (size x_c0) \<and>
   x_c1 = smt_extract (nat j) (nat i) x_c0 \<and>
   int (size x_c1) = 1 + (j - i) \<and>
   i \<le> j \<and>
   0 \<le> i \<and>
   x_c0 = word_cat (cvc_list_left word_cat xs y) x \<and>
   int (size x_c0) =
   int (size xs) + int (size y) + int (size x) \<longrightarrow>
   j \<le> int (size x) \<longrightarrow> x_c1 = x_c3"
  apply (cases xs)
  subgoal for xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_extract_concat_1_lemma)
  done

named_theorems rewrite_bv_extract_concat_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_concat_2]:
  fixes x::"'a ::len word" and xs::"'b ::len word cvc_ListVar" and y::"'b ::len word" and i::"int" and j::"int"
  shows "x_c5 = word_cat x_c3 x_c4 \<and>
   int (size x_c5) = int (size x_c3) + int (size x_c4) \<and>
   int (size x) - 1 < int (size x) \<and>
   x_c4 = smt_extract (nat (int (size x) - 1)) (nat i) x \<and>
   int (size x_c4) = 1 + (int (size x) - 1 - i) \<and>
   i \<le> int (size x) - 1 \<and>
   j - int (size x) < int (size x_c2) \<and>
   x_c3 = smt_extract (nat (j - int (size x))) (nat 0) x_c2 \<and>
   int (size x_c3) = 1 + (j - int (size x) - 0) \<and>
   0 \<le> j - int (size x) \<and>
   0 \<le> 0 \<and>
   x_c2 = cvc_list_left word_cat xs y \<and>
   int (size x_c2) = int (size xs) + int (size y) \<and>
   j < int (size x_c0) \<and>
   x_c1 = smt_extract (nat j) (nat i) x_c0 \<and>
   int (size x_c1) = 1 + (j - i) \<and>
   i \<le> j \<and>
   0 \<le> i \<and>
   x_c0 = word_cat (cvc_list_left word_cat xs y) x \<and>
   int (size x_c0) =
   int (size xs) + int (size y) + int (size x) \<longrightarrow>
   i < int (size x) \<and> int (size x) \<le> j \<longrightarrow>
   x_c1 = x_c5"
  apply (cases xs)
  subgoal for xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_extract_concat_2_lemma)
  done

named_theorems rewrite_bv_extract_concat_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_concat_3]:
  fixes x::"'a ::len word" and y::"'b ::len word" and xs::"'b ::len word cvc_ListVar" and i::"int" and j::"int"
  shows "j - int (size x) < int (size x_c2) \<and>
   x_c3 =
   smt_extract (nat (j - int (size x))) (nat (i - int (size x)))
    x_c2 \<and>
   int (size x_c3) = 1 + (j - int (size x) - (i - int (size x))) \<and>
   i - int (size x) \<le> j - int (size x) \<and>
   0 \<le> i - int (size x) \<and>
   x_c2 = cvc_list_left word_cat xs y \<and>
   int (size x_c2) = int (size xs) + int (size y) \<and>
   j < int (size x_c0) \<and>
   x_c1 = smt_extract (nat j) (nat i) x_c0 \<and>
   int (size x_c1) = 1 + (j - i) \<and>
   i \<le> j \<and>
   0 \<le> i \<and>
   x_c0 = word_cat (cvc_list_left word_cat xs y) x \<and>
   int (size x_c0) =
   int (size xs) + int (size y) + int (size x) \<longrightarrow>
   int (size x) \<le> i \<longrightarrow> x_c1 = x_c3"
  apply (cases xs)
  subgoal for xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_extract_concat_3_lemma)
  done

named_theorems rewrite_bv_ugt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(y < x) = (y < x)"
  by auto

named_theorems rewrite_bv_uge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_uge_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(y \<le> x) = (y \<le> x)"
  by auto

named_theorems rewrite_bv_sgt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sgt_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(y <s x) = (y <s x)"
  by auto

named_theorems rewrite_bv_sge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sge_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(y \<le>s x) = (y \<le>s x)"
  by auto

named_theorems rewrite_bv_slt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_slt_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(x <s y) =
   (x + push_bit (unat (Word.Word (int (size x) - 1))) (Word.Word 1)
    < y + push_bit (unat (Word.Word (int (size x) - 1))) (Word.Word 1))"
  by auto

named_theorems rewrite_bv_sle_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(x \<le>s y) = (\<not> y <s x)"
  by auto

named_theorems rewrite_bv_redor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redor_eliminate]:
  fixes x::"'a ::len word"
  shows "smt_redor x = not (smt_comp x (Word.Word 0))"
  by auto

named_theorems rewrite_bv_redand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redand_eliminate]:
  fixes x::"'a ::len word"
  shows "smt_redand x = not (smt_comp x (not (Word.Word 0)))"
  by auto

named_theorems rewrite_bv_sub_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sub_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "x - y = x + - y"
  by auto

named_theorems rewrite_bv_ule_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(x \<le> y) = (\<not> y < x)"
  by auto

named_theorems rewrite_bv_comp_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_comp_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "smt_comp x y = (if x = y then Word.Word 1 else Word.Word 0)"
  by auto

named_theorems rewrite_bv_repeat_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_1]:
  fixes x::"'a ::len word" and n::"int"
  shows "x_c2 = word_cat x x_c1 \<and>
   int (size x_c2) = int (size x) + int (size x_c1) \<and>
   x_c1 = smt_repeat (nat (n - 1)) x \<and>
   int (size x_c1) = int (size x) * (n - 1) \<and>
   0 \<le> n - 1 \<and>
   x_c0 = smt_repeat (nat n) x \<and>
   int (size x_c0) = int (size x) * n \<and> 0 \<le> n \<longrightarrow>
   1 < n \<longrightarrow> x_c0 = x_c2"
  by auto

named_theorems rewrite_bv_repeat_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_2]:
  fixes x::"'a ::len word"
  shows "x_c0 = smt_repeat (nat 1) x \<and>
   int (size x_c0) = int (size x) * 1 \<and> 0 \<le> 1 \<longrightarrow>
   x_c0 = x"
  by auto

named_theorems rewrite_bv_rotate_left_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_1]:
  fixes x::"'a ::len word" and amount::"int"
  shows "x_c2 = word_cat x_c0 x_c1 \<and>
   int (size x_c2) = int (size x_c0) + int (size x_c1) \<and>
   0 < int (size x) \<and>
   x_c1 = smt_extract (nat 0) (nat amount) x \<and>
   int (size x_c1) = 1 + (0 - amount) \<and>
   amount \<le> 0 \<and>
   int (size x) - (1 + amount) < int (size x) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - (1 + amount))) (nat 0) x \<and>
   int (size x_c0) = 1 + (int (size x) - (1 + amount) - 0) \<and>
   0 \<le> int (size x) - (1 + amount) \<and>
   0 \<le> 0 \<and> 0 \<le> amount \<longrightarrow>
   word_rotl (nat amount) x = x_c2"
  by auto

named_theorems rewrite_bv_rotate_left_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_2]:
  fixes x::"'a ::len word"
  shows "0 \<le> 0 \<longrightarrow> word_rotl (nat 0) x = x"
  by auto

named_theorems rewrite_bv_rotate_right_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_1]:
  fixes x::"'a ::len word" and amount::"int"
  shows "x_c2 = word_cat x_c0 x_c1 \<and>
   int (size x_c2) = int (size x_c0) + int (size x_c1) \<and>
   int (size x) - 1 < int (size x) \<and>
   x_c1 = smt_extract (nat (int (size x) - 1)) (nat amount) x \<and>
   int (size x_c1) = 1 + (int (size x) - 1 - amount) \<and>
   amount \<le> int (size x) - 1 \<and>
   amount - 1 < int (size x) \<and>
   x_c0 = smt_extract (nat (amount - 1)) (nat 0) x \<and>
   int (size x_c0) = 1 + (amount - 1 - 0) \<and>
   0 \<le> amount - 1 \<and>
   0 \<le> 0 \<and> 0 \<le> amount \<longrightarrow>
   word_rotr (nat amount) x = x_c2"
  by auto

named_theorems rewrite_bv_rotate_right_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_2]:
  fixes x::"'a ::len word"
  shows "0 \<le> 0 \<longrightarrow> word_rotr (nat 0) x = x"
  by auto

named_theorems rewrite_bv_nand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_nand_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "not (and x y) = not (and x y)"
  by auto

named_theorems rewrite_bv_nor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_nor_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "not (or x y) = not (or x y)"
  by auto

named_theorems rewrite_bv_xnor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_xnor_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "not (semiring_bit_operations_class.xor x y) =
   not (semiring_bit_operations_class.xor x y)"
  by auto

named_theorems rewrite_bv_sdiv_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sdiv_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "int (size x) - 1 < int (size y) \<and>
   x_c1 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    y \<and>
   int (size x_c1) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 < int (size x) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    x \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   0 \<le> int (size x) - 1 \<longrightarrow>
   x div y =
   (if (x_c0 = Word.Word 1) [+] (x_c1 = Word.Word 1)
    then - ((if x_c0 = Word.Word 1 then - x else x) div
            (if x_c1 = Word.Word 1 then - y else y))
    else (if x_c0 = Word.Word 1 then - x else x) div
         (if x_c1 = Word.Word 1 then - y else y))"
  by auto

named_theorems rewrite_bv_sdiv_eliminate_fewer_bitwise_ops \<open>automatically_generated\<close>

lemma [rewrite_bv_sdiv_eliminate_fewer_bitwise_ops]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "x_c0 = word_cat (Word.Word 1) (Word.Word 0) \<and>
   int (size x_c0) =
   int (size (Word.Word 1)) + int (size (Word.Word 0)) \<longrightarrow>
   x div y =
   (if (x_c0 \<le> x) [+] (x_c0 \<le> y)
    then - ((if x_c0 \<le> x then - x else x) div
            (if x_c0 \<le> y then - y else y))
    else (if x_c0 \<le> x then - x else x) div
         (if x_c0 \<le> y then - y else y))"
  by auto

named_theorems rewrite_bv_zero_extend_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eliminate]:
  fixes x::"'a ::len word" and n::"int"
  shows "x_c1 = word_cat (Word.Word 0) x \<and>
   int (size x_c1) = int (size (Word.Word 0)) + int (size x) \<and>
   x_c0 = push_bit (nat n) x \<and>
   int (size x_c0) = int (size x) + n \<and> 0 \<le> n \<longrightarrow>
   x_c0 = x_c1"
  by auto

named_theorems rewrite_bv_sign_extend_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eliminate]:
  fixes x::"'a ::len word" and n::"int"
  shows "x_c3 = word_cat x_c2 x \<and>
   int (size x_c3) = int (size x_c2) + int (size x) \<and>
   x_c2 = smt_repeat (nat n) x_c1 \<and>
   int (size x_c2) = int (size x_c1) * n \<and>
   int (size x) - 1 < int (size x) \<and>
   x_c1 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    x \<and>
   int (size x_c1) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   0 \<le> int (size x) - 1 \<and>
   x_c0 = signed_take_bit (nat n) x \<and>
   int (size x_c0) = int (size x) + n \<and> 0 \<le> n \<longrightarrow>
   x_c0 = x_c3"
  by auto

named_theorems rewrite_bv_uaddo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_uaddo_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "int (size x) < int (size (x_c0 + x_c1)) \<and>
   x_c2 =
   smt_extract (nat (int (size x))) (nat (int (size x)))
    (x_c0 + x_c1) \<and>
   int (size x_c2) = 1 + (int (size x) - int (size x)) \<and>
   int (size x) \<le> int (size x) \<and>
   0 \<le> int (size x) \<and>
   x_c1 = word_cat (Word.Word 0) y \<and>
   int (size x_c1) = int (size (Word.Word 0)) + int (size y) \<and>
   x_c0 = word_cat (Word.Word 0) x \<and>
   int (size x_c0) =
   int (size (Word.Word 0)) + int (size x) \<longrightarrow>
   smt_uaddo itself x y = (x_c2 = Word.Word 1)"
  by auto

named_theorems rewrite_bv_saddo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_saddo_eliminate]:
  fixes x::"'a ::len word" and y::"'b ::len word"
  shows "int (size x) - 1 < int (size (x_c0 + x_c1)) \<and>
   x_c2 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    (x_c0 + x_c1) \<and>
   int (size x_c2) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   0 \<le> int (size x) - 1 \<and>
   x_c1 = word_cat (Word.Word 0) y \<and>
   int (size x_c1) = int (size (Word.Word 0)) + int (size y) \<and>
   x_c0 = word_cat (Word.Word 0) x \<and>
   int (size x_c0) =
   int (size (Word.Word 0)) + int (size x) \<longrightarrow>
   smt_saddo itself x y = (x_c2 = Word.Word 1)"
  by auto

named_theorems rewrite_bv_sdivo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sdivo_eliminate]:
  fixes x::"'a ::len word" and y::"'b ::len word"
  shows "x_c0 = word_cat (Word.Word 1) (Word.Word 0) \<and>
   int (size x_c0) =
   int (size (Word.Word 1)) + int (size (Word.Word 0)) \<longrightarrow>
   smt_sdivo itself x y = (x = x_c0 \<and> y = not (Word.Word 0))"
  by auto

named_theorems rewrite_bv_smod_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_smod_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "int (size x) - 1 < int (size y) \<and>
   x_c1 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    y \<and>
   int (size x_c1) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 < int (size x) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    x \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   0 \<le> int (size x) - 1 \<longrightarrow>
   smt_smod x y =
   (if smt_urem (if x_c0 = Word.Word 1 then - x else x)
        (if x_c1 = Word.Word 1 then - y else y) =
       Word.Word 0
    then smt_urem (if x_c0 = Word.Word 1 then - x else x)
          (if x_c1 = Word.Word 1 then - y else y)
    else if x_c0 \<noteq> Word.Word 1 \<and> x_c1 \<noteq> Word.Word 1
         then smt_urem (if x_c0 = Word.Word 1 then - x else x)
               (if x_c1 = Word.Word 1 then - y else y)
         else if x_c0 = Word.Word 1 \<and> x_c1 \<noteq> Word.Word 1
              then - smt_urem (if x_c0 = Word.Word 1 then - x else x)
                      (if x_c1 = Word.Word 1 then - y else y) +
                   y
              else if x_c0 \<noteq> Word.Word 1 \<and> x_c1 = Word.Word 1
                   then smt_urem (if x_c0 = Word.Word 1 then - x else x)
                         (if x_c1 = Word.Word 1 then - y else y) +
                        y
                   else - smt_urem (if x_c0 = Word.Word 1 then - x else x)
                           (if x_c1 = Word.Word 1 then - y else y))"
  by auto

named_theorems rewrite_bv_smod_eliminate_fewer_bitwise_ops \<open>automatically_generated\<close>

lemma [rewrite_bv_smod_eliminate_fewer_bitwise_ops]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "x_c0 = word_cat (Word.Word 1) (Word.Word 0) \<and>
   int (size x_c0) =
   int (size (Word.Word 1)) + int (size (Word.Word 0)) \<longrightarrow>
   smt_smod x y =
   (if smt_urem (if x_c0 \<le> x then - x else x)
        (if x_c0 \<le> y then - y else y) =
       Word.Word 0
    then smt_urem (if x_c0 \<le> x then - x else x)
          (if x_c0 \<le> y then - y else y)
    else if \<not> x_c0 \<le> x \<and> \<not> x_c0 \<le> y
         then smt_urem (if x_c0 \<le> x then - x else x)
               (if x_c0 \<le> y then - y else y)
         else if x_c0 \<le> x \<and> \<not> x_c0 \<le> y
              then - smt_urem (if x_c0 \<le> x then - x else x)
                      (if x_c0 \<le> y then - y else y) +
                   y
              else if \<not> x_c0 \<le> x \<and> x_c0 \<le> y
                   then smt_urem (if x_c0 \<le> x then - x else x)
                         (if x_c0 \<le> y then - y else y) +
                        y
                   else - smt_urem (if x_c0 \<le> x then - x else x)
                           (if x_c0 \<le> y then - y else y))"
  by auto

named_theorems rewrite_bv_srem_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_srem_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "int (size x) - 1 < int (size y) \<and>
   x_c1 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    y \<and>
   int (size x_c1) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 < int (size x) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    x \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   0 \<le> int (size x) - 1 \<longrightarrow>
   smt_srem x y =
   (if bit x_c0 0
    then - smt_urem (if bit x_c0 0 then - x else x)
            (if bit x_c1 0 then - y else y)
    else smt_urem (if bit x_c0 0 then - x else x)
          (if bit x_c1 0 then - y else y))"
  by auto

named_theorems rewrite_bv_srem_eliminate_fewer_bitwise_ops \<open>automatically_generated\<close>

lemma [rewrite_bv_srem_eliminate_fewer_bitwise_ops]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "x_c0 = word_cat (Word.Word 1) (Word.Word 0) \<and>
   int (size x_c0) =
   int (size (Word.Word 1)) + int (size (Word.Word 0)) \<longrightarrow>
   smt_srem x y =
   (if x_c0 \<le> x
    then - smt_urem (if x_c0 \<le> x then - x else x)
            (if x_c0 \<le> y then - y else y)
    else smt_urem (if x_c0 \<le> x then - x else x)
          (if x_c0 \<le> y then - y else y))"
  by auto

named_theorems rewrite_bv_usubo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_usubo_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "int (size x) - 1 < int (size (x_c0 - x_c1)) \<and>
   x_c2 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    (x_c0 - x_c1) \<and>
   int (size x_c2) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   0 \<le> int (size x) - 1 \<and>
   x_c1 = push_bit (nat 1) y \<and>
   int (size x_c1) = int (size y) + 1 \<and>
   x_c0 = push_bit (nat 1) x \<and>
   int (size x_c0) = int (size x) + 1 \<and> 0 \<le> 1 \<longrightarrow>
   smt_usubo x y = (x_c2 = Word.Word 1)"
  by auto

named_theorems rewrite_bv_ssubo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ssubo_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "int (size x) - 1 < int (size (x - y)) \<and>
   x_c2 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    (x - y) \<and>
   int (size x_c2) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 < int (size y) \<and>
   x_c1 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    y \<and>
   int (size x_c1) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 < int (size x) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    x \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   0 \<le> int (size x) - 1 \<longrightarrow>
   smt_ssubo x y =
   (x_c0 = Word.Word 1 \<and>
    x_c1 \<noteq> Word.Word 1 \<and> x_c2 \<noteq> Word.Word 1 \<or>
    x_c0 \<noteq> Word.Word 1 \<and>
    x_c1 = Word.Word 1 \<and> x_c2 = Word.Word 1)"
  by auto

named_theorems rewrite_bv_ite_equal_children \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_children]:
  fixes c::"1 ::len word" and x::"'a ::len word"
  shows "(if bit c 0 then x else x) = x"
  by auto

named_theorems rewrite_bv_ite_const_children_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_1]:
  fixes c::"1 ::len word"
  shows "(if bit c 0 then Word.Word 0 else Word.Word 1) = not c"
  by auto

named_theorems rewrite_bv_ite_const_children_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_2]:
  fixes c::"1 ::len word"
  shows "(if bit c 0 then Word.Word 1 else Word.Word 0) = c"
  by auto

named_theorems rewrite_bv_ite_equal_cond_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_1]:
  fixes c0::"1 ::len word" and t0::"'a ::len word" and e0::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 0 then if bit c0 0 then t0 else e0 else e1) =
   (if bit c0 0 then t0 else e1)"
  by auto

named_theorems rewrite_bv_ite_equal_cond_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_2]:
  fixes c0::"1 ::len word" and t0::"'a ::len word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 0 then t0 else if bit c0 0 then t1 else e1) =
   (if bit c0 0 then t0 else e1)"
  by auto

named_theorems rewrite_bv_ite_equal_cond_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_3]:
  fixes c0::"1 ::len word" and t0::"'a ::len word" and e0::"'a ::len word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 0 then if bit c0 0 then t0 else e0
    else if bit c0 0 then t1 else e1) =
   (if bit c0 0 then t0 else e1)"
  by auto

named_theorems rewrite_bv_ite_merge_then_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_if]:
  fixes c0::"1 ::len word" and c1::"1 ::len word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 0 then if bit c1 0 then t1 else e1 else t1) =
   (if bit (and c0 (not c1)) 0 then e1 else t1)"
  by auto

named_theorems rewrite_bv_ite_merge_else_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_if]:
  fixes c0::"1 ::len word" and c1::"1 ::len word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 0 then if bit c1 0 then t1 else e1 else e1) =
   (if bit (and c0 c1) 0 then t1 else e1)"
  by auto

named_theorems rewrite_bv_ite_merge_then_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_else]:
  fixes c0::"1 ::len word" and c1::"1 ::len word" and t0::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 0 then t0 else if bit c1 0 then t0 else e1) =
   (if bit (not (or c0 c1)) 0 then e1 else t0)"
  by auto

named_theorems rewrite_bv_ite_merge_else_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_else]:
  fixes c0::"1 ::len word" and c1::"1 ::len word" and t1::"'a ::len word" and t0::"'a ::len word"
  shows "(if bit c0 0 then t0 else if bit c1 0 then t1 else t0) =
   (if bit (and (not c0) c1) 0 then t1 else t0)"
  by auto

named_theorems rewrite_bv_shl_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_1]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "x_c1 = word_cat x_c0 (Word.Word 0) \<and>
   int (size x_c1) = int (size x_c0) + int (size (Word.Word 0)) \<and>
   int (size x) < int (size x) \<and>
   x_c0 =
   smt_extract (nat (int (size x))) (nat (int (size x) - (1 + amount)))
    x \<and>
   int (size x_c0) =
   1 + (int (size x) - (int (size x) - (1 + amount))) \<and>
   int (size x) - (1 + amount) \<le> int (size x) \<and>
   0 \<le> int (size x) - (1 + amount) \<longrightarrow>
   amount < int (size x) \<longrightarrow>
   push_bit (unat (Word.Word amount)) x = x_c1"
  by auto

named_theorems rewrite_bv_shl_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_2]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow>
   push_bit (unat (Word.Word amount)) x = Word.Word 0"
  by auto

named_theorems rewrite_bv_lshr_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_1]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "x_c1 = word_cat (Word.Word 0) x_c0 \<and>
   int (size x_c1) = int (size (Word.Word 0)) + int (size x_c0) \<and>
   int (size x) - 1 < int (size x) \<and>
   x_c0 = smt_extract (nat (int (size x) - 1)) (nat amount) x \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - amount) \<and>
   amount \<le> int (size x) - 1 \<and> 0 \<le> amount \<longrightarrow>
   amount < int (size x) \<longrightarrow>
   drop_bit (unat (Word.Word amount)) x = x_c1"
  by auto

named_theorems rewrite_bv_lshr_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_2]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow>
   drop_bit (unat (Word.Word amount)) x = Word.Word 0"
  by auto

named_theorems rewrite_bv_ashr_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_by_const_1]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "x_c3 = word_cat x_c1 x_c2 \<and>
   int (size x_c3) = int (size x_c1) + int (size x_c2) \<and>
   x_c2 = smt_extract (nat (int (size x) - 1)) (nat amount) x \<and>
   int (size x_c2) = 1 + (int (size x) - 1 - amount) \<and>
   amount \<le> int (size x) - 1 \<and>
   x_c1 = smt_repeat (nat amount) x_c0 \<and>
   int (size x_c1) = int (size x_c0) * amount \<and>
   0 \<le> amount \<and>
   int (size x) - 1 < int (size x) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    x \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   0 \<le> int (size x) - 1 \<longrightarrow>
   amount < int (size x) \<longrightarrow>
   drop_bit (unat (Word.Word amount)) x = x_c3"
  by auto

named_theorems rewrite_bv_ashr_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_by_const_2]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "x_c1 = smt_repeat (nat (int (size x))) x_c0 \<and>
   int (size x_c1) = int (size x_c0) * int (size x) \<and>
   0 \<le> int (size x) \<and>
   int (size x) - 1 < int (size x) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    x \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   0 \<le> int (size x) - 1 \<longrightarrow>
   int (size x) \<le> amount \<longrightarrow>
   drop_bit (unat (Word.Word amount)) x = x_c1"
  by auto

named_theorems rewrite_bv_bitwise_idemp_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_idemp_1]:
  fixes x::"'a ::len word"
  shows "and x x = x"
  by auto

named_theorems rewrite_bv_bitwise_idemp_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_idemp_2]:
  fixes x::"'a ::len word"
  shows "or x x = x"
  by auto

named_theorems rewrite_bv_and_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_and_zero]:
  fixes x::"'a ::len word"
  shows "and x (Word.Word 0) = Word.Word 0"
  by auto

named_theorems rewrite_bv_and_one \<open>automatically_generated\<close>

lemma [rewrite_bv_and_one]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "y = not (Word.Word 0) \<longrightarrow> and x y = x"
  by auto

named_theorems rewrite_bv_or_one \<open>automatically_generated\<close>

lemma [rewrite_bv_or_one]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "y = not (Word.Word 0) \<longrightarrow> or x y = not (Word.Word 0)"
  by auto

named_theorems rewrite_bv_xor_duplicate \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_duplicate]:
  fixes x::"'a ::len word"
  shows "semiring_bit_operations_class.xor x x = Word.Word 0"
  by auto

named_theorems rewrite_bv_xor_ones \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_ones]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "y = not (Word.Word 0) \<longrightarrow>
   semiring_bit_operations_class.xor x y = not x"
  by auto

named_theorems rewrite_bv_xor_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_zero]:
  fixes x::"'a ::len word"
  shows "semiring_bit_operations_class.xor x (Word.Word 0) = x"
  by auto

named_theorems rewrite_bv_bitwise_not_and \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_not_and]:
  fixes x::"'a ::len word"
  shows "and x (not x) = Word.Word 0"
  by auto

named_theorems rewrite_bv_bitwise_not_or \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_not_or]:
  fixes x::"'a ::len word"
  shows "or x (not x) = not (Word.Word 0)"
  by auto

named_theorems rewrite_bv_xor_not \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_not]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "semiring_bit_operations_class.xor (not x) (not y) =
   semiring_bit_operations_class.xor x y"
  by auto

named_theorems rewrite_bv_not_idemp \<open>automatically_generated\<close>

lemma [rewrite_bv_not_idemp]:
  fixes x::"'a ::len word"
  shows "not (not x) = x"
  by auto

named_theorems rewrite_bv_ult_zero_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_1]:
  fixes x::"'a ::len word"
  shows "(Word.Word 0 < x) = (Word.Word 0 \<noteq> x)"
  by auto

named_theorems rewrite_bv_ult_zero_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_2]:
  fixes x::"'a ::len word"
  shows "(x < Word.Word 0) = False"
  by auto

named_theorems rewrite_bv_ult_self \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_self]:
  fixes x::"'a ::len word"
  shows "(x < x) = False"
  by auto

named_theorems rewrite_bv_lt_self \<open>automatically_generated\<close>

lemma [rewrite_bv_lt_self]:
  fixes x::"'a ::len word"
  shows "(x <s x) = False"
  by auto

named_theorems rewrite_bv_ule_self \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_self]:
  fixes x::"'a ::len word"
  shows "(x \<le> x) = True"
  by auto

named_theorems rewrite_bv_ule_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_zero]:
  fixes x::"'a ::len word"
  shows "(x \<le> Word.Word 0) = (x = Word.Word 0)"
  by auto

named_theorems rewrite_bv_zero_ule \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ule]:
  fixes x::"'a ::len word"
  shows "(Word.Word 0 \<le> x) = True"
  by auto

named_theorems rewrite_bv_sle_self \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_self]:
  fixes x::"'a ::len word"
  shows "(x \<le>s x) = True"
  by auto

named_theorems rewrite_bv_ule_max \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_max]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "y = not (Word.Word 0) \<longrightarrow> (x \<le> y) = True"
  by auto

named_theorems rewrite_bv_not_ult \<open>automatically_generated\<close>

lemma [rewrite_bv_not_ult]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(\<not> x < y) = (y \<le> x)"
  by auto

named_theorems rewrite_bv_not_ule \<open>automatically_generated\<close>

lemma [rewrite_bv_not_ule]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(\<not> x \<le> y) = (y < x)"
  by auto

named_theorems rewrite_bv_not_sle \<open>automatically_generated\<close>

lemma [rewrite_bv_not_sle]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(\<not> x \<le>s y) = (y <s x)"
  by auto

named_theorems rewrite_bv_extract_mult_leading_bit \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_mult_leading_bit]:
  fixes high::"int" and low::"int" and x1i::"int" and x1in::"int" and x2::"'a ::len word" and y1i::"int" and y1in::"int" and y2::"'b ::len word"
  shows "high < int (size (x_c0 * x_c1)) \<and>
   x_c2 = smt_extract (nat high) (nat low) (x_c0 * x_c1) \<and>
   int (size x_c2) = 1 + (high - low) \<and>
   low \<le> high \<and>
   0 \<le> low \<and>
   x_c1 = word_cat (Word.Word y1i) y2 \<and>
   int (size x_c1) = int (size (Word.Word y1i)) + int (size y2) \<and>
   x_c0 = word_cat (Word.Word x1i) x2 \<and>
   int (size x_c0) =
   int (size (Word.Word x1i)) + int (size x2) \<longrightarrow>
   64 < x1in + int (size x2) \<and>
   low
   < 2 * (x1in + int (size x2)) -
     ((if x1i = 0 then x1in else x1in - int (floorlog (nat x1i) 2)) +
      (if y1i = 0 then y1in
       else y1in - int (floorlog (nat y1i) 2))) \<longrightarrow>
   x_c2 = Word.Word 0"
  by auto

named_theorems rewrite_bv_neg_idemp \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_idemp]:
  fixes x::"'a ::len word"
  shows "- (- x) = x"
  by auto

named_theorems rewrite_bv_udiv_pow2_1p \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_1p]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "x_c1 = word_cat (Word.Word 0) x_c0 \<and>
   int (size x_c1) = int (size (Word.Word 0)) + int (size x_c0) \<and>
   n - 1 < int (size x) \<and>
   x_c0 =
   smt_extract (nat (n - 1)) (nat (int (floorlog (nat v) 2))) x \<and>
   int (size x_c0) = 1 + (n - 1 - int (floorlog (nat v) 2)) \<and>
   int (floorlog (nat v) 2) \<le> n - 1 \<and>
   0 \<le> int (floorlog (nat v) 2) \<longrightarrow>
   True \<and> 1 < v \<longrightarrow> x div Word.Word v = x_c1"
  by auto

named_theorems rewrite_bv_udiv_pow2_1n \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_1n]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "x_c1 = word_cat (Word.Word 0) x_c0 \<and>
   int (size x_c1) = int (size (Word.Word 0)) + int (size x_c0) \<and>
   n - 1 < int (size x) \<and>
   x_c0 =
   smt_extract (nat (n - 1)) (nat (int (floorlog (nat (- v)) 2)))
    x \<and>
   int (size x_c0) = 1 + (n - 1 - int (floorlog (nat (- v)) 2)) \<and>
   int (floorlog (nat (- v)) 2) \<le> n - 1 \<and>
   0 \<le> int (floorlog (nat (- v)) 2) \<longrightarrow>
   True \<and> v < - 1 \<longrightarrow> x div Word.Word v = - x_c1"
  by auto

named_theorems rewrite_bv_udiv_pow2_2p \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_2p]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "v = 1 \<longrightarrow> x div Word.Word v = x"
  by auto

named_theorems rewrite_bv_udiv_pow2_2n \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_2n]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "v = - 1 \<longrightarrow> x div Word.Word v = - x"
  by auto

named_theorems rewrite_bv_udiv_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_zero]:
  fixes x::"'a ::len word"
  shows "x div Word.Word 0 = not (Word.Word 0)"
  by auto

named_theorems rewrite_bv_udiv_one \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_one]:
  fixes x::"'a ::len word"
  shows "x div Word.Word 1 = x"
  by auto

named_theorems rewrite_bv_urem_pow2_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_pow2_1]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "x_c1 = word_cat (Word.Word 0) x_c0 \<and>
   int (size x_c1) = int (size (Word.Word 0)) + int (size x_c0) \<and>
   int (floorlog (nat v) 2) - 1 < int (size x) \<and>
   x_c0 =
   smt_extract (nat (int (floorlog (nat v) 2) - 1)) (nat 0) x \<and>
   int (size x_c0) = 1 + (int (floorlog (nat v) 2) - 1 - 0) \<and>
   0 \<le> int (floorlog (nat v) 2) - 1 \<and> 0 \<le> 0 \<longrightarrow>
   True \<and> 1 < v \<longrightarrow> smt_urem x (Word.Word v) = x_c1"
  by auto

named_theorems rewrite_bv_urem_pow2_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_pow2_2]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "x_c1 = word_cat (Word.Word 0) x_c0 \<and>
   int (size x_c1) = int (size (Word.Word 0)) + int (size x_c0) \<and>
   int (floorlog (nat (- v)) 2) - 1 < int (size x) \<and>
   x_c0 =
   smt_extract (nat (int (floorlog (nat (- v)) 2) - 1)) (nat 0) x \<and>
   int (size x_c0) = 1 + (int (floorlog (nat (- v)) 2) - 1 - 0) \<and>
   0 \<le> int (floorlog (nat (- v)) 2) - 1 \<and>
   0 \<le> 0 \<longrightarrow>
   True \<and> v < - 1 \<longrightarrow> smt_urem x (Word.Word v) = x_c1"
  by auto

named_theorems rewrite_bv_urem_one \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_one]:
  fixes x::"'a ::len word"
  shows "smt_urem x (Word.Word 1) = Word.Word 0"
  by auto

named_theorems rewrite_bv_urem_self \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_self]:
  fixes x::"'a ::len word"
  shows "x div x = Word.Word 0"
  by auto

named_theorems rewrite_bv_shl_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "push_bit (unat a) (Word.Word 0) = Word.Word 0"
  by auto

named_theorems rewrite_bv_lshr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "drop_bit (unat a) (Word.Word 0) = Word.Word 0"
  by auto

named_theorems rewrite_bv_ashr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "signed_drop_bit (unat a) (Word.Word 0) = Word.Word 0"
  by auto

named_theorems rewrite_bv_ugt_urem \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_urem]:
  fixes y::"'a ::len word" and x::"'a ::len word"
  shows "(x < smt_urem y x) = (Word.Word 0 < y \<and> x = Word.Word 0)"
  by auto

named_theorems rewrite_bv_ult_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_one]:
  fixes x::"'a ::len word"
  shows "(x < Word.Word 1) = (x = Word.Word 0)"
  by auto

named_theorems rewrite_bv_slt_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_slt_zero]:
  fixes x::"'a ::len word"
  shows "int (size x) - 1 < int (size x) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    x \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   0 \<le> int (size x) - 1 \<longrightarrow>
   (x <s Word.Word 0) = (x_c0 = Word.Word 1)"
  by auto

named_theorems rewrite_bv_zero_ult \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ult]:
  fixes x::"'a ::len word"
  shows "(Word.Word 0 < x) = (x \<noteq> Word.Word 0)"
  by auto

named_theorems rewrite_bv_merge_sign_extend_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_1]:
  fixes x::"'a ::len word" and i::"int" and j::"int"
  shows "x_c2 = signed_take_bit (nat (i + j)) x \<and>
   int (size x_c2) = int (size x) + (i + j) \<and>
   0 \<le> i + j \<and>
   x_c1 = signed_take_bit (nat i) x_c0 \<and>
   int (size x_c1) = int (size x_c0) + i \<and>
   0 \<le> i \<and>
   x_c0 = signed_take_bit (nat j) x \<and>
   int (size x_c0) = int (size x) + j \<and> 0 \<le> j \<longrightarrow>
   x_c1 = x_c2"
  by auto

named_theorems rewrite_bv_merge_sign_extend_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_2]:
  fixes x::"'a ::len word" and i::"int" and j::"int"
  shows "x_c2 = push_bit (nat (i + j)) x \<and>
   int (size x_c2) = int (size x) + (i + j) \<and>
   0 \<le> i + j \<and>
   x_c1 = signed_take_bit (nat i) x_c0 \<and>
   int (size x_c1) = int (size x_c0) + i \<and>
   0 \<le> i \<and>
   x_c0 = push_bit (nat j) x \<and>
   int (size x_c0) = int (size x) + j \<and> 0 \<le> j \<longrightarrow>
   1 < j \<longrightarrow> x_c1 = x_c2"
  by auto

named_theorems rewrite_bv_merge_sign_extend_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_3]:
  fixes x::"'a ::len word" and i::"int"
  shows "x_c2 = signed_take_bit (nat i) x \<and>
   int (size x_c2) = int (size x) + i \<and>
   x_c1 = signed_take_bit (nat i) x_c0 \<and>
   int (size x_c1) = int (size x_c0) + i \<and>
   0 \<le> i \<and>
   x_c0 = push_bit (nat 0) x \<and>
   int (size x_c0) = int (size x) + 0 \<and> 0 \<le> 0 \<longrightarrow>
   x_c1 = x_c2"
  by auto

named_theorems rewrite_bv_sign_extend_eq_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eq_const_1]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "x_c2 = signed_take_bit (nat m) x \<and>
   int (size x_c2) = int (size x) + m \<and>
   0 \<le> m \<and>
   nm - 1 < int (size (Word.Word c)) \<and>
   x_c1 =
   smt_extract (nat (nm - 1)) (nat (int (size x) - 1))
    (Word.Word c) \<and>
   int (size x_c1) = 1 + (nm - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> nm - 1 \<and>
   int (size x) - 1 < int (size (Word.Word c)) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - 0) \<and>
   0 \<le> int (size x) - 1 \<and> 0 \<le> 0 \<longrightarrow>
   (x_c2 = Word.Word c) =
   ((x_c1 = Word.Word 0 \<or> x_c1 = not (Word.Word 0)) \<and> x = x_c0)"
  by auto

named_theorems rewrite_bv_sign_extend_eq_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eq_const_2]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "x_c2 = signed_take_bit (nat m) x \<and>
   int (size x_c2) = int (size x) + m \<and>
   0 \<le> m \<and>
   nm - 1 < int (size (Word.Word c)) \<and>
   x_c1 =
   smt_extract (nat (nm - 1)) (nat (int (size x) - 1))
    (Word.Word c) \<and>
   int (size x_c1) = 1 + (nm - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> nm - 1 \<and>
   int (size x) - 1 < int (size (Word.Word c)) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - 0) \<and>
   0 \<le> int (size x) - 1 \<and> 0 \<le> 0 \<longrightarrow>
   (Word.Word c = x_c2) =
   ((x_c1 = Word.Word 0 \<or> x_c1 = not (Word.Word 0)) \<and> x = x_c0)"
  by auto

named_theorems rewrite_bv_zero_extend_eq_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eq_const_1]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "x_c2 = push_bit (nat m) x \<and>
   int (size x_c2) = int (size x) + m \<and>
   0 \<le> m \<and>
   nm - 1 < int (size (Word.Word c)) \<and>
   x_c1 =
   smt_extract (nat (nm - 1)) (nat (int (size x) - 1))
    (Word.Word c) \<and>
   int (size x_c1) = 1 + (nm - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> nm - 1 \<and>
   int (size x) - 1 < int (size (Word.Word c)) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - 0) \<and>
   0 \<le> int (size x) - 1 \<and> 0 \<le> 0 \<longrightarrow>
   (x_c2 = Word.Word c) = (x_c1 = Word.Word 0 \<and> x = x_c0)"
  by auto

named_theorems rewrite_bv_zero_extend_eq_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eq_const_2]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "x_c2 = push_bit (nat m) x \<and>
   int (size x_c2) = int (size x) + m \<and>
   0 \<le> m \<and>
   nm - 1 < int (size (Word.Word c)) \<and>
   x_c1 =
   smt_extract (nat (nm - 1)) (nat (int (size x) - 1))
    (Word.Word c) \<and>
   int (size x_c1) = 1 + (nm - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> nm - 1 \<and>
   int (size x) - 1 < int (size (Word.Word c)) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - 0) \<and>
   0 \<le> int (size x) - 1 \<and> 0 \<le> 0 \<longrightarrow>
   (Word.Word c = x_c2) = (x_c1 = Word.Word 0 \<and> x = x_c0)"
  by auto

named_theorems rewrite_bv_zero_extend_ult_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_ult_const_1]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "x_c2 = push_bit (nat m) x \<and>
   int (size x_c2) = int (size x) + m \<and>
   0 \<le> m \<and>
   nm - 1 < int (size (Word.Word c)) \<and>
   x_c1 =
   smt_extract (nat (nm - 1)) (nat (int (size x))) (Word.Word c) \<and>
   int (size x_c1) = 1 + (nm - 1 - int (size x)) \<and>
   int (size x) \<le> nm - 1 \<and>
   0 \<le> int (size x) \<and>
   int (size x) - 1 < int (size (Word.Word c)) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - 0) \<and>
   0 \<le> int (size x) - 1 \<and> 0 \<le> 0 \<longrightarrow>
   x_c1 = Word.Word 0 \<longrightarrow> (x_c2 < Word.Word c) = (x < x_c0)"
  by auto

named_theorems rewrite_bv_zero_extend_ult_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_ult_const_2]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "x_c2 = push_bit (nat m) x \<and>
   int (size x_c2) = int (size x) + m \<and>
   0 \<le> m \<and>
   nm - 1 < int (size (Word.Word c)) \<and>
   x_c1 =
   smt_extract (nat (nm - 1)) (nat (int (size x))) (Word.Word c) \<and>
   int (size x_c1) = 1 + (nm - 1 - int (size x)) \<and>
   int (size x) \<le> nm - 1 \<and>
   0 \<le> int (size x) \<and>
   int (size x) - 1 < int (size (Word.Word c)) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - 0) \<and>
   0 \<le> int (size x) - 1 \<and> 0 \<le> 0 \<longrightarrow>
   x_c1 = Word.Word 0 \<longrightarrow> (Word.Word c < x_c2) = (x_c0 < x)"
  by auto

named_theorems rewrite_bv_sign_extend_ult_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_1]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "x_c1 = signed_take_bit (nat m) x \<and>
   int (size x_c1) = int (size x) + m \<and>
   0 \<le> m \<and>
   int (size x) - 1 < int (size (Word.Word c)) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - 0) \<and>
   0 \<le> int (size x) - 1 \<and> 0 \<le> 0 \<longrightarrow>
   Word.Word c
   \<le> push_bit (unat (Word.Word 1)) (Word.Word (int (size x) - 1)) \<or>
   push_bit (unat (not (Word.Word 0))) (Word.Word (int (size x) - 1))
   \<le> Word.Word c \<longrightarrow>
   (x_c1 < Word.Word c) = (x < x_c0)"
  by auto

named_theorems rewrite_bv_sign_extend_ult_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_2]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "int (size x) - 1 < int (size x) \<and>
   x_c2 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    x \<and>
   int (size x_c2) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   x_c1 = signed_take_bit (nat m) x \<and>
   int (size x_c1) = int (size x) + m \<and>
   0 \<le> m \<and>
   int (size x) - 1 < int (size (Word.Word c)) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - 0) \<and>
   0 \<le> int (size x) - 1 \<and> 0 \<le> 0 \<longrightarrow>
   push_bit (unat (Word.Word 1)) (Word.Word (int (size x) - 1))
   < Word.Word c \<and>
   Word.Word c
   \<le> push_bit (unat (not (Word.Word 0)))
          (Word.Word (int (size x) - 1)) \<longrightarrow>
   (x_c1 < Word.Word c) = (x_c2 = Word.Word 0)"
  by auto

named_theorems rewrite_bv_sign_extend_ult_const_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_3]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "x_c1 = signed_take_bit (nat m) x \<and>
   int (size x_c1) = int (size x) + m \<and>
   0 \<le> m \<and>
   int (size x) - 1 < int (size (Word.Word c)) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - 0) \<and>
   0 \<le> int (size x) - 1 \<and> 0 \<le> 0 \<longrightarrow>
   Word.Word c
   < push_bit (unat (Word.Word 1)) (Word.Word (int (size x) - 1)) \<or>
   not (push_bit (unat (Word.Word 1)) (Word.Word (int (size x) - 1)))
   \<le> Word.Word c \<longrightarrow>
   (Word.Word c < x_c1) = (x_c0 < x)"
  by auto

named_theorems rewrite_bv_sign_extend_ult_const_4 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_4]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "int (size x) - 1 < int (size x) \<and>
   x_c2 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    x \<and>
   int (size x_c2) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   x_c1 = signed_take_bit (nat m) x \<and>
   int (size x_c1) = int (size x) + m \<and>
   0 \<le> m \<and>
   int (size x) - 1 < int (size (Word.Word c)) \<and>
   x_c0 =
   smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) \<and>
   int (size x_c0) = 1 + (int (size x) - 1 - 0) \<and>
   0 \<le> int (size x) - 1 \<and> 0 \<le> 0 \<longrightarrow>
   not (push_bit (unat (not (Word.Word 0))) (Word.Word (int (size x) - 1)))
   \<le> Word.Word c \<and>
   Word.Word c
   \<le> not (push_bit (unat (Word.Word 1))
               (Word.Word (int (size x) - 1))) \<longrightarrow>
   (Word.Word c < x_c1) = (x_c2 = Word.Word 0)"
  by auto

named_theorems rewrite_bv_extract_bitwise_and \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_and]:
  fixes x::"'a ::len word" and y::"'a ::len word" and i::"int" and j::"int"
  shows "i < int (size y) \<and>
   x_c2 = smt_extract (nat i) (nat j) y \<and>
   int (size x_c2) = 1 + (i - j) \<and>
   i < int (size x) \<and>
   x_c1 = smt_extract (nat i) (nat j) x \<and>
   int (size x_c1) = 1 + (i - j) \<and>
   i < int (size (and x y)) \<and>
   x_c0 = smt_extract (nat i) (nat j) (and x y) \<and>
   int (size x_c0) = 1 + (i - j) \<and>
   j \<le> i \<and> 0 \<le> j \<longrightarrow>
   x_c0 = and x_c1 x_c2"
  by auto

named_theorems rewrite_bv_extract_bitwise_or \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_or]:
  fixes x::"'a ::len word" and y::"'a ::len word" and i::"int" and j::"int"
  shows "i < int (size y) \<and>
   x_c2 = smt_extract (nat i) (nat j) y \<and>
   int (size x_c2) = 1 + (i - j) \<and>
   i < int (size x) \<and>
   x_c1 = smt_extract (nat i) (nat j) x \<and>
   int (size x_c1) = 1 + (i - j) \<and>
   i < int (size (or x y)) \<and>
   x_c0 = smt_extract (nat i) (nat j) (or x y) \<and>
   int (size x_c0) = 1 + (i - j) \<and>
   j \<le> i \<and> 0 \<le> j \<longrightarrow>
   x_c0 = or x_c1 x_c2"
  apply simp

named_theorems rewrite_bv_extract_bitwise_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_xor]:
  fixes x::"'a ::len word" and y::"'a ::len word" and i::"int" and j::"int"
  shows "i < int (size y) \<and>
   x_c2 = smt_extract (nat i) (nat j) y \<and>
   int (size x_c2) = 1 + (i - j) \<and>
   i < int (size x) \<and>
   x_c1 = smt_extract (nat i) (nat j) x \<and>
   int (size x_c1) = 1 + (i - j) \<and>
   i < int (size (semiring_bit_operations_class.xor x y)) \<and>
   x_c0 =
   smt_extract (nat i) (nat j)
    (semiring_bit_operations_class.xor x y) \<and>
   int (size x_c0) = 1 + (i - j) \<and>
   j \<le> i \<and> 0 \<le> j \<longrightarrow>
   x_c0 = semiring_bit_operations_class.xor x_c1 x_c2"
  by auto

named_theorems rewrite_bv_extract_not \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_not]:
  fixes x::"'a ::len word" and i::"int" and j::"int"
  shows "i < int (size x) \<and>
   x_c1 = smt_extract (nat i) (nat j) x \<and>
   int (size x_c1) = 1 + (i - j) \<and>
   i < int (size (not x)) \<and>
   x_c0 = smt_extract (nat i) (nat j) (not x) \<and>
   int (size x_c0) = 1 + (i - j) \<and>
   j \<le> i \<and> 0 \<le> j \<longrightarrow>
   x_c0 = not x_c1"
  by auto

named_theorems rewrite_bv_extract_sign_extend_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_1]:
  fixes x::"'a ::len word" and low::"int" and high::"int" and k::"int"
  shows "high < int (size x) \<and>
   x_c2 = smt_extract (nat high) (nat low) x \<and>
   int (size x_c2) = 1 + (high - low) \<and>
   high < int (size x_c0) \<and>
   x_c1 = smt_extract (nat high) (nat low) x_c0 \<and>
   int (size x_c1) = 1 + (high - low) \<and>
   low \<le> high \<and>
   0 \<le> low \<and>
   x_c0 = signed_take_bit (nat k) x \<and>
   int (size x_c0) = int (size x) + k \<and> 0 \<le> k \<longrightarrow>
   high < int (size x) \<longrightarrow> x_c1 = x_c2"
  by auto

named_theorems rewrite_bv_extract_sign_extend_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_3]:
  fixes x::"'a ::len word" and low::"int" and high::"int" and k::"int"
  shows "x_c3 = smt_repeat (nat (1 + (high - low))) x_c2 \<and>
   int (size x_c3) = int (size x_c2) * (1 + (high - low)) \<and>
   0 \<le> 1 + (high - low) \<and>
   int (size x) - 1 < int (size x) \<and>
   x_c2 =
   smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1))
    x \<and>
   int (size x_c2) = 1 + (int (size x) - 1 - (int (size x) - 1)) \<and>
   int (size x) - 1 \<le> int (size x) - 1 \<and>
   0 \<le> int (size x) - 1 \<and>
   high < int (size x_c0) \<and>
   x_c1 = smt_extract (nat high) (nat low) x_c0 \<and>
   int (size x_c1) = 1 + (high - low) \<and>
   low \<le> high \<and>
   0 \<le> low \<and>
   x_c0 = signed_take_bit (nat k) x \<and>
   int (size x_c0) = int (size x) + k \<and> 0 \<le> k \<longrightarrow>
   int (size x) \<le> low \<longrightarrow> x_c1 = x_c3"
  by auto

named_theorems rewrite_bv_neg_mult \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_mult]:
  fixes xs::"'a ::len word" and ys::"'a ::len word" and n::"int" and m::"int"
  shows "- (xs * Word.Word n * ys) = xs * Word.Word (- n) * ys"
  by auto

named_theorems rewrite_bv_neg_sub \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_sub]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "- (x - y) = y - x"
  by auto

named_theorems rewrite_bv_mult_distrib_const_neg \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_neg]:
  fixes x::"'a ::len word" and n::"int" and m::"int"
  shows "- x * Word.Word n = x * Word.Word (- n)"
  by auto

named_theorems rewrite_bv_mult_distrib_const_add \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_add]:
  fixes x::"'a ::len word" and y::"'a ::len word" and n::"int" and m::"int"
  shows "(x + y) * Word.Word n = x * Word.Word n + y * Word.Word n"
  by auto

named_theorems rewrite_bv_mult_distrib_const_sub \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_sub]:
  fixes x::"'a ::len word" and y::"'a ::len word" and n::"int" and m::"int"
  shows "(x - y) * Word.Word n = x * Word.Word n - y * Word.Word n"
  by auto

named_theorems rewrite_bv_mult_distrib_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_1]:
  fixes x1::"'a ::len word" and x2::"'a ::len word" and y::"'a ::len word"
  shows "(x1 + x2) * y = x1 * y + x2 * y"
  by auto

named_theorems rewrite_bv_mult_distrib_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_2]:
  fixes x1::"'a ::len word" and x2::"'a ::len word" and y::"'a ::len word"
  shows "y * (x1 + x2) = y * x1 + y * x2"
  by auto

named_theorems rewrite_bv_not_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_not_xor]:
  fixes x::"'a ::len word" and xs::"'a ::len word cvc_ListVar"
  shows "not (cvc_list_right semiring_bit_operations_class.xor x xs) =
   cvc_list_right semiring_bit_operations_class.xor (not x) xs"
  apply (cases xs)
  subgoal for xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_not_xor_lemma)
  done

named_theorems rewrite_bv_ult_add_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_add_one]:
  fixes x::"'a ::len word" and y::"'a ::len word" and n::"int"
  shows "(x < y + Word.Word 1) = (\<not> y < x \<and> y \<noteq> - Word.Word 0)"
  by auto

named_theorems rewrite_bv_concat_to_mult \<open>automatically_generated\<close>

lemma [rewrite_bv_concat_to_mult]:
  fixes x::"'a ::len word" and i::"int" and m::"int"
  shows "x_c1 = word_cat x_c0 (Word.Word 0) \<and>
   int (size x_c1) = int (size x_c0) + int (size (Word.Word 0)) \<and>
   i < int (size x) \<and>
   x_c0 = smt_extract (nat i) (nat 0) x \<and>
   int (size x_c0) = 1 + (i - 0) \<and>
   0 \<le> i \<and> 0 \<le> 0 \<longrightarrow>
   1 + i + m = int (size x) \<longrightarrow>
   x_c1 = x * push_bit (unat (Word.Word m)) (Word.Word 1)"
  by auto

named_theorems rewrite_bv_mult_slt_mult_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_slt_mult_1]:
  fixes x::"'a ::len word" and t::"'a ::len word" and a::"'a ::len word" and n::"int" and m::"int"
  shows "x_c2 = signed_take_bit (nat n) x \<and>
   int (size x_c2) = int (size x) + n \<and>
   x_c1 = signed_take_bit (nat m) a \<and>
   int (size x_c1) = int (size a) + m \<and>
   0 \<le> m \<and>
   x_c0 = signed_take_bit (nat n) (x + t) \<and>
   int (size x_c0) = int (size (x + t)) + n \<and>
   0 \<le> n \<longrightarrow>
   (x_c0 * x_c1 <s x_c2 * x_c1) =
   (t \<noteq> Word.Word 0 \<and>
    a \<noteq> Word.Word 0 \<and> (x + t <s x) = (Word.Word 0 <s a))"
  by auto

named_theorems rewrite_bv_mult_slt_mult_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_slt_mult_2]:
  fixes x::"'a ::len word" and t::"'a ::len word" and a::"'a ::len word" and n::"int" and m::"int"
  shows "x_c2 = push_bit (nat n) x \<and>
   int (size x_c2) = int (size x) + n \<and>
   x_c1 = signed_take_bit (nat m) a \<and>
   int (size x_c1) = int (size a) + m \<and>
   0 \<le> m \<and>
   x_c0 = push_bit (nat n) (x + t) \<and>
   int (size x_c0) = int (size (x + t)) + n \<and>
   0 \<le> n \<longrightarrow>
   (x_c0 * x_c1 <s x_c2 * x_c1) =
   (t \<noteq> Word.Word 0 \<and>
    a \<noteq> Word.Word 0 \<and> (x + t < x) = (Word.Word 0 <s a))"
  by auto

named_theorems rewrite_bv_commutative_and \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_and]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "and x y = and y x"
  by auto

named_theorems rewrite_bv_commutative_or \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_or]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "or x y = or y x"
  by auto

named_theorems rewrite_bv_commutative_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_xor]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "semiring_bit_operations_class.xor x y =
   semiring_bit_operations_class.xor y x"
  by auto

end