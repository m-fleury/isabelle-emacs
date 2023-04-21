theory BV_Rewrites
  imports BV_Rewrites_Lemmas
begin

(*TODO: Talk about signed_take_bit*)


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
thm cat_slices

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


named_theorems rewrite_bv_concat_extract_merge \<open>automatically_generated\<close>

lemma [rewrite_bv_concat_extract_merge]:
  fixes xs::"'a ::len word cvc_ListVar" and s::"'b ::len word" and ys::"'a ::len word cvc_ListVar" and i::"int" and j::"int" and k::"int"
  shows "(0::int) \<le> i \<and>
   (0::int) \<le> j \<and> (0::int) \<le> k \<and> i \<le> j \<and> j < k \<longrightarrow>nat k < size (s::'b::len word) \<longrightarrow> 
   int LENGTH('a) = k - j \<longrightarrow> 
   int LENGTH('a) = k - i \<longrightarrow>
   int LENGTH('c) = j + 1 - i \<longrightarrow> 
   cvc_list_right word_cat
    (word_cat
      (cvc_list_left word_cat xs (smt_extract (nat k) (nat (j + (1::int))) s::'a::len word) :: 'a ::len word)
      (smt_extract (nat j) (nat i) s::'c::len word) ::'a::len word)
    ys =
   cvc_list_right word_cat
    (cvc_list_left word_cat xs (smt_extract (nat k) (nat i) s::'a::len word)) ys"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
     apply (induction yss arbitrary: ys)
     apply simp_all
     apply (induction xss arbitrary: xs)
      apply simp_all
    using word_cat_smt_extract[of "nat i" "nat j" "nat k" s, where 'b="'a"]
    


     apply (induction xss)
      apply simp_all
    
     apply (case_tac [!] xss)
       apply simp_all
    unfolding smt_extract_def
    
    by (simp add: bv_concat_extract_merge_lemma)
  done

named_theorems rewrite_bv_extract_extract \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_extract]:
  fixes x::"'a::len word" and i::"int" and j::"int" and k::"int" and l::"int"
  shows "k \<ge> 0 \<longrightarrow> l \<ge> k \<longrightarrow> j \<ge> i \<longrightarrow> i+l \<ge> i+k \<longrightarrow> i+k \<ge>0 \<longrightarrow> 
LENGTH('b) = j + 1 -i \<longrightarrow> 
LENGTH('c) = l + 1 -k \<longrightarrow>
(smt_extract (nat l) (nat k) (smt_extract (nat j) (nat i) x::'b::len word)::'c::len word) =
   (smt_extract (nat (i + l)) (nat (i + k)) x)"
  

named_theorems rewrite_bv_extract_whole \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_whole]:
  fixes x::"'a ::len word" and n::"int"
  shows "n = int (size x) \<longrightarrow>
   smt_extract (nat (n - (1::int))) (nat (0::int)) x = x"
  by (simp add: Suc_nat_eq_nat_zadd1 slice_id smt_extract_def word_size)

named_theorems rewrite_bv_extract_concat_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_concat_1]:
  fixes x::"'a ::len word" and xs::"'b ::len word cvc_ListVar" and y::"'b ::len word" and i::"int" and j::"int"
  shows "j \<le> int (size x) \<longrightarrow> i \<le> j \<longrightarrow> 
   smt_extract (nat j) (nat i)
    (word_cat (cvc_list_left word_cat xs y) x) =
   word_cat (cvc_list_left word_cat xs y)
    (smt_extract (nat j) (nat i) x)"
  apply (cases xs)
  subgoal for xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction xss arbitrary: xs)
     apply simp_all
    by (simp add: bv_extract_concat_1_lemma)
  done

named_theorems rewrite_bv_extract_concat_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_concat_2]:
  fixes x::"'a ::len word" and xs::"'b ::len word cvc_ListVar" and y::"'b ::len word" and i::"int" and j::"int"
  shows "i < int (size x) \<and> int (size x) \<le> j \<longrightarrow>
   smt_extract (nat j) (nat i)
    (word_cat (cvc_list_left word_cat xs y) x) =
   word_cat
    (smt_extract (nat (j - int (size x))) (nat (0::int))
      (cvc_list_left word_cat xs y))
    (smt_extract (nat (int (size x) - (1::int))) (nat i) x)"
  apply (cases xs)
  subgoal for xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_extract_concat_2_lemma)
  done

named_theorems rewrite_bv_extract_concat_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_concat_3]:
  fixes x::"'a ::len word" and y::"'b ::len word" and xs::"'b ::len word cvc_ListVar" and i::"int" and j::"int"
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
   (x +
    push_bit (unat (Word.Word (int (size x) - (1::int))))
     (Word.Word (1::int))
    < y +
      push_bit (unat (Word.Word (int (size x) - (1::int))))
       (Word.Word (1::int)))"
  by auto

named_theorems rewrite_bv_sle_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(x \<le>s y) = (\<not> y <s x)"
  by auto

named_theorems rewrite_bv_redor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redor_eliminate]:
  fixes x::"'a ::len word"
  shows "smt_redor x = not (smt_comp x (Word.Word (0::int)))"
  unfolding smt_redor_def
  by simp

named_theorems rewrite_bv_redand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redand_eliminate]:
  fixes x::"'a ::len word"
  shows "smt_redand x = not (smt_comp x (not (Word.Word (0::int))))"
  unfolding smt_redand_def by auto

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
  shows "smt_comp x y = (if x = y then Word.Word (1::int) else Word.Word (0::int))"
  by (metis one_word.abs_eq smt_comp_def zero_word.abs_eq)

named_theorems rewrite_bv_repeat_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_1]:
  fixes x::"'a ::len word" and n::"int"
  shows "(1::int) < n \<longrightarrow>
   smt_repeat (nat n) x = word_cat x (smt_repeat (nat (n - (1::int))) x)"
  unfolding smt_repeat_def
  by (metis One_nat_def Suc_diff_Suc Suc_lessD Suc_pred' linorder_linear nat_1 nat_diff_distrib not_one_le_zero one_less_nat_eq order_less_imp_le repeat.simps(2))

named_theorems rewrite_bv_repeat_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_2]:
  fixes x::"'a ::len word"
  shows "smt_repeat (nat (1::int)) x = x"
  unfolding smt_repeat_def
  by auto

named_theorems rewrite_bv_rotate_left_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_1]:
  fixes x::"'a ::len word" and amount::"int"
  shows "amount < int (size x)  \<longrightarrow> word_rotl (nat amount) x =
   word_cat
    (smt_extract (nat (int (size x) - ((1::int) + amount)))
      (nat (0::int)) x)
    (smt_extract (nat (0::int)) (nat amount) x)"
  

named_theorems rewrite_bv_rotate_left_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_2]:
  fixes x::"'a ::len word"
  shows "word_rotl (nat (0::int)) x = x"
  by (metis add_0 nat_zero_as_int word_rot_lr word_rotr_word_rotr_eq)

named_theorems rewrite_bv_rotate_right_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_1]:
  fixes x::"'a ::len word" and amount::"int"
  shows "amount > 0 \<longrightarrow> size x > 0  \<longrightarrow>
LENGTH('b) = amount \<longrightarrow> LENGTH('c) = LENGTH('a) - amount
\<longrightarrow> size x > amount \<longrightarrow>
 word_rotr (nat amount) x =
   word_cat (smt_extract (nat (amount - (1::int))) (nat (0::int)) x::'b::len word)
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x::'c::len word)"
  sorry

named_theorems rewrite_bv_rotate_right_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_2]:
  fixes x::"'a ::len word"
  shows "word_rotr (nat (0::int)) x = x"
  by (metis add.right_neutral nat_code(2) word_rot_rl word_rotr_word_rotr_eq)

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
  shows "x div y =
   (if (smt_extract (nat (int (size x) - (1::int)))
         (nat (int (size x) - (1::int))) x =
        Word.Word (1::int)) [+1]
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

(*(define-rule bv-sdiv-eliminate-fewer-bitwise-ops ((x ?BitVec) (y ?BitVec))
 (def (n (bvsize x))
      (xLt0 (bvuge x (concat (bv 1 1) (bv 0 (- n 1)))))
      (yLt0 (bvuge y (concat (bv 1 1) (bv 0 (- n 1)))))
      (rUdiv (bvudiv (ite xLt0 (bvneg x) x) (ite yLt0 (bvneg y) y))))
 (bvsdiv x y) (ite (xor xLt0 yLt0) (bvneg rUdiv) rUdiv))
*)
lemma [rewrite_bv_sdiv_eliminate_fewer_bitwise_ops]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "LENGTH('a) = LENGTH('b) + 1 \<longrightarrow> 
x div y =
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
  apply (simp add: xor_def)
  apply (cases "word_cat (1::1 word) (0::'b word) \<le> y")
   apply simp_all
  defer






named_theorems rewrite_bv_zero_extend_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eliminate]:
  fixes x::"'a ::len word" and n::"int"
  shows "size x = n \<longrightarrow> push_bit (nat n) x = word_cat (Word.Word (0::int)::'a word) x"
  apply simp
  apply (simp add: word_cat_eq)
  

named_theorems rewrite_bv_sign_extend_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eliminate]:
  fixes x::"'a ::len word" and n::"int"
  shows "signed_take_bit (nat n) x =
   word_cat
    (smt_repeat (nat n)
      (smt_extract (nat (int (size x) - (1::int)))
        (nat (int (size x) - (1::int))) x))
    x"
  by auto

named_theorems rewrite_bv_uaddo_eliminate \<open>automatically_generated\<close>

(*TODO: Change smt_uaddo in SMT.thy *)
lemma [rewrite_bv_uaddo_eliminate]:
  fixes x::"'a ::len word" and y::"'b ::len word"
  shows "LENGTH('c) = LENGTH('a) + 1
       \<and> LENGTH('c) = LENGTH('b) + 1 \<and> int (size x) > 0 \<and> int (size y) > 0 
\<longrightarrow> smt_uaddo (TYPE('c::len)) x y =
   (smt_extract (nat (int (size x))) (nat (int (size x)))
     (word_cat (Word.Word (0::int)::1 word) x
 + word_cat (Word.Word (0::int)::1 word) y :: 'c ::len word) =
    (Word.Word (1::int):: 1 word))"
    using smt_uaddo_def[of x y, where 'c="'c"]
    by simp  
    


named_theorems rewrite_bv_saddo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_saddo_eliminate]:
  fixes x::"'a ::len word" and y::"'b ::len word"
  shows "LENGTH('c) = LENGTH('a) + 1 \<and> LENGTH('c) = LENGTH('b) + 1 \<and>  int (size x) > 0 \<and> int (size y) > 0 
 \<longrightarrow> smt_saddo TYPE('c::len) x y =
   (smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int)))
     ((word_cat (Word.Word (0::int):: 1 word) x::'c::len word) + (word_cat (Word.Word (0::int)::1 word) y)::'c::len word) =
    (Word.Word (1::int):: 1 word))"
  using smt_saddo_def[of x y, where 'c="'c"]
  apply simp
  by (metis diff_Suc_1 nat_1 nat_minus_as_int nat_one_as_int of_nat_eq_1_iff size_word.rep_eq)


named_theorems rewrite_bv_sdivo_eliminate \<open>automatically_generated\<close>

(*TODO: (itself::'c itself) instead of (itself::'c ::len itself) is printed
when you print without types it works ^^*)
(*TODO: This is an interesting one to see if types are autogenerated*)
lemma [rewrite_bv_sdivo_eliminate]:
  fixes x::"'a ::len word" and y::"'b ::len word"
  shows "LENGTH('c) = LENGTH('a) - 1  \<longrightarrow> smt_sdivo TYPE('c::len) x y =
   (x = word_cat (Word.Word (1::int):: 1 word) (Word.Word (0::int)::'c::len word) \<and>
    y = not (Word.Word (0::int)::'b::len word))"
    using smt_sdivo_def[of x y, where 'c="'c"] 
mask_full[where 'a="'b"]
    by (metis bit.compl_zero one_word_def word_size zero_word_def)

  

named_theorems rewrite_bv_smod_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_smod_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "smt_smod x y =
   (if smt_urem
        (if smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) x =
            (Word.Word (1::int)::1 word)
         then - x else x)
        (if smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) y =
            (Word.Word (1::int)::1 word)
         then - y else y) =
       Word.Word (0::int)
    then smt_urem
          (if smt_extract (nat (int (size x) - (1::int)))
               (nat (int (size x) - (1::int))) x =
              (Word.Word (1::int)::1 word)
           then - x else x)
          (if smt_extract (nat (int (size x) - (1::int)))
               (nat (int (size x) - (1::int))) y =
              (Word.Word (1::int)::1 word)
           then - y else y)
    else if smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) x \<noteq>
            (Word.Word (1::int)::1 word) \<and>
            smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) y \<noteq>
            (Word.Word (1::int)::1 word)
         then smt_urem
               (if smt_extract (nat (int (size x) - (1::int)))
                    (nat (int (size x) - (1::int))) x =
                   (Word.Word (1::int)::1 word)
                then - x else x)
               (if smt_extract (nat (int (size x) - (1::int)))
                    (nat (int (size x) - (1::int))) y =
                   (Word.Word (1::int)::1 word)
                then - y else y)
         else if smt_extract (nat (int (size x) - (1::int)))
                  (nat (int (size x) - (1::int))) x =
                 (Word.Word (1::int)::1 word) \<and>
                 smt_extract (nat (int (size x) - (1::int)))
                  (nat (int (size x) - (1::int))) y \<noteq>
                 (Word.Word (1::int)::1 word)
              then - smt_urem
                      (if smt_extract (nat (int (size x) - (1::int)))
                           (nat (int (size x) - (1::int))) x =
                          (Word.Word (1::int)::1 word)
                       then - x else x)
                      (if smt_extract (nat (int (size x) - (1::int)))
                           (nat (int (size x) - (1::int))) y =
                          (Word.Word (1::int)::1 word)
                       then - y else y) +
                   y
              else if smt_extract (nat (int (size x) - (1::int)))
                       (nat (int (size x) - (1::int))) x \<noteq>
                      (Word.Word (1::int)::1 word) \<and>
                      smt_extract (nat (int (size x) - (1::int)))
                       (nat (int (size x) - (1::int))) y =
                      (Word.Word (1::int)::1 word)
                   then smt_urem
                         (if smt_extract (nat (int (size x) - (1::int)))
                              (nat (int (size x) - (1::int))) x =
                             (Word.Word (1::int)::1 word)
                          then - x else x)
                         (if smt_extract (nat (int (size x) - (1::int)))
                              (nat (int (size x) - (1::int))) y =
                             (Word.Word (1::int)::1 word)
                          then - y else y) +
                        y
                   else - smt_urem
                           (if smt_extract
                                (nat (int (size x) - (1::int)))
                                (nat (int (size x) - (1::int))) x =
                               (Word.Word (1::int)::1 word)
                            then - x else x)
                           (if smt_extract
                                (nat (int (size x) - (1::int)))
                                (nat (int (size x) - (1::int))) y =
                               (Word.Word (1::int)::1 word)
                            then - y else y))"
  using smt_smod_def[of x y] 
  unfolding Let_def
  apply simp
  apply (cases "smt_urem x y = (0::'a word)")
   apply simp_all
   apply (case_tac [!] "smt_urem x (- y) = (0::'a word)")
   apply (case_tac [!] "smt_urem (- x) y = (0::'a word)")
  apply (case_tac [!] "smt_urem (- x) (- y) = (0::'a word)")

  apply simp_all
                apply (case_tac [!] "smt_extract (size x - Suc (0::nat)) (size x - Suc (0::nat)) x = (0::1 word)")
                      apply simp_all
  apply (metis One_nat_def nat_minus_as_int of_nat_eq_1_iff zero_neq_one)
  



named_theorems rewrite_bv_smod_eliminate_fewer_bitwise_ops \<open>automatically_generated\<close>

lemma [rewrite_bv_smod_eliminate_fewer_bitwise_ops]:
  fixes x::"'a ::len word" and y::"'a ::len word"
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
  fixes x::"'a ::len word" and y::"'a ::len word"
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
  fixes x::"'a ::len word" and y::"'a ::len word"
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
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "smt_usubo x y =
   (smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int)))
     (push_bit (nat (1::int)) x - push_bit (nat (1::int)) y) =
    (Word.Word (1::int):: 1 word))"
  unfolding smt_usubo_def
  apply simp
  by (simp add: nat_minus_as_int word_size)

named_theorems rewrite_bv_ssubo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ssubo_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "smt_ssubo x y =
   (smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) x =
    (Word.Word (1::int)::1 word) \<and>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) y \<noteq>
    (Word.Word (1::int)::1 word) \<and>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) (x - y) \<noteq>
    (Word.Word (1::int)::1 word) \<or>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) x \<noteq>
    (Word.Word (1::int)::1 word) \<and>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) y =
    (Word.Word (1::int)::1 word) \<and>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) (x - y) =
    (Word.Word (1::int)::1 word))"
  unfolding smt_ssubo_def Let_def
  apply simp
  apply (cases "smt_extract (size x - Suc (0::nat)) (size x - Suc (0::nat)) x = (1::1 word)")
   apply simp_all
   apply (case_tac [!] "smt_extract (size x - Suc (0::nat)) (size x - Suc (0::nat)) y = (1::1 word)")
     apply simp_all
  apply (simp add: nat_minus_as_int)
    apply (simp add: nat_diff_distrib')
    apply (simp add: nat_minus_as_int)
    by (simp add: nat_minus_as_int)



named_theorems rewrite_bv_ite_equal_children \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_children]:
  fixes c::"1  word" and x::"'a ::len word"
  shows "(if bit c (0::nat) then x else x) = x"
  by auto

named_theorems rewrite_bv_ite_const_children_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_1]:
  fixes c::"1  word"
  shows "(if bit c (0::nat) then Word.Word (0::int) else Word.Word (1::int)) =
   not c"
  by (metis (mono_tags, opaque_lifting) Word.of_nat_unat Word_eq_word_of_int add.group_left_neutral bit.compl_one bit.compl_zero bit_0_eq inc_le len_of_numeral_defs(2) mask_1 nat_int nle_le nth_0 take_bit_minus_one_eq_mask test_bit_1 ucast_id unsigned_1 unsigned_of_int word_neq_0_conv word_of_int_0 word_of_int_1 word_of_int_neg_1 word_order.extremum)

named_theorems rewrite_bv_ite_const_children_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_2]:
  fixes c::"1 word"
  shows "(if bit c (0::nat) then Word.Word (1::int) else Word.Word (0::int)) = c"
  by (metis (mono_tags, opaque_lifting) Word.of_nat_unat add.group_left_neutral bit.compl_zero len_of_numeral_defs(2) mask_1 nat_int nth_0 one_word_def take_bit_minus_one_eq_mask ucast_id unsigned_1 unsigned_of_int word_and_1 word_ao_nth word_exists_nth word_of_int_neg_1 word_plus_and_or_coroll2 zero_word_def)

named_theorems rewrite_bv_ite_equal_cond_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_1]:
  fixes c0::"1 word" and t0::"'a ::len word" and e0::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto

named_theorems rewrite_bv_ite_equal_cond_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_2]:
  fixes c0::"1 word" and t0::"'a ::len word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 (0::nat) then t0 else if bit c0 (0::nat) then t1 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto

named_theorems rewrite_bv_ite_equal_cond_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_3]:
  fixes c0::"1 word" and t0::"'a ::len word" and e0::"'a ::len word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0
    else if bit c0 (0::nat) then t1 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto

named_theorems rewrite_bv_ite_merge_then_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_if]:
  fixes c0::"1 word" and c1::"1  word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else t1) =
   (if bit (and c0 (not c1)) (0::nat) then e1 else t1)"
  by (metis lsb0)

named_theorems rewrite_bv_ite_merge_else_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_if]:
  fixes c0::"1 word" and c1::"1 word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else e1) =
   (if bit (and c0 c1) (0::nat) then t1 else e1)"
  by (metis word_ao_nth)

named_theorems rewrite_bv_ite_merge_then_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_else]:
  fixes c0::"1 word" and c1::"1 word" and t0::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t0 else e1) =
   (if bit (not (or c0 c1)) (0::nat) then e1 else t0)"
  by (metis lsb0)

named_theorems rewrite_bv_ite_merge_else_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_else]:
  fixes c0::"1  word" and c1::"1 word" and t1::"'a ::len word" and t0::"'a ::len word"
  shows "(if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t1 else t0) =
   (if bit (and (not c0) c1) (0::nat) then t1 else t0)"
  by (metis lsb0)

named_theorems rewrite_bv_shl_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_1]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
   push_bit (unat (Word.Word amount)) x =
   word_cat
    (smt_extract (nat (int (size x)))
      (nat (int (size x) - ((1::int) + amount))) x)
    (Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_shl_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_2]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow>
   push_bit (unat (Word.Word amount)) x = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_lshr_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_1]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
   drop_bit (unat (Word.Word amount)) x =
   word_cat (Word.Word (0::int))
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x)"
  by auto

named_theorems rewrite_bv_lshr_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_2]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow>
   drop_bit (unat (Word.Word amount)) x = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_ashr_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_by_const_1]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
   drop_bit (unat (Word.Word amount)) x =
   word_cat
    (smt_repeat (nat amount)
      (smt_extract (nat (int (size x) - (1::int)))
        (nat (int (size x) - (1::int))) x))
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x)"
  by auto

named_theorems rewrite_bv_ashr_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_by_const_2]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow>
   drop_bit (unat (Word.Word amount)) x =
   smt_repeat (nat (int (size x)))
    (smt_extract (nat (int (size x) - (1::int)))
      (nat (int (size x) - (1::int))) x)"
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
  shows "semiring_bit_operations_class.xor x x = Word.Word (0::int)"
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
  shows "and x (not x) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_bitwise_not_or \<open>automatically_generated\<close>

lemma [rewrite_bv_bitwise_not_or]:
  fixes x::"'a ::len word"
  shows "or x (not x) = not (Word.Word (0::int))"
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
  shows "(Word.Word (0::int) < x) = (Word.Word (0::int) \<noteq> x)"
  using word_neq_0_conv by auto

named_theorems rewrite_bv_ult_zero_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_2]:
  fixes x::"'a ::len word"
  shows "(x < Word.Word (0::int)) = False"
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
  shows "(x \<le> Word.Word (0::int)) = (x = Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_zero_ule \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ule]:
  fixes x::"'a ::len word"
  shows "(Word.Word (0::int) \<le> x) = True"
  by auto

named_theorems rewrite_bv_sle_self \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_self]:
  fixes x::"'a ::len word"
  shows "(x \<le>s x) = True"
  by auto

named_theorems rewrite_bv_ule_max \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_max]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "y = not (Word.Word (0::int)) \<longrightarrow> (x \<le> y) = True"
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

(*TODO: An error I did not catch in Isabelle since there are no words of bvsize 0! 
We could add it as implicit assumptions but it would also make lemmas harder to read...*)
lemma [rewrite_bv_not_sle]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(\<not> x \<le>s y) = (y <s x)"
  by auto

named_theorems rewrite_bv_extract_mult_leading_bit \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_mult_leading_bit]:
  fixes high::"int" and low::"int" and x1i::"int" and x1in::"int" and x2::"'a ::len word" and y1i::"int" and y1in::"int" and y2::"'b ::len word"
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
  apply (cases "x1i = (0::int)")
  apply (case_tac [!] "y1i = (0::int)")
  apply simp_all

named_theorems rewrite_bv_neg_idemp \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_idemp]:
  fixes x::"'a ::len word"
  shows "- (- x) = x"
  by auto

named_theorems rewrite_bv_udiv_pow2_1p \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_1p]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "True \<and> (1::int) < v \<longrightarrow>
   x div Word.Word v =
   word_cat (Word.Word (0::int))
    (smt_extract (nat (n - (1::int)))
      (nat (int (floorlog (nat v) (2::nat)))) x)"
  by auto

named_theorems rewrite_bv_udiv_pow2_1n \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_1n]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "True \<and> v < - (1::int) \<longrightarrow>
   x div Word.Word v =
   - word_cat (Word.Word (0::int))
      (smt_extract (nat (n - (1::int)))
        (nat (int (floorlog (nat (- v)) (2::nat)))) x)"
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


(*This is an example where Isabelle and SMTLIB semantics are completely different*)

lemma [rewrite_bv_udiv_zero]:
  fixes x::"'a ::len word"
  shows "x div Word.Word (0::int) =  (Word.Word (0::int))"
  apply simp

named_theorems rewrite_bv_udiv_one \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_one]:
  fixes x::"'a ::len word"
  shows "x div Word.Word (1::int) = x"
  by auto

named_theorems rewrite_bv_urem_pow2_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_pow2_1]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "is_pow2 v \<and> 1 < v \<longrightarrow>
   smt_urem x (Word.Word v) =
   word_cat (Word.Word 0)
    (smt_extract (nat (int (floorlog (nat v) 2) - 1)) (nat 0) x)"
  by auto

named_theorems rewrite_bv_urem_pow2_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_pow2_2]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "is_pow2 (- v) \<and> v < - 1 \<longrightarrow>
   smt_urem x (Word.Word v) =
   word_cat (Word.Word 0)
    (smt_extract (nat (int (floorlog (nat (- v)) 2) - 1)) (nat 0) x)"
  unfolding is_pow2_def smt_urem_def
  apply simp
  by force

named_theorems rewrite_bv_urem_one \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_one]:
  fixes x::"'a ::len word"
  shows "smt_urem x (Word.Word (1::int)) = Word.Word (0::int)"
  unfolding smt_urem_def
  apply simp
  by (simp add: unsigned_eq_0_iff)

named_theorems rewrite_bv_urem_self \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_self]:
  fixes x::"'a ::len word"
  shows "x> 0 \<longrightarrow> smt_urem x x = Word.Word (0::int)"
  unfolding smt_urem_def
  apply simp
  using unat_eq_zero by auto

named_theorems rewrite_bv_shl_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "push_bit (unat a) (Word.Word (0::int)) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_lshr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "drop_bit (unat a) (Word.Word (0::int)) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_ashr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "signed_drop_bit (unat a) (Word.Word (0::int)) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_and_concat_pullup \<open>automatically_generated\<close>

lemma [rewrite_bv_and_concat_pullup]:
  fixes x::"'a::len word" and y::"'b::len word" and z::"'c::len word" and ys::"'c::len word cvc_ListVar"
  shows "LENGTH('c) = i - size y \<longrightarrow> size y \<le> size x - 1 \<longrightarrow> 

  and x (word_cat (cvc_list_left word_cat ys z) y) =
   word_cat
    (and (smt_extract (nat (int (size x) - (1::int)))
           (nat (int (size y))) x :: 'c::len word)
      (cvc_list_left word_cat ys z))
    (and (smt_extract (nat (int (size y) - (1::int))) (nat (0::int)) x :: 'b::len word)
      y)"
  apply (cases ys)
  subgoal for yss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction yss arbitrary: ys)
     apply simp_all
    by (simp add: bv_and_concat_pullup_lemma)
  done

named_theorems rewrite_bv_or_concat_pullup \<open>automatically_generated\<close>

lemma [rewrite_bv_or_concat_pullup]:
  fixes x::"'a::len word" and y::"'b::len word" and z::"'c::len word" and ys::"'c::len word cvc_ListVar"
  shows "or x (word_cat (cvc_list_left word_cat ys z) y) =
   word_cat
    (or (SMT.smt_extract (nat (int (size x) - (1::int)))
          (nat (int (size y))) x)
      (cvc_list_left word_cat ys z))
    (or (SMT.smt_extract (nat (int (size y) - (1::int))) (nat (0::int)) x)
      y)"
  apply (cases ys)
  subgoal for yss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    by (simp add: bv_or_concat_pullup_lemma)
  done

named_theorems rewrite_bv_ugt_urem \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_urem]:
  fixes y::"'a ::len word" and x::"'a ::len word"
  shows "(x < smt_urem y x) =
   (Word.Word (0::int) < y \<and> x = Word.Word (0::int))"
  unfolding smt_urem_def
  apply simp
  by (metis not_less_iff_gr_or_eq unat_gt_0 word_arith_nat_mod word_gt_a_gt_0 word_mod_by_0 word_mod_less_divisor)

named_theorems rewrite_bv_ult_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_one]:
  fixes x::"'a ::len word"
  shows "(x < Word.Word (1::int)) = (x = Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_slt_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_slt_zero]:
  fixes x::"'a ::len word"
  shows "(x <s Word.Word (0::int)) =
   (smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) x =
    Word.Word (1::int))"
  by auto

named_theorems rewrite_bv_zero_ult \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ult]:
  fixes x::"'a ::len word"
  shows "(Word.Word 0 < x) = (x \<noteq> Word.Word 0)"
  using word_neq_0_conv by auto

named_theorems rewrite_bv_merge_sign_extend_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_1]:
  fixes x::"'a ::len word" and i::"int" and j::"int"
  shows "signed_take_bit (nat i) (signed_take_bit (nat j) x) =
   signed_take_bit (nat (i + j)) x"
  by auto

named_theorems rewrite_bv_merge_sign_extend_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_2]:
  fixes x::"'a ::len word" and i::"int" and j::"int"
  shows "1 < j \<longrightarrow>
   signed_take_bit (nat i) (push_bit (nat j) x) = push_bit (nat (i + j)) x"
  by auto

named_theorems rewrite_bv_merge_sign_extend_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_3]:
  fixes x::"'a ::len word" and i::"int"
  shows "signed_take_bit (nat i) (push_bit (nat 0) x) = signed_take_bit (nat i) x"
  by auto

named_theorems rewrite_bv_sign_extend_eq_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eq_const_1]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "(signed_take_bit (nat m) x = Word.Word c) =
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
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "(Word.Word c = signed_take_bit (nat m) x) =
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
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "(push_bit (nat m) x = Word.Word c) =
   (smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
     (Word.Word c) =
    Word.Word (0::int) \<and>
    x =
    smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
     (Word.Word c))"
  by auto

named_theorems rewrite_bv_zero_extend_eq_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eq_const_2]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "(Word.Word c = push_bit (nat m) x) =
   (smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
     (Word.Word c) =
    Word.Word (0::int) \<and>
    x =
    smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
     (Word.Word c))"
  by auto


named_theorems rewrite_bv_sign_extend_ult_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_1]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "Word.Word c
   \<le> push_bit (unat (Word.Word 1)) (Word.Word (int (size x) - 1)) \<or>
   push_bit (unat (not (Word.Word 0))) (Word.Word (int (size x) - 1))
   \<le> Word.Word c \<longrightarrow>
   (signed_take_bit (nat m) x < Word.Word c) =
   (x < smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c))"
  by auto

named_theorems rewrite_bv_sign_extend_ult_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_2]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "push_bit (unat (Word.Word 1)) (Word.Word (int (size x) - 1))
   < Word.Word c \<and>
   Word.Word c
   \<le> push_bit (unat (not (Word.Word 0)))
          (Word.Word (int (size x) - 1)) \<longrightarrow>
   (signed_take_bit (nat m) x < Word.Word c) =
   (smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1)) x =
    Word.Word 0)"
  by auto

named_theorems rewrite_bv_sign_extend_ult_const_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_3]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "Word.Word c
   < push_bit (unat (Word.Word 1)) (Word.Word (int (size x) - 1)) \<or>
   not (push_bit (unat (Word.Word 1)) (Word.Word (int (size x) - 1)))
   \<le> Word.Word c \<longrightarrow>
   (Word.Word c < signed_take_bit (nat m) x) =
   (smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) < x)"
  by auto

named_theorems rewrite_bv_sign_extend_ult_const_4 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_4]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "not (push_bit (unat (not (Word.Word 0))) (Word.Word (int (size x) - 1)))
   \<le> Word.Word c \<and>
   Word.Word c
   \<le> not (push_bit (unat (Word.Word 1))
               (Word.Word (int (size x) - 1))) \<longrightarrow>
   (Word.Word c < signed_take_bit (nat m) x) =
   (smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1)) x =
    Word.Word 0)"
  by auto

named_theorems rewrite_bv_zero_extend_ult_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_ult_const_1]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "SMT.smt_extract (nat (nm - 1)) (nat (int (size x))) (Word.Word c) =
   Word.Word 0 \<longrightarrow>
   (push_bit (nat m) x < Word.Word c) =
   (x < SMT.smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c))"
  by auto

named_theorems rewrite_bv_zero_extend_ult_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_ult_const_2]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "SMT.smt_extract (nat (nm - 1)) (nat (int (size x))) (Word.Word c) =
   Word.Word 0 \<longrightarrow>
   (Word.Word c < push_bit (nat m) x) =
   (SMT.smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) < x)"
  by auto

named_theorems rewrite_bv_extract_bitwise_and \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_and]:
  fixes x::"'a ::len word" and y::"'a ::len word" and i::"int" and j::"int"
  shows "0 \<le> j \<longrightarrow> nat i < size x \<longrightarrow> int LENGTH('b) = i + 1 - j \<longrightarrow> j \<le> i \<longrightarrow> (smt_extract (nat i) (nat j) (and x y)::'b::len word) =
   and ((smt_extract (nat i) (nat j) x)::'b::len word) 
    ((smt_extract (nat i) (nat j) y)::'b::len word)"
  apply (rule impI)+
proof-
  assume a0: "0 \<le> j" and a1: "nat i < size x" and a2: "int LENGTH('b) = i + 1 - j" and a3: "j \<le> i"

  have t0: "unat (smt_extract (nat i) (nat j) (and x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (and (unat x) (unat y)))"
  proof-
    have "unat (smt_extract (nat i) (nat j) (and x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (unat (and x y)))"
      using unat_smt_extract[of "nat j" "nat i" "(and x y)", where 'b="'b"]  
      by (metis Suc_as_int Suc_eq_plus1 a0 a1 a2 a3 int_nat_eq nat_diff_distrib' nat_int nat_mono not_less_eq_eq order_trans word_size)
    then show "unat (smt_extract (nat i) (nat j) (and x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (and (unat x) (unat y)))"
      using unsigned_and_eq by metis
  qed
  moreover have "unat (and ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
  = (and (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    proof-
      have "unat (and ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
        = (and (unat ((smt_extract (nat i) (nat j) x)::'b::len word)) (unat ((smt_extract (nat i) (nat j) y)::'b::len word)))"
    using unsigned_and_eq by blast
    moreover have " nat (j::int) \<le> nat (i::int) \<and> nat i < size (x::'a::len word) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j "
      using a0 a1 a2 a3 by force
    moreover have "nat i < size (y::'a::len word)"
      by (metis a1 size_word.rep_eq)
    ultimately show t1: "unat (and ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
    = (and (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    using unat_smt_extract[of "nat j" "nat i" "x", where 'b="'b"]
    using unat_smt_extract[of "nat j" "nat i" "y", where 'b="'b"]
    by presburger
  qed
  moreover have  "drop_bit (nat j) (take_bit (Suc (nat i)) (and (unat x) (unat y)))
  = (and (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    by auto
  ultimately show "(smt_extract (nat i) (nat j) (and x y)::'b::len word) =
   and ((smt_extract (nat i) (nat j) x)::'b::len word) 
    ((smt_extract (nat i) (nat j) y)::'b::len word)"
    by (metis unsigned_word_eqI)
qed

named_theorems rewrite_bv_extract_bitwise_or \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_or]:
  fixes x::"'a ::len word" and y::"'a ::len word" and i::"int" and j::"int"
  shows "0 \<le> j \<longrightarrow> nat i < size x \<longrightarrow> int LENGTH('b) = i + 1 - j \<longrightarrow> j \<le> i \<longrightarrow>
   (smt_extract (nat i) (nat j) (or x y)::'b::len word) =
   or (smt_extract (nat i) (nat j) x::'b::len word)
    (smt_extract (nat i) (nat j) y::'b::len word)"
  apply (rule impI)+
proof-
  assume a0: "0 \<le> j" and a1: "nat i < size x" and a2: "int LENGTH('b) = i + 1 - j" and a3: "j \<le> i"

  have t0: "unat (smt_extract (nat i) (nat j) (or x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (or (unat x) (unat y)))"
  proof-
    have "unat (smt_extract (nat i) (nat j) (or x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (unat (or x y)))"
      using unat_smt_extract[of "nat j" "nat i" "(or x y)", where 'b="'b"]  
      by (metis Suc_as_int Suc_eq_plus1 a0 a1 a2 a3 int_nat_eq nat_diff_distrib' nat_int nat_mono not_less_eq_eq order_trans word_size)
    then show "unat (smt_extract (nat i) (nat j) (or x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (or (unat x) (unat y)))"
      using unsigned_or_eq by metis
  qed
  moreover have "unat (or ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
  = (or (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    proof-
      have "unat (or ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
        = (or (unat ((smt_extract (nat i) (nat j) x)::'b::len word)) (unat ((smt_extract (nat i) (nat j) y)::'b::len word)))"
    using unsigned_or_eq by blast
    moreover have " nat (j::int) \<le> nat (i::int) \<and> nat i < size (x::'a::len word) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j "
      using a0 a1 a2 a3 by force
    moreover have "nat i < size (y::'a::len word)"
      by (metis a1 size_word.rep_eq)
    ultimately show t1: "unat (or ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
    = (or (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    using unat_smt_extract[of "nat j" "nat i" "x", where 'b="'b"]
    using unat_smt_extract[of "nat j" "nat i" "y", where 'b="'b"]
    by presburger
  qed
  moreover have  "drop_bit (nat j) (take_bit (Suc (nat i)) (or (unat x) (unat y)))
  = (or (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    by auto
  ultimately show "(smt_extract (nat i) (nat j) (or x y)::'b::len word) =
   or ((smt_extract (nat i) (nat j) x)::'b::len word) 
    ((smt_extract (nat i) (nat j) y)::'b::len word)"
    by (metis unsigned_word_eqI)
qed


named_theorems rewrite_bv_extract_bitwise_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_xor]:
  fixes x::"'a ::len word" and y::"'a ::len word" and i::"int" and j::"int"
  shows "0 \<le> j \<longrightarrow> nat i < size x \<longrightarrow> int LENGTH('b) = i + 1 - j \<longrightarrow> j \<le> i \<longrightarrow>
smt_extract (nat i) (nat j) (semiring_bit_operations_class.xor x y) =
semiring_bit_operations_class.xor (smt_extract (nat i) (nat j) x::'b::len word)
    (smt_extract (nat i) (nat j) y::'b::len word)"
  apply (rule impI)+
proof-
  assume a0: "0 \<le> j" and a1: "nat i < size x" and a2: "int LENGTH('b) = i + 1 - j" and a3: "j \<le> i"

  have t0: "unat (smt_extract (nat i) (nat j) (xor x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (xor (unat x) (unat y)))"
  proof-
    have "unat (smt_extract (nat i) (nat j) (xor x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (unat (xor x y)))"
      using unat_smt_extract[of "nat j" "nat i" "(xor x y)", where 'b="'b"]  
      by (metis Suc_as_int Suc_eq_plus1 a0 a1 a2 a3 int_nat_eq nat_diff_distrib' nat_int nat_mono not_less_eq_eq order_trans word_size)
    then show "unat (smt_extract (nat i) (nat j) (xor x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (xor (unat x) (unat y)))"
      using unsigned_xor_eq by metis
  qed
  moreover have "unat (xor ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
  = (xor (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    proof-
      have "unat (xor ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
        = (xor (unat ((smt_extract (nat i) (nat j) x)::'b::len word)) (unat ((smt_extract (nat i) (nat j) y)::'b::len word)))"
    using unsigned_xor_eq by blast
    moreover have " nat (j::int) \<le> nat (i::int) \<and> nat i < size (x::'a::len word) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j "
      using a0 a1 a2 a3 by force
    moreover have "nat i < size (y::'a::len word)"
      by (metis a1 size_word.rep_eq)
    ultimately show t1: "unat (xor ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
    = (xor (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    using unat_smt_extract[of "nat j" "nat i" "x", where 'b="'b"]
    using unat_smt_extract[of "nat j" "nat i" "y", where 'b="'b"]
    by presburger
  qed
  moreover have  "drop_bit (nat j) (take_bit (Suc (nat i)) (xor (unat x) (unat y)))
  = (xor (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    by auto
  ultimately show "(smt_extract (nat i) (nat j) (xor x y)::'b::len word) =
   xor ((smt_extract (nat i) (nat j) x)::'b::len word) 
    ((smt_extract (nat i) (nat j) y)::'b::len word)"
    by (metis unsigned_word_eqI)
qed




named_theorems rewrite_bv_extract_bitwise_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_bitwise_xor]:
  fixes x::"'a ::len word" and y::"'a ::len word" and i::"int" and j::"int"
  shows "smt_extract (nat i) (nat j) (semiring_bit_operations_class.xor x y) =
   semiring_bit_operations_class.xor (smt_extract (nat i) (nat j) x)
    (smt_extract (nat i) (nat j) y)"
  by auto
    
named_theorems rewrite_bv_extract_not \<open>automatically_generated\<close>

lemma "uint (not x::'a::len word) = take_bit LENGTH('a::len) (not (unsigned x))"
  using unsigned_not_eq by auto

(*  Bit_Operations.not_int_div_2: not (?k::int) div (2::int) = not (?k div (2::int))
*)



lemma [rewrite_bv_extract_not]:
  fixes x::"'a ::len word" and i::"int" and j::"int"
  shows "j \<ge> 0 \<longrightarrow> i \<ge> j \<longrightarrow> i < int (size x) \<longrightarrow> int (LENGTH('b)) = i + 1 - j \<longrightarrow>
   (smt_extract (nat i) (nat j) (not x)::'b::len word) =
   not (smt_extract (nat i) (nat j) x::'b::len word)"
  apply (rule impI)+
  apply (simp add: word_uint_eq_iff)
proof-
  assume a0: "(0::int) \<le> j" and a1: "j \<le> i" and a2: "i < int (size x)"
    and a3: "int LENGTH('b) = i + (1::int) - j"

  have t0: "uint (smt_extract (nat i) (nat j) (not x)::'b::len word)
  = drop_bit (nat j) (take_bit (Suc (nat i)) (not (unsigned x)))"
  proof-
  have "nat (j::int) \<le> nat (i::int) \<and> nat i < size (not (x::'a::len word)) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j"
    by (metis Suc_eq_plus1_left Suc_nat_eq_nat_zadd1 a0 a1 a2 a3 add.commute diff_ge_0_iff_ge int_eq_iff nat_diff_distrib nat_less_iff nat_mono order_trans word_size)
  then have "uint (smt_extract (nat i) (nat j) (not x)::'b::len word)
  = drop_bit (nat j) (take_bit (Suc (nat i)) (uint (not x)))"
  using uint_smt_extract[of "nat j" "nat i" "not x", where 'b="'b"]
  by blast
  then have t0: "uint (smt_extract (nat i) (nat j) (not x)::'b::len word)
  = drop_bit (nat j) (take_bit (Suc (nat i)) (take_bit LENGTH('a::len) (not (unsigned x))))"
    using unsigned_not_eq[of x] by metis
  moreover have "(min (Suc (nat i)) LENGTH('a::len)) = Suc (nat i)"
    by (metis Suc_leI \<open>nat (j::int) \<le> nat (i::int) \<and> nat i < size (not (x::'a::len word)) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j\<close> min.orderE word_size)
  ultimately show "uint (smt_extract (nat i) (nat j) (not x)::'b::len word)
  = drop_bit (nat j) (take_bit (Suc (nat i)) (not (unsigned x)))"
    by auto
  qed

 moreover have t1: "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
drop_bit (nat j) (take_bit (nat (i + (1::int))) (not (uint x)))"
proof-
  have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) =
take_bit LENGTH('b::len) (not (unsigned (smt_extract (nat i) (nat j) x::'b::len word)))"
    using unsigned_not_eq[of "(smt_extract (nat i) (nat j) x::'b::len word)"]
    by blast
  moreover have "nat (j::int) \<le> nat (i::int) \<and> nat i < size (not (x::'a::len word)) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j"
    by (metis Suc_eq_plus1_left Suc_nat_eq_nat_zadd1 a0 a1 a2 a3 add.commute diff_ge_0_iff_ge int_eq_iff nat_diff_distrib nat_less_iff nat_mono order_trans word_size)
  moreover have "nat (j::int) \<le> nat (i::int) \<and> nat i < size (x::'a::len word) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j"
    by (metis \<open>nat (j::int) \<le> nat (i::int) \<and> nat i < size (not (x::'a::len word)) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j\<close> word_size)
  ultimately have t1: "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
take_bit LENGTH('b::len) (not (drop_bit (nat j) (take_bit (Suc (nat i)) (uint x))))"
    using uint_smt_extract[of "nat j" "nat i" x, where 'b="'b"] 
    by presburger
  then have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
take_bit LENGTH('b::len) (not (take_bit (Suc (nat i) - nat j) (drop_bit (nat j) (uint x))))"
    using drop_bit_take_bit[of "nat j" "Suc (nat i)" "uint x"]
    by presburger
 then have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
take_bit LENGTH('b::len) (not (take_bit (LENGTH('b)) (drop_bit (nat j) (uint x))))"
   using Suc_eq_plus1 \<open>nat (j::int) \<le> nat (i::int) \<and> nat i < size (x::'a::len word) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j\<close> by presburger
then have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
take_bit LENGTH('b::len) (not (drop_bit (nat j) (uint x)))"
  using take_bit_not_take_bit[of "LENGTH('b)" "(drop_bit (nat j) (uint x))"]
  by presburger
then have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
take_bit LENGTH('b::len) (not (drop_bit (nat j) (uint x)))"
  using take_bit_not_take_bit[of "LENGTH('b)" "(drop_bit (nat j) (uint x))"]
  by presburger
then have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
take_bit LENGTH('b::len) (drop_bit (nat j) (not (uint x)))"
  using not_drop_bit[of j x] by simp
then have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
drop_bit (nat j) (take_bit (nat (i + (1::int) - j) + nat j) (not (uint x)))"
  using take_bit_drop_bit[of "LENGTH('b)" "nat j" "not (uint x)"]
  by (metis a3 nat_int)
then show "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
drop_bit (nat j) (take_bit (nat (i + (1::int))) (not (uint x)))"
  using a0 a1 nat_diff_distrib' by auto
qed

  moreover have "drop_bit (nat j) (take_bit (Suc (nat i)) (not (unsigned x)))
= drop_bit (nat j) (take_bit (nat (i + (1::int))) (not (uint x)))"
    by (metis Suc_nat_eq_nat_zadd1 a0 a1 add.commute order_trans)

  ultimately show "uint (smt_extract (nat i) (nat j) (not x)::'b::len word) = uint (not (smt_extract (nat i) (nat j) x ::'b::len word))"
    by presburger
qed



named_theorems rewrite_bv_extract_sign_extend_1 \<open>automatically_generated\<close>

(*(define-cond-rule bv-extract-sign-extend-1 ((x ?BitVec) (low Int) (high Int) (k Int))
 (< high (bvsize x)) (extract high low (sign_extend k x)) (extract high low x) )
*)
lemma [rewrite_bv_extract_sign_extend_1]:
  fixes x::"'a ::len word" and low::"int" and high::"int" and k::"int"
  shows "LENGTH('b) = nat high + 1 - nat low \<and> low \<le> high \<and> nat high < size (signed_take_bit (nat (k::int)) (x::'a::len word)) \<and> nat high < size x
 \<Longrightarrow>
   (smt_extract (nat high) (nat low) (signed_take_bit (nat k) x::'a::len word)::'b::len word) =
   smt_extract (nat high) (nat low) x" 
 apply (simp add: word_unat_eq_iff)
  apply (simp add: unat_smt_extract[of "nat low" "nat high" "(signed_take_bit (nat k) x)", where 'b="'b"] nat_mono)
  apply (simp add: unat_smt_extract[of "nat low" "nat high" "x", where 'b="'b"] nat_mono)
  apply (simp add: signed_take_bit_def[of "nat k" x])
   apply (simp_all add: unsigned_or_eq unsigned_take_bit_eq unsigned_not_eq)
   apply (simp_all add: drop_bit_eq_div take_bit_eq_mod drop_bit_eq_div bit_or_iff mask_eq_exp_minus_1)
  subgoal sorry
  
  using unsigned_not_eq[of "mask (nat k)::'a::len word"]
  subgoal
  proof-
    assume a0: "bit x (nat k)"
    and a1: "LENGTH('b) = Suc (nat high) - nat low \<and> low \<le> high \<and> nat high < size (or (take_bit (nat k) x) (not (mask (nat k)))) \<and> nat high < size x"
    have "(unsigned (not (mask (nat k)::'a::len word)::'a::len word)::'b::len word) = (take_bit LENGTH('a::len) (not (unsigned (mask (nat k)::'a::len word)))::'b::len word)"
      using unsigned_not_eq[of "mask (nat k)::'a::len word"] 
      by blast
    then have "
    or (drop_bit (nat low) (take_bit (min (Suc (nat high)) (nat k)) (unat x))) (drop_bit (nat low) (take_bit (Suc (nat high)) (unat (not (mask (nat k)::'a::len word))))) =
    or (drop_bit (nat low) (take_bit (min (Suc (nat high)) (nat k)) (unat x))) (drop_bit (nat low) (take_bit (Suc (nat high)) (take_bit LENGTH('a::len) (not (unsigned (mask (nat k)::'a::len word)))::nat)))"
    show "
    or (drop_bit (nat low) (take_bit (min (Suc (nat high)) (nat k)) (unat x))) (drop_bit (nat low) (take_bit (Suc (nat high)) (unat (not (mask (nat k)::'a::len word))))) =
    drop_bit (nat low) (take_bit (Suc (nat high)) (unat x))"
      


  subgoal 


proof-
  assume a0: "LENGTH('b) = nat high + 1 - nat low \<and> low \<le> high \<and> nat high < size (signed_take_bit (nat (k::int)) (x::'a::len word)) \<and> nat high < size x"
  then have "unat (smt_extract (nat high) (nat low) (signed_take_bit (nat k) x::'a::len word)::'b::len word) = 
        drop_bit (nat low) (take_bit (Suc (nat high)) (unat (signed_take_bit (nat k) x ::'a::len word)))"
    using unat_smt_extract[of "nat low" "nat high" "(signed_take_bit (nat k) x)", where 'b="'b"]
    using nat_mono by blast
  then have "unat (smt_extract (nat high) (nat low) (signed_take_bit (nat k) x::'a::len word)::'b::len word) = 
        drop_bit (nat low) (take_bit (Suc (nat high)) (unat (or (take_bit (nat k) x) (of_bool (bit x (nat k)) * not (mask (nat k))))))"
    using signed_take_bit_def[of "nat k" x] by simp
then have "unat (smt_extract (nat high) (nat low) (signed_take_bit (nat k) x::'a::len word)::'b::len word) = 
        drop_bit (nat low) (take_bit (Suc (nat high)) (or (unat (take_bit (nat k) x ::'a::len word)) (unat (of_bool (bit x (nat k)) * not (mask (nat k))::'a::len word))))"
  using unsigned_or_eq by metis
then have "unat (smt_extract (nat high) (nat low) (signed_take_bit (nat k) x::'a::len word)::'b::len word) = 
        drop_bit (nat low) (take_bit (Suc (nat high)) (or (take_bit (nat k) (unat x)) (unat (of_bool (bit x (nat k)) * not (mask (nat k))::'a::len word))))"
  using unsigned_take_bit_eq 
  by metis
then have "unat (smt_extract (nat high) (nat low) (signed_take_bit (nat k) x::'a::len word)::'b::len word) = 
        drop_bit (nat low) (take_bit (Suc (nat high)) (or (take_bit (nat k) (unat x)) (unat (of_bool (bit x (nat k)) * not (mask (nat k))::'a::len word))))"
  using unat_word_ariths(2)[of "of_bool (bit x (nat k))" "not (mask (nat k))"]



  have


 apply (simp add: word_unat_eq_iff)
  apply (simp add: unat_smt_extract[of "nat low" "nat high" "(signed_take_bit (nat k) x)", where 'b="'b"] nat_mono)
  apply (simp add: unat_smt_extract[of "nat low" "nat high" "x", where 'b="'b"] nat_mono)
  apply (simp add: signed_take_bit_def[of "nat k" x])
   apply (simp_all add: unsigned_or_eq unsigned_take_bit_eq unsigned_not_eq)


  have
 apply (simp add: word_unat_eq_iff)
  apply (simp add: unat_smt_extract[of "nat low" "nat high" "(signed_take_bit (nat k) x::'b::len word)"]
          nat_mono)
  apply (simp add: signed_take_bit_def[of "nat k" x])
   apply (simp_all add: unsigned_or_eq unsigned_take_bit_eq unsigned_not_eq)

lemma "unat (smt_extract (nat high) (nat low) x) = drop_bit (nat low) (take_bit (Suc (nat high)) (unat x))"
  using unat_smt_extract[of "nat low" "nat high" "x", where 'b="'a"] 

  thm unat_smt_extract[of "nat low" "nat high" "x", where 'b="'b"]
  apply (simp add: unat_smt_extract[of "nat low" "nat high" "x", where 'b="'b"] nat_mono)


  apply (simp add: word_unat_eq_iff)

  using unat_smt_extract[of "nat low" "nat high" "(signed_take_bit (nat k) x)", where 'b="'b"]
  using unat_smt_extract[of "nat low" "nat high" x]
  apply simp
  

named_theorems rewrite_bv_extract_sign_extend_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_2]:
  fixes x::"'a ::len word" and low::"int" and high::"int" and k::"int"
  shows "low < int (size x) \<and> int (size x) \<le> high \<longrightarrow>
   smt_extract (nat high) (nat low) (signed_take_bit (nat k) x) =
   signed_take_bit (nat (1 + (high - int (size x))))
    (smt_extract (nat (int (size x) - 1)) (nat low) x)"
  by auto

named_theorems rewrite_bv_extract_sign_extend_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_3]:
  fixes x::"'a ::len word" and low::"int" and high::"int" and k::"int"
  shows "int (size x) \<le> low \<longrightarrow>
   smt_extract (nat high) (nat low) (signed_take_bit (nat k) x) =
   smt_repeat (nat (1 + (high - low)))
    (smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1)) x)"
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

named_theorems rewrite_bv_neg_add \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_add]:
  fixes x::"'a::len word" and y::"'a::len word" and zs::"'a::len word cvc_ListVar"
  shows "- (x + cvc_list_right (+) y zs) = - x + - cvc_list_right (+) y zs"
  apply (cases zs)
  subgoal for zss 
    by (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
  done

named_theorems rewrite_bv_mult_distrib_const_neg \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_neg]:
  fixes x::"'a ::len word" and n::"int" and m::"int"
  shows "- x * Word.Word n = x * Word.Word (- n)"
  by auto

named_theorems rewrite_bv_mult_distrib_const_add \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_add]:
  fixes x::"'a ::len word" and y::"'a ::len word" and n::"int" and m::"int"
  shows "(x + y) * Word.Word n = x * Word.Word n + y * Word.Word n"
  by (simp add: distrib_right)

named_theorems rewrite_bv_mult_distrib_const_sub \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_const_sub]:
  fixes x::"'a ::len word" and y::"'a ::len word" and n::"int" and m::"int"
  shows "(x - y) * Word.Word n = x * Word.Word n - y * Word.Word n"
  using left_diff_distrib' by auto

named_theorems rewrite_bv_mult_distrib_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_1]:
  fixes x1::"'a ::len word" and x2::"'a ::len word" and y::"'a ::len word"
  shows "(x1 + x2) * y = x1 * y + x2 * y"
  using distrib_right by blast

named_theorems rewrite_bv_mult_distrib_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_distrib_2]:
  fixes x1::"'a ::len word" and x2::"'a ::len word" and y::"'a ::len word"
  shows "y * (x1 + x2) = y * x1 + y * x2"
  using ring_class.ring_distribs(1) by blast

named_theorems rewrite_bv_not_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_not_xor]:
  fixes x::"'a ::len word" and xs::"'a ::len word cvc_ListVar"
  shows "not (cvc_list_right semiring_bit_operations_class.xor x xs) =
   cvc_list_right semiring_bit_operations_class.xor (not x) xs"
  apply (cases xs)
  subgoal for xss 
    by (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
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
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (induction zss arbitrary: zs)
      apply simp_all
    apply (simp add: word_bw_comms(2))
    apply (simp add: or.left_commute word_bw_assocs(2))
    by (simp add: word_bw_assocs(2))
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
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (induction zss arbitrary: zs)
      apply simp_all
    apply (simp add: word_bw_comms(2))
    apply (simp add: or.left_commute word_bw_assocs(2))
    by (simp add: word_bw_assocs(2))
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
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (induction zss arbitrary: zs)
      apply simp_all
      apply (simp add: or.assoc word_bw_lcs(2))
     apply (metis or.left_commute word_bw_assocs(2) word_or_max)
    by (simp add: or.assoc)
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
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (induction zss arbitrary: zs)
      apply simp_all
      apply (simp add: word_bw_assocs(3) xor.left_commute)
    apply (simp add: xor.commute)
    by (simp add: word_bw_assocs(3))
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
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (induction zss arbitrary: zs)
      apply simp_all
      apply (simp add: word_bw_assocs(3) xor.left_commute)
    apply (simp add: xor.commute)
    by (simp add: word_bw_assocs(3))
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
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (induction zss arbitrary: zs)
      apply simp_all
      apply (simp add: word_bw_assocs(3) xor.left_commute)
    apply (simp add: xor.commute)
    by (simp add: word_bw_assocs(3))
  done

named_theorems rewrite_bv_ult_add_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_add_one]:
  fixes x::"'a ::len word" and y::"'a ::len word" and n::"int"
  shows "(x < y + (Word.Word (1::int)::'a::len word)) =
   (\<not> y < x \<and> y \<noteq> not (Word.Word 0))"
  apply simp
  by (metis ab_left_minus word_Suc_le word_not_le word_not_simps(1))

named_theorems rewrite_bv_concat_to_mult \<open>automatically_generated\<close>

lemma [rewrite_bv_concat_to_mult]:
  fixes x::"'a ::len word" and i::"int" and m::"int"
  shows "(1::int) + i + m = int (size x)
   \<longrightarrow> LENGTH('b) = nat i + 1
   \<longrightarrow> LENGTH('b) + LENGTH('c) = LENGTH('a)
   \<longrightarrow> int (LENGTH('c)) = m
   \<longrightarrow> 
   (word_cat (smt_extract (nat i) (nat (0::int)) x :: 'b:: len word) (Word.Word (0::int):: 'c::len word) ::'a::len word) =
   x * (push_bit (unat (Word.Word m :: 'a::len word)) (Word.Word (1::int)::'a::len word)::'a::len word)"
  using BV_Rewrites_Lemmas.rewrite_bv_concat_to_mult by blast

named_theorems rewrite_bv_mult_slt_mult_1 \<open>automatically_generated\<close>

(*(define-rule bv-mult-slt-mult-1 ((x ?BitVec) (t ?BitVec) (a ?BitVec) (n Int) (m Int))
 (def (tn (bvsize t)) (an (bvsize a)) )
 (bvslt (bvmul (sign_extend n (bvadd x t)) (sign_extend m a)) (bvmul (sign_extend n x) (sign_extend m a)))
 (and (not (= t (bv 0 tn))) (not (= a (bv 0 an))) (= (bvslt (bvadd x t) x) (bvsgt a (bv 0 an)))))
*)
lemma [rewrite_bv_mult_slt_mult_1]:
  fixes x::"'a ::len word" and t::"'a ::len word" and a::"'a ::len word" and n::"int" and m::"int"
  shows "
    (signed_take_bit (nat n) (x + t) * signed_take_bit (nat m) a
    <s signed_take_bit (nat n) x * signed_take_bit (nat m) a) =
   (t \<noteq> (Word.Word 0::'a::len word) \<and>
    a \<noteq> (Word.Word 0::'a::len word) \<and>
   (x + t <s x) = (Word.Word 0 <s a))"
  apply (cases "t = (Word.Word 0::'a::len word)")
   apply simp
  apply (cases "a = (Word.Word 0::'a::len word)")
   apply simp
 apply (simp add: word_sless.rep_eq[of "x + t" x])
  apply (simp add: word_sless.rep_eq[of 0 a])
 apply (simp add: word_sless.rep_eq[of "signed_take_bit (nat n) (x + t) * signed_take_bit (nat m) a" "signed_take_bit (nat n) x * signed_take_bit (nat m) a"])
  sorry  

named_theorems rewrite_bv_mult_slt_mult_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_slt_mult_2]:
  fixes x::"'a ::len word" and t::"'a ::len word" and a::"'a ::len word" and n::"int" and m::"int"
  shows "(push_bit (nat n) (x + t) * signed_take_bit (nat m) a
    <s push_bit (nat n) x * signed_take_bit (nat m) a) =
   (t \<noteq> Word.Word 0 \<and>
    a \<noteq> Word.Word 0 \<and> (x + t < x) = (Word.Word 0 <s a))"
  by auto

named_theorems rewrite_bv_commutative_and \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_and]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "and x y = and y x"
  by (simp add: abel_semigroup.commute and.abel_semigroup_axioms)

named_theorems rewrite_bv_commutative_or \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_or]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "or x y = or y x"
  using or.commute by auto

named_theorems rewrite_bv_commutative_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_xor]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "semiring_bit_operations_class.xor x y =
   semiring_bit_operations_class.xor y x"
  by (simp add: xor.commute)

end