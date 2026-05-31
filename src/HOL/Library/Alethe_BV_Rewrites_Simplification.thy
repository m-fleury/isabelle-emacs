theory Alethe_BV_Rewrites_Simplification
  imports Alethe_BV_Rewrites_Lemmas 
begin

declare[[show_types,show_sorts]]
declare[[smt_expert_debug_alethe_level=0]]

(*
(define-rule bv-ite-equal-children ((c (_ BitVec 1)) (x ?BitVec)) (bvite c x x) x)
*)

named_theorems rewrite_bv_ite_equal_children \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_children]:
  fixes c::"1 word" and x::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined c x)
    \<Longrightarrow> (if bit c (0::nat) then x else x) = x"
  by simp

(*
(define-rule bv-ite-const-children-1 (
    (c (_ BitVec 1))
  )
  (bvite c (@bv 0 1) (@bv 1 1))
  (bvnot c))
*)

named_theorems rewrite_bv_ite_const_children_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_1]:
  fixes c::"1 word"
  shows "NO_MATCH cvc_a (undefined c)
    \<Longrightarrow> (if bit c (0::nat) then (0::1 word) else (1::1 word)) = not c"
  apply (cases "lsb c")
  apply (metis (mono_tags, opaque_lifting) and_one_neq_simps(2) bit.compl_eq_compl_iff bit.compl_zero nth_0 sint_minus1 smt_redand_cast_1(2,3) test_bit.Rep_inject unsigned_1 word_and_max_word
      word_test_bit_def)
  by (metis (no_types, lifting) One_nat_def and.right_neutral and_one_neq_simps(2) bit.compl_zero bit_1_0 sint_minus1 smt_redand_cast_1(1,3) unat_eq_1)

(*
(define-rule bv-ite-const-children-2 (
    (c (_ BitVec 1))
  )
  (bvite c (@bv 1 1) (@bv 0 1))
  c)
*)

named_theorems rewrite_bv_ite_const_children_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_2]:
  fixes c::"1 word"
  shows "NO_MATCH cvc_a (undefined c)
    \<Longrightarrow> (if bit c (0::nat) then (1::1 word) else (0::1 word)) = c"
  by (metis (mono_tags, opaque_lifting) Word.of_nat_unat add.group_left_neutral bit.compl_zero len_of_numeral_defs(2) mask_1 nat_int nth_0 take_bit_minus_one_eq_mask ucast_id unsigned_1 unsigned_of_int word_and_1 word_ao_nth word_exists_nth word_of_int_neg_1 word_plus_and_or_coroll2 zero_word_def)


(*
(define-rule bv-ite-equal-cond-1 (
    (c0 (_ BitVec 1))
    (t0 ?BitVec)
    (e0 ?BitVec)
    (e1 ?BitVec)
  )
  (bvite c0 (bvite c0 t0 e0) e1)
  (bvite c0 t0 e1))
*)

named_theorems rewrite_bv_ite_equal_cond_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_1]:
  fixes c0::"1 word" and t0::"'a ::len word" and e0::"'a ::len word" and e1::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined c0 t0 e0 e1)
    \<Longrightarrow> (if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by simp


(*
(define-rule bv-ite-equal-cond-2 (
    (c0 (_ BitVec 1))
    (t0 ?BitVec)
    (t1 ?BitVec)
    (e1 ?BitVec)
  )
  (bvite c0 t0 (bvite c0 t1 e1))
  (bvite c0 t0 e1))
*)

named_theorems rewrite_bv_ite_equal_cond_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_2]:
  fixes c0::"1 word" and t0::"'a ::len word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined c0 t0 t1 e1)
    \<Longrightarrow> (if bit c0 (0::nat) then t0 else if bit c0 (0::nat) then t1 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto


(*
(define-rule bv-ite-equal-cond-3 (
    (c0 (_ BitVec 1))
    (t0 ?BitVec)
    (e0 ?BitVec)
    (t1 ?BitVec)
    (e1 ?BitVec)
  )
  (bvite c0 (bvite c0 t0 e0) (bvite c0 t1 e1))
  (bvite c0 t0 e1))
*)


named_theorems rewrite_bv_ite_equal_cond_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_3]:
  fixes c0::"1 word" and t0::"'a ::len word" and e0::"'a ::len word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined c0 t0 e0 t1 e1)
    \<Longrightarrow> (if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0
    else if bit c0 (0::nat) then t1 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto

(*
(define-rule bv-ite-merge-then-if (
    (c0 (_ BitVec 1))
    (c1 (_ BitVec 1))
    (t1 ?BitVec)
    (e1 ?BitVec)
  )
  (bvite c0 (bvite c1 t1 e1) t1)
  (bvite (bvand c0 (bvnot c1)) e1 t1))
*)

named_theorems rewrite_bv_ite_merge_then_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_if]:
  fixes c0::"1 word" and c1::"1  word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined c0 c1 t1 e1)
    \<Longrightarrow> (if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else t1) =
   (if bit (and c0 (not c1)) (0::nat) then e1 else t1)"
  by (metis lsb0)


(*
(define-rule bv-ite-merge-else-if (
    (c0 (_ BitVec 1))
    (c1 (_ BitVec 1))
    (t1 ?BitVec)
    (e1 ?BitVec)
  )
  (bvite c0 (bvite c1 t1 e1) e1)
  (bvite (bvand c0 c1) t1 e1))
*)

named_theorems rewrite_bv_ite_merge_else_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_if]:
  fixes c0::"1 word" and c1::"1 word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined c0 c1 t1 e1)
    \<Longrightarrow> (if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else e1) =
   (if bit (and c0 c1) (0::nat) then t1 else e1)"
  by (metis word_ao_nth)


(*
(define-rule bv-ite-merge-then-else (
    (c0 (_ BitVec 1))
    (c1 (_ BitVec 1))
    (t0 ?BitVec)
    (e1 ?BitVec)
  )
  (bvite c0 t0 (bvite c1 t0 e1))
  (bvite (bvand (bvnot c0) (bvnot c1)) e1 t0))
*)

named_theorems rewrite_bv_ite_merge_then_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_else]:
  fixes c0::"1 word" and c1::"1 word" and t0::"'a ::len word" and e1::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined c0 c1 t0 e1)
    \<Longrightarrow>(if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t0 else e1) =
   (if bit (and (not c0) (not c1)) (0::nat) then e1 else t0)"
  by (metis lsb0)


(*
(define-rule bv-ite-merge-else-else (
    (c0 (_ BitVec 1))
    (c1 (_ BitVec 1))
    (t1 ?BitVec)
    (t0 ?BitVec)
  )
  (bvite c0 t0 (bvite c1 t1 t0))
  (bvite (bvand (bvnot c0) c1) t1 t0))
*)

named_theorems rewrite_bv_ite_merge_else_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_else]:
  fixes c0::"1  word" and c1::"1 word" and t1::"'a ::len word" and t0::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined c0 c1 t1 t0)
    \<Longrightarrow>(if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t1 else t0) =
   (if bit (and (not c0) c1) (0::nat) then t1 else t0)"
  by (metis lsb0)


(*
(define-rule bv-shl-by-const-0
  ((x ?BitVec) (sz Int))
  (bvshl x (@bv 0 sz))
  x)
*)
named_theorems rewrite_bv_shl_by_const_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_0]:
  fixes x::"'a::len word" and sz::"int"
  shows "NO_MATCH cvc_a (undefined x sz) \<Longrightarrow> smtlib_bvshl x 0 = x"
  unfolding smtlib_bvshl_def by simp


(*
(define-cond-rule bv-shl-by-const-1
  ((x ?BitVec) (amount Int) (sz Int) (en Int))
  (def (n (@bvsize x)))
  (and (< amount n) (= en (- n (+ 1 amount))))
  (bvshl x (@bv amount sz))
  (concat (extract en 0 x) (@bv 0 amount)))
*)

named_theorems rewrite_bv_shl_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_1]:
  fixes x::"'a::len word" and amount::"int" and sz::"int" and en::"int"
  shows "NO_MATCH cvc_a (undefined x amount sz en w_amount)
    \<Longrightarrow> LENGTH('b) = nat amount
    \<Longrightarrow> LENGTH('a) = LENGTH('c) + LENGTH('b)
    \<Longrightarrow> LENGTH('c) = nat en + 1
    \<Longrightarrow> w_amount = Word.Word amount
    \<Longrightarrow> (amount < int (size x)) = True
    \<Longrightarrow> en = int (size x) - (1 + amount)
    \<Longrightarrow>
   (smtlib_bvshl x w_amount::'a::len word) =
   word_cat
    (smtlib_extract en 0 x::'c::len word)
    (0::'b::len word)"
proof -
  assume lb: "LENGTH('b) = nat amount"
     and la: "LENGTH('a) = LENGTH('c) + LENGTH('b)"
     and lc: "LENGTH('c) = nat en + 1"
     and wa: "w_amount = Word.Word amount"
     and ax: "(amount < int (size x)) = True"
     and en_eq: "en = int (size x) - (1 + amount)"
  have ax': "amount < int LENGTH('a)" using ax by (simp add: word_size)
  have pos_b: "0 < LENGTH('b)" by (rule len_gt_0)
  have pos_nat: "0 < nat amount" using pos_b lb by linarith
  have nn: "0 \<le> amount" using pos_nat by simp
  have ub: "amount < 2 ^ LENGTH('a)"
  proof -
    have "int LENGTH('a) < int (2 ^ LENGTH('a))"
      using less_exp[of "LENGTH('a)"] of_nat_less_iff by blast
    thus ?thesis using ax' la by auto
  qed
  have wa': "w_amount = word_of_int amount" using wa by simp
  have unat_eq: "unat (w_amount :: 'a word) = nat amount"
    using wa' nn ub
    by (simp add: unat_eq_of_nat)
  have lhs: "smtlib_bvshl x w_amount = push_bit (nat amount) x"
    unfolding smtlib_bvshl_def by (simp add: unat_eq push_bit_eq_mult)
  show "smtlib_bvshl x w_amount =
        word_cat (smtlib_extract en 0 x :: 'c word) (0 :: 'b word)"
    unfolding lhs
  proof (rule bit_word_eqI)
    fix n :: nat assume n_lt: "n < LENGTH('a)"
    show "bit (push_bit (nat amount) x) n =
          bit (word_cat (smtlib_extract en 0 x :: 'c word) (0 :: 'b word) :: 'a word) n"
    proof (cases "n < LENGTH('b)")
      case True
      hence "\<not> bit (push_bit (nat amount) x) n"
        using lb by (simp add: bit_push_bit_iff)
      moreover from True n_lt have
        "\<not> bit (word_cat (smtlib_extract en 0 x :: 'c word) (0 :: 'b word) :: 'a word) n"
        by (simp add: bit_word_cat_iff)
      ultimately show ?thesis by simp
    next
      case False
      hence n_ge: "LENGTH('b) \<le> n" by linarith
      let ?k = "n - LENGTH('b)"
      have k_lt_c: "?k < LENGTH('c)" using n_lt n_ge la by linarith
      have k_lt_en1: "?k < nat en + 1" using k_lt_c lc by simp
      have "bit (push_bit (nat amount) x) n = bit x ?k"
        using n_ge n_lt lb by (simp add: bit_push_bit_iff)
      moreover
      have "bit (word_cat (smtlib_extract en 0 x :: 'c word) (0 :: 'b word) :: 'a word) n
            = bit (smtlib_extract en 0 x :: 'c word) ?k"
        using False n_lt by (simp add: bit_word_cat_iff)
      moreover
      have "bit (smtlib_extract en 0 x :: 'c word) ?k = bit x ?k"
        unfolding smtlib_extract_def
        using k_lt_c k_lt_en1 la pos_b
        by (metis One_nat_def Suc_nat_eq_nat_zadd1[of "en::int"]
            Suc_pred[of "nat (en::int) + Suc 0"] add.commute[of "en::int" "1"]
            add.commute[of "1" "amount::int"]
            add_cancel_left_right[of "(n::nat) - LENGTH('f::len0)" "0"]
            add_diff_cancel_right'[of "nat (en::int)" "Suc 0"] ax
            bit_take_bit_iff[of "Suc (nat (en::int))" "x::'a::len word"
              "(n::nat) - LENGTH('f::len0)"]
            diff_ge_0_iff_ge[of "int (size (x::'a::len word))" "1 + (amount::int)"]
            en_eq lc len_gt_0 nat_code(2)
            nth_slice[of "0" "take_bit (Suc (nat (en::int))) (x::'a::len word)"
              "(n::nat) - LENGTH('f::len0)"]
            zless_imp_add1_zle[of "amount::int"
              "int (size (x::'a::len word))"])
      ultimately show ?thesis by simp
    qed
  qed
qed
(*
(define-cond-rule bv-shl-by-const-2
  ((x ?BitVec) (amount Int) (sz Int) (w Int))
  (and (>= amount (@bvsize x)) (= w (@bvsize x)))
  (bvshl x (@bv amount sz))
  (@bv 0 w))

Note assumption: int LENGTH('a) = w is not needed here
*)

named_theorems rewrite_bv_shl_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_2]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int" and w::"int"
  shows "NO_MATCH cvc_a (undefined x amount sz w)
    \<Longrightarrow>
   (int (size x) \<le> amount) = True \<Longrightarrow>
   amount < 2^LENGTH('a::len) \<Longrightarrow>
   int LENGTH('a) = sz \<Longrightarrow>
    Word.Word amount = w_amount \<Longrightarrow> int LENGTH('a) = w \<Longrightarrow>
   smtlib_bvshl x w_amount = (0::'a::len word)"
proof -
  assume a1: "(int (size x) \<le> amount) = True"
     and a2: "amount < 2^LENGTH('a::len)"
     and a4: "Word.Word amount = w_amount"
  from a1 have a1': "int LENGTH('a) \<le> amount" by (simp add: word_size)
  have nn: "0 \<le> amount" using a1' by (meson of_nat_0_le_iff order_trans)
  have unat_eq: "unat (w_amount::'a::len word) = nat amount"
    using a4[symmetric] a2 nn
    by (simp add: unat_eq_of_nat)
  have len_le: "LENGTH('a) \<le> nat amount" using a1' nn by linarith
  show "smtlib_bvshl x w_amount = (0::'a::len word)"
    unfolding smtlib_bvshl_def
    by (simp add: push_bit_eq_mult [symmetric] unat_eq push_bit_word_beyond len_le)
qed

(*
(define-rule bv-lshr-by-const-0
  ((x ?BitVec) (sz Int))
  (bvlshr x (@bv 0 sz))
  x)

Note: LENGTH('a) = sz not needed
*)

named_theorems rewrite_bv_lshr_by_const_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_0]:
  fixes x::"'a ::len word"  and sz::"int"
  shows "NO_MATCH cvc_a (undefined x sz)
    \<Longrightarrow> smtlib_bvlshr x 0 = x"
  unfolding smtlib_bvlshr_def
  by force


(*
(define-cond-rule bv-lshr-by-const-1
  ((x ?BitVec) (amount Int) (sz Int) (nm1 Int))
  (def (n (@bvsize x)))
  (and (< amount n) (= nm1 (- n 1)))
  (bvlshr x (@bv amount sz))
  (concat (@bv 0 amount) (extract nm1 amount x)))

*)
named_theorems rewrite_bv_lshr_by_const_1 \<open>automatically_generated\<close>

lemma rewrite_bv_lshr_by_const_1_original:
  fixes x::"'a ::len word" and amount::"int" and sz::"int" and nm1::"int" 
  shows "NO_MATCH cvc_a (undefined x amount sz nm1)  \<Longrightarrow>
   LENGTH('a) = LENGTH('b) + LENGTH('c) \<Longrightarrow> 
   amount < int (size x) \<Longrightarrow> 
   LENGTH('c) = nat nm1 + 1 - nat amount \<Longrightarrow>
   nm1 = int (size x) - 1 \<Longrightarrow> 
   (drop_bit (nat (amount)) x::'a::len word) =
   word_cat (0::'b::len word)
    (smt_extract (nat nm1) (nat amount) x::'c::len word)" 
proof-
  assume "NO_MATCH cvc_a (undefined x amount sz nm1)"
   and a0: "LENGTH('a) = LENGTH('b) + LENGTH('c)"
   and a1:  "amount < int (size x)"
   and a3: "LENGTH('c) = nat nm1 + 1 - nat amount"
  and a4: "nm1 =int (size x) - 1"

  
  have a2: "nat nm1 < size x"
    by (simp add: a4 nat_less_iff)
  have a4': "nm1 = LENGTH('a) - 1"
    by (simp add: a4 int_minus size_word.rep_eq)
  have "unat (drop_bit (nat amount) x) = drop_bit (nat amount) (unat x)"
    by (simp only: unat_drop_bit_eq)
  moreover have "(take_bit (Suc (nat nm1)) (unat x)) = unat x"
    using a4'
    by (metis One_nat_def Suc_pred len_gt_0 nat_int take_bit_length_eq unsigned_take_bit_eq)
  moreover have "unat (word_cat (0::'b::len word)
    (smt_extract (nat nm1) (nat amount) x::'c::len word)::'a::len word) =  drop_bit (nat amount) (take_bit (Suc (nat nm1)) (unat x))"
    apply (subst unat_word_cat)
     apply (simp add: a0)
    apply (subst unat_smt_extract)
       apply (simp_all add: a1 a2 a3)
    by (metis a3 add.commute len_gt_0 less_Suc_eq_le plus_1_eq_Suc zero_less_diff)
  ultimately show "(drop_bit (nat (amount)) x::'a::len word) =
   word_cat (0::'b::len word)
    (smt_extract (nat nm1) (nat amount) x::'c::len word)" 
    by (metis word_unat.Rep_inverse)
qed


(*
(define-cond-rule bv-lshr-by-const-1
  ((x ?BitVec) (amount Int) (sz Int) (nm1 Int))
  (def (n (@bvsize x)))
  (and (< amount n) (= nm1 (- n 1)))
  (bvlshr x (@bv amount sz))
  (concat (@bv 0 amount) (extract nm1 amount x)))
*)

lemma [rewrite_bv_lshr_by_const_1]:
  fixes x::"'a::len word" and amount::"int" and sz::"int" and nm1::"int"
  shows "NO_MATCH cvc_a (undefined x amount sz nm1 w_amount)
    \<Longrightarrow> LENGTH('b) = nat amount
    \<Longrightarrow> LENGTH('a) = LENGTH('b) + LENGTH('c)
    \<Longrightarrow> LENGTH('c) = nat nm1 + 1 - nat amount
    \<Longrightarrow> w_amount = Word.Word amount
    \<Longrightarrow> (amount < int (size x)) = True
    \<Longrightarrow> nm1 = int (size x) - 1
    \<Longrightarrow>
   (smtlib_bvlshr x w_amount::'a::len word) =
   word_cat
    (0::'b::len word)
    (smtlib_extract nm1 amount x::'c::len word)"
proof -                                                     
  assume lb: "LENGTH('b) = nat amount"
     and la: "LENGTH('a) = LENGTH('b) + LENGTH('c)"
     and lc: "LENGTH('c) = nat nm1 + 1 - nat amount"
     and wa: "w_amount = Word.Word amount"
     and ax: "(amount < int (size x)) = True"
     and nm: "nm1 = int (size x) - 1"
  have ax': "amount < int LENGTH('a)" using ax by (simp add: word_size)
  have pos_b: "0 < LENGTH('b)" by (rule len_gt_0)
  have pos_nat: "0 < nat amount" using pos_b lb by linarith
  have nn: "0 \<le> amount" using pos_nat by simp
  have ub: "amount < 2 ^ LENGTH('a)"
  proof -
    have "int LENGTH('a) < int (2 ^ LENGTH('a))"
      using less_exp[of "LENGTH('a)"] of_nat_less_iff by blast
    thus ?thesis using ax'
      using of_nat_less_two_power order_less_trans by blast              
  qed                                               
  have wa': "w_amount = word_of_int amount" using wa by simp
  have unat_eq: "unat (w_amount :: 'a word) = nat amount"
    using wa' nn ub by (simp add: unat_eq_nat_uint uint_word_of_int)
  have nat_nm: "nat nm1 + 1 = LENGTH('a)"
    using nm 
    by (metis Nat.le_imp_diff_is_add add.commute diff_is_0_eq' la lb lc
        len_not_eq_0 nle_le)
  have lc_eq: "LENGTH('c) = LENGTH('a) - nat amount"
    using lc nat_nm by simp
  have lhs: "smtlib_bvlshr x w_amount = drop_bit (nat amount) x"
    unfolding smtlib_bvlshr_def by (simp add: unat_eq flip: drop_bit_eq_div)
  show "smtlib_bvlshr x w_amount =
        word_cat (0::'b word) (smtlib_extract nm1 amount x :: 'c word)"
    unfolding lhs
  proof (rule bit_word_eqI)
    fix n :: nat assume n_lt: "n < LENGTH('a)"
    show "bit (drop_bit (nat amount) x) n =
          bit (word_cat (0::'b word) (smtlib_extract nm1 amount x :: 'c word) :: 'a word) n"
    proof (cases "n < LENGTH('c)")
      case True
      hence k_lt: "nat amount + n < LENGTH('a)" using lc_eq by linarith
      have "bit (drop_bit (nat amount) x) n = bit x (nat amount + n)"
        by (simp add: bit_drop_bit_eq)
      moreover
      have "bit (word_cat (0::'b word) (smtlib_extract nm1 amount x :: 'c word) :: 'a word) n
            = bit (smtlib_extract nm1 amount x :: 'c word) n"
        using True n_lt
        by (simp add: bit_ucast_iff)
      moreover
      have "bit (smtlib_extract nm1 amount x :: 'c word) n = bit x (nat amount + n)"
        unfolding smtlib_extract_def
        using True k_lt nat_nm lc_eq
        by (metis add.commute diff_add_cancel nat_int.Rep_inverse nm nth_slice
            size_word.rep_eq take_bit_length_eq)
      ultimately show ?thesis by simp
    next
      case False
      hence n_ge: "LENGTH('c) \<le> n" by linarith
      hence k_ge: "LENGTH('a) \<le> nat amount + n" using lc_eq by linarith
      have "\<not> bit (drop_bit (nat amount) x) n"
        using k_ge by (auto simp: bit_drop_bit_eq dest: bit_imp_le_length)
      moreover from False n_lt have
        "\<not> bit (word_cat (0::'b word) (smtlib_extract nm1 amount x :: 'c word) :: 'a word) n"
        by (simp add: bit_word_ucast_iff)
      ultimately show ?thesis by simp
    qed
  qed
qed                

(*
(define-cond-rule bv-lshr-by-const-2
  ((x ?BitVec) (amount Int) (sz Int))
  (>= amount (@bvsize x))
  (bvlshr x (@bv amount sz))
  (@bv 0 sz))                                      
*)
named_theorems rewrite_bv_lshr_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_2]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "NO_MATCH cvc_a (undefined x amount sz w_amount)
    \<Longrightarrow>
   (int (size x) \<le> amount) = True \<Longrightarrow>
   amount < 2 ^ LENGTH('a::len) \<Longrightarrow>
   int LENGTH('a) = sz \<Longrightarrow>
   Word.Word amount = w_amount \<Longrightarrow>
   smtlib_bvlshr x w_amount = (0::'a::len word)"
proof -
  assume ax: "(int (size x) \<le> amount) = True"
     and ub: "amount < 2 ^ LENGTH('a::len)"
     and wa: "Word.Word amount = w_amount"
  from ax have ax': "int LENGTH('a) \<le> amount" by (simp add: word_size)
  have nn: "0 \<le> amount" using ax' by (meson of_nat_0_le_iff order_trans)
  have wa': "w_amount = word_of_int amount" using wa[symmetric] by simp
  have unat_eq: "unat (w_amount :: 'a word) = nat amount"
    using wa' nn ub by (simp add: unat_eq_nat_uint uint_word_of_int)
  have len_le: "LENGTH('a) \<le> nat amount" using ax' nn by linarith
  show "smtlib_bvlshr x w_amount = (0::'a::len word)"
    unfolding smtlib_bvlshr_def
    by (simp add: unat_eq drop_bit_word_beyond len_le flip: drop_bit_eq_div)
qed

(*
(define-rule bv-ashr-by-const-0
  ((x ?BitVec) (sz Int))
  (bvashr x (@bv 0 sz))
  x)
*)

named_theorems rewrite_bv_ashr_by_const_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_by_const_0]:
  fixes x::"'a::len word" and sz::"int"
  shows "NO_MATCH cvc_a (undefined x sz) \<Longrightarrow> 
    LENGTH('a) = nat sz \<Longrightarrow>
   smtlib_bvashr x 0 = x"
  unfolding smtlib_bvashr_def smtlib_extract_def smtlib_bvlshr_def
  by simp


(*
(define-cond-rule bv-ashr-by-const-1
  ((x ?BitVec) (amount Int) (sz Int) (nm1 Int))
  (def (n (@bvsize x)))
  (and (< amount n) (= nm1 (- n 1)))
  (bvashr x (@bv amount sz))
  (concat
    (repeat amount (extract nm1 nm1 x))
    (extract nm1 amount x)
  ))
*)

named_theorems rewrite_bv_ashr_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_by_const_1]:
  fixes x::"'a::len word" and amount::"int" and sz::"int" and nm1::"int"
  shows "NO_MATCH cvc_a (undefined x amount sz nm1 w_amount)
    \<Longrightarrow> LENGTH('b) = nat amount
    \<Longrightarrow> LENGTH('a) = LENGTH('b) + LENGTH('c)
    \<Longrightarrow> w_amount = Word.Word amount
    \<Longrightarrow> (amount < int (size x)) = True
    \<Longrightarrow> nm1 = int (size x) - 1
    \<Longrightarrow>
   (smtlib_bvashr x w_amount::'a::len word) =
   word_cat
    (smt_repeat amount (smtlib_extract nm1 nm1 x ::1 word)::'b::len word)
    (smtlib_extract nm1 amount x::'c::len word)"
proof -
  assume lb: "LENGTH('b) = nat amount"
     and la: "LENGTH('a) = LENGTH('b) + LENGTH('c)"
     and wa: "w_amount = Word.Word amount"
     and ax: "(amount < int (size x)) = True"
     and nm: "nm1 = int (size x) - 1"
  have  lc: "LENGTH('c) = nat nm1 + 1 - nat amount"
    by (metis Suc_diff_1 Suc_eq_plus1 add_diff_cancel_left' int_minus la lb len_gt_0 nat_int nm of_nat_1 word_size)
  have ax': "amount < int LENGTH('a)" using ax by (simp add: word_size)
  have pos_b: "0 < LENGTH('b)" by (rule len_gt_0)
  have pos_nat: "0 < nat amount" using pos_b lb by linarith
  have nn: "0 \<le> amount" using pos_nat by simp
  have amount_pos: "0 < amount" using pos_nat by simp
  have ub: "amount < 2 ^ LENGTH('a)"
  proof -
    have "int LENGTH('a) < int (2 ^ LENGTH('a))"
      using less_exp[of "LENGTH('a)"] of_nat_less_iff by blast
    thus ?thesis using ax'
      using of_nat_less_two_power order_less_trans by blast
  qed
  have wa': "w_amount = word_of_int amount" using wa by simp
  have nat_nm: "nat nm1 + 1 = LENGTH('a)"
    using nm
    by (metis Nat.le_imp_diff_is_add add.commute diff_is_0_eq' la lb lc
        len_not_eq_0 nle_le)
  have lc_eq: "LENGTH('c) = LENGTH('a) - nat amount"
    using lc nat_nm by simp
  have nat_amount_lt: "nat amount < LENGTH('a)"
    using ax' nn by linarith
  have amount_eq_lenb: "amount = int LENGTH('b)" using lb nn by simp
  have nm_alt: "int (LENGTH('a) - 1) = nm1"
  proof -
    have "int (LENGTH('a) - 1) = int LENGTH('a) - 1"
      using len_gt_0[where 'a='a] by linarith
    also have "\<dots> = nm1" using nm by (simp add: word_size)
    finally show ?thesis .
  qed

  (* LHS reduces to signed_drop_bit *)
  have lhs: "smtlib_bvashr x w_amount = signed_drop_bit (nat amount) x"
  proof -
    have eq1: "(word_of_int (int (nat amount)) :: 'a word) = w_amount"
      using wa' nn by simp
    have "signed_drop_bit (nat amount) x
          = smtlib_bvashr x (word_of_int (int (nat amount)))"
      using signed_drop_bit_lift[of "nat amount" x] nat_amount_lt by simp
    thus ?thesis using eq1 by simp
  qed

  let ?top = "smtlib_extract nm1 nm1 x :: 1 word"
  let ?bot = "smtlib_extract nm1 amount x :: 'c word"
  let ?rep = "smt_repeat amount ?top :: 'b word"

  have top_eq: "?top = (if bit x (LENGTH('a) - 1) then 1 else 0)"
    using smtlib_extract_msb_eq[of x] nm_alt by metis

  have rep_zero_case: "(smt_repeat amount (0::1 word) :: 'b word) = 0"
    using smt_repeat_zeros amount_eq_lenb amount_pos
    by simp
  have rep_ones_case:
    "(smt_repeat amount (1::1 word) :: 'b word) = mask (Suc LENGTH('b))"
    using smt_repeat_ones_mask amount_eq_lenb amount_pos
    by simp

  show "smtlib_bvashr x w_amount = word_cat ?rep ?bot"
    unfolding lhs
  proof (rule bit_word_eqI)
    fix n :: nat assume n_lt: "n < LENGTH('a)"
    show "bit (signed_drop_bit (nat amount) x) n =
          bit (word_cat ?rep ?bot :: 'a word) n"
    proof (cases "n < LENGTH('c)")
      case True
      hence k_lt: "nat amount + n < LENGTH('a)" using lc_eq by linarith
      have lhs_bit:
        "bit (signed_drop_bit (nat amount) x) n = bit x (nat amount + n)"
        using True lc_eq by (simp add: bit_signed_drop_bit_iff)
      have cat_bit: "bit (word_cat ?rep ?bot :: 'a word) n = bit ?bot n"
        using True n_lt by (simp add: bit_word_cat_iff)
      have ext_bit: "bit ?bot n = bit x (nat amount + n)"
        unfolding smtlib_extract_def
        using True k_lt nat_nm lc_eq
        by (metis add.commute diff_add_cancel nat_int.Rep_inverse nm nth_slice
            size_word.rep_eq take_bit_length_eq)
      from lhs_bit cat_bit ext_bit show ?thesis by simp
    next
      case False
      hence n_ge: "LENGTH('c) \<le> n" by linarith
      hence k_ge: "LENGTH('a) - nat amount \<le> n" using lc_eq by simp
      have lhs_bit:
        "bit (signed_drop_bit (nat amount) x) n = bit x (LENGTH('a) - 1)"
        using k_ge n_lt by (simp add: bit_signed_drop_bit_iff)
      have k_lt_b: "n - LENGTH('c) < LENGTH('b)"
        using n_ge n_lt la by linarith
      have cat_bit:
        "bit (word_cat ?rep ?bot :: 'a word) n = bit ?rep (n - LENGTH('c))"
        using False n_lt n_ge by (simp add: bit_word_cat_iff)
      have rep_bit: "bit ?rep (n - LENGTH('c)) = bit x (LENGTH('a) - 1)"
      proof (cases "bit x (LENGTH('a) - 1)")
        case True
        hence "?top = 1" using top_eq by simp
        hence "?rep = mask (Suc LENGTH('b))" using rep_ones_case by simp
        moreover have "bit (mask (Suc LENGTH('b)) :: 'b word) (n - LENGTH('c))"
          using k_lt_b by (simp add: bit_mask_iff)
        ultimately show ?thesis using True by simp
      next
        case False
        hence "?top = 0" using top_eq by simp
        hence "?rep = 0" using rep_zero_case by simp
        thus ?thesis using False by simp
      qed
      from lhs_bit cat_bit rep_bit show ?thesis by simp
    qed
  qed
qed


(*
(define-cond-rule bv-ashr-by-const-2
  ((x ?BitVec) (amount Int) (sz Int) (nm1 Int) (rn Int))
  (and (>= amount (@bvsize x)) (= nm1 (- (@bvsize x) 1)) (= rn (@bvsize x)))
  (bvashr x (@bv amount sz))
  (repeat rn (extract nm1 nm1 x)))
*)

named_theorems rewrite_bv_ashr_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_by_const_2]:
  fixes x::"'a::len word" and amount::"int" and sz::"int" and nm1::"int" and rn::"int"
  shows "NO_MATCH cvc_a (undefined x amount sz nm1 rn)
    \<Longrightarrow> amount \<ge> LENGTH('a)
    \<Longrightarrow> nm1 = LENGTH('a) - 1
    \<Longrightarrow> rn = LENGTH('a)
    \<Longrightarrow> w_amount = Word.Word amount
    \<Longrightarrow> amount < 2 ^ LENGTH('a)
    \<Longrightarrow>
   (smtlib_bvashr x w_amount::'a::len word) =
    (smt_repeat rn (smtlib_extract nm1 nm1 x ::1 word)::'a::len word)"
proof -                                                                                                           
  assume ax: "amount \<ge> LENGTH('a)"
    and ub: "amount < 2 ^ LENGTH('a)"
    and nm: "nm1 = LENGTH('a) - 1"
    and rn_eq: "rn = LENGTH('a)"
    and wa: "w_amount = Word.Word amount"
  have ax': "int LENGTH('a) \<le> amount" using ax by simp
  have nn: "0 \<le> amount" using ax' by (meson of_nat_0_le_iff order_trans)
  have wa': "w_amount = word_of_int amount" using wa by simp
  have unat_eq: "unat (w_amount :: 'a word) = nat amount"
   using wa' nn ub by (simp add: unat_eq_nat_uint uint_word_of_int)
  have len_le: "LENGTH('a) \<le> nat amount" using ax' nn by linarith
  have pos_a: "0 < LENGTH('a)" by (rule len_gt_0)
  have rn_eq_lenA: "rn = int LENGTH('a)" using rn_eq by simp
  have rn_pos: "0 < rn" using rn_eq_lenA pos_a by linarith
  have nm_alt: "int (LENGTH('a) - 1) = nm1"
  proof -                                                                                                         
   have "int (LENGTH('a) - 1) = int LENGTH('a) - 1"                                                              
     using pos_a by linarith                                                                                     
   also have "\<dots> = nm1" using nm
     by (metis nm calculation)
   finally show ?thesis .
 qed

 let ?top = "smtlib_extract nm1 nm1 x :: 1 word"
 have top_eq: "?top = (if bit x (LENGTH('a) - 1) then 1 else 0)"
   using smtlib_extract_msb_eq[of x] nm_alt by metis

 have rep_zero: "(smt_repeat rn (0::1 word) :: 'a word) = 0"
   using smt_repeat_zeros rn_eq_lenA rn_pos by simp
 have rep_ones_mask:                                                                                             
   "(smt_repeat rn (1::1 word) :: 'a word) = mask (Suc LENGTH('a))"                                              
   using smt_repeat_ones_mask rn_eq_lenA rn_pos by simp                                      
 have mask_eq_minus1: "(mask (Suc LENGTH('a)) :: 'a word) = -1"                                                  
   by (rule bit_word_eqI) (auto simp: bit_simps)                                                                 
                                                                                                                 
 show "smtlib_bvashr x w_amount = (smt_repeat rn ?top :: 'a word)"                                               
 proof (cases "bit x (LENGTH('a) - 1)")                                                                          
   case True                                                                                                     
   have top1: "?top = 1" using top_eq True by simp                                                               
   have rep_rhs: "(smt_repeat rn ?top :: 'a word) = -1"                                                          
     using top1 rep_ones_mask mask_eq_minus1 by simp                                                             
   have msb_one:                                                                                                 
     "(smtlib_extract (int LENGTH('a) - 1) (int LENGTH('a) - 1) x :: 1 word) = 1"                            
     using smtlib_extract_msb_eq[of x] True 
     using rn_eq_lenA rn_pos by auto
   have lhs_ashr: "smtlib_bvashr x w_amount = not (smtlib_bvlshr (not x) w_amount)"                              
     unfolding smtlib_bvashr_def by (simp add: msb_one)
   have inner_zero: "smtlib_bvlshr (not x) w_amount = 0"                                                         
     unfolding smtlib_bvlshr_def                                                                                 
     by (simp add: unat_eq drop_bit_word_beyond len_le flip: drop_bit_eq_div)  
   then show ?thesis
     by (simp add: lhs_ashr mask_eq_minus1 rep_ones_mask top1)
 next
   case False
   have top0: "?top = 0" using top_eq False by simp
   have msb_zero:
     "(smtlib_extract (int (LENGTH('a) - 1)) (int (LENGTH('a) - 1)) x :: 1 word) = 0"
     using smtlib_extract_msb_eq[of x] False by simp
   have lhs_ashr: "smtlib_bvashr x w_amount = smtlib_bvlshr x w_amount"
     unfolding smtlib_bvashr_def using msb_zero
     using rn_eq_lenA rn_pos by auto
   have lhs_zero: "smtlib_bvlshr x w_amount = 0"
     unfolding smtlib_bvlshr_def
     by (simp add: unat_eq drop_bit_word_beyond len_le flip: drop_bit_eq_div)
   then show ?thesis
     by (simp add: lhs_ashr rep_zero top0)
 qed
qed


(*
(define-cond-rule bv-and-concat-pullup
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (ys ?BitVec :list)
   (nxm1 Int) (ny Int) (nym1 Int))
  (def
    (nx (@bvsize (concat z y ys)))
  )
  (and (= ny (@bvsizeet.minus x x)
  (@set.empty_of_typ y)) (= nxm1 (- nx 1)) (= nym1 (- (@bvsize y) 1)))
  (bvand xs (concat ys z y) ws)
  (concat
    (bvand (extract nxm1 ny (bvand xs ws)) (concat ys z))
    (bvand (extract nym1 0 (bvand xs ws)) y)
  ))

*)

named_theorems rewrite_bv_and_concat_pullup \<open>automatically_generated\<close>

lemma rewrite_bv_and_concat_pullup_lemma1:
  fixes t1::"'a::len word" and y::"'b::len word" and z::"'c::len word"
  assumes LEN: "LENGTH('a) = LENGTH('b) + LENGTH('c)"
  shows
    "(and (word_cat z y::'a::len word) t1::'a word)
   = (word_cat
        (and (smt_extract (LENGTH('a) - 1) (LENGTH('b)) t1::'c::len word) z::'c::len word)
        (and (smt_extract (LENGTH('b) - 1) (nat 0) t1::'b::len word) y::'b::len word)
      ::'a word)"
proof (rule bit_word_eqI)
  fix n :: nat
  assume nlt: "n < LENGTH('a)"
  show "bit (and (word_cat z y::'a word) t1) n
      = bit (word_cat
              (and (smt_extract (LENGTH('a) - 1) LENGTH('b) t1::'c word) z::'c word)
              (and (smt_extract (LENGTH('b) - 1) (nat 0) t1::'b word) y::'b word)
            ::'a word) n"
  proof (cases "n < LENGTH('b)")
    case True
    have ext_lo: "bit (smt_extract (LENGTH('b) - 1) 0 t1::'b word) n = bit t1 n"
      using True by (simp add: bit_smt_extract)
    show ?thesis
      using True nlt ext_lo
      by (metis bit_and_iff bit_word_cat_iff nat_code(2))
  next
    case False
    hence nge: "LENGTH('b) \<le> n" by simp
    have plus_back: "n - LENGTH('b) + LENGTH('b) = n" using nge by simp
    have lt_lc: "n - LENGTH('b) < LENGTH('c)" using nge nlt LEN by linarith
    have lt_sucla: "n - LENGTH('b) + LENGTH('b) < Suc (LENGTH('a) - 1)"
      using plus_back nlt by linarith
    have ext_hi:
      "bit (smt_extract (LENGTH('a) - 1) LENGTH('b) t1::'c word) (n - LENGTH('b)) = bit t1 n"
      using lt_sucla lt_lc plus_back by (simp add: bit_smt_extract)
    show ?thesis
      using nge nlt ext_hi
      by (metis nlt nge ext_hi bit_word_cat_iff False bit_and_iff)
  qed
qed

lemma rewrite_bv_and_concat_pullup_todo1 [rewrite_bv_and_concat_pullup]:
  fixes z::"'a::len word" and y::"'b::len word"
    and xs::"bool list list" and ws::"bool list list"
    and nxm1::int  and ys::"bool list list" and ny::int and nym1::int
  shows
"NO_MATCH cvc_a (undefined xs ws y z ys nxm1 ny nym1)
\<Longrightarrow> xs \<noteq> []
\<Longrightarrow> ys \<noteq> []
 \<Longrightarrow> ny = int LENGTH('b)
 \<Longrightarrow> nxm1 = int LENGTH('c) - 1
 \<Longrightarrow> nym1 = int LENGTH('b) - 1
 \<Longrightarrow> LENGTH('b) + LENGTH('a) = LENGTH('c)
 \<Longrightarrow> xs_w = map of_bl xs
 \<Longrightarrow> ws_w = map of_bl ws
 \<Longrightarrow> ys_w = map of_bl ys

 \<Longrightarrow> (cvc_list_left and (ListVar xs_w) (cvc_list_right and (word_cat z y::'c::len word) (ListVar ws_w))::'c word)
  = (word_cat
       (and (smtlib_extract nxm1 ny (cvc_list_both' and (ListVar xs_w) (ListVar ws_w)::'c::len word)::'a::len word) z::'a word)
       (and (smtlib_extract nym1 0 (cvc_list_both' and (ListVar xs_w) (ListVar ws_w)::'c::len word)::'b::len word) y::'b word)
     ::'c word)"
proof -
  assume "NO_MATCH cvc_a (undefined xs ws y z ys nxm1 ny nym1)"
  assume xs_ne: "xs \<noteq> []"
  assume "ys \<noteq> []"
  assume ny_eq: "ny = int LENGTH('b)"
  assume nxm1_eq: "nxm1 = int LENGTH('c) - 1"
  assume nym1_eq: "nym1 = int LENGTH('b) - 1"
  assume LEN: "LENGTH('b) + LENGTH('a) = LENGTH('c)"
  assume xs_w_def: "xs_w = map of_bl xs"
  assume ws_w_def: "ws_w = map of_bl ws"
  assume ys_w_def: "ys_w = map of_bl ys"

  have xs'_ne: "xs_w \<noteq> []" using xs_ne xs_w_def by simp

  have ext_hi:
    "\<And>T::'c word. (smtlib_extract nxm1 ny T::'a word) = (smt_extract (LENGTH('c) - 1) LENGTH('b) T::'a word)"
    using nxm1_eq ny_eq len_gt_0[where 'a='c]
    by (simp add: smtlib_extract_def smt_extract_def Suc_diff_1 nat_diff_distrib)
  have ext_lo:
    "\<And>T::'c word. (smtlib_extract nym1 0 T::'b word) = (smt_extract (LENGTH('b) - 1) (nat 0) T::'b word)"
    using nym1_eq len_gt_0[where 'a='b]
    by (simp add: smtlib_extract_def smt_extract_def Suc_diff_1 nat_diff_distrib)

  have lemma1_inst:
    "\<And>T::'c word. and (word_cat z y::'c word) T
   = (word_cat
       (and (smt_extract (LENGTH('c) - 1) LENGTH('b) T::'a word) z::'a word)
       (and (smt_extract (LENGTH('b) - 1) (nat 0) T::'b word) y::'b word)
     ::'c word)"
    by (rule rewrite_bv_and_concat_pullup_lemma1[OF LEN[symmetric]])

  show "(cvc_list_left and (ListVar xs_w) (cvc_list_right and (word_cat z y::'c word) (ListVar ws_w))::'c word)
      = (word_cat
           (and (smtlib_extract nxm1 ny (cvc_list_both' and (ListVar xs_w) (ListVar ws_w)::'c word)::'a word) z::'a word)
           (and (smtlib_extract nym1 0 (cvc_list_both' and (ListVar xs_w) (ListVar ws_w)::'c word)::'b word) y::'b word)
         ::'c word)"
  proof (cases "ws_w = []")
    case True
    define T :: "'c word" where "T = cvc_nary_op_fold and xs_w"

    have both_eq: "(cvc_list_both' and (ListVar xs_w) (ListVar ws_w)::'c word) = T"
      unfolding T_def True by (simp add: cvc_list_both'_def)

    have Tval: "T = foldr and (butlast xs_w) (last xs_w)"
      unfolding T_def using xs'_ne by (rule cvc_nary_op_fold_butlast)

    have R: "cvc_list_right and (word_cat z y::'c word) (ListVar ws_w) = word_cat z y"
      unfolding True by (simp add: cvc_list_right_Nil)
    have L: "cvc_list_left and (ListVar xs_w) (word_cat z y::'c word)
           = foldr and xs_w (word_cat z y::'c word)"
      by (rule cvc_list_left_transfer)
    have step1: "foldr and xs_w (word_cat z y::'c word)
               = foldr and (butlast xs_w) (and (last xs_w) (word_cat z y::'c word))"
    proof -
      have "foldr and xs_w (word_cat z y::'c word)
          = foldr and (butlast xs_w @ [last xs_w]) (word_cat z y::'c word)"
        using xs'_ne by (simp add: append_butlast_last_id)
      also have "... = foldr and (butlast xs_w) (and (last xs_w) (word_cat z y::'c word))"
        by simp
      finally show ?thesis .
    qed
    have step2: "foldr and (butlast xs_w) (and (last xs_w) (word_cat z y::'c word))
               = and (word_cat z y::'c word) T"
      unfolding Tval by (metis and.commute foldr_word_and_pullout)

    have lhs_simp:
      "(cvc_list_left and (ListVar xs_w) (cvc_list_right and (word_cat z y::'c word) (ListVar ws_w))::'c word)
     = and (word_cat z y::'c word) T"
      using R L step1 step2 by metis

    show ?thesis
      unfolding both_eq ext_hi ext_lo lhs_simp
      by (rule lemma1_inst)
  next
    case False
    hence ws'_ne: "ws_w \<noteq> []" by simp

    define T :: "'c word"
      where "T = foldr and xs_w (foldr and (butlast ws_w) (last ws_w))"

    have both_eq: "(cvc_list_both' and (ListVar xs_w) (ListVar ws_w)::'c word) = T"
      unfolding T_def using cvc_list_both_transfer'[OF ws'_ne xs'_ne] by metis

    have lhs_simp:
      "(cvc_list_left and (ListVar xs_w) (cvc_list_right and (word_cat z y::'c word) (ListVar ws_w))::'c word)
     = and (word_cat z y::'c word) T"
    proof -
      have R: "cvc_list_right and (word_cat z y::'c word) (ListVar ws_w)
             = foldr and (word_cat z y # butlast ws_w) (last ws_w)"
        using cvc_list_right_transfer_2[OF ws'_ne, of "and" "word_cat z y"] by metis
      have R': "cvc_list_right and (word_cat z y::'c word) (ListVar ws_w)
              = and (word_cat z y) (foldr and (butlast ws_w) (last ws_w))"
        using R by simp
      have L: "cvc_list_left and (ListVar xs_w) (cvc_list_right and (word_cat z y::'c word) (ListVar ws_w))
            = foldr and xs_w (cvc_list_right and (word_cat z y::'c word) (ListVar ws_w))"
        using cvc_list_left_transfer by metis
      show ?thesis
        unfolding L R' T_def
        by (metis R' L foldr_word_and_pullout)
    qed

    show ?thesis
      unfolding both_eq ext_hi ext_lo lhs_simp
      by (rule lemma1_inst)
  qed
qed

lemma rewrite_bv_and_concat_pullup_todo [rewrite_bv_and_concat_pullup]:
  fixes z::"'a::len word" and y::"'b::len word"
    and xs::"('c::len word) cvc_ListVar" and ws::"('c::len word) cvc_ListVar"
    and nxm1::int  and ys::"('d::len word) cvc_ListVar" and ny::int and nym1::int
  shows
"NO_MATCH cvc_a (undefined xs ws y z ys nxm1 ny nym1)
 \<Longrightarrow> xs \<noteq> ListVar []
 \<Longrightarrow> ws \<noteq> ListVar []
 \<Longrightarrow> ny = int LENGTH('b)
 \<Longrightarrow> nxm1 = int LENGTH('c) - 1
 \<Longrightarrow> nym1 = int LENGTH('b) - 1
 \<Longrightarrow> LENGTH('b) + LENGTH('a) = LENGTH('c)
 \<Longrightarrow> (cvc_list_left and xs (cvc_list_right and (word_cat z y::'c::len word) ws)::'c word)
  = (word_cat
       (and (smtlib_extract nxm1 ny (cvc_list_both' and xs ws::'c::len word)::'a::len word) z::'a word)
       (and (smtlib_extract nym1 0 (cvc_list_both' and xs ws::'c::len word)::'b::len word) y::'b word)
     ::'c word)"
proof -
  assume "NO_MATCH cvc_a (undefined xs ws y z ys nxm1 ny nym1)"
  assume xs_ne: "xs \<noteq> ListVar []"
  assume ws_ne: "ws \<noteq> ListVar []"
  assume ny_eq: "ny = int LENGTH('b)"
  assume nxm1_eq: "nxm1 = int LENGTH('c) - 1"
  assume nym1_eq: "nym1 = int LENGTH('b) - 1"
  assume LEN: "LENGTH('b) + LENGTH('a) = LENGTH('c)"

  obtain xs' where xs_def: "xs = ListVar xs'" and xs'_ne: "xs' \<noteq> []"
    using xs_ne by (cases xs) auto
  obtain ws' where ws_def: "ws = ListVar ws'" and ws'_ne: "ws' \<noteq> []"
    using ws_ne by (cases ws) auto

  define T :: "'c word"
    where "T = foldr and xs' (foldr and (butlast ws') (last ws'))"

  have both_eq: "(cvc_list_both' and xs ws::'c word) = T"
    unfolding T_def using cvc_list_both_transfer'[OF ws'_ne xs'_ne] xs_def ws_def by metis

  have ext_hi:
    "(smtlib_extract nxm1 ny T::'a word) = (smt_extract (LENGTH('c) - 1) LENGTH('b) T::'a word)"
    using nxm1_eq ny_eq len_gt_0[where 'a='c]
    by (simp add: smtlib_extract_def smt_extract_def Suc_diff_1 nat_diff_distrib)
  have ext_lo:
    "(smtlib_extract nym1 0 T::'b word) = (smt_extract (LENGTH('b) - 1) (nat 0) T::'b word)"
    using nym1_eq len_gt_0[where 'a='b]
    by (simp add: smtlib_extract_def smt_extract_def Suc_diff_1 nat_diff_distrib)

  have lhs_simp:
    "(cvc_list_left and xs (cvc_list_right and (word_cat z y::'c word) ws)::'c word)
   = and (word_cat z y::'c word) T"
  proof -
    have R: "cvc_list_right and (word_cat z y::'c word) ws
           = foldr and (word_cat z y # butlast ws') (last ws')"
      using cvc_list_right_transfer_2[OF ws'_ne, of "and" "word_cat z y"] ws_def by metis
    have R': "cvc_list_right and (word_cat z y::'c word) ws
            = and (word_cat z y) (foldr and (butlast ws') (last ws'))"
      using R by simp
    have L: "cvc_list_left and xs (cvc_list_right and (word_cat z y::'c word) ws)
          = foldr and xs' (cvc_list_right and (word_cat z y::'c word) ws)"
      using cvc_list_left_transfer xs_def by metis
    show ?thesis
      unfolding L R' T_def
      by (metis R' L foldr_word_and_pullout)
  qed

  have lemma1_inst:
    "and (word_cat z y::'c word) T
   = (word_cat
       (and (smt_extract (LENGTH('c) - 1) LENGTH('b) T::'a word) z::'a word)
       (and (smt_extract (LENGTH('b) - 1) (nat 0) T::'b word) y::'b word)
     ::'c word)"
    by (rule rewrite_bv_and_concat_pullup_lemma1[OF LEN[symmetric]])

  show "(cvc_list_left and xs (cvc_list_right and (word_cat z y::'c word) ws)::'c word)
      = (word_cat
           (and (smtlib_extract nxm1 ny (cvc_list_both' and xs ws::'c word)::'a word) z::'a word)
           (and (smtlib_extract nym1 0 (cvc_list_both' and xs ws::'c word)::'b word) y::'b word)
         ::'c word)"
    unfolding both_eq ext_hi ext_lo lhs_simp
    by (rule lemma1_inst)
qed
(*
xs empty, ys empty, length ws > 1:

(define-cond-rule bv-and-concat-pullup_v1
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (ys ?BitVec :list)
   (nxm1 Int) (ny Int) (nym1 Int))
  (def
    (nx (@bvsize (bvand [] ws)))
  )
  (and (= ny (@bvsize y)) (= nxm1 (- nx 1)) (= nym1 (- (@bvsize y) 1)))
  (bvand (concat z y) ws)
  (concat
    (bvand (extract nxm1 ny (bvand ws)) z)
    (bvand (extract nym1 0 (bvand ws)))
  ))

*)









(* Goal: "rare_rewrite"
       assumptions:
         (7::int) = int (size 0)
         (7::int) = int (size (word_cat 1 0)) - 1
         (6::int) = int (size 0) - 1
       arguments:
         ''bv-and-concat-pullup''
         ListVar []
         ListVar [b::8 word, d::8 word]
         0
         1
         ListVar []
         7::int
         7::int
         6::int
       proposition:
         and (and (word_cat 1 0) (b::8 word)) (d::8 word) =
         word_cat (and (smtlib_extract (7::int) (7::int) (and b d)) 1) (and (smtlib_extract (6::int) 0 (and b d)) 0) *)


(*
(define-cond-rule bv-or-concat-pullup
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (ys ?BitVec :list)
   (nxm1 Int) (ny Int) (nym1 Int))
  (def
    (nx (@bvsize (bvor xs ws)))
  )
  (and (= ny (@bvsize y)) (= nxm1 (- nx 1)) (= nym1 (- (@bvsize y) 1)))
  (bvor xs (concat ys z y) ws)
  (concat
    (bvor (extract nxm1 ny (bvor xs ws)) (concat ys z))
    (bvor (extract nym1 0 (bvor xs ws)) y)
  ))
*)

(*
(define-cond-rule bv-xor-concat-pullup
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (ys ?BitVec :list)
   (nxm1 Int) (ny Int) (nym1 Int))
  (def
    (nx (@bvsize (bvxor xs ws)))
  )
  (and (= ny (@bvsize y)) (= nxm1 (- nx 1)) (= nym1 (- (@bvsize y) 1)))
  (bvxor xs (concat ys z y) ws)
  (concat
    (bvxor (extract nxm1 ny (bvxor xs ws)) (concat ys z))
    (bvxor (extract nym1 0 (bvxor xs ws)) y)
  ))
*)

named_theorems rewrite_bv_xor_concat_pullup \<open>automatically_generated\<close>


(*
(define-cond-rule bv-xor-concat-pullup
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (ys ?BitVec :list)
   )
  (bvxor xs (concat ys (concat z y)) ws)
  (concat
    (bvxor (extract (- (@bvsize (bvxor xs ws)) 1) (@bvsize y) (bvxor xs ws)) (concat ys z))
    (bvxor (extract (- (@bvsize y) 1) 0 (bvxor xs ws)) y)
  ))

*)


(*(define-cond-rule bv-xor-concat-pullup
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (ys ?BitVec :list)
   (nxm1 Int) (ny Int) (nym1 Int))
  (def
    (nx (@bvsize (bvxor xs ws)))
  )
  (and (= ny (@bvsize y)) (= nxm1 (- nx 1)) (= nym1 (- (@bvsize y) 1)))
  (bvxor xs (concat ys z y) ws)
  (concat
    (bvxor (extract nxm1 ny (bvxor xs ws)) (concat ys z))
    (bvxor (extract nym1 0 (bvxor xs ws)) y)
  ))*)



(*
(define-cond-rule bv-and-concat-pullup2
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (ys ?BitVec :list)
   (nxm1 Int) (ny Int) (nym1 Int))
  (def
    (s (@bvsize (bvand xs ws)))
    (sy (@bvsize (concat y ys)))
  )
  (and (= ny sy) (= nxm1 (- s 1)) (= nym1 (- sy 1)))
  (bvand xs (concat z y ys) ws)
  (concat
    (bvand (extract nxm1 ny (bvand xs ws)) z)
    (bvand (extract nym1 0 (bvand xs ws)) (concat y ys))
  ))
*)

(*
(define-cond-rule bv-or-concat-pullup2
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (ys ?BitVec :list)
   (nxm1 Int) (ny Int) (nym1 Int))
  (def
    (s (@bvsize (bvor xs ws)))
    (sy (@bvsize (concat y ys)))
  )
  (and (= ny sy) (= nxm1 (- s 1)) (= nym1 (- sy 1)))
  (bvor xs (concat z y ys) ws)
  (concat
    (bvor (extract nxm1 ny (bvor xs ws)) z)
    (bvor (extract nym1 0 (bvor xs ws)) (concat y ys))
  ))
*)


(*
(define-cond-rule bv-xor-concat-pullup2
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (ys ?BitVec :list)
   (nxm1 Int) (ny Int) (nym1 Int))
  (def
    (s (@bvsize (bvxor xs ws)))
    (sy (@bvsize (concat y ys)))
  )
  (and (= ny sy) (= nxm1 (- s 1)) (= nym1 (- sy 1)))
  (bvxor xs (concat z y ys) ws)
  (concat
    (bvxor (extract nxm1 ny (bvxor xs ws)) z)
    (bvxor (extract nym1 0 (bvxor xs ws)) (concat y ys))
  ))
*)



(*
(define-cond-rule bv-and-concat-pullup3
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (u ?BitVec)
   (nxm1 Int) (nyu Int) (nyum1 Int) (nu Int) (num1 Int))
  (def
    (s (@bvsize (bvand xs ws)))
    (su (@bvsize u))
    (sy (@bvsize y))
  )
  (and (= nxm1 (- s 1)) (= nyu (+ sy su)) (= nyum1 (- (+ sy su) 1)) (= nu su) (= num1 (- su 1)))
  (bvand xs (concat z y u) ws)
  (concat
    (bvand (extract nxm1 nyu (bvand xs ws)) z)
    (bvand (extract nyum1 nu (bvand xs ws)) y)
    (bvand (extract num1 0 (bvand xs ws)) u)
  ))
*)


(*
(define-cond-rule bv-or-concat-pullup3
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (u ?BitVec)
   (nxm1 Int) (nyu Int) (nyum1 Int) (nu Int) (num1 Int))
  (def
    (s (@bvsize (bvor xs ws)))
    (su (@bvsize u))
    (sy (@bvsize y))
  )
  (and (= nxm1 (- s 1)) (= nyu (+ sy su)) (= nyum1 (- (+ sy su) 1)) (= nu su) (= num1 (- su 1)))
  (bvor xs (concat z y u) ws)
  (concat
    (bvor (extract nxm1 nyu (bvor xs ws)) z)
    (bvor (extract nyum1 nu (bvor xs ws)) y)
    (bvor (extract num1 0 (bvor xs ws)) u)
  ))
*)

(*
(define-cond-rule bv-xor-concat-pullup3
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (u ?BitVec)
   (nxm1 Int) (nyu Int) (nyum1 Int) (nu Int) (num1 Int))
  (def
    (s (@bvsize (bvxor xs ws)))
    (su (@bvsize u))
    (sy (@bvsize y))
  )
  (and (= nxm1 (- s 1)) (= nyu (+ sy su)) (= nyum1 (- (+ sy su) 1)) (= nu su) (= num1 (- su 1)))
  (bvxor xs (concat z y u) ws)
  (concat
    (bvxor (extract nxm1 nyu (bvxor xs ws)) z)
    (bvxor (extract nyum1 nu (bvxor xs ws)) y)
    (bvxor (extract num1 0 (bvxor xs ws)) u)
  ))
*)


(*
(define-cond-rule bv-xor-duplicate ((x ?BitVec) (w Int))
  (= w (@bvsize x))
  (bvxor x x) 
  (@bv 0 w))

Note: Constraint LENGTH('a) = w is not needed so omitted
*)

named_theorems rewrite_bv_xor_duplicate \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_duplicate]:
  fixes x::"'a ::len word" and w::int
  shows "NO_MATCH cvc_a (undefined x w) \<Longrightarrow>
 semiring_bit_operations_class.xor x x = 0"
  by auto


(*
(define-cond-rule bv-xor-ones ((xs ?BitVec :list) (zs ?BitVec :list) (n Int) (w Int))
  (= n (- (int.pow2 w) 1))
  (bvxor xs (@bv n w) zs)
  (bvnot (bvxor xs zs)))

Simplified (without commutativity): 
(define-cond-rule bv-xor-ones ((w Int) (x ?BitVec))
  (= w (size x))
  (bvxor (@bv (- (int.pow2 w) 1) w) x)
  (bvnot x))


*)

named_theorems rewrite_bv_xor_ones \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_ones]:
  fixes xs::"('a ::len word) cvc_ListVar" and zs::"('a ::len word) cvc_ListVar" and n::int and w::int
  shows "NO_MATCH cvc_a (undefined xs zs n w) 
    \<Longrightarrow> n = int (2 ^ (nat w)) - 1 \<Longrightarrow> w = LENGTH('a) \<Longrightarrow> \<not>(xs = ListVar [] \<and> zs = ListVar [])
    \<Longrightarrow> o1 = (Word.Word n::'a::len word) \<Longrightarrow>
  (cvc_list_left xor xs (cvc_list_right xor o1 zs))
 = not (cvc_list_both xor (Word.Word 0) xs zs)"
  apply (cases xs)
  subgoal for xs'
    apply (cases zs)
    subgoal for zs'
      apply (simp only: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
      apply simp_all
      by (simp add: rewrite_bv_xor_ones_lemma)
    done
  done
      
      

(*
(define-rule bv-xor-not ((x ?BitVec) (y ?BitVec))
  (bvxor (bvnot x) (bvnot y)) (bvxor x y))
*)


named_theorems rewrite_bv_xor_not \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_not]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> semiring_bit_operations_class.xor (not x) (not y) =
   semiring_bit_operations_class.xor x y"
  by auto

(*
(define-rule bv-not-idemp ((x ?BitVec))
  (bvnot (bvnot x)) x)
*)

named_theorems rewrite_bv_not_idemp \<open>automatically_generated\<close>

lemma [rewrite_bv_not_idemp]:
  fixes x::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> not (not x) = x"
  by auto


(*
(define-rule bv-ult-zero-1
  ((x ?BitVec) (n Int))
  (bvult (@bv 0 n) x)
  (not (= x (@bv 0 n))))

Note: Constraint LENGTH('a) = w is not needed so omitted
*)

named_theorems rewrite_bv_ult_zero_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_1]:
  fixes x::"'a ::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (0 < x) = (x \<noteq> 0)"
  using word_neq_0_conv by auto

(*
(define-rule bv-ult-zero-2
  ((x ?BitVec) (n Int))
  (bvult x (@bv 0 n))
  false)

Note: Constraint LENGTH('a) = w is not needed so omitted

*)

named_theorems rewrite_bv_ult_zero_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_2]:
  fixes x::"'a ::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow> (x < 0) = False"
  by auto

(*
(define-rule bv-ult-self ((x ?BitVec)) (bvult x x) false)
*)

named_theorems rewrite_bv_ult_self \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_self]:
  fixes x::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x < x) = False"
  by auto

(*
(define-rule bv-lt-self ((x ?BitVec)) (bvslt x x) false)
*)

named_theorems rewrite_bv_lt_self \<open>automatically_generated\<close>

lemma [rewrite_bv_lt_self]:
  fixes x::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x <s x) = False"
  by auto

(*
(define-rule bv-ule-self ((x ?BitVec)) (bvule x x) true)
*)


named_theorems rewrite_bv_ule_self \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_self]:
  fixes x::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<le> x) = True"
  by auto


(*
(define-rule bv-ule-zero
  ((x ?BitVec) (n Int))
  (bvule x (@bv 0 n))
  (= x (@bv 0 n)))

Note: Constraint LENGTH('a) = w is not needed so omitted

*)

named_theorems rewrite_bv_ule_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_zero]:
  fixes x::"'a ::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) 
    \<Longrightarrow> (x \<le> 0) = (x = 0)"
  by auto

(*
(define-rule bv-zero-ule
  ((x ?BitVec) (n Int))
  (bvule (@bv 0 n) x)
  true)

Note: Constraint LENGTH('a) = w is not needed so omitted

*)

named_theorems rewrite_bv_zero_ule \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ule]:
  fixes x::"'a ::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) 
    \<Longrightarrow> (0  \<le> x) = True"
  by auto


(*
(define-rule bv-sle-self ((x ?BitVec)) (bvsle x x) true)
*)


named_theorems rewrite_bv_sle_self \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_self]:
  fixes x::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (x \<le>s x) = True"
  by auto

(*
(define-cond-rule bv-ule-max ((x ?BitVec) (n Int) (w Int))
  (and (= w (@bvsize x)) (= n (- (int.pow2 (@bvsize x)) 1)))
  (bvule x (@bv n w)) true)
*)

named_theorems rewrite_bv_ule_max \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_max]:
  fixes x::"'a ::len word" and n::int and w::int
  shows
 "NO_MATCH cvc_a (undefined x n w) \<Longrightarrow>

  w = int (size x) \<Longrightarrow>
  n = int ((2::nat) ^ nat (int (size x))) - 1 \<Longrightarrow>

  n_w = Word.Word n \<Longrightarrow>
  (x \<le> n_w) = True"
  by (simp add: word_size)

(*
(define-rule bv-not-ult ((x ?BitVec) (y ?BitVec))
  (not (bvult x y))
  (bvule y x))
*)


named_theorems rewrite_bv_not_ult \<open>automatically_generated\<close>

lemma [rewrite_bv_not_ult]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> (\<not> x < y) = (y \<le> x)"
  by auto


(*
(define-cond-rule bv-mult-pow2-1
  ((xs ?BitVec :list) (ys ?BitVec :list) (z ?BitVec) (size Int) (n Int) (exponent Int) (u Int))
  (and (int.ispow2 n) (= exponent (int.log2 n)) (= u (- (- size (int.log2 n)) 1)))
  (bvmul xs z (@bv n size) ys)
  (concat
    (extract u 0 (bvmul xs z ys))
    (@bv 0 exponent)))

*)
named_theorems rewrite_bv_mult_pow2_1 \<open>manually generated\<close>

lemma [rewrite_bv_mult_pow2_1]:
  fixes xs ys :: "'b::len word cvc_ListVar"
    and z :: "'b::len word"
    and exponent size u n :: int
  shows "NO_MATCH (cvc_a) (undefined xs ys z size n exponent u)

    \<Longrightarrow> is_pow2 n = True
    \<Longrightarrow> exponent = int (floorlog 2 (nat n) - 1)
    \<Longrightarrow> u = size - int (floorlog 2 (nat n) - 1) - 1

    \<Longrightarrow> (n_w::'b::len word) = Word.Word n
    \<Longrightarrow> LENGTH('a) + LENGTH('c) = LENGTH('b)
    \<Longrightarrow> LENGTH('c) = u + 1 \<Longrightarrow> u \<ge> 0
    \<Longrightarrow> exponent = int (LENGTH('a))
    \<Longrightarrow>
(cvc_list_left (*) xs (z * (cvc_list_right (*) n_w ys ::'b::len word)))
   = (word_cat (smtlib_extract u 0 (cvc_list_left (*) xs (cvc_list_right (*) z ys))::'c::len word) (0::'a::len word))"
proof -
  assume pow: "is_pow2 n = True"
     and exp_eq: "exponent = int (floorlog 2 (nat n) - 1)"
     and u_eq: "u = size - int (floorlog 2 (nat n) - 1) - 1"
     and nw_eq: "(n_w::'b::len word) = Word.Word n"
     and la: "LENGTH('a) + LENGTH('c) = LENGTH('b)"
     and lc: "LENGTH('c) = u + 1" and uge0: "u \<ge>0"
     and ea: "exponent = int (LENGTH('a))"

  from pow have n_pos: "0 < n"
    unfolding is_pow2_def by auto

  define k where k_def: "k = LENGTH('a)"
  have fl_eq: "floorlog 2 (nat n) - 1 = k"
    using exp_eq ea k_def by simp
 
  have n_is_pow: "n = 2 ^ k"
    using pow unfolding is_pow2_def using k_def word_size
    by (metis fl_eq is_pow2_imp_eq_2_pow pow)

  have nw_pow: "n_w = (2 :: 'b word) ^ k"
  proof -
    have "n_w = word_of_int (2 ^ k)" using nw_eq n_is_pow by simp
    thus ?thesis by (simp add: word_of_int_2p)
  qed

  let ?w = "cvc_list_left (*) xs (cvc_list_right (*) z ys) :: 'b word"

  have lhs_collapse:
    "cvc_list_left (*) xs (z * cvc_list_right (*) n_w ys :: 'b word) = ?w * n_w"
  proof -
    obtain xs' where xs_eq: "xs = ListVar xs'" by (cases xs)
    obtain ys' where ys_eq: "ys = ListVar ys'" by (cases ys)
    show ?thesis
    proof (cases "ys' = []")
      case True
      have step: "cvc_bin_op_fold (*) xs' (z * n_w :: 'b word)
                 = cvc_bin_op_fold (*) xs' z * n_w"
        by (induct xs') (simp_all add: ac_simps)
      show ?thesis
        unfolding xs_eq ys_eq cvc_list_left_def cvc_list_right_def
        using True step by simp
    next
      case False
      define Y where "Y = cvc_nary_op_fold ((*) :: 'b word \<Rightarrow> 'b word \<Rightarrow> 'b word) ys'"
      have step: "cvc_bin_op_fold (*) xs' (z * (n_w * Y))
                 = cvc_bin_op_fold (*) xs' (z * Y) * n_w"
        by (induct xs') (simp_all add: ac_simps)
      show ?thesis
        unfolding xs_eq ys_eq cvc_list_left_def cvc_list_right_def Y_def
        using False step
        using False local.step Y_def by simp
    qed
  qed

  have shifted: "?w * n_w = push_bit k ?w"
    unfolding nw_pow by (simp add: push_bit_eq_mult)

  have u_nonneg: "0 \<le> u" using lc len_gt_0[where 'a='c] by linarith
  have lc_nat: "LENGTH('c) = nat u + 1" using lc u_nonneg by (simp add: nat_add_distrib)

  have cat_eq:
    "push_bit k ?w = word_cat (smtlib_extract u 0 ?w :: 'c word) (0 :: 'a word)"
  proof (rule bit_word_eqI)
    fix m :: nat assume m_lt: "m < LENGTH('b)"
    show "bit (push_bit k ?w) m =
          bit (word_cat (smtlib_extract u 0 ?w :: 'c word) (0 :: 'a word) :: 'b word) m"
    proof (cases "m < LENGTH('a)")
      case True
      hence "\<not> bit (push_bit k ?w) m"
        using k_def by (simp add: bit_push_bit_iff)
      moreover have "\<not> bit (word_cat (smtlib_extract u 0 ?w :: 'c word) (0 :: 'a word) :: 'b word) m"
        using True m_lt by (simp add: bit_word_cat_iff)
      ultimately show ?thesis by simp
    next
      case False
      hence m_ge: "LENGTH('a) \<le> m" by linarith
      let ?j = "m - LENGTH('a)"
      have j_lt_c: "?j < LENGTH('c)" using m_lt m_ge la by linarith
      have j_lt_u1: "?j < nat (u + 1)" using j_lt_c lc uge0
        by (simp add: nat_add_distrib)
      have "bit (push_bit k ?w) m = bit ?w ?j"
        using m_ge m_lt k_def by (simp add: bit_push_bit_iff)
      moreover have "bit (word_cat (smtlib_extract u 0 ?w :: 'c word) (0 :: 'a word) :: 'b word) m
                    = bit (smtlib_extract u 0 ?w :: 'c word) ?j"
        using False m_lt by (simp add: bit_word_cat_iff)
      moreover have "bit (smtlib_extract u 0 ?w :: 'c word) ?j = bit ?w ?j"
        unfolding smtlib_extract_def
        using j_lt_c j_lt_u1 la
        by (simp add: bit_slice_iff bit_take_bit_iff)
      ultimately show ?thesis by simp
    qed
  qed

  show "cvc_list_left (*) xs (z * cvc_list_right (*) n_w ys :: 'b word)
      = word_cat (smtlib_extract u 0 (cvc_list_left (*) xs (cvc_list_right (*) z ys)) :: 'c word) (0 :: 'a word)"
    using lhs_collapse shifted cat_eq by simp
qed



(*
(define-cond-rule bv-mult-pow2-2
  ((xs ?BitVec :list) (ys ?BitVec :list) (z ?BitVec) (size Int) (n Int) (exponent Int) (u Int))
  (def (ns (- (int.pow2 size) n)) (e (int.log2 ns)))
  (and (int.ispow2 ns) (= exponent e) (= u (- (- size e) 1)))
  (bvmul xs z (@bv n size) ys)
  (concat
    (extract u 0 (bvneg (bvmul xs z ys)))
    (@bv 0 exponent)))
*)
named_theorems rewrite_bv_mult_pow2_2 \<open>manually generated\<close>

lemma [rewrite_bv_mult_pow2_2]:
  fixes xs ys :: "'b::len word cvc_ListVar"
    and z :: "'b::len word"
    and exponent size u n :: int
  shows "NO_MATCH (cvc_a) (undefined xs ys z size n exponent u)

    \<Longrightarrow> is_pow2 (2 ^ nat size - n) = True
    \<Longrightarrow> exponent = int (floorlog 2 (nat (2 ^ nat size - n)) - 1)
    \<Longrightarrow> u = size - int (floorlog 2 (nat (2 ^ nat size - n)) - 1) - 1

    \<Longrightarrow> (n_w::'b::len word) = Word.Word n
    \<Longrightarrow> LENGTH('a) + LENGTH('c) = LENGTH('b)
    \<Longrightarrow> int LENGTH('c) = u + 1 \<Longrightarrow> u \<ge> 0
    \<Longrightarrow> exponent = int (LENGTH('a))
    \<Longrightarrow>
(cvc_list_left (*) xs (z * (cvc_list_right (*) n_w ys ::'b::len word)))
   = (word_cat
        (smtlib_extract u 0 (- (cvc_list_left (*) xs (cvc_list_right (*) z ys)))::'c::len word)
        (0::'a::len word))"
proof -
  assume pow: "is_pow2 (2 ^ nat size - n) = True"
     and exp_eq: "exponent = int (floorlog 2 (nat (2 ^ nat size - n)) - 1)"
     and u_eq: "u = size - int (floorlog 2 (nat (2 ^ nat size - n)) - 1) - 1"
     and nw_eq: "(n_w::'b::len word) = Word.Word n"
     and la: "LENGTH('a) + LENGTH('c) = LENGTH('b)"
     and lc: "int LENGTH('c) = u + 1" and uge0: "u \<ge> 0"
     and ea: "exponent = int (LENGTH('a))"

  define k where k_def: "k = LENGTH('a)"
  have fl_eq: "floorlog 2 (nat (2 ^ nat size - n)) - 1 = k"
    using exp_eq ea k_def by simp

  have ns_pow: "(2::int) ^ nat size - n = 2 ^ k"
    by (metis fl_eq is_pow2_imp_eq_2_pow pow)

  have len_b_int: "int LENGTH('b) = size"
    using la lc u_eq ea exp_eq by linarith
  have len_b: "LENGTH('b) = nat size"
    using len_b_int by simp

  have n_alt: "n = (2::int) ^ nat size - 2 ^ k"
    using ns_pow by simp

  have nw_pow: "n_w = - ((2 :: 'b word) ^ k)"
  proof -
    have "n_w = of_int ((2::int) ^ nat size - 2 ^ k)"
      using nw_eq n_alt by simp
    also have "\<dots> = (of_int ((2::int) ^ nat size) :: 'b word) - of_int (2 ^ k)"
      by simp
    also have "(of_int ((2::int) ^ nat size) :: 'b word) = (2 :: 'b word) ^ nat size"
      by simp
    also have "(2 :: 'b word) ^ nat size = 0"
      using len_b by simp
    also have "(of_int ((2::int) ^ k) :: 'b word) = (2 :: 'b word) ^ k"
      by simp
    finally show ?thesis by simp
  qed

  let ?w = "cvc_list_left (*) xs (cvc_list_right (*) z ys) :: 'b word"

  have lhs_collapse:
    "cvc_list_left (*) xs (z * cvc_list_right (*) n_w ys :: 'b word) = ?w * n_w"
  proof -
    obtain xs' where xs_eq: "xs = ListVar xs'" by (cases xs)
    obtain ys' where ys_eq: "ys = ListVar ys'" by (cases ys)
    show ?thesis
    proof (cases "ys' = []")
      case True
      have step: "cvc_bin_op_fold (*) xs' (z * n_w :: 'b word)
                 = cvc_bin_op_fold (*) xs' z * n_w"
        by (induct xs') (simp_all add: ac_simps)
      show ?thesis
        unfolding xs_eq ys_eq cvc_list_left_def cvc_list_right_def
        using True step by simp
    next
      case False
      define Y where "Y = cvc_nary_op_fold ((*) :: 'b word \<Rightarrow> 'b word \<Rightarrow> 'b word) ys'"
      have step: "cvc_bin_op_fold (*) xs' (z * (n_w * Y))
                 = cvc_bin_op_fold (*) xs' (z * Y) * n_w"
        by (induct xs') (simp_all add: ac_simps)
      show ?thesis
        unfolding xs_eq ys_eq cvc_list_left_def cvc_list_right_def Y_def
        using False step
        by (simp add: Y_def)
    qed
  qed

  have neg_shifted: "?w * n_w = push_bit k (- ?w)"
  proof -
    have "?w * n_w = ?w * (- ((2 :: 'b word) ^ k))" using nw_pow by simp
    also have "\<dots> = - (?w * (2 :: 'b word) ^ k)" by simp
    also have "\<dots> = - push_bit k ?w" by (simp add: push_bit_eq_mult)
    also have "\<dots> = push_bit k (- ?w)" by (simp add: push_bit_minus)
    finally show ?thesis .
  qed

  have cat_eq:
    "push_bit k (- ?w) = word_cat (smtlib_extract u 0 (- ?w) :: 'c word) (0 :: 'a word)"
  proof (rule bit_word_eqI)
    fix m :: nat assume m_lt: "m < LENGTH('b)"
    show "bit (push_bit k (- ?w)) m =
          bit (word_cat (smtlib_extract u 0 (- ?w) :: 'c word) (0 :: 'a word) :: 'b word) m"
    proof (cases "m < LENGTH('a)")
      case True
      hence "\<not> bit (push_bit k (- ?w)) m"
        using k_def by (simp add: bit_push_bit_iff)
      moreover have "\<not> bit (word_cat (smtlib_extract u 0 (- ?w) :: 'c word) (0 :: 'a word) :: 'b word) m"
        using True m_lt by (simp add: bit_word_cat_iff)
      ultimately show ?thesis by simp
    next
      case False
      hence m_ge: "LENGTH('a) \<le> m" by linarith
      let ?j = "m - LENGTH('a)"
      have j_lt_c: "?j < LENGTH('c)" using m_lt m_ge la by linarith
      have j_lt_u1: "?j < nat (u + 1)" using j_lt_c lc uge0
        by (simp add: nat_add_distrib)
      have "bit (push_bit k (- ?w)) m = bit (- ?w) ?j"
        using m_ge m_lt k_def by (simp add: bit_push_bit_iff)
      moreover have "bit (word_cat (smtlib_extract u 0 (- ?w) :: 'c word) (0 :: 'a word) :: 'b word) m
                    = bit (smtlib_extract u 0 (- ?w) :: 'c word) ?j"
        using False m_lt by (simp add: bit_word_cat_iff)
      moreover have "bit (smtlib_extract u 0 (- ?w) :: 'c word) ?j = bit (- ?w) ?j"
        unfolding smtlib_extract_def
        using j_lt_c j_lt_u1 la
        by (simp add: bit_slice_iff bit_take_bit_iff)
      ultimately show ?thesis by simp
    qed
  qed

  show "cvc_list_left (*) xs (z * cvc_list_right (*) n_w ys :: 'b word)
      = word_cat (smtlib_extract u 0 (- (cvc_list_left (*) xs (cvc_list_right (*) z ys))) :: 'c word) (0 :: 'a word)"
    using lhs_collapse neg_shifted cat_eq by simp
qed


(*
(define-cond-rule bv-mult-pow2-2b
  ((z ?BitVec) (size Int) (n Int) (exponent Int) (u Int))
  (def (ns (- (int.pow2 size) n)) (e (int.log2 ns)))
  (and (int.ispow2 ns) (= exponent e) (= u (- (- size e) 1)))
  (bvmul z (@bv n size))
  (concat
    (extract u 0 (bvneg z))
    (@bv 0 exponent)))
*)
named_theorems rewrite_bv_mult_pow2_2b \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_pow2_2b]:
  fixes z::"'a::len word" and size n exponent u::int
  shows "NO_MATCH (cvc_a) (undefined z size n exponent u)
    \<Longrightarrow>
is_pow2 (int ((2::nat) ^ nat size) - n) = True \<Longrightarrow>
         exponent = int (floorlog (2::nat) (nat (int ((2::nat) ^ nat size) - n)) - 1) \<Longrightarrow>
        u = size - int (floorlog (2::nat) (nat (int ((2::nat) ^ nat size) - n)) - 1) - 1 \<Longrightarrow>
  n_w = Word.Word n \<Longrightarrow>
  LENGTH('b) = u + 1 \<Longrightarrow> u \<ge> 0 \<Longrightarrow>
  LENGTH('c) = exponent \<Longrightarrow>
  LENGTH('a) = size \<Longrightarrow>
  LENGTH('a) = LENGTH('b) + LENGTH('c) \<Longrightarrow>
  (z * n_w) = (word_cat (smtlib_extract u 0 (-z)::'b::len word) (0::'c::len word))
"
proof -
  assume pow: "is_pow2 (int ((2::nat) ^ nat size) - n) = True"
     and exp_eq: "exponent = int (floorlog (2::nat) (nat (int ((2::nat) ^ nat size) - n)) - 1)"
     and u_eq: "u = size - int (floorlog (2::nat) (nat (int ((2::nat) ^ nat size) - n)) - 1) - 1"
     and nw_eq: "n_w = Word.Word n"
     and lb: "LENGTH('b) = u + 1"
     and uge0: "u \<ge> 0"
     and lc: "LENGTH('c) = exponent"
     and la: "LENGTH('a) = size"
     and labc: "LENGTH('a) = LENGTH('b) + LENGTH('c)"

  define k where k_def: "k = LENGTH('c)"
  have fl_eq: "floorlog (2::nat) (nat (int ((2::nat) ^ nat size) - n)) - 1 = k"
    using exp_eq lc k_def by simp

  have ns_pow: "int ((2::nat) ^ nat size) - n = 2 ^ k"
    using is_pow2_imp_eq_2_pow fl_eq pow by blast

  have len_a: "LENGTH('a) = nat size"
    using la by simp

  have n_alt: "n = int ((2::nat) ^ nat size) - 2 ^ k"
    using ns_pow by simp

  have nw_pow: "n_w = - ((2 :: 'a word) ^ k)"
  proof -
    have "n_w = of_int (int ((2::nat) ^ nat size) - 2 ^ k)"
      using nw_eq n_alt by simp
    also have "\<dots> = (of_int (int ((2::nat) ^ nat size)) :: 'a word) - of_int (2 ^ k)"
      by simp
    also have "(of_int (int ((2::nat) ^ nat size)) :: 'a word) = (2 :: 'a word) ^ nat size"
      by simp
    also have "(2 :: 'a word) ^ nat size = 0"
      using len_a by simp
    also have "(of_int ((2::int) ^ k) :: 'a word) = (2 :: 'a word) ^ k"
      by simp
    finally show ?thesis by simp
  qed

  have neg_shifted: "z * n_w = push_bit k (- z)"
  proof -
    have "z * n_w = z * (- ((2 :: 'a word) ^ k))" using nw_pow by simp
    also have "\<dots> = - (z * (2 :: 'a word) ^ k)" by simp
    also have "\<dots> = - push_bit k z" by (simp add: push_bit_eq_mult)
    also have "\<dots> = push_bit k (- z)" by (simp add: push_bit_minus)
    finally show ?thesis .
  qed

  have cat_eq:
    "push_bit k (- z) = word_cat (smtlib_extract u 0 (- z) :: 'b word) (0 :: 'c word)"
  proof (rule bit_word_eqI)
    fix m :: nat assume m_lt: "m < LENGTH('a)"
    show "bit (push_bit k (- z)) m =
          bit (word_cat (smtlib_extract u 0 (- z) :: 'b word) (0 :: 'c word) :: 'a word) m"
    proof (cases "m < LENGTH('c)")
      case True
      hence "\<not> bit (push_bit k (- z)) m"
        using k_def by (simp add: bit_push_bit_iff)
      moreover have "\<not> bit (word_cat (smtlib_extract u 0 (- z) :: 'b word) (0 :: 'c word) :: 'a word) m"
        using True m_lt by (simp add: bit_word_cat_iff)
      ultimately show ?thesis by simp
    next
      case False
      hence m_ge: "LENGTH('c) \<le> m" by linarith
      let ?j = "m - LENGTH('c)"
      have j_lt_b: "?j < LENGTH('b)" using m_lt m_ge labc by linarith
      have j_lt_u1: "?j < nat (u + 1)" using j_lt_b lb uge0
        by (simp add: nat_add_distrib)
      have "bit (push_bit k (- z)) m = bit (- z) ?j"
        using m_ge m_lt k_def by (simp add: bit_push_bit_iff)
      moreover have "bit (word_cat (smtlib_extract u 0 (- z) :: 'b word) (0 :: 'c word) :: 'a word) m
                    = bit (smtlib_extract u 0 (- z) :: 'b word) ?j"
        using False m_lt by (simp add: bit_word_cat_iff)
      moreover have "bit (smtlib_extract u 0 (- z) :: 'b word) ?j = bit (- z) ?j"
        unfolding smtlib_extract_def
        using j_lt_b j_lt_u1 labc
        by (simp add: bit_slice_iff bit_take_bit_iff)
      ultimately show ?thesis by simp
    qed
  qed

  show "(z * n_w) = (word_cat (smtlib_extract u 0 (-z)::'b::len word) (0::'c::len word))"
    using neg_shifted cat_eq by simp
qed

(*
(define-cond-rule bv-extract-mult-leading-bit
  (
    (high Int) (low Int)
    (x1i Int) (x1in Int) (x2 ?BitVec)
    (y1i Int) (y1in Int) (y2 ?BitVec)
    (w Int)
  )
  (def
    (n (+ x1in (@bvsize x2)))
    (x0n (ite (= x1i 0) x1in (- x1in (+ 1 (int.log2 x1i)))))
    (y0n (ite (= y1i 0) y1in (- y1in (+ 1 (int.log2 y1i)))))
  )
  (and (> n 64) (<= (- (\* 2 n) (+ x0n y0n)) low) (= w (+ 1 (- high low))))
  (extract high low (bvmul
    (concat (@bv x1i x1in) x2)
    (concat (@bv y1i y1in) y2)))
  (@bv 0 w))
*)
named_theorems rewrite_bv_extract_mult_leading_bit \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_mult_leading_bit]:
  fixes high low x1i x1in ::int and x2::"'a::len word" and y1i y1in ::int and y2::"'b::len word"
    and w::int
  shows "NO_MATCH (cvc_a) (undefined high low x1i x1in x2 y1i y1in y2 w)
    \<Longrightarrow>
    (x1in + int (size x2)) > 64 \<Longrightarrow>
    ((2 * (x1in + int (size x2))) -
      ((if x1i = 0 then x1in else x1in - (1 + int (floorlog (2::nat) (nat x1i) - 1)))
     + (if y1i = 0 then y1in else y1in - (1 + int (floorlog (2::nat) (nat y1i) - 1))))) \<le> low \<Longrightarrow>
    w = 1 + (high - low) \<Longrightarrow>
LENGTH('e) = LENGTH('c) + LENGTH('a) \<Longrightarrow> LENGTH('e) = LENGTH('d) + LENGTH('b) \<Longrightarrow>
    (x1i_w::'c::len word) = Word.Word x1i \<Longrightarrow> LENGTH('c) = x1in \<Longrightarrow>
    (y1i_w::'d::len word) = Word.Word y1i \<Longrightarrow> LENGTH('d) = y1in \<Longrightarrow>
    LENGTH('f) = w \<Longrightarrow> high \<ge> low \<Longrightarrow> low \<ge> 0 \<Longrightarrow>
    0 \<le> x1i \<Longrightarrow> 0 \<le> y1i \<Longrightarrow>
    (smtlib_extract high low ((word_cat x1i_w x2::'e::len word) * (word_cat y1i_w y2))::'f::len word)
    = 0"
  unfolding smtlib_extract_def
  apply simp
  apply (rule bit_word_eqI)
  apply (simp add: nth_slice semiring_bit_operations_class.bit_take_bit_iff bit_word_cat_iff)
  apply (rule impI)
  apply (cases " x1i = 0")
   apply simp_all
   apply (case_tac [!] "y1i = 0")
     apply simp_all
proof goal_cases
  case (1 n)
  then have ba: "x1in + (2 * int (size x2) - y1in) \<le> low"
    and lcd_lab: "LENGTH('d) + LENGTH('b) = LENGTH('c) + LENGTH('a)"
    and le_eq: "LENGTH('e) = LENGTH('c) + LENGTH('a)"
    and lc: "int LENGTH('c) = x1in"
    and ld: "int LENGTH('d) = y1in"
    and l_pos: "0 \<le> low"
    by auto

  have le_a: "LENGTH('a) \<le> LENGTH('e)" using le_eq by simp
  have le_b: "LENGTH('b) \<le> LENGTH('e)" using lcd_lab le_eq by simp

  have ab_le_low: "LENGTH('a) + LENGTH('b) \<le> nat low"
  proof -
    have "int LENGTH('c) + 2 * int LENGTH('a) - int LENGTH('d) \<le> low"
      using ba lc ld by (simp add: word_size)
    moreover have "int (LENGTH('a) + LENGTH('b))
                 = int LENGTH('c) + 2 * int LENGTH('a) - int LENGTH('d)"
      using lcd_lab by linarith
    ultimately have "int (LENGTH('a) + LENGTH('b)) \<le> low" by linarith
    thus ?thesis using l_pos by linarith
  qed

  have unat_x_eq: "unat (ucast x2 :: 'e word) = unat x2"
    using le_a by (simp add: is_up.rep_eq source_size target_size unat_ucast_upcast)
  have unat_y_eq: "unat (ucast y2 :: 'e word) = unat y2"
    using le_b by (simp add: is_up.rep_eq source_size target_size unat_ucast_upcast)

  have prod_lt: "unat x2 * unat y2 < 2 ^ nat low"
  proof -
    have "unat x2 * unat y2 < 2 ^ LENGTH('a) * 2 ^ LENGTH('b)"
      apply (intro mult_strict_mono) by simp_all
    also have "\<dots> = 2 ^ (LENGTH('a) + LENGTH('b))"
      by (simp add: power_add)
    also have "\<dots> \<le> (2 ^ nat low :: nat)"
      using ab_le_low by simp
    finally show ?thesis .
  qed

  have unat_prod: "unat ((ucast x2 :: 'e word) * ucast y2) < 2 ^ nat low"
  proof -
    have "unat ((ucast x2 :: 'e word) * ucast y2)
        = (unat x2 * unat y2) mod 2 ^ LENGTH('e)"
      using unat_x_eq unat_y_eq
      by (simp add: unat_word_ariths(2))
    also have "\<dots> \<le> unat x2 * unat y2" by simp
    finally show ?thesis using prod_lt by linarith
  qed

  show "\<not> bit ((ucast x2 :: 'e word) * ucast y2) (n + nat low)"
  proof -
    have lt: "unat ((ucast x2 :: 'e word) * ucast y2) < 2 ^ (n + nat low)"
      using unat_prod
      by (meson less_le_trans nat_zero_less_power_iff one_le_numeral
                power_increasing le_add_same_cancel2 zero_le)
    hence "(unat ((ucast x2 :: 'e word) * ucast y2)) div 2 ^ (n + nat low) = 0"
      by simp
    hence not_bit_unat: "\<not> bit (unat ((ucast x2 :: 'e word) * ucast y2)) (n + nat low)"
      by (simp add: bit_iff_odd_drop_bit drop_bit_eq_div)
    show ?thesis
      using bit_unsigned_iff not_bit_unat possible_bit_nat by blast
    qed
next
  case (2 n)
  then have ba: "x1in + (2 * int (size x2) - (y1in - (1 + int (floorlog 2 (nat y1i) - Suc 0)))) \<le> low"
    and lcd_lab: "LENGTH('d) + LENGTH('b) = LENGTH('c) + LENGTH('a)"
    and le_eq: "LENGTH('e) = LENGTH('c) + LENGTH('a)"
    and lc: "int LENGTH('c) = x1in"
    and ld: "int LENGTH('d) = y1in"
    and l_pos: "0 \<le> low"
    and y_pos: "0 \<le> y1i"
    and y_ne: "y1i \<noteq> 0"
    by auto

  have le_a: "LENGTH('a) \<le> LENGTH('e)" using le_eq by simp
  have le_b: "LENGTH('b) \<le> LENGTH('e)" using lcd_lab le_eq by simp
  have le_db: "LENGTH('e) = LENGTH('d) + LENGTH('b)" using le_eq lcd_lab by simp

  have ny_gt: "0 < nat y1i" using y_pos y_ne by linarith
  have fy_pos: "0 < floorlog 2 (nat y1i)"
    using ny_gt by (simp add: floorlog_def)
  have fy_int: "int (floorlog 2 (nat y1i) - Suc 0) = int (floorlog 2 (nat y1i)) - 1"
    using fy_pos by simp
  have y_lt: "nat y1i < 2 ^ floorlog 2 (nat y1i)"
    using floorlog_bounds[of "nat y1i" 2] ny_gt by simp

  have unat_y1iw_lt: "unat (word_of_int y1i :: 'd word) < 2 ^ floorlog 2 (nat y1i)"
  proof -
    have "unat (word_of_int y1i :: 'd word) = nat (y1i mod 2 ^ LENGTH('d))"
      by (simp add: uint_word_of_int unat_eq_nat_uint)
    also have "\<dots> \<le> nat y1i"
      using y_pos
      using nat_le_eq_zle zmod_le_nonneg_dividend by presburger
    finally show ?thesis using y_lt by linarith
  qed

  have unat_x_eq: "unat (ucast x2 :: 'e word) = unat x2"
    using le_a by (simp add: is_up.rep_eq source_size target_size unat_ucast_upcast)

  have unat_wc_lt: "unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)
                  < 2 ^ (floorlog 2 (nat y1i) + LENGTH('b))"
  proof -
    have wc_eq: "unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)
               = unat (word_of_int y1i :: 'd word) * 2 ^ LENGTH('b) + unat y2"
      using le_db
      by (simp add: push_bit_eq_mult unat_word_cat)
    have y2_lt: "unat y2 < 2 ^ LENGTH('b)" by simp
    have y1iw_le: "unat (word_of_int y1i :: 'd word) + 1 \<le> 2 ^ floorlog 2 (nat y1i)"
      using unat_y1iw_lt by simp
    have "unat (word_of_int y1i :: 'd word) * 2 ^ LENGTH('b) + unat y2
        < unat (word_of_int y1i :: 'd word) * 2 ^ LENGTH('b) + 2 ^ LENGTH('b)"
      using y2_lt by simp
    also have "\<dots> = (unat (word_of_int y1i :: 'd word) + 1) * 2 ^ LENGTH('b)"
      by simp
    also have "\<dots> \<le> 2 ^ floorlog 2 (nat y1i) * 2 ^ LENGTH('b)"
      using y1iw_le by (intro mult_right_mono) auto
    finally show ?thesis using wc_eq by (simp add: power_add)
  qed

  have ab_fy_le_low: "LENGTH('a) + LENGTH('b) + floorlog 2 (nat y1i) \<le> nat low"
  proof -
    have "x1in + 2 * int (size x2) - y1in + int (floorlog 2 (nat y1i)) \<le> low"
      using ba fy_int by linarith
    hence "int LENGTH('c) + 2 * int LENGTH('a) - int LENGTH('d) + int (floorlog 2 (nat y1i)) \<le> low"
      using lc ld by (simp add: word_size)
    moreover have "int (LENGTH('a) + LENGTH('b) + floorlog 2 (nat y1i))
                 = int LENGTH('c) + 2 * int LENGTH('a) - int LENGTH('d) + int (floorlog 2 (nat y1i))"
      using lcd_lab by linarith
    ultimately have "int (LENGTH('a) + LENGTH('b) + floorlog 2 (nat y1i)) \<le> low" by linarith
    thus ?thesis using l_pos by linarith
  qed

  have prod_lt: "unat x2 * unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word) < 2 ^ nat low"
  proof -
    have "unat x2 * unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)
        < 2 ^ LENGTH('a) * 2 ^ (floorlog 2 (nat y1i) + LENGTH('b))"
      by (simp add: mult_strict_mono' unat_wc_lt)
    also have "\<dots> = 2 ^ (LENGTH('a) + LENGTH('b) + floorlog 2 (nat y1i))"
      by (simp add: power_add add.commute add.left_commute)
    also have "\<dots> \<le> (2 :: nat) ^ nat low"
      using ab_fy_le_low by simp
    finally show ?thesis .
  qed

  have unat_prod: "unat ((ucast x2 :: 'e word) * (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word))
                  < 2 ^ nat low"
  proof -
    have "unat ((ucast x2 :: 'e word) * (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word))
        = (unat (ucast x2 :: 'e word) * unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word))
          mod 2 ^ LENGTH('e)"
      by (simp add: unat_word_ariths(2))
    also have "\<dots> \<le> unat (ucast x2 :: 'e word) * unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)"
      by simp
    also have "\<dots> = unat x2 * unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)"
      using unat_x_eq by simp
    finally show ?thesis using prod_lt by linarith
  qed

  show "\<not> bit ((ucast x2 :: 'e word) * (word_cat (word_of_int y1i :: 'd word) y2)) (n + nat low)"
  proof -
    have lt: "unat ((ucast x2 :: 'e word) * (word_cat (word_of_int y1i :: 'd word) y2))
            < 2 ^ (n + nat low)"
      using unat_prod
      by (meson less_le_trans nat_zero_less_power_iff one_le_numeral
                power_increasing le_add_same_cancel2 zero_le)
    hence "(unat ((ucast x2 :: 'e word) * (word_cat (word_of_int y1i :: 'd word) y2)))
            div 2 ^ (n + nat low) = 0"
      by simp
    hence not_bit_unat: "\<not> bit (unat ((ucast x2 :: 'e word)
                                       * (word_cat (word_of_int y1i :: 'd word) y2))) (n + nat low)"
      by (simp add: bit_iff_odd_drop_bit drop_bit_eq_div)
    show ?thesis
      using bit_unsigned_iff not_bit_unat possible_bit_nat by blast
  qed
next
  case (3 n)
  then have ba: "x1in + (2 * int (size x2) + (1 + (int (floorlog 2 (nat x1i) - Suc 0) - y1in))) \<le> low"
    and lcd_lab: "LENGTH('d) + LENGTH('b) = LENGTH('c) + LENGTH('a)"
    and le_eq: "LENGTH('e) = LENGTH('c) + LENGTH('a)"
    and lc: "int LENGTH('c) = x1in"
    and ld: "int LENGTH('d) = y1in"
    and l_pos: "0 \<le> low"
    and x_pos: "0 \<le> x1i"
    and x_ne: "x1i \<noteq> 0"
    by auto

  have le_a: "LENGTH('a) \<le> LENGTH('e)" using le_eq by simp
  have le_b: "LENGTH('b) \<le> LENGTH('e)" using lcd_lab le_eq by simp
  have le_ca: "LENGTH('e) = LENGTH('c) + LENGTH('a)" using le_eq .

  have nx_gt: "0 < nat x1i" using x_pos x_ne by linarith
  have fx_pos: "0 < floorlog 2 (nat x1i)"
    using nx_gt by (simp add: floorlog_def)
  have fx_int: "int (floorlog 2 (nat x1i) - Suc 0) = int (floorlog 2 (nat x1i)) - 1"
    using fx_pos by simp
  have x_lt: "nat x1i < 2 ^ floorlog 2 (nat x1i)"
    using floorlog_bounds[of "nat x1i" 2] nx_gt by simp

  have unat_x1iw_lt: "unat (word_of_int x1i :: 'c word) < 2 ^ floorlog 2 (nat x1i)"
  proof -
    have "unat (word_of_int x1i :: 'c word) = nat (x1i mod 2 ^ LENGTH('c))"
      by (simp add: int_word_uint unat_eq_nat_uint)
    also have "\<dots> \<le> nat x1i"
      using x_pos
      using nat_mono zmod_le_nonneg_dividend by presburger

    finally show ?thesis using x_lt by linarith
  qed

  have unat_y_eq: "unat (ucast y2 :: 'e word) = unat y2"
    using le_b by (simp add: is_up.rep_eq source_size target_size unat_ucast_upcast)

  have unat_wc_lt: "unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
                  < 2 ^ (floorlog 2 (nat x1i) + LENGTH('a))"
  proof -
    have wc_eq: "unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
               = unat (word_of_int x1i :: 'c word) * 2 ^ LENGTH('a) + unat x2"
      using le_ca
      by (simp add: push_bit_eq_mult unat_word_cat)
    have x2_lt: "unat x2 < 2 ^ LENGTH('a)" by simp
    have x1iw_le: "unat (word_of_int x1i :: 'c word) + 1 \<le> 2 ^ floorlog 2 (nat x1i)"
      using unat_x1iw_lt by simp
    have "unat (word_of_int x1i :: 'c word) * 2 ^ LENGTH('a) + unat x2
        < unat (word_of_int x1i :: 'c word) * 2 ^ LENGTH('a) + 2 ^ LENGTH('a)"
      using x2_lt by simp
    also have "\<dots> = (unat (word_of_int x1i :: 'c word) + 1) * 2 ^ LENGTH('a)"
      by simp
    also have "\<dots> \<le> 2 ^ floorlog 2 (nat x1i) * 2 ^ LENGTH('a)"
      using x1iw_le by (intro mult_right_mono) auto
    finally show ?thesis using wc_eq by (simp add: power_add)
  qed

  have ab_fx_le_low: "LENGTH('a) + LENGTH('b) + floorlog 2 (nat x1i) \<le> nat low"
  proof -
    have "x1in + 2 * int (size x2) - y1in + int (floorlog 2 (nat x1i)) \<le> low"
      using ba fx_int by linarith
    hence "int LENGTH('c) + 2 * int LENGTH('a) - int LENGTH('d) + int (floorlog 2 (nat x1i)) \<le> low"
      using lc ld by (simp add: word_size)
    moreover have "int (LENGTH('a) + LENGTH('b) + floorlog 2 (nat x1i))
                 = int LENGTH('c) + 2 * int LENGTH('a) - int LENGTH('d) + int (floorlog 2 (nat x1i))"
      using lcd_lab by linarith
    ultimately have "int (LENGTH('a) + LENGTH('b) + floorlog 2 (nat x1i)) \<le> low" by linarith
    thus ?thesis using l_pos by linarith
  qed

  have prod_lt: "unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word) * unat y2 < 2 ^ nat low"
  proof -
    have "unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word) * unat y2
        < 2 ^ (floorlog 2 (nat x1i) + LENGTH('a)) * 2 ^ LENGTH('b)"
      using unat_wc_lt
      using mult_strict_mono' by blast
    also have "\<dots> = 2 ^ (LENGTH('a) + LENGTH('b) + floorlog 2 (nat x1i))"
      by (simp add: power_add add.commute add.left_commute)
    also have "\<dots> \<le> (2 :: nat) ^ nat low"
      using ab_fx_le_low by simp
    finally show ?thesis .
  qed

  have unat_prod: "unat ((word_cat (word_of_int x1i :: 'c word) x2 :: 'e word) * (ucast y2 :: 'e word))
                  < 2 ^ nat low"
  proof -
    have "unat ((word_cat (word_of_int x1i :: 'c word) x2 :: 'e word) * (ucast y2 :: 'e word))
        = (unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word) * unat (ucast y2 :: 'e word))
          mod 2 ^ LENGTH('e)"
      by (simp add: unat_word_ariths(2))
    also have "\<dots> \<le> unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word) * unat (ucast y2 :: 'e word)"
      by simp
    also have "\<dots> = unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word) * unat y2"
      using unat_y_eq by simp
    finally show ?thesis using prod_lt by linarith
  qed

  show "\<not> bit ((word_cat (word_of_int x1i :: 'c word) x2 :: 'e word) * ucast y2) (n + nat low)"
  proof -
    have lt: "unat ((word_cat (word_of_int x1i :: 'c word) x2 :: 'e word) * ucast y2)
            < 2 ^ (n + nat low)"
      using unat_prod
      by (meson less_le_trans nat_zero_less_power_iff one_le_numeral
                power_increasing le_add_same_cancel2 zero_le)
    hence "(unat ((word_cat (word_of_int x1i :: 'c word) x2 :: 'e word) * ucast y2))
            div 2 ^ (n + nat low) = 0"
      by simp
    hence not_bit_unat: "\<not> bit (unat ((word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
                                       * ucast y2)) (n + nat low)"
      by (simp add: bit_iff_odd_drop_bit drop_bit_eq_div)
    show ?thesis
      using bit_unsigned_iff not_bit_unat possible_bit_nat by blast
  qed
next
  case (4 n)
  then have ba: "x1in + (2 * int (size x2)
                          + ((2::int) + (int (floorlog 2 (nat x1i) - Suc 0)
                                       + (int (floorlog 2 (nat y1i) - Suc 0) - y1in)))) \<le> low"
    and lcd_lab: "LENGTH('d) + LENGTH('b) = LENGTH('c) + LENGTH('a)"
    and le_eq: "LENGTH('e) = LENGTH('c) + LENGTH('a)"
    and lc: "int LENGTH('c) = x1in"
    and ld: "int LENGTH('d) = y1in"
    and l_pos: "0 \<le> low"
    and x_pos: "0 \<le> x1i" and x_ne: "x1i \<noteq> 0"
    and y_pos: "0 \<le> y1i" and y_ne: "y1i \<noteq> 0"
    by auto

  have le_a: "LENGTH('a) \<le> LENGTH('e)" using le_eq by simp
  have le_b: "LENGTH('b) \<le> LENGTH('e)" using lcd_lab le_eq by simp
  have le_db: "LENGTH('e) = LENGTH('d) + LENGTH('b)" using le_eq lcd_lab by simp
  have le_ca: "LENGTH('e) = LENGTH('c) + LENGTH('a)" using le_eq .

  have nx_gt: "0 < nat x1i" using x_pos x_ne by linarith
  have ny_gt: "0 < nat y1i" using y_pos y_ne by linarith
  have fx_pos: "0 < floorlog 2 (nat x1i)" using nx_gt by (simp add: floorlog_def)
  have fy_pos: "0 < floorlog 2 (nat y1i)" using ny_gt by (simp add: floorlog_def)
  have fx_int: "int (floorlog 2 (nat x1i) - Suc 0) = int (floorlog 2 (nat x1i)) - 1"
    using fx_pos by simp
  have fy_int: "int (floorlog 2 (nat y1i) - Suc 0) = int (floorlog 2 (nat y1i)) - 1"
    using fy_pos by simp
  have x_lt: "nat x1i < 2 ^ floorlog 2 (nat x1i)"
    using floorlog_bounds[of "nat x1i" 2] nx_gt by simp
  have y_lt: "nat y1i < 2 ^ floorlog 2 (nat y1i)"
    using floorlog_bounds[of "nat y1i" 2] ny_gt by simp

  have unat_x1iw_lt: "unat (word_of_int x1i :: 'c word) < 2 ^ floorlog 2 (nat x1i)"
  proof -
    have "unat (word_of_int x1i :: 'c word) = nat (x1i mod 2 ^ LENGTH('c))"
      by (simp add: uint_word_of_int unat_eq_nat_uint)
    also have "\<dots> \<le> nat x1i" using x_pos
      by (metis x_pos nat_mono zmod_le_nonneg_dividend)
    finally show ?thesis using x_lt by linarith
  qed
  have unat_y1iw_lt: "unat (word_of_int y1i :: 'd word) < 2 ^ floorlog 2 (nat y1i)"
  proof -
    have "unat (word_of_int y1i :: 'd word) = nat (y1i mod 2 ^ LENGTH('d))"
      by (metis uint_word_of_int unat_eq_nat_uint)
      also have "\<dots> \<le> nat y1i" using y_pos
        by (metis y_pos zmod_le_nonneg_dividend nat_mono)
    finally show ?thesis using y_lt by linarith
  qed

  have unat_wcx_lt: "unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
                   < 2 ^ (floorlog 2 (nat x1i) + LENGTH('a))"
  proof -
    have wc_eq: "unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
               = unat (word_of_int x1i :: 'c word) * 2 ^ LENGTH('a) + unat x2"
      using le_ca
      by (metis le_eq push_bit_eq_mult unat_word_cat)
    have x2_lt: "unat x2 < 2 ^ LENGTH('a)" by simp
    have x1iw_le: "unat (word_of_int x1i :: 'c word) + 1 \<le> 2 ^ floorlog 2 (nat x1i)"
      using unat_x1iw_lt by simp
    have "unat (word_of_int x1i :: 'c word) * 2 ^ LENGTH('a) + unat x2
        < unat (word_of_int x1i :: 'c word) * 2 ^ LENGTH('a) + 2 ^ LENGTH('a)"
      using x2_lt by simp
    also have "\<dots> = (unat (word_of_int x1i :: 'c word) + 1) * 2 ^ LENGTH('a)"
      by simp
    also have "\<dots> \<le> 2 ^ floorlog 2 (nat x1i) * 2 ^ LENGTH('a)"
      using x1iw_le by (intro mult_right_mono) auto
    finally show ?thesis using wc_eq by (simp add: power_add)
  qed
  have unat_wcy_lt: "unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)
                   < 2 ^ (floorlog 2 (nat y1i) + LENGTH('b))"
  proof -
    have wc_eq: "unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)
               = unat (word_of_int y1i :: 'd word) * 2 ^ LENGTH('b) + unat y2"
      using le_db
      by (metis le_db push_bit_eq_mult unat_word_cat)
    have y2_lt: "unat y2 < 2 ^ LENGTH('b)" by simp
    have y1iw_le: "unat (word_of_int y1i :: 'd word) + 1 \<le> 2 ^ floorlog 2 (nat y1i)"
      using unat_y1iw_lt by simp
    have "unat (word_of_int y1i :: 'd word) * 2 ^ LENGTH('b) + unat y2
        < unat (word_of_int y1i :: 'd word) * 2 ^ LENGTH('b) + 2 ^ LENGTH('b)"
      using y2_lt by simp
    also have "\<dots> = (unat (word_of_int y1i :: 'd word) + 1) * 2 ^ LENGTH('b)"
      by simp
    also have "\<dots> \<le> 2 ^ floorlog 2 (nat y1i) * 2 ^ LENGTH('b)"
      using y1iw_le by (intro mult_right_mono) auto
    finally show ?thesis using wc_eq by (simp add: power_add)
  qed

  have abf_le_low: "LENGTH('a) + LENGTH('b) + floorlog 2 (nat x1i) + floorlog 2 (nat y1i) \<le> nat low"
  proof -
    have "x1in + 2 * int (size x2) - y1in
            + int (floorlog 2 (nat x1i)) + int (floorlog 2 (nat y1i)) \<le> low"
      using ba fx_int fy_int by linarith
    hence "int LENGTH('c) + 2 * int LENGTH('a) - int LENGTH('d)
              + int (floorlog 2 (nat x1i)) + int (floorlog 2 (nat y1i)) \<le> low"
      using lc ld by (simp add: word_size)
    moreover have "int (LENGTH('a) + LENGTH('b) + floorlog 2 (nat x1i) + floorlog 2 (nat y1i))
                 = int LENGTH('c) + 2 * int LENGTH('a) - int LENGTH('d)
                     + int (floorlog 2 (nat x1i)) + int (floorlog 2 (nat y1i))"
      using lcd_lab by linarith
    ultimately have "int (LENGTH('a) + LENGTH('b) + floorlog 2 (nat x1i) + floorlog 2 (nat y1i)) \<le> low"
      by linarith
    thus ?thesis using l_pos by linarith
  qed

  have prod_lt: "unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
              * unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word) < 2 ^ nat low"
  proof -
    have "unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
        * unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)
        < 2 ^ (floorlog 2 (nat x1i) + LENGTH('a)) * 2 ^ (floorlog 2 (nat y1i) + LENGTH('b))"
      using unat_wcx_lt unat_wcy_lt by (intro mult_strict_mono) auto
    also have "\<dots> = 2 ^ (LENGTH('a) + LENGTH('b) + floorlog 2 (nat x1i) + floorlog 2 (nat y1i))"
      by (simp add: power_add add.commute add.left_commute)
    also have "\<dots> \<le> (2 :: nat) ^ nat low"
      using abf_le_low by simp
    finally show ?thesis .
  qed

  have unat_prod: "unat ((word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
                       * (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)) < 2 ^ nat low"
  proof -
    have "unat ((word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
              * (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word))
        = (unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
         * unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)) mod 2 ^ LENGTH('e)"
      by (simp add: unat_word_ariths(2))
    also have "\<dots> \<le> unat (word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
                * unat (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)" by simp
    finally show ?thesis using prod_lt by linarith
  qed

  show "\<not> bit ((word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
              * (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)) (n + nat low)"
  proof -
    have lt: "unat ((word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
                  * (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word))
            < 2 ^ (n + nat low)"
      using unat_prod
      by (meson less_le_trans nat_zero_less_power_iff one_le_numeral
                power_increasing le_add_same_cancel2 zero_le)
    hence "(unat ((word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
                * (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)))
            div 2 ^ (n + nat low) = 0"
      by simp
    hence not_bit_unat: "\<not> bit (unat ((word_cat (word_of_int x1i :: 'c word) x2 :: 'e word)
                                     * (word_cat (word_of_int y1i :: 'd word) y2 :: 'e word)))
                          (n + nat low)"
      by (simp add: bit_iff_odd_drop_bit drop_bit_eq_div)
    show ?thesis
      using bit_unsigned_iff not_bit_unat possible_bit_nat by blast
  qed
qed

(*
(define-cond-rule bv-udiv-pow2-not-one
  ((x ?BitVec) (v Int) (n Int) (power Int) (nm1 Int))
  (and (int.ispow2 v) (> v 1) (= power (int.log2 v)) (= nm1 (- n 1)))
  (bvudiv x (@bv v n))
  (concat (@bv 0 power) (extract nm1 power x)))
*)



named_theorems rewrite_bv_udiv_pow2_not_one \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_not_one]:
 fixes x::"'a ::len word" and v n power nm1 ::int
 shows "NO_MATCH (cvc_a) (undefined x v n power nm1) \<Longrightarrow>
 v_w = Word.Word v \<Longrightarrow>
 n = LENGTH('a) \<Longrightarrow>

 LENGTH('a) = LENGTH('b) + LENGTH('c) \<Longrightarrow>
 LENGTH('c) = nm1 - power + 1 \<Longrightarrow> nm1 \<ge> power \<Longrightarrow> power \<ge> 0 \<Longrightarrow>

 is_pow2 v \<Longrightarrow>
  v > 1 \<Longrightarrow> power = int (floorlog (2::nat) (nat v) - 1) \<Longrightarrow> nm1 = n - 1 \<Longrightarrow>

 LENGTH('b) = power \<Longrightarrow>
 smt_udiv x v_w = (word_cat (0::'b::len word) (smtlib_extract nm1 power x::'c::len word))"
proof -
  assume vw_eq: "v_w = Word.Word v"
     and n_eq: "n = LENGTH('a)"
     and la: "LENGTH('a) = LENGTH('b) + LENGTH('c)"
     and lc: "LENGTH('c) = nm1 - power + 1"
     and power_nn: "power \<ge> 0"
     and pow: "is_pow2 v"
     and vgt: "v > 1"
     and power_def: "power = int (floorlog (2::nat) (nat v) - 1)"
     and nm1_eq: "nm1 = n - 1"
     and lb_eq: "LENGTH('b) = power"

  define k where k_def: "k = floorlog 2 (nat v) - 1"

  have power_k: "power = int k"
    using power_def k_def by simp

  have v_pow: "v = 2 ^ k"
    using is_pow2_imp_eq_2_pow[OF pow] k_def by simp

  have k_pos: "1 \<le> k"
  proof (rule ccontr)
    assume "\<not> 1 \<le> k"
    hence "k = 0" by simp
    hence "v = 1" using v_pow by simp
    with vgt show False by simp
  qed

  have lb_eq_k: "LENGTH('b) = k"
    using lb_eq power_k by simp

  have lc_eq_nk: "LENGTH('c) = LENGTH('a) - k"
  proof -
    have "int LENGTH('c) = int LENGTH('a) - int k"
      using lc nm1_eq n_eq power_k by linarith
    thus ?thesis by linarith
  qed

  have k_lt_n: "k < LENGTH('a)"
  proof -
    have "0 < LENGTH('c)" by simp
    thus ?thesis using lc_eq_nk by linarith
  qed

  have v_w_pow: "v_w = (2::'a word) ^ k"
  proof -
    have "v_w = (Word.Word (2 ^ k) :: 'a word)" using vw_eq v_pow by simp
    also have "\<dots> = word_of_int (2 ^ k)" by simp
    also have "\<dots> = ((2::'a word) ^ k)" by (rule word_of_int_2p)
    finally show ?thesis .
  qed

  have vw_neq_0: "(v_w::'a word) \<noteq> 0"
    using v_w_pow k_lt_n by simp

  have udiv_eq: "smt_udiv x v_w = drop_bit k x"
  proof -
    have "unat (v_w::'a word) \<noteq> 0"
      using vw_neq_0 by (simp add: unsigned_eq_0_iff)
    hence "smt_udiv x v_w = x div v_w"
      unfolding smt_udiv_def by simp
    also have "\<dots> = x div ((2::'a word) ^ k)" using v_w_pow by simp
    also have "\<dots> = drop_bit k x" by (simp add: drop_bit_eq_div)
    finally show ?thesis .
  qed

  have ext_slice: "(smtlib_extract nm1 power x :: 'c word) = slice k x"
  proof -
    have "nat power = k" using power_k by simp
    moreover have "nat (nm1 + 1) = LENGTH('a)"
      using nm1_eq n_eq by simp
    moreover have "take_bit LENGTH('a) (x :: 'a word) = x"
      by simp
    ultimately show ?thesis
      unfolding smtlib_extract_def by simp
  qed

  have cat_eq: "drop_bit k x = word_cat (0::'b word) (smtlib_extract nm1 power x :: 'c word)"
  proof (rule bit_word_eqI)
    fix m :: nat assume m_lt: "m < LENGTH('a)"
    show "bit (drop_bit k x :: 'a word) m =
          bit (word_cat (0::'b word) (smtlib_extract nm1 power x :: 'c word) :: 'a word) m"
    proof (cases "m < LENGTH('c)")
      case True
      hence m_plus: "m + k < LENGTH('a)"
        using lc_eq_nk by linarith
      have lhs: "bit (drop_bit k x :: 'a word) m \<longleftrightarrow> bit x (m + k)"
        by (simp add: bit_drop_bit_eq add.commute)
      have ext_bit: "bit (smtlib_extract nm1 power x :: 'c word) m \<longleftrightarrow> bit x (m + k)"
        unfolding ext_slice
        using True m_plus
        by (simp add: bit_slice_iff lc_eq_nk)
      have cat_bit: "bit (word_cat (0::'b word) (smtlib_extract nm1 power x :: 'c word) :: 'a word) m
                   \<longleftrightarrow> bit (smtlib_extract nm1 power x :: 'c word) m"
        using True m_lt apply (simp add: bit_word_cat_iff)
        by (metis nth_ucast_weak)
      show ?thesis using lhs ext_bit cat_bit by simp
    next
      case False
      hence m_ge: "LENGTH('c) \<le> m" by simp
      hence "LENGTH('a) \<le> m + k" using lc_eq_nk by linarith
      hence "\<not> bit (x::'a word) (m + k)"
        
        using \<open>LENGTH('a::len) \<le> (m::nat) + (k::nat)\<close> bit_imp_le_length by fastforce
      hence lhs: "\<not> bit (drop_bit k x :: 'a word) m"
        by (simp add: bit_drop_bit_eq add.commute)
      have "bit (word_cat (0::'b word) (smtlib_extract nm1 power x :: 'c word) :: 'a word) m
          \<longleftrightarrow> bit (0::'b word) (m - LENGTH('c))"
        using m_ge m_lt apply (simp add: bit_word_cat_iff)
        by (metis bit_word_ucast_iff False)
      hence "\<not> bit (word_cat (0::'b word) (smtlib_extract nm1 power x :: 'c word) :: 'a word) m"
        by simp
      thus ?thesis using lhs by simp
    qed
  qed

  show "smt_udiv x v_w = word_cat (0::'b word) (smtlib_extract nm1 power x :: 'c word)"
    using udiv_eq cat_eq by simp
qed

(*
(define-rule bv-udiv-zero
  ((x ?BitVec) (n Int))
  (bvudiv x (@bv 0 n))
  (bvnot (@bv 0 n)))

Note: Constraint LENGTH('a) = n is not needed so omitted
 smt_udiv (x::5 word) 0 = not 0 
*)

named_theorems rewrite_bv_udiv_zero \<open>automatically_generated\<close>

(*This is an example where Isabelle and SMTLIB semantics are completely different*)

lemma [rewrite_bv_udiv_zero]:
  fixes x::"'a ::len word" and n::int
  shows "NO_MATCH (cvc_a) (undefined x n)
 \<Longrightarrow> smt_udiv x 0 = not 0"
  unfolding smt_udiv_def
  apply (simp add: unat_0) 
  by (simp add: size_word.rep_eq)


(*
(define-rule bv-udiv-one ((x ?BitVec) (n Int))
  (bvudiv x (@bv 1 n))
  x)

Note: Constraint LENGTH('a) = n is not needed so omitted

*)


named_theorems rewrite_bv_udiv_one \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_one]:
  fixes x::"'a ::len word" and n::int
  shows "NO_MATCH (cvc_a) (undefined x n) \<Longrightarrow> smt_udiv x 1 = x"
  unfolding smt_udiv_def by simp


(*
(define-cond-rule bv-urem-pow2-not-one
  ((x ?BitVec) (v Int) (n Int) (nmp Int) (pm1 Int))
  (def (power (int.log2 v)))
  (and (int.ispow2 v) (> v 1) (= nmp (- n power)) (= pm1 (- power 1)))
  (bvurem x (@bv v n))
  (concat (@bv 0 nmp) (extract pm1 0 x)))

*)

named_theorems rewrite_bv_urem_pow2_not_one \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_pow2_not_one]:
 fixes x::"'a ::len word" and v n nmp pm1 ::int
 shows "NO_MATCH (cvc_a) (undefined x v n nmp pm1) \<Longrightarrow>
 v_w = Word.Word v \<Longrightarrow>
 n = LENGTH('a) \<Longrightarrow>
 nmp = LENGTH('b) \<Longrightarrow>
 LENGTH('a) = LENGTH('b) + LENGTH('c) \<Longrightarrow>
 LENGTH('c) = pm1 + 1 \<Longrightarrow> pm1 \<ge> 0 \<Longrightarrow>

 is_pow2 v \<Longrightarrow>
  v > 1 \<Longrightarrow> nmp = n - int (floorlog (2::nat) (nat v) - 1) \<Longrightarrow> pm1 = int (floorlog (2::nat) (nat x1i) - 1) - 1 \<Longrightarrow>
 smt_urem x v_w = (word_cat (0::'b::len word) (smtlib_extract pm1 0 x::'c::len word))"
proof -
  assume vw_eq: "v_w = Word.Word v"
     and n_eq: "n = LENGTH('a)"
     and nmp_eq: "nmp = LENGTH('b)"
     and la: "LENGTH('a) = LENGTH('b) + LENGTH('c)"
     and lc: "LENGTH('c) = pm1 + 1"
     and pm1_nn: "pm1 \<ge> 0"
     and pow: "is_pow2 v"
     and vgt: "v > 1"
     and nmp_def: "nmp = n - int (floorlog (2::nat) (nat v) - 1)"

  define k where k_def: "k = floorlog 2 (nat v) - 1"

  have v_pow: "v = 2 ^ k"
    using is_pow2_imp_eq_2_pow[OF pow] k_def by simp

  have k_pos: "1 \<le> k"
  proof (rule ccontr)
    assume "\<not> 1 \<le> k"
    hence "k = 0" by simp
    hence "v = 1" using v_pow by simp
    with vgt show False by simp
  qed

  have nmp_eq_k: "nmp = int LENGTH('a) - int k"
    using nmp_def n_eq k_def by simp

  have lc_eq_k: "LENGTH('c) = k"
  proof -
    from la have "int LENGTH('a) = int LENGTH('b) + int LENGTH('c)" by linarith
    hence "int LENGTH('c) = int LENGTH('a) - int LENGTH('b)" by simp
    also have "\<dots> = int LENGTH('a) - nmp" using nmp_eq by simp
    also have "\<dots> = int k" using nmp_eq_k by simp
    finally show ?thesis by simp
  qed

  have k_lt_n: "k < LENGTH('a)"
  proof -
    have "0 < LENGTH('b)" by simp
    hence "0 < nmp" using nmp_eq by simp
    hence "int k < int LENGTH('a)" using nmp_eq_k by linarith
    thus ?thesis by simp
  qed

  have v_w_pow: "v_w = (2::'a word) ^ k"
  proof -
    have "v_w = (Word.Word (2 ^ k) :: 'a word)" using vw_eq v_pow by simp
    also have "\<dots> = word_of_int (2 ^ k)" by simp
    also have "\<dots> = ((2::'a word) ^ k)" by (rule word_of_int_2p)
    finally show ?thesis .
  qed

  have uint_vw: "uint (v_w::'a word) = 2 ^ k"
  proof -
    have "(2::'a word) ^ k \<noteq> 0" using k_lt_n by simp
    hence "(0::'a word) < (2::'a word) ^ k" using word_neq_0_conv by blast
    hence "uint ((2::'a word) ^ k) = 2 ^ k" using uint_2p by blast
    thus ?thesis using v_w_pow by simp
  qed

  have unat_vw: "unat (v_w::'a word) = 2 ^ k"
    using uint_vw by (simp add: nat_power_eq unat_eq_nat_uint)

  have urem_unat: "unat (smt_urem x v_w) = unat x mod 2 ^ k"
  proof (cases "x = 0")
    case True
    thus ?thesis using uint_smt_urem(2)[of x v_w] by simp
  next
    case False
    thus ?thesis using uint_smt_urem(2)[of x v_w] unat_vw by simp
  qed

  have take_bit_unat: "unat (take_bit k x) = unat x mod 2 ^ k"
    by (metis take_bit_eq_mod unsigned_take_bit_eq)
  have urem_eq: "smt_urem x v_w = take_bit k x"
    using urem_unat take_bit_unat word_unat_eq_iff by metis

  have pm1_to_k: "nat (pm1 + 1) = k"
    using lc lc_eq_k pm1_nn by linarith

  have cat_eq: "take_bit k x = word_cat (0::'b word) (smtlib_extract pm1 0 x :: 'c word)"
  proof (rule bit_word_eqI)
    fix m :: nat assume m_lt: "m < LENGTH('a)"
    show "bit (take_bit k x :: 'a word) m =
          bit (word_cat (0::'b word) (smtlib_extract pm1 0 x :: 'c word) :: 'a word) m"
    proof (cases "m < k")
      case True
      hence m_lt_lc: "m < LENGTH('c)" using lc_eq_k by simp
      have lhs: "bit (take_bit k x :: 'a word) m \<longleftrightarrow> bit x m"
        using True by (simp add: bit_take_bit_iff)
      have ext_bit: "bit (smtlib_extract pm1 0 x :: 'c word) m \<longleftrightarrow> bit x m"
        unfolding smtlib_extract_def
        using True m_lt k_lt_n pm1_to_k lc_eq_k
        by (simp add: bit_slice_iff bit_take_bit_iff)
      have cat_bit: "bit (word_cat (0::'b word) (smtlib_extract pm1 0 x :: 'c word) :: 'a word) m
            \<longleftrightarrow> bit (smtlib_extract pm1 0 x :: 'c word) m"
        using m_lt_lc m_lt
        by (simp add: bit_word_ucast_iff)
      show ?thesis using lhs ext_bit cat_bit by simp
    next
      case False
      hence m_ge_k: "k \<le> m" by simp
      have lhs: "\<not> bit (take_bit k x :: 'a word) m"
        using m_ge_k by (simp add: bit_take_bit_iff)
      have m_ge_lc: "\<not> (m < LENGTH('c))" using m_ge_k lc_eq_k by simp
      have "bit (word_cat (0::'b word) (smtlib_extract pm1 0 x :: 'c word) :: 'a word) m
           \<longleftrightarrow> bit (0::'b word) (m - LENGTH('c))"
        using m_ge_lc m_lt
        by (simp add: bit_word_ucast_iff)
      hence "\<not> bit (word_cat (0::'b word) (smtlib_extract pm1 0 x :: 'c word) :: 'a word) m"
        by simp
      thus ?thesis using lhs by simp
    qed
  qed

  show "smt_urem x v_w = word_cat (0::'b word) (smtlib_extract pm1 0 x :: 'c word)"
    using urem_eq cat_eq by simp
qed

(*
(define-rule bv-urem-one
  ((x ?BitVec) (n Int))
  (bvurem x (@bv 1 n))
  (@bv 0 n))

Note: Constraint LENGTH('a) = n is not needed so omitted

*)


named_theorems rewrite_bv_urem_one \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_one]:
 fixes x::"'a ::len word" and n::int
  shows "NO_MATCH (cvc_a) (undefined x n) \<Longrightarrow> smt_urem x 1 = 0"
  unfolding smt_urem_def
  apply simp
  by (simp add: unsigned_eq_0_iff)

(*
(define-cond-rule bv-urem-self
  ((x ?BitVec) (w Int))
  (= w (@bvsize x))
  (bvurem x x)
  (@bv 0 w))

premise is really not helping here so I deleted it
*)

named_theorems rewrite_bv_urem_self \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_self]:
  fixes x::"'a ::len word" and n::int
  shows "NO_MATCH (cvc_a) (undefined x n) \<Longrightarrow> smt_urem x x = 0"
  unfolding smt_urem_def
  using unat_eq_zero by auto


(*
(define-rule bv-shl-zero
  ((a ?BitVec) (n Int))
  (bvshl (@bv 0 n) a)
  (@bv 0 n))

Note: Constraint LENGTH('a) = n is not needed so omitted

*)


named_theorems rewrite_bv_shl_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "NO_MATCH (cvc_a) (undefined a n) \<Longrightarrow> smtlib_bvshl 0 a = 0"
  unfolding smtlib_bvshl_def by simp

(*
(define-rule bv-lshr-zero
  ((a ?BitVec) (n Int))
  (bvlshr (@bv 0 n) a)
  (@bv 0 n))

Note: Constraint LENGTH('a) = n is not needed so omitted
*)

named_theorems rewrite_bv_lshr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "NO_MATCH (cvc_a) (undefined a n) \<Longrightarrow> smtlib_bvlshr 0 a = 0"
  unfolding smtlib_bvlshr_def by simp



(*
(define-rule bv-ashr-zero
  ((a ?BitVec) (n Int))
  (bvashr (@bv 0 n) a)
  (@bv 0 n))

Note: Constraint LENGTH('a) = n is not needed so omitted

*)

named_theorems rewrite_bv_ashr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined a n) 
    \<Longrightarrow> smtlib_bvashr 0 a = 0"
  unfolding smtlib_bvashr_def smtlib_bvlshr_def
  by (metis div_of_0_id len_gt_0 less_one linorder_not_le nth_0 of_nat_1 of_nat_diff order.refl
      smtlib_extract_msb_eq)
(*
(define-cond-rule bv-ugt-urem
  ((y ?BitVec) (x ?BitVec) (w Int))
  (= w (@bvsize y))
  (bvugt (bvurem y x) x)
  (and
    (= x (@bv 0 w))
    (bvugt y (@bv 0 w))
  ))
*)



named_theorems rewrite_bv_ugt_urem \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_urem]:
  fixes y::"'a ::len word" and x::"'a ::len word" and w::int
  shows "NO_MATCH cvc_a (undefined y x w) 
    \<Longrightarrow> w = int (size y) \<Longrightarrow> (x < smt_urem y x) =
   (x = 0 \<and> 0 < y)"
  unfolding smt_urem_def
  apply simp
  by (metis not_less_iff_gr_or_eq unat_gt_0 word_arith_nat_mod word_gt_a_gt_0 word_mod_by_0 word_mod_less_divisor)

(*
(define-rule bv-ult-one
  ((x ?BitVec) (n Int))
  (bvult x (@bv 1 n))
  (= x (@bv 0 n)))
*)


named_theorems rewrite_bv_ult_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_one]:
  fixes x::"'a ::len word" and n::int
  shows "NO_MATCH cvc_a (undefined x n) 
    \<Longrightarrow> (x < 1) = (x = 0)"
  by auto

(*
(define-cond-rule bv-slt-zero
  ((x ?BitVec) (n Int) (nm1 Int))
  (= nm1 (- n 1))
  (bvslt x (@bv 0 n))
  (= (extract nm1 nm1 x) (@bv 1 1)))

Premise is not helping so left it away
*)


named_theorems rewrite_bv_slt_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_slt_zero]:
  fixes x::"'a ::len word" and n nm1 ::int
  shows "NO_MATCH cvc_a (undefined x n nm1)
    \<Longrightarrow> nm1 = LENGTH('a) - 1 \<Longrightarrow> 
  (x <s 0) = (smtlib_extract nm1 nm1 x = (1::1 word))"
proof -
  assume nm1_eq: "nm1 = LENGTH('a) - 1"

  have nm1_int: "nm1 = int (LENGTH('a) - 1)"
    using nm1_eq by (simp add: of_nat_diff)

  have ext_eq: "(smtlib_extract nm1 nm1 x :: 1 word)
              = (if bit x (LENGTH('a) - 1) then 1 else 0)"
    using smtlib_extract_msb_eq[of x] nm1_int by simp

  have one_iff: "((smtlib_extract nm1 nm1 x :: 1 word) = 1) \<longleftrightarrow> bit x (LENGTH('a) - 1)"
    using ext_eq by (cases "bit x (LENGTH('a) - 1)") simp_all

  have slt_iff: "(x <s 0) \<longleftrightarrow> bit (x::'a word) (LENGTH('a) - 1)"
    by (simp add: word_sless_alt bit_last_iff)

  show "(x <s 0) = (smtlib_extract nm1 nm1 x = (1::1 word))"
    using slt_iff one_iff by simp
qed

(*
(define-cond-rule bv-merge-sign-extend-1
  ((x ?BitVec) (i Int) (j Int) (k Int))
  (= k (+ i j))
  (sign_extend i (sign_extend j x))
  (sign_extend k x)
  )
*)

named_theorems rewrite_bv_merge_sign_extend_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_1]:
  fixes x::"'a::len word" and i j k::"int"
  shows "NO_MATCH cvc_a (undefined x i j k) 
    \<Longrightarrow>
LENGTH('b) = LENGTH('a) + j \<Longrightarrow>
LENGTH('c) = LENGTH('b) + i \<Longrightarrow>
LENGTH('c) = LENGTH('a) + k \<Longrightarrow>
i \<ge> 0 \<Longrightarrow> j \<ge> 0 \<Longrightarrow>
k = i + j \<Longrightarrow> 

 (scast (scast x::'b::len word)::'c::len word) = scast x"
  using scast_up_scast_id[of x]
  by (simp add: is_up.rep_eq scast_up_scast)


(*
(define-cond-rule bv-merge-sign-extend-2
  ((x ?BitVec) (i Int) (j Int) (k Int))
  (and (> j 0) (= k (+ i j)))
  (sign_extend i (zero_extend j x))
  (zero_extend k x)
  )
*)

named_theorems rewrite_bv_merge_sign_extend_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_2]:
  fixes x::"'a::len word" and i j k::"int"
  shows "NO_MATCH cvc_a (undefined x i j k)
    \<Longrightarrow>
 LENGTH('c) = LENGTH('b) + i \<Longrightarrow>
 i \<ge> 0 \<Longrightarrow> j \<ge> 0
 \<Longrightarrow> LENGTH('b) = LENGTH('a) + j \<Longrightarrow> LENGTH('c) = LENGTH('a) + k \<Longrightarrow>

j > 0 \<Longrightarrow>
k = i + j \<Longrightarrow>
   ( Word.signed_cast (ucast x::'b::len word)::'c::len word) = ucast x"
proof -
  assume lb_a: "LENGTH('b) = LENGTH('a) + j"
     and j_pos: "j > 0"

  have lb_gt_a: "LENGTH('a) < LENGTH('b)"
    using lb_a j_pos by linarith

  show "(Word.signed_cast (ucast x::'b::len word)::'c::len word) = ucast x"
  proof (rule bit_word_eqI)
    fix m :: nat assume m_lt: "m < LENGTH('c)"

    have msb_zero: "\<not> bit (ucast x :: 'b word) (LENGTH('b) - Suc 0)"
      using lb_gt_a by (simp add: bit_word_ucast_iff)

    show "bit (Word.signed_cast (ucast x::'b::len word) :: 'c::len word) m
        = bit (ucast x :: 'c::len word) m"
      using msb_zero m_lt lb_gt_a
      by (auto simp: bit_word_scast_iff bit_word_ucast_iff)
  qed
qed
(*
(define-cond-rule bv-sign-extend-eq-const-1
  ((x ?BitVec) (m Int) (c Int) (nm Int) (mp1 Int) (nm1 Int) (nmm1 Int))
  (def
    (n (@bvsize x))
    (clo (extract nm1 0 (@bv c nm)))
    ; Combines the sign bit c[n-1] and the high part
    (chi (extract nmm1 nm1 (@bv c nm)))
  )
  (and (= mp1 (+ m 1)) (= nm1 (- n 1)) (= nmm1 (- nm 1)))
  (= (sign_extend m x) (@bv c nm))
  (and
    (or (= chi (@bv 0 mp1)) (= chi (bvnot (@bv 0 mp1))))
    (= x clo)))
*)

named_theorems rewrite_bv_sign_extend_eq_const_1 \<open>manually generated\<close>

lemma [rewrite_bv_sign_extend_eq_const_1]:
  fixes x::"'a::len word" and m c nm mp1 nm1 nmm1 ::int
  shows "NO_MATCH cvc_a (undefined x m c nm mp1 nm1 nmm1) \<Longrightarrow>
  c_w = Word.Word c \<Longrightarrow>
  nm = LENGTH('b) \<Longrightarrow>
  LENGTH('b) = LENGTH('a) + m \<Longrightarrow>
  m \<ge> 0 \<Longrightarrow>
  mp1 = m + 1 \<Longrightarrow>
  nm1 = int LENGTH('a) - 1 \<Longrightarrow>
  nmm1 = nm - 1 \<Longrightarrow>
  int LENGTH('c) = mp1 \<Longrightarrow>
  ((Word.signed_cast x::'b::len word) = c_w)
   =
  (((smtlib_extract nmm1 nm1 c_w :: 'c::len word) = 0
      \<or> (smtlib_extract nmm1 nm1 c_w :: 'c::len word) = not 0)
   \<and> x = (smtlib_extract nm1 0 c_w :: 'a::len word))"
proof -
  assume nm_eq: "nm = LENGTH('b)"
     and lb_a: "LENGTH('b) = LENGTH('a) + m"
     and m_nn: "m \<ge> 0"
     and mp1_eq: "mp1 = m + 1"
     and nm1_eq: "nm1 = int LENGTH('a) - 1"
     and nmm1_eq: "nmm1 = nm - 1"
     and lc_eq: "int LENGTH('c) = mp1"

  have la_le_lb: "LENGTH('a) \<le> LENGTH('b)"
    using lb_a m_nn by linarith
  have lc_val: "LENGTH('c) = LENGTH('b) - LENGTH('a) + 1"
    using lc_eq mp1_eq lb_a m_nn by linarith
  have lc_pos: "0 < LENGTH('c)"
    using lc_val la_le_lb by linarith
  have nm1_nat: "nat nm1 = LENGTH('a) - Suc 0"
    using nm1_eq by (simp add: of_nat_diff)
  have nm1p1_nat: "nat (nm1 + 1) = LENGTH('a)"
    using nm1_eq by simp
  have nmm1p1_nat: "nat (nmm1 + 1) = LENGTH('b)"
    using nmm1_eq nm_eq by simp

  let ?MSB = "LENGTH('a) - Suc 0"
  let ?clo = "smtlib_extract nm1 0 c_w :: 'a::len word"
  let ?chi = "smtlib_extract nmm1 nm1 c_w :: 'c::len word"
  let ?sx = "Word.signed_cast x :: 'b::len word"

  have MSB_lt_a: "?MSB < LENGTH('a)" by simp
  have MSB_lt_b: "?MSB < LENGTH('b)" using la_le_lb by simp

  have clo_bit: "\<And>i. i < LENGTH('a) \<Longrightarrow> bit ?clo i = bit c_w i"
  proof -
    fix i :: nat assume i_lt: "i < LENGTH('a)"
    have "?clo = slice 0 (take_bit LENGTH('a) (c_w :: 'b word) :: 'b word)"
      unfolding smtlib_extract_def using nm1p1_nat by simp
    moreover have "bit (slice 0 (take_bit LENGTH('a) (c_w :: 'b word) :: 'b word) :: 'a word) i
                  = bit c_w i"
      using i_lt la_le_lb
      by (simp add: bit_slice_iff bit_take_bit_iff min_def)
    ultimately show "bit ?clo i = bit c_w i" by simp
  qed

  have chi_bit: "\<And>i. i < LENGTH('c) \<Longrightarrow> bit ?chi i = bit c_w (i + ?MSB)"
  proof -
    fix i :: nat assume i_lt: "i < LENGTH('c)"
    have "?chi = slice ?MSB (c_w :: 'b word)"
      unfolding smtlib_extract_def using nm1_nat nmm1p1_nat by simp
    moreover have "bit (slice ?MSB (c_w :: 'b word) :: 'c word) i = bit c_w (i + ?MSB)"
    proof -
      have lcs: "LENGTH('b) - ?MSB = LENGTH('c)" using lc_val la_le_lb
        by (metis MSB_lt_b Suc_diff_Suc Suc_eq_plus1 Suc_pred len_gt_0)
      have lhs: "bit (slice ?MSB (c_w :: 'b word) :: 'c word) i
                = (i < min LENGTH('c) (LENGTH('b) - ?MSB)
                   \<and> bit c_w (i + LENGTH('b) - (LENGTH('b) - ?MSB)))"
        by (simp add: bit_slice_iff)
      have "LENGTH('b) - (LENGTH('b) - ?MSB) = ?MSB" using MSB_lt_b by linarith
      thus ?thesis using lhs lcs i_lt
        using nth_slice by blast
    qed
    ultimately show "bit ?chi i = bit c_w (i + ?MSB)" by simp
  qed

  have sx_bit: "\<And>i. i < LENGTH('b) \<Longrightarrow>
       bit ?sx i = (if i < LENGTH('a) then bit x i else bit x ?MSB)"
    apply (auto simp: bit_word_scast_iff)
    by (metis bit_imp_le_length)
  show "(?sx = c_w)
       = ((?chi = 0 \<or> ?chi = not 0) \<and> x = ?clo)"
  proof
    assume eq: "?sx = c_w"

    have clo_eq: "x = ?clo"
    proof (rule bit_word_eqI)
      fix i :: nat assume i_lt: "i < LENGTH('a)"
      have i_lt_b: "i < LENGTH('b)" using i_lt la_le_lb by linarith
      have "bit x i = bit ?sx i" using i_lt sx_bit[OF i_lt_b] by simp
      also have "\<dots> = bit c_w i" using eq by simp
      also have "\<dots> = bit ?clo i" using i_lt clo_bit by simp
      finally show "bit x i = bit ?clo i" .
    qed

    have chi_uniform: "\<forall>j < LENGTH('c). bit ?chi j = bit x ?MSB"
    proof (intro allI impI)
      fix j :: nat assume j_lt: "j < LENGTH('c)"
      have jpMSB_lt: "j + ?MSB < LENGTH('b)" using j_lt lc_val la_le_lb
        using MSB_lt_a by linarith
      have "bit ?chi j = bit c_w (j + ?MSB)" using j_lt chi_bit by simp
      also have "\<dots> = bit ?sx (j + ?MSB)" using eq by simp
      also have "\<dots> = bit x ?MSB"
      proof (cases "j + ?MSB < LENGTH('a)")
        case True
        hence "j + ?MSB = ?MSB" by linarith
        thus ?thesis using True sx_bit[OF jpMSB_lt] by simp
      next
        case False
        thus ?thesis using sx_bit[OF jpMSB_lt] by simp
      qed
      finally show "bit ?chi j = bit x ?MSB" .
    qed

    have chi_alt: "?chi = 0 \<or> ?chi = not 0"
    proof (cases "bit x ?MSB")
      case True
      have "?chi = (not 0 :: 'c word)"
      proof (rule bit_word_eqI)
        fix j :: nat assume j_lt: "j < LENGTH('c)"
        thus "bit ?chi j = bit (not 0 :: 'c word) j"
          using True chi_uniform by (simp add: bit_not_iff)
      qed
      thus ?thesis ..
    next
      case False
      have "?chi = (0 :: 'c word)"
      proof (rule bit_word_eqI)
        fix j :: nat assume j_lt: "j < LENGTH('c)"
        thus "bit ?chi j = bit (0 :: 'c word) j"
          using False chi_uniform by simp
      qed
      thus ?thesis ..
    qed

    show "(?chi = 0 \<or> ?chi = not 0) \<and> x = ?clo"
      using chi_alt clo_eq by simp
  next
    assume "(?chi = 0 \<or> ?chi = not 0) \<and> x = ?clo"
    hence chi_alt: "?chi = 0 \<or> ?chi = not 0" and x_eq: "x = ?clo" by auto

    have chi_uniform: "\<forall>j < LENGTH('c). bit ?chi j = bit ?chi 0"
      using chi_alt lc_pos by (auto simp: bit_not_iff)

    show "?sx = c_w"
    proof (rule bit_word_eqI)
      fix i :: nat assume i_lt: "i < LENGTH('b)"
      show "bit ?sx i = bit c_w i"
      proof (cases "i < LENGTH('a)")
        case True
        have "bit ?sx i = bit x i" using True sx_bit[OF i_lt] by simp
        also have "\<dots> = bit ?clo i" using x_eq by simp
        also have "\<dots> = bit c_w i" using True clo_bit by simp
        finally show ?thesis .
      next
        case False
        hence i_ge: "LENGTH('a) \<le> i" by simp
        let ?j = "i - ?MSB"
        have j_lt: "?j < LENGTH('c)"
          using i_lt i_ge lc_val by linarith
        have i_eq: "i = ?j + ?MSB"
          using i_ge by simp
        have "bit ?sx i = bit x ?MSB" using False sx_bit[OF i_lt] by simp
        also have "\<dots> = bit ?clo ?MSB" using x_eq by simp
        also have "\<dots> = bit c_w ?MSB" using MSB_lt_a clo_bit by simp
        also have "\<dots> = bit ?chi 0" using lc_pos chi_bit[of 0] by simp
        also have "\<dots> = bit ?chi ?j" using j_lt chi_uniform by blast
        also have "\<dots> = bit c_w (?j + ?MSB)" using j_lt chi_bit by simp
        also have "\<dots> = bit c_w i" using i_eq by simp
        finally show ?thesis .
      qed
    qed
  qed
qed

(*
(define-cond-rule bv-sign-extend-eq-const-2
  ((x ?BitVec) (m Int) (c Int) (nm Int) (mp1 Int) (nm1 Int) (nmm1 Int))
  (def
    (n (@bvsize x))
    (clo (extract nm1 0 (@bv c nm)))
    ; Combines the sign bit c[n-1] and the high part
    (chi (extract nmm1 nm1 (@bv c nm)))
  )
  (and (= mp1 (+ m 1)) (= nm1 (- n 1)) (= nmm1 (- nm 1)))
  (= (@bv c nm) (sign_extend m x))
  (and
    (or (= chi (@bv 0 mp1)) (= chi (bvnot (@bv 0 mp1))))
    (= x clo)))
*)

named_theorems rewrite_bv_sign_extend_eq_const_2 \<open>manually generated\<close>

lemma [rewrite_bv_sign_extend_eq_const_2]:
  fixes x::"'a::len word" and m c nm mp1 nm1 nmm1 ::int
  shows "NO_MATCH cvc_a (undefined x m c nm mp1 nm1 nmm1) \<Longrightarrow>
  c_w = Word.Word c \<Longrightarrow>
  nm = LENGTH('b) \<Longrightarrow>
  LENGTH('b) = LENGTH('a) + m \<Longrightarrow>
  m \<ge> 0 \<Longrightarrow>
  mp1 = m + 1 \<Longrightarrow>
  nm1 = int LENGTH('a) - 1 \<Longrightarrow>
  nmm1 = nm - 1 \<Longrightarrow>
  int LENGTH('c) = mp1 \<Longrightarrow>
  (c_w = (Word.signed_cast x::'b::len word))
   =
  (((smtlib_extract nmm1 nm1 c_w :: 'c::len word) = 0
      \<or> (smtlib_extract nmm1 nm1 c_w :: 'c::len word) = not 0)
   \<and> x = (smtlib_extract nm1 0 c_w :: 'a::len word))"
proof -
  assume H1: "NO_MATCH cvc_a (undefined x m c nm mp1 nm1 nmm1)"
     and H2: "c_w = Word.Word c"
     and H3: "nm = LENGTH('b)"
     and H4: "LENGTH('b) = LENGTH('a) + m"
     and H5: "m \<ge> 0"
     and H6: "mp1 = m + 1"
     and H7: "nm1 = int LENGTH('a) - 1"
     and H8: "nmm1 = nm - 1"
     and H9: "int LENGTH('c) = mp1"
  have main: "((Word.signed_cast x::'b::len word) = c_w)
       = (((smtlib_extract nmm1 nm1 c_w :: 'c::len word) = 0
             \<or> (smtlib_extract nmm1 nm1 c_w :: 'c::len word) = not 0)
          \<and> x = (smtlib_extract nm1 0 c_w :: 'a::len word))"
    using rewrite_bv_sign_extend_eq_const_1[OF H1 H2 H3 H4 H5 H6 H7 H8 H9] .
  thus ?thesis by metis
qed


(*
(define-cond-rule bv-zero-extend-eq-const-1
  ((x ?BitVec) (m Int) (c Int) (nm Int) (nm1 Int) (nmm1 Int))
  (def
    (n (@bvsize x))
    (clo (extract nm1 0 (@bv c nm)))
    (chi (extract nmm1 nm1 (@bv c nm)))
  )
  (and (= nm1 (- n 1)) (= nmm1 (- nm 1)))
  (= (zero_extend m x) (@bv c nm))
  (and
    (= chi (@bv 0 m))
    (= x clo)))

Note: the cvc5 rule above has chi = extract nmm1 nm1 c which is (m+1) bits, but
compares to (@bv 0 m) which is m bits -- type mismatch / unsound. The lemma here
uses chi = extract nmm1 n c (m bits, the strictly-above-x range), which is the
mathematically correct condition for zero_extend.
*)

named_theorems rewrite_bv_zero_extend_eq_const_1 \<open>manually generated\<close>

lemma [rewrite_bv_zero_extend_eq_const_1]:
  fixes x::"'a::len word" and m c n nm nm1 nmm1 ::int
  shows "NO_MATCH cvc_a (undefined x m c n nm nm1 nmm1) \<Longrightarrow>
  c_w = Word.Word c \<Longrightarrow>
  n = int LENGTH('a) \<Longrightarrow>
  nm = LENGTH('b) \<Longrightarrow>
  LENGTH('b) = LENGTH('a) + m \<Longrightarrow>
  m \<ge> 0 \<Longrightarrow>
  nm1 = n - 1 \<Longrightarrow>
  nmm1 = nm - 1 \<Longrightarrow>
  int LENGTH('c) = m \<Longrightarrow>
  ((ucast x::'b::len word) = c_w)
   =
  ((smtlib_extract nmm1 n c_w :: 'c::len word) = 0
   \<and> x = (smtlib_extract nm1 0 c_w :: 'a::len word))"
proof -
  assume n_eq: "n = int LENGTH('a)"
     and nm_eq: "nm = LENGTH('b)"
     and lb_a: "LENGTH('b) = LENGTH('a) + m"
     and m_nn: "m \<ge> 0"
     and nm1_eq: "nm1 = n - 1"
     and nmm1_eq: "nmm1 = nm - 1"
     and lc_eq: "int LENGTH('c) = m"

  have la_le_lb: "LENGTH('a) \<le> LENGTH('b)"
    using lb_a m_nn by linarith
  have lc_val: "LENGTH('c) = LENGTH('b) - LENGTH('a)"
    using lc_eq lb_a m_nn by linarith
  have lc_pos: "0 < LENGTH('c)" by simp
  have n_nat: "nat n = LENGTH('a)"
    using n_eq by simp
  have nm1p1_nat: "nat (nm1 + 1) = LENGTH('a)"
    using nm1_eq n_eq by simp
  have nmm1p1_nat: "nat (nmm1 + 1) = LENGTH('b)"
    using nmm1_eq nm_eq by simp

  let ?clo = "smtlib_extract nm1 0 c_w :: 'a::len word"
  let ?chi = "smtlib_extract nmm1 n c_w :: 'c::len word"
  let ?ux = "ucast x :: 'b::len word"

  have clo_bit: "\<And>i. i < LENGTH('a) \<Longrightarrow> bit ?clo i = bit c_w i"
  proof -
    fix i :: nat assume i_lt: "i < LENGTH('a)"
    have "?clo = slice 0 (take_bit LENGTH('a) (c_w :: 'b word) :: 'b word)"
      unfolding smtlib_extract_def using nm1p1_nat by simp
    moreover have "bit (slice 0 (take_bit LENGTH('a) (c_w :: 'b word) :: 'b word) :: 'a word) i
                  = bit c_w i"
      using i_lt la_le_lb
      by (simp add: bit_slice_iff bit_take_bit_iff min_def)
    ultimately show "bit ?clo i = bit c_w i" by simp
  qed

  have chi_bit: "\<And>i. i < LENGTH('c) \<Longrightarrow> bit ?chi i = bit c_w (i + LENGTH('a))"
  proof -
    fix i :: nat assume i_lt: "i < LENGTH('c)"
    have "?chi = slice LENGTH('a) (c_w :: 'b word)"
      unfolding smtlib_extract_def using n_nat nmm1p1_nat by simp
    moreover have "bit (slice LENGTH('a) (c_w :: 'b word) :: 'c word) i = bit c_w (i + LENGTH('a))"
    proof -
      have lcs: "LENGTH('b) - LENGTH('a) = LENGTH('c)" using lc_val by simp
      have lhs: "bit (slice LENGTH('a) (c_w :: 'b word) :: 'c word) i
                = (i < min LENGTH('c) (LENGTH('b) - LENGTH('a))
                   \<and> bit c_w (i + LENGTH('b) - (LENGTH('b) - LENGTH('a))))"
        by (simp add: bit_slice_iff)
      have "LENGTH('b) - (LENGTH('b) - LENGTH('a)) = LENGTH('a)" using la_le_lb by linarith
      thus ?thesis using lhs lcs i_lt
        using nth_slice by blast
    qed
    ultimately show "bit ?chi i = bit c_w (i + LENGTH('a))" by simp
  qed

  have ux_bit: "\<And>i. i < LENGTH('b) \<Longrightarrow> bit ?ux i = (i < LENGTH('a) \<and> bit x i)"
    by (auto simp: bit_word_ucast_iff)

  show "(?ux = c_w) = ((?chi = 0) \<and> x = ?clo)"
  proof
    assume eq: "?ux = c_w"

    have clo_eq: "x = ?clo"
    proof (rule bit_word_eqI)
      fix i :: nat assume i_lt: "i < LENGTH('a)"
      have i_lt_b: "i < LENGTH('b)" using i_lt la_le_lb by linarith
      have "bit x i = bit ?ux i" using i_lt ux_bit[OF i_lt_b] by simp
      also have "\<dots> = bit c_w i" using eq by simp
      also have "\<dots> = bit ?clo i" using i_lt clo_bit by simp
      finally show "bit x i = bit ?clo i" .
    qed

    have chi_eq: "?chi = (0 :: 'c word)"
    proof (rule bit_word_eqI)
      fix j :: nat assume j_lt: "j < LENGTH('c)"
      have jpa_lt: "j + LENGTH('a) < LENGTH('b)" using j_lt lc_val by linarith
      have "bit ?chi j = bit c_w (j + LENGTH('a))" using j_lt chi_bit by simp
      also have "\<dots> = bit ?ux (j + LENGTH('a))" using eq by simp
      also have "\<dots> = False" using ux_bit[OF jpa_lt] by simp
      finally show "bit ?chi j = bit (0::'c word) j" by simp
    qed

    show "(?chi = 0) \<and> x = ?clo"
      using chi_eq clo_eq by simp
  next
    assume "(?chi = 0) \<and> x = ?clo"
    hence chi_eq: "?chi = 0" and x_eq: "x = ?clo" by auto

    show "?ux = c_w"
    proof (rule bit_word_eqI)
      fix i :: nat assume i_lt: "i < LENGTH('b)"
      show "bit ?ux i = bit c_w i"
      proof (cases "i < LENGTH('a)")
        case True
        have "bit ?ux i = bit x i" using True ux_bit[OF i_lt] by simp
        also have "\<dots> = bit ?clo i" using x_eq by simp
        also have "\<dots> = bit c_w i" using True clo_bit by simp
        finally show ?thesis .
      next
        case False
        hence i_ge: "LENGTH('a) \<le> i" by simp
        let ?j = "i - LENGTH('a)"
        have j_lt: "?j < LENGTH('c)" using i_lt i_ge lc_val by linarith
        have i_eq: "i = ?j + LENGTH('a)" using i_ge by simp
        have "bit ?ux i = False" using False ux_bit[OF i_lt] by simp
        also have "False = bit (0::'c word) ?j" by simp
        also have "\<dots> = bit ?chi ?j" using chi_eq by simp
        also have "\<dots> = bit c_w (?j + LENGTH('a))" using j_lt chi_bit by simp
        also have "\<dots> = bit c_w i" using i_eq by simp
        finally show ?thesis .
      qed
    qed
  qed
qed


(*
(define-cond-rule bv-zero-extend-eq-const-2
  ((x ?BitVec) (m Int) (c Int) (nm Int) (nm1 Int) (nmm1 Int))
  (def
    (n (@bvsize x))
    (clo (extract nm1 0 (@bv c nm)))
    (chi (extract nmm1 nm1 (@bv c nm)))
  )
  (and (= nm1 (- n 1)) (= nmm1 (- nm 1)))
  (= (@bv c nm) (zero_extend m x))
  (and
    (= chi (@bv 0 m))
    (= x clo)))

See note above on bv-zero-extend-eq-const-1: chi must be m bits (not m+1) for
the lemma to be sound.
*)

named_theorems rewrite_bv_zero_extend_eq_const_2 \<open>manually generated\<close>

lemma [rewrite_bv_zero_extend_eq_const_2]:
  fixes x::"'a::len word" and m c n nm nm1 nmm1 ::int
  shows "NO_MATCH cvc_a (undefined x m c n nm nm1 nmm1) \<Longrightarrow>
  c_w = Word.Word c \<Longrightarrow>
  n = int LENGTH('a) \<Longrightarrow>
  nm = LENGTH('b) \<Longrightarrow>
  LENGTH('b) = LENGTH('a) + m \<Longrightarrow>
  m \<ge> 0 \<Longrightarrow>
  nm1 = n - 1 \<Longrightarrow>
  nmm1 = nm - 1 \<Longrightarrow>
  int LENGTH('c) = m \<Longrightarrow>
  (c_w = (ucast x::'b::len word))
   =
  ((smtlib_extract nmm1 n c_w :: 'c::len word) = 0
   \<and> x = (smtlib_extract nm1 0 c_w :: 'a::len word))"
proof -
  assume H1: "NO_MATCH cvc_a (undefined x m c n nm nm1 nmm1)"
     and H2: "c_w = Word.Word c"
     and H3: "n = int LENGTH('a)"
     and H4: "nm = LENGTH('b)"
     and H5: "LENGTH('b) = LENGTH('a) + m"
     and H6: "m \<ge> 0"
     and H7: "nm1 = n - 1"
     and H8: "nmm1 = nm - 1"
     and H9: "int LENGTH('c) = m"
  have main: "((ucast x::'b::len word) = c_w)
       = ((smtlib_extract nmm1 n c_w :: 'c::len word) = 0
          \<and> x = (smtlib_extract nm1 0 c_w :: 'a::len word))"
    using rewrite_bv_zero_extend_eq_const_1[OF H1 H2 H3 H4 H5 H6 H7 H8 H9] .
  thus ?thesis by metis
qed



(*
(define-cond-rule bv-zero-extend-ult-const-1
  ((x ?BitVec) (m Int) (c Int) (nm Int) (nm1 Int))
  (def
    (n (@bvsize x))
    (clo (extract nm1 0 (@bv c nm)))
  )
  (and (= nm1 (- n 1)) (= (@bv c nm) (zero_extend m clo)))
  (bvult (zero_extend m x) (@bv c nm))
  (bvult x clo))
*)

named_theorems rewrite_bv_zero_extend_ult_const_1 \<open>manually generated\<close>

lemma [rewrite_bv_zero_extend_ult_const_1]:
  fixes x::"'a::len word" and m c n nm nm1 ::int
  shows "NO_MATCH cvc_a (undefined x m c n nm nm1) \<Longrightarrow>
  c_w = Word.Word c \<Longrightarrow>
  n = int LENGTH('a) \<Longrightarrow>
  nm = LENGTH('b) \<Longrightarrow>
  LENGTH('b) = LENGTH('a) + m \<Longrightarrow>
  m \<ge> 0 \<Longrightarrow>
  nm1 = n - 1 \<Longrightarrow>
  c_w = (ucast (smtlib_extract nm1 0 c_w :: 'a::len word) :: 'b::len word) \<Longrightarrow>
  ((ucast x::'b::len word) < c_w)
   =
  (x < (smtlib_extract nm1 0 c_w :: 'a::len word))"
proof -
  assume lb_a: "LENGTH('b) = LENGTH('a) + m"
     and m_nn: "m \<ge> 0"
     and cond: "c_w = (ucast (smtlib_extract nm1 0 c_w :: 'a::len word) :: 'b::len word)"

  have la_le_lb: "LENGTH('a) \<le> LENGTH('b)" using lb_a m_nn by linarith
  have is_up_cast: "is_up (ucast :: 'a::len word \<Rightarrow> 'b::len word)"
    using la_le_lb is_up by blast

  let ?clo = "smtlib_extract nm1 0 c_w :: 'a::len word"

  have unat_ux: "unat (ucast x :: 'b word) = unat x"
    using is_up_cast uint_up_ucast unat_eq_nat_uint by metis
  have unat_uclo: "unat (ucast ?clo :: 'b word) = unat ?clo"
    using is_up_cast uint_up_ucast unat_eq_nat_uint by metis

  have "((ucast x :: 'b word) < c_w) = ((ucast x :: 'b word) < (ucast ?clo :: 'b word))"
    using cond by simp
  also have "\<dots> = (unat (ucast x :: 'b word) < unat (ucast ?clo :: 'b word))"
    by (rule word_less_nat_alt)
  also have "\<dots> = (unat x < unat ?clo)" using unat_ux unat_uclo by simp
  also have "\<dots> = (x < ?clo)" by (rule word_less_nat_alt[symmetric])
  finally show ?thesis .
qed


(*
(define-cond-rule bv-zero-extend-ult-const-2
  ((x ?BitVec) (m Int) (c Int) (nm Int) (nm1 Int))
  (def
    (n (@bvsize x))
    (clo (extract nm1 0 (@bv c nm)))
  )
  (and (= nm1 (- n 1)) (= (@bv c nm) (zero_extend m clo)))
  (bvult (@bv c nm) (zero_extend m x))
  (bvult clo x))
*)

named_theorems rewrite_bv_zero_extend_ult_const_2 \<open>manually generated\<close>

lemma [rewrite_bv_zero_extend_ult_const_2]:
  fixes x::"'a::len word" and m c n nm nm1 ::int
  shows "NO_MATCH cvc_a (undefined x m c n nm nm1) \<Longrightarrow>
  c_w = Word.Word c \<Longrightarrow>
  n = int LENGTH('a) \<Longrightarrow>
  nm = LENGTH('b) \<Longrightarrow>
  LENGTH('b) = LENGTH('a) + m \<Longrightarrow>
  m \<ge> 0 \<Longrightarrow>
  nm1 = n - 1 \<Longrightarrow>
  c_w = (ucast (smtlib_extract nm1 0 c_w :: 'a::len word) :: 'b::len word) \<Longrightarrow>
  (c_w < (ucast x::'b::len word))
   =
  ((smtlib_extract nm1 0 c_w :: 'a::len word) < x)"
proof -
  assume lb_a: "LENGTH('b) = LENGTH('a) + m"
     and m_nn: "m \<ge> 0"
     and cond: "c_w = (ucast (smtlib_extract nm1 0 c_w :: 'a::len word) :: 'b::len word)"

  have la_le_lb: "LENGTH('a) \<le> LENGTH('b)" using lb_a m_nn by linarith
  have is_up_cast: "is_up (ucast :: 'a::len word \<Rightarrow> 'b::len word)"
    using la_le_lb is_up by blast

  let ?clo = "smtlib_extract nm1 0 c_w :: 'a::len word"

  have unat_ux: "unat (ucast x :: 'b word) = unat x"
    using is_up_cast uint_up_ucast unat_eq_nat_uint by metis
  have unat_uclo: "unat (ucast ?clo :: 'b word) = unat ?clo"
    using is_up_cast uint_up_ucast unat_eq_nat_uint by metis

  have "(c_w < (ucast x :: 'b word)) = ((ucast ?clo :: 'b word) < (ucast x :: 'b word))"
    using cond by simp
  also have "\<dots> = (unat (ucast ?clo :: 'b word) < unat (ucast x :: 'b word))"
    by (rule word_less_nat_alt)
  also have "\<dots> = (unat ?clo < unat x)" using unat_ux unat_uclo by simp
  also have "\<dots> = (?clo < x)" by (rule word_less_nat_alt[symmetric])
  finally show ?thesis .
qed


(*
(define-cond-rule bv-sign-extend-ult-const-1
  ((x ?BitVec) (m Int) (c Int) (nm Int) (nm1 Int))
  (def
    (n (@bvsize x))
    (clo (extract nm1 0 (@bv c nm)))
    (a (bvshl (@bv 1 nm) (@bv (- n 1) nm))) ; 1 << (n-1)
    (b (bvshl (bvnot (@bv 0 nm)) (@bv (- n 1) nm))) ; ~0 << (n-1)
  )
  (and (or (bvule (@bv c nm) a) (bvuge (@bv c nm) b)) (= nm1 (- n 1)))
  (bvult (sign_extend m x) (@bv c nm))
  (bvult x clo))

Here a = 2^(n-1) and b = -2^(n-1) (in nm-bit word arithmetic).
*)

\<comment> \<open>Helper: unat of a widening scast.\<close>
lemma unat_scast_widen_aux:
  fixes x :: "'a::len word"
  assumes lae: "LENGTH('a) \<le> LENGTH('b::len)"
  shows "unat (Word.signed_cast x :: 'b::len word) =
         unat x + (if bit x (LENGTH('a) - Suc 0) then 2 ^ LENGTH('b::len) - 2 ^ LENGTH('a) else 0)"
proof -
  let ?MSB = "LENGTH('a) - Suc 0"
  let ?S = "Word.signed_cast x :: 'b::len word"

  have suc_msb: "Suc ?MSB = LENGTH('a)" by simp
  have isup: "is_up (Word.signed_cast :: 'a word \<Rightarrow> 'b::len word)" using lae by (simp add: is_up)
  have sint_eq: "sint ?S = sint x" using isup sint_up_scast
    using sint_up_scast isup by auto

  have sint_x_id: "sint x = uint x - 2 ^ LENGTH('a) * of_bool (bit x ?MSB)"
  proof -
    have bit_uint_x: "bit (uint x) ?MSB = bit x ?MSB" by (simp add: bit_uint_iff)
    have "sint x = signed_take_bit ?MSB (uint x)" by (rule sint_uint)
    also have "\<dots> = take_bit (Suc ?MSB) (uint x) - 2 ^ Suc ?MSB * of_bool (bit (uint x) ?MSB)"
      by (rule signed_take_bit_eq_take_bit_minus)
    also have "\<dots> = uint x - 2 ^ LENGTH('a) * of_bool (bit x ?MSB)"
      using suc_msb bit_uint_x by simp
    finally show ?thesis .
  qed

  have ux_nn: "(0::int) \<le> uint x" by simp
  have ux_lt: "uint x < (2::int) ^ LENGTH('a)" by simp
  have pow_le: "(2 :: int) ^ LENGTH('a) \<le> 2 ^ LENGTH('b::len)" using lae by simp

  have uint_S_eq: "uint ?S = uint x + of_bool (bit x ?MSB) * (2 ^ LENGTH('b::len) - 2 ^ LENGTH('a))"
  proof (cases "bit x ?MSB")
    case True
    have sint_x: "sint x = uint x - 2 ^ LENGTH('a)" using True sint_x_id by simp
    have sintx_neg: "sint x < 0" using sint_x ux_lt by simp
    have sintx_lb: "- ((2::int) ^ LENGTH('b)) \<le> sint x" using sint_x ux_nn pow_le by linarith

    have "uint ?S = take_bit LENGTH('b) (sint x)" using sint_eq uint_sint by metis
    also have "\<dots> = sint x mod 2 ^ LENGTH('b)" by (simp add: take_bit_eq_mod)
    also have "\<dots> = (sint x + 2 ^ LENGTH('b)) mod 2 ^ LENGTH('b)" by simp
    also have "\<dots> = sint x + 2 ^ LENGTH('b)"
      using sintx_neg sintx_lb apply (simp add: mod_pos_pos_trivial)
      by (metis add.commute add.right_inverse add_le_cancel_left add_less_same_cancel2 mod_add_self2 mod_pos_pos_trivial)
    also have "\<dots> = uint x + (2 ^ LENGTH('b) - 2 ^ LENGTH('a))" using sint_x by simp
    finally show ?thesis using True by simp
  next
    case False
    have sint_x: "sint x = uint x" using False sint_x_id by simp
    have ux_lt_b: "uint x < (2::int) ^ LENGTH('b)" using ux_lt pow_le by linarith

    have "uint ?S = take_bit LENGTH('b) (sint x)" using sint_eq uint_sint by metis
    also have "\<dots> = take_bit LENGTH('b) (uint x)" using sint_x by simp
    also have "\<dots> = uint x" using ux_nn ux_lt_b by (simp add: take_bit_eq_mod mod_pos_pos_trivial)
    finally show ?thesis using False by simp
  qed

  have nonneg: "0 \<le> of_bool (bit x ?MSB) * ((2 :: int) ^ LENGTH('b) - 2 ^ LENGTH('a))"
    using pow_le by simp

  have nat_delta: "nat (of_bool (bit x ?MSB) * ((2 :: int) ^ LENGTH('b::len) - 2 ^ LENGTH('a)))
                 = (if bit x ?MSB then 2 ^ LENGTH('b) - 2 ^ LENGTH('a) else 0)"
  proof (cases "bit x ?MSB")
    case True
    have pow_nn: "(0 :: int) \<le> 2 ^ LENGTH('a)" by simp
    have "nat (of_bool (bit x ?MSB) * ((2 :: int) ^ LENGTH('b) - 2 ^ LENGTH('a)))
        = nat ((2 :: int) ^ LENGTH('b) - 2 ^ LENGTH('a))"
      using True by simp
    also have "\<dots> = nat ((2::int) ^ LENGTH('b)) - nat ((2::int) ^ LENGTH('a))"
      using pow_nn pow_le by (rule nat_diff_distrib)
    also have "\<dots> = 2 ^ LENGTH('b) - 2 ^ LENGTH('a)" by (simp add: nat_power_eq)
    finally show ?thesis using True by simp
  next
    case False
    thus ?thesis by simp
  qed

  have "unat ?S = nat (uint ?S)" by (rule unat_eq_nat_uint)
  also have "\<dots> = nat (uint x + of_bool (bit x ?MSB) * (2 ^ LENGTH('b) - 2 ^ LENGTH('a)))"
    using uint_S_eq by simp
  also have "\<dots> = nat (uint x) + nat (of_bool (bit x ?MSB) * (2 ^ LENGTH('b) - 2 ^ LENGTH('a)))"
    using ux_nn nonneg by (simp add: nat_add_distrib)
  also have "nat (uint x) = unat x" by simp
  also have "nat (of_bool (bit x ?MSB) * ((2 :: int) ^ LENGTH('b) - 2 ^ LENGTH('a)))
           = (if bit x ?MSB then 2 ^ LENGTH('b::len) - 2 ^ LENGTH('a::len) else 0)"
    by (rule nat_delta)
  finally show ?thesis by simp
qed



named_theorems rewrite_bv_sign_extend_ult_const_1 \<open>manually generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_1]:
  fixes x::"'a::len word" and m c n nm nm1 ::int
  shows "NO_MATCH cvc_a (undefined x m c n nm nm1) \<Longrightarrow>
  c_w = Word.Word c \<Longrightarrow>
  n = int LENGTH('a::len) \<Longrightarrow>
  nm = LENGTH('b::len) \<Longrightarrow>
  LENGTH('b) = LENGTH('a) + m \<Longrightarrow>
  m > 0 \<Longrightarrow>
  nm1 = n - 1 \<Longrightarrow>
  (c_w \<le> ((2::'b::len word) ^ (LENGTH('a) - 1))
   \<or> - ((2::'b::len word) ^ (LENGTH('a) - 1)) \<le> c_w) \<Longrightarrow>
  ((Word.signed_cast x::'b::len word) < c_w)
   =
  (x < (smtlib_extract nm1 0 c_w :: 'a::len word))"
proof -
  assume n_eq: "n = int LENGTH('a)"
     and lb_a: "LENGTH('b) = LENGTH('a) + m"
     and m_pos: "m > 0"
     and nm1_eq: "nm1 = n - 1"
     and cond: "c_w \<le> ((2::'b::len word) ^ (LENGTH('a) - 1))
              \<or> - ((2::'b::len word) ^ (LENGTH('a) - 1)) \<le> c_w"

  have la_lt_lb: "LENGTH('a) < LENGTH('b)" using lb_a m_pos by linarith
  have la_le_lb: "LENGTH('a) \<le> LENGTH('b)" using la_lt_lb by simp
  have msb_lt_b: "LENGTH('a) - 1 < LENGTH('b)" using la_lt_lb by linarith
  have nm1p1_nat: "nat (nm1 + 1) = LENGTH('a)" using nm1_eq n_eq by simp

  let ?MSB = "LENGTH('a) - Suc 0"
  let ?delta = "(2::nat) ^ LENGTH('b) - 2 ^ LENGTH('a)"
  let ?clo = "smtlib_extract nm1 0 c_w :: 'a::len word"

  have unat_S: "unat (Word.signed_cast x :: 'b word)
              = unat x + (if bit x ?MSB then ?delta else 0)"
    using unat_scast_widen_aux[OF la_le_lb, of x] .

  have ux_lt: "unat x < 2 ^ LENGTH('a)" by (simp add: unsigned_less)
  have ucw_lt: "unat c_w < 2 ^ LENGTH('b)" by (simp add: unsigned_less)

  have clo_bit: "\<And>i. i < LENGTH('a) \<Longrightarrow> bit ?clo i = bit c_w i"
  proof -
    fix i :: nat assume i_lt: "i < LENGTH('a)"
    have "?clo = slice 0 (take_bit LENGTH('a) (c_w :: 'b word) :: 'b word)"
      unfolding smtlib_extract_def using nm1p1_nat by simp
    moreover have "bit (slice 0 (take_bit LENGTH('a) (c_w :: 'b word) :: 'b word) :: 'a word) i
                  = bit c_w i"
      using i_lt la_le_lb
      by (simp add: bit_slice_iff bit_take_bit_iff min_def)
    ultimately show "bit ?clo i = bit c_w i" by simp
  qed



    have  "int (unat ?clo) = int (unat c_w mod 2 ^ LENGTH('a))"
    proof -
      have "uint ?clo = take_bit LENGTH('a) (uint c_w)"
      proof (rule bit_eqI)
        fix i :: nat assume "possible_bit TYPE(int) i"
        show "bit (uint ?clo) i = bit (take_bit LENGTH('a) (uint c_w)) i"
        proof (cases "i < LENGTH('a)")
          case True
          have "bit (uint ?clo) i = bit ?clo i"
            using True by (simp add: bit_uint_iff)
          also have "\<dots> = bit c_w i" using True clo_bit by simp
          also have "\<dots> = bit (uint c_w) i"
            using test_bit_def' by auto
          also have "\<dots> = bit (take_bit LENGTH('a) (uint c_w)) i"
            using True by (simp add: bit_take_bit_iff)
          finally show ?thesis .
        next
          case False
          hence "\<not> bit (uint ?clo) i" by (simp add: bit_uint_iff)
          moreover have "\<not> bit (take_bit LENGTH('a) (uint c_w)) i"
            using False by (simp add: bit_take_bit_iff)
          ultimately show ?thesis by simp
        qed
      qed


  then have unat_clo: "unat ?clo = unat c_w mod 2 ^ LENGTH('a)"
    using nat_eq_iff[THEN iffD2]
    by (metis unat_eq_nat_uint unat_ucast unsigned_ucast_eq)
   
      thus ?thesis
        by (metis nat_int of_nat_mod of_nat_numeral of_nat_power
                  take_bit_eq_mod unat_eq_nat_uint)
    qed

  have pow_pos: "(0 :: 'b word) < (2 :: 'b word) ^ (LENGTH('a) - 1)"
  proof -
    have "(2 :: 'b word) ^ (LENGTH('a) - 1) \<noteq> 0" using msb_lt_b by simp
    thus ?thesis
      by (simp add: word_gt_0)
  qed
  have uint_pow: "uint ((2 :: 'b word) ^ (LENGTH('a) - 1)) = 2 ^ (LENGTH('a) - 1)"
    using pow_pos uint_2p by blast
  have pow_n_eq: "unat ((2 :: 'b word) ^ (LENGTH('a) - 1)) = 2 ^ (LENGTH('a) - 1)"
    using uint_pow by (simp add: unat_eq_nat_uint nat_power_eq)

  have pow_lt_b_int: "(2 :: int) ^ (LENGTH('a) - 1) < 2 ^ LENGTH('b)"
    using msb_lt_b by simp
  have pow_pos_int: "(0 :: int) < 2 ^ (LENGTH('a) - 1)" by simp
  have uint_neg: "uint (- ((2 :: 'b word) ^ (LENGTH('a) - 1)))
                = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
  proof -
    have "uint (- ((2 :: 'b word) ^ (LENGTH('a) - 1)))
        = - uint ((2 :: 'b word) ^ (LENGTH('a) - 1)) mod 2 ^ LENGTH('b)"
      by (rule uint_word_ariths(4))
    also have "\<dots> = - ((2 :: int) ^ (LENGTH('a) - 1)) mod 2 ^ LENGTH('b)"
      using uint_pow by simp
    also have "\<dots> = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
      using pow_pos_int pow_lt_b_int by (simp add: zmod_zminus1_eq_if)
    finally show ?thesis .
  qed
  have negpow_eq: "unat (- ((2 :: 'b word) ^ (LENGTH('a) - 1)))
                 = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
  proof -
    have pow_nn: "(0 :: int) \<le> 2 ^ (LENGTH('a) - 1)" by simp
    have pow_le_b: "(2 :: int) ^ (LENGTH('a) - 1) \<le> 2 ^ LENGTH('b)"
      using pow_lt_b_int by simp
    have "unat (- ((2 :: 'b word) ^ (LENGTH('a) - 1)))
        = nat (uint (- ((2 :: 'b word) ^ (LENGTH('a) - 1))))"
      by (rule unat_eq_nat_uint)
    also have "\<dots> = nat (2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1))" using uint_neg by simp
    also have "\<dots> = nat (2 ^ LENGTH('b)) - nat (2 ^ (LENGTH('a) - 1))"
      using pow_nn pow_le_b by (rule nat_diff_distrib)
    also have "\<dots> = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
      by (simp add: nat_power_eq)
    finally show ?thesis .
  qed

  have cond_unat: "unat c_w \<le> 2 ^ (LENGTH('a) - 1)
                 \<or> 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) \<le> unat c_w"
    using cond pow_n_eq negpow_eq word_le_nat_alt by metis

  have la_eq: "LENGTH('a) = Suc ?MSB" by simp
  have pow_la_eq: "(2::nat) ^ LENGTH('a) = 2 * 2 ^ ?MSB"
    by (metis la_eq power_Suc)
  have pow_la_le_b: "(2::nat) ^ LENGTH('a) \<le> 2 ^ LENGTH('b)" using la_le_lb by simp
  have two_msb_le_b: "2 * (2::nat) ^ ?MSB \<le> 2 ^ LENGTH('b)" using pow_la_le_b pow_la_eq by simp

  have bit_iff_unat_ge: "bit x ?MSB \<longleftrightarrow> (2::nat) ^ ?MSB \<le> unat x"
  proof -
    have ux_lt_2msb: "unat x < 2 * 2 ^ ?MSB" using ux_lt pow_la_eq by simp
    have d_pos: "(0::nat) < 2 ^ ?MSB" by simp
    have div_lt2: "unat x div 2 ^ ?MSB < 2"
      using ux_lt_2msb by (simp add: less_mult_imp_div_less)
    hence div_01: "unat x div 2 ^ ?MSB = 0 \<or> unat x div 2 ^ ?MSB = 1" by linarith

    have "bit x ?MSB \<longleftrightarrow> bit (unat x :: nat) ?MSB"
      by (simp add: bit_unsigned_iff)
    also have "\<dots> \<longleftrightarrow> odd (unat x div 2 ^ ?MSB)"
      by (simp add: bit_iff_odd_drop_bit drop_bit_eq_div)
    also have "\<dots> \<longleftrightarrow> unat x div 2 ^ ?MSB = 1" using div_01 by auto
    also have "\<dots> \<longleftrightarrow> (2::nat) ^ ?MSB \<le> unat x"
    proof
      assume "unat x div 2 ^ ?MSB = 1"
      hence "0 < unat x div 2 ^ ?MSB" by simp
      thus "(2::nat) ^ ?MSB \<le> unat x"
        using d_pos div_greater_zero_iff by metis
    next
      assume "(2::nat) ^ ?MSB \<le> unat x"
      hence "0 < unat x div 2 ^ ?MSB"
        using d_pos div_greater_zero_iff by metis
      thus "unat x div 2 ^ ?MSB = 1" using div_lt2 by linarith
    qed
    finally show ?thesis .
  qed

  have unat_clo_low: "unat c_w \<le> 2 ^ (LENGTH('a) - 1) \<Longrightarrow> unat ?clo = unat c_w"
  proof -
    assume cw_low: "unat c_w \<le> 2 ^ (LENGTH('a) - 1)"
    have "unat c_w < (2::nat) ^ LENGTH('a)" using cw_low pow_la_eq
      by (simp add: order_le_less_trans)
    thus ?thesis
      using \<open>int (unat (smtlib_extract (nm1::int) 0 (c_w::'b::len word))) = int (unat c_w mod (2::nat) ^ LENGTH('a::len))\<close> mod_less
        nat_int.Rep_eqD by presburger
  qed

  have unat_clo_high: "(2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) \<le> unat c_w
       \<Longrightarrow> unat ?clo = unat c_w - ((2::nat) ^ LENGTH('b) - 2 ^ LENGTH('a))"
  proof -
    assume cw_high: "(2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) \<le> unat c_w"

    have power_split: "(2::nat) ^ LENGTH('b) = 2 ^ LENGTH('a) * 2 ^ (LENGTH('b) - LENGTH('a))"
      using la_le_lb by (metis le_add_diff_inverse power_add)

    have delta_mult: "?delta = (2 ^ (LENGTH('b) - LENGTH('a)) - 1) * (2::nat) ^ LENGTH('a)"
    proof -
      have "(2 ^ (LENGTH('b) - LENGTH('a)) - 1) * (2::nat) ^ LENGTH('a)
          = 2 ^ (LENGTH('b) - LENGTH('a)) * 2 ^ LENGTH('a) - 1 * 2 ^ LENGTH('a)"
        by (rule diff_mult_distrib)
      also have "\<dots> = 2 ^ ((LENGTH('b) - LENGTH('a)) + LENGTH('a)) - 2 ^ LENGTH('a)"
        by (simp add: power_add)
      also have "(LENGTH('b) - LENGTH('a)) + LENGTH('a) = LENGTH('b)" using la_le_lb by simp
      finally show ?thesis by simp
    qed

    have msb_pow_lt_la_pow: "(2::nat) ^ (LENGTH('a) - 1) \<le> 2 ^ LENGTH('a)" by simp
    have cw_ge_delta: "?delta \<le> unat c_w"
    proof -
      have "?delta \<le> (2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
        using msb_pow_lt_la_pow pow_la_le_b by linarith
      thus ?thesis using cw_high by simp
    qed

    have delta_plus_la: "?delta + (2::nat) ^ LENGTH('a) = 2 ^ LENGTH('b)"
      using pow_la_le_b by simp
    have diff_lt_la: "unat c_w - ?delta < (2::nat) ^ LENGTH('a)"
      using ucw_lt cw_ge_delta delta_plus_la by linarith

    have "unat c_w mod (2::nat) ^ LENGTH('a)
        = ((unat c_w - ?delta) + ?delta) mod 2 ^ LENGTH('a)"
      using cw_ge_delta by simp
    also have "\<dots> = ((unat c_w - ?delta) + (2 ^ (LENGTH('b) - LENGTH('a)) - 1) * 2 ^ LENGTH('a))
                       mod 2 ^ LENGTH('a)"
      using delta_mult by simp
    also have "\<dots> = (unat c_w - ?delta) mod 2 ^ LENGTH('a)"
      by (rule mod_mult_self1)
    also have "\<dots> = unat c_w - ?delta" using diff_lt_la by simp
    finally show ?thesis
      by (metis \<open>int (unat (smtlib_extract (nm1::int) 0 (c_w::'b::len word))) = int (unat c_w mod (2::nat) ^ LENGTH('a::len))\<close>
          nat_int)
  qed

  show "((Word.signed_cast x::'b::len word) < c_w) = (x < ?clo)"
  proof (cases "bit x ?MSB")
    case False
    have ux_lt_msb: "unat x < (2::nat) ^ ?MSB"
      using False bit_iff_unat_ge by linarith
    have unat_S_eq: "unat (Word.signed_cast x :: 'b word) = unat x"
      using False unat_S by simp
    from cond_unat show ?thesis
    proof
      assume cw_low: "unat c_w \<le> 2 ^ (LENGTH('a) - 1)"
      have unat_clo_eq: "unat ?clo = unat c_w" using cw_low unat_clo_low by simp
      have "((Word.signed_cast x :: 'b word) < c_w) = (unat x < unat c_w)"
        using unat_S_eq word_less_nat_alt by metis
      also have "\<dots> = (unat x < unat ?clo)" using unat_clo_eq by simp
      also have "\<dots> = (x < ?clo)" using word_less_nat_alt by metis
      finally show ?thesis .
    next
      assume cw_high: "(2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) \<le> unat c_w"
      have msb_le_high: "(2::nat) ^ ?MSB \<le> 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
        using two_msb_le_b by auto
      have lhs_lt: "unat x < unat c_w"
        using ux_lt_msb msb_le_high cw_high by linarith
      have is_lt: "(Word.signed_cast x :: 'b word) < c_w"
        using lhs_lt unat_S_eq word_less_nat_alt by metis
      have unat_clo_eq: "unat ?clo = unat c_w - ?delta" using cw_high unat_clo_high by simp
      have clo_ge_msb: "(2::nat) ^ ?MSB \<le> unat ?clo"
      proof -
        have "?delta + (2::nat) ^ ?MSB \<le> 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
          using pow_la_eq pow_la_le_b by auto
        hence "?delta + (2::nat) ^ ?MSB \<le> unat c_w" using cw_high by linarith
        thus ?thesis using unat_clo_eq by linarith
      qed
      have rhs_lt: "unat x < unat ?clo" using ux_lt_msb clo_ge_msb by linarith
      have is_rhs: "x < ?clo" using rhs_lt word_less_nat_alt by metis
      show ?thesis using is_lt is_rhs by simp
    qed
  next
    case True
    have ux_ge: "(2::nat) ^ ?MSB \<le> unat x" using True bit_iff_unat_ge by simp
    have unat_S_eq: "unat (Word.signed_cast x :: 'b word) = unat x + ?delta"
      using True unat_S by simp
    from cond_unat show ?thesis
    proof
      assume cw_low: "unat c_w \<le> 2 ^ (LENGTH('a) - 1)"
      have unat_S_ge: "(2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) \<le> unat (Word.signed_cast x :: 'b word)"
      proof -
        have "(2::nat) ^ LENGTH('b) - 2 ^ ?MSB = ?delta + 2 ^ ?MSB"
          using pow_la_eq pow_la_le_b by linarith
        also have "\<dots> \<le> unat x + ?delta" using ux_ge by linarith
        finally show ?thesis using unat_S_eq by simp
      qed
      have cw_lt: "unat c_w \<le> 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
        using cw_low two_msb_le_b pow_la_eq by auto
      have not_lt: "\<not> (Word.signed_cast x :: 'b word) < c_w"
        using unat_S_ge cw_lt word_less_nat_alt[of "Word.signed_cast x :: 'b word" c_w]
        by linarith
      have unat_clo_eq: "unat ?clo = unat c_w" using cw_low unat_clo_low by simp
      have not_rhs: "\<not> x < ?clo"
      proof -
        have "unat c_w \<le> unat x"
          using cw_low ux_ge by auto
        thus ?thesis using unat_clo_eq word_less_nat_alt[of x ?clo] by linarith
      qed
      show ?thesis using not_lt not_rhs by simp
    next
      assume cw_high: "(2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) \<le> unat c_w"
      have unat_clo_eq: "unat ?clo = unat c_w - ?delta" using cw_high unat_clo_high by simp
      have "((Word.signed_cast x :: 'b word) < c_w) = (unat x + ?delta < unat c_w)"
        using unat_S_eq word_less_nat_alt by metis
      also have "\<dots> = (unat x < unat c_w - ?delta)"
      proof -
        have "?delta \<le> unat c_w"
        proof -
          have "?delta \<le> (2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
            using pow_la_le_b
            by (simp add: diff_le_mono2)
          thus ?thesis using cw_high by simp
        qed
        thus ?thesis by linarith
      qed
      also have "\<dots> = (unat x < unat ?clo)" using unat_clo_eq by simp
      also have "\<dots> = (x < ?clo)" using word_less_nat_alt by metis
      finally show ?thesis .
    qed
  qed
qed


(*
(define-cond-rule bv-sign-extend-ult-const-2
  ((x ?BitVec) (m Int) (c Int) (nm Int) (nm1 Int))
  (def
    (n (@bvsize x))
    (a (bvshl (@bv 1 nm) (@bv (- n 1) nm))) ; 1 << (n-1)
    (b (bvshl (bvnot (@bv 0 nm)) (@bv (- n 1) nm))) ; ~0 << (n-1)
  )
  (and (bvult a (@bv c nm)) (bvule (@bv c nm) b) (= nm1 (- n 1)))
  (bvult (sign_extend m x) (@bv c nm))
  (= (extract nm1 nm1 x) (@bv 0 1)))
*)

named_theorems rewrite_bv_sign_extend_ult_const_2 \<open>manually generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_2]:
  fixes x::"'a::len word" and m c n nm nm1 ::int
  shows "NO_MATCH cvc_a (undefined x m c n nm nm1) \<Longrightarrow>
  c_w = Word.Word c \<Longrightarrow>
  n = int LENGTH('a) \<Longrightarrow>
  nm = LENGTH('b) \<Longrightarrow>
  LENGTH('b) = LENGTH('a) + m \<Longrightarrow>
  m > 0 \<Longrightarrow>
  nm1 = n - 1 \<Longrightarrow>
  ((2::'b::len word) ^ (LENGTH('a) - 1)) < c_w \<Longrightarrow>
  c_w \<le> - ((2::'b::len word) ^ (LENGTH('a) - 1)) \<Longrightarrow>
  ((Word.signed_cast x::'b::len word) < c_w)
   =
  ((smtlib_extract nm1 nm1 x :: 1 word) = 0)"
proof -
  assume n_eq: "n = int LENGTH('a)"
     and lb_a: "LENGTH('b) = LENGTH('a) + m"
     and m_pos: "m > 0"
     and nm1_eq: "nm1 = n - 1"
     and lower_cond: "((2::'b::len word) ^ (LENGTH('a) - 1)) < c_w"
     and upper_cond: "c_w \<le> - ((2::'b::len word) ^ (LENGTH('a) - 1))"

  have la_lt_lb: "LENGTH('a) < LENGTH('b)" using lb_a m_pos by linarith
  have la_le_lb: "LENGTH('a) \<le> LENGTH('b)" using la_lt_lb by simp
  have msb_lt_b: "LENGTH('a) - 1 < LENGTH('b)" using la_lt_lb by linarith

  let ?MSB = "LENGTH('a) - Suc 0"
  let ?delta = "(2::nat) ^ LENGTH('b) - 2 ^ LENGTH('a)"

  have unat_S: "unat (Word.signed_cast x :: 'b word)
              = unat x + (if bit x ?MSB then ?delta else 0)"
    using unat_scast_widen_aux[OF la_le_lb, of x] .

  have ux_lt: "unat x < 2 ^ LENGTH('a)" by (simp add: unsigned_less)

  \<comment> \<open>unat of @{term \<open>(2::'b word) ^ (LENGTH('a) - 1)\<close>}\<close>
  have pow_pos: "(0 :: 'b word) < (2 :: 'b word) ^ (LENGTH('a) - 1)"
  proof -
    have "(2 :: 'b word) ^ (LENGTH('a) - 1) \<noteq> 0" using msb_lt_b by simp
    thus ?thesis
      by (simp add: word_gt_0)
  qed
  have uint_pow: "uint ((2 :: 'b word) ^ (LENGTH('a) - 1)) = 2 ^ (LENGTH('a) - 1)"
    using pow_pos uint_2p by blast
  have pow_n_eq: "unat ((2 :: 'b word) ^ (LENGTH('a) - 1)) = 2 ^ (LENGTH('a) - 1)"
    using uint_pow by (simp add: unat_eq_nat_uint nat_power_eq)

  \<comment> \<open>unat of @{term \<open>- ((2::'b word) ^ (LENGTH('a) - 1))\<close>}\<close>
  have pow_lt_b_int: "(2 :: int) ^ (LENGTH('a) - 1) < 2 ^ LENGTH('b)"
    using msb_lt_b by simp
  have pow_pos_int: "(0 :: int) < 2 ^ (LENGTH('a) - 1)" by simp
  have uint_neg: "uint (- ((2 :: 'b word) ^ (LENGTH('a) - 1)))
                = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
  proof -
    have "uint (- ((2 :: 'b word) ^ (LENGTH('a) - 1)))
        = - uint ((2 :: 'b word) ^ (LENGTH('a) - 1)) mod 2 ^ LENGTH('b)"
      by (rule uint_word_ariths(4))
    also have "\<dots> = - (power (2 :: int)  (LENGTH('a) - 1)) mod 2 ^ LENGTH('b)"
      using uint_pow by simp
    also have "\<dots> = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
      using pow_pos_int pow_lt_b_int by (simp add: zmod_zminus1_eq_if)
    finally show ?thesis .
  qed
  have negpow_eq: "unat (- ((2 :: 'b word) ^ (LENGTH('a) - 1)))
                 = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
  proof -
    have pow_nn: "(0 :: int) \<le> 2 ^ (LENGTH('a) - 1)" by simp
    have pow_le_b: "(2 :: int) ^ (LENGTH('a) - 1) \<le> 2 ^ LENGTH('b)"
      using pow_lt_b_int by simp
    have "unat (- ((2 :: 'b word) ^ (LENGTH('a) - 1)))
        = nat (uint (- ((2 :: 'b word) ^ (LENGTH('a) - 1))))"
      by (rule unat_eq_nat_uint)
    also have "\<dots> = nat (2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1))" using uint_neg by simp
    also have "\<dots> = nat (2 ^ LENGTH('b)) - nat (2 ^ (LENGTH('a) - 1))"
      using pow_nn pow_le_b by (rule nat_diff_distrib)
    also have "\<dots> = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
      by (simp add: nat_power_eq)
    finally show ?thesis .
  qed

  have lower: "2 ^ (LENGTH('a) - 1) < unat c_w"
    using lower_cond pow_n_eq word_less_nat_alt by metis
  have upper: "unat c_w \<le> 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
    using upper_cond negpow_eq word_le_nat_alt by metis

  have la_eq: "LENGTH('a) = Suc ?MSB" by simp
  have pow_la_eq: "(2::nat) ^ LENGTH('a) = 2 * 2 ^ ?MSB" 

  \<comment> \<open>Translate @{term \<open>bit x ?MSB\<close>} to a threshold on @{term \<open>unat x\<close>}.\<close>
    by (metis la_eq power_Suc)
  have bit_iff_unat_ge: "bit x ?MSB \<longleftrightarrow> (2::nat) ^ ?MSB \<le> unat x"
  proof -
    have ux_lt_2msb: "unat x < 2 * 2 ^ ?MSB" using ux_lt pow_la_eq by simp
    have d_pos: "(0::nat) < 2 ^ ?MSB" by simp
    have div_lt2: "unat x div 2 ^ ?MSB < 2"
      using ux_lt_2msb by (simp add: less_mult_imp_div_less)
    hence div_01: "unat x div 2 ^ ?MSB = 0 \<or> unat x div 2 ^ ?MSB = 1" by linarith

    have "bit x ?MSB \<longleftrightarrow> bit (unat x :: nat) ?MSB"
      by (simp add: bit_unsigned_iff)
    also have "\<dots> \<longleftrightarrow> odd (unat x div 2 ^ ?MSB)"
      by (simp add: bit_iff_odd_drop_bit drop_bit_eq_div)
    also have "\<dots> \<longleftrightarrow> unat x div 2 ^ ?MSB = 1" using div_01 by auto
    also have "\<dots> \<longleftrightarrow> (2::nat) ^ ?MSB \<le> unat x"
    proof
      assume "unat x div 2 ^ ?MSB = 1"
      hence "0 < unat x div 2 ^ ?MSB" by simp
      thus "(2::nat) ^ ?MSB \<le> unat x"
        using d_pos div_greater_zero_iff by metis
    next
      assume "(2::nat) ^ ?MSB \<le> unat x"
      hence "0 < unat x div 2 ^ ?MSB"
        using d_pos div_greater_zero_iff by metis
      thus "unat x div 2 ^ ?MSB = 1" using div_lt2 by linarith
    qed
    finally show ?thesis .
  qed

  have nm1_msb: "nm1 = int ?MSB"
    using nm1_eq n_eq
    by (simp add: Suc_leI)
  have extr_msb: "(smtlib_extract nm1 nm1 x :: 1 word) = (if bit x ?MSB then 1 else 0)"
    using smtlib_extract_msb_eq[of x] nm1_msb by simp

  show ?thesis
  proof (cases "bit x ?MSB")
    case True
    have ux_ge: "(2::nat) ^ ?MSB \<le> unat x" using True bit_iff_unat_ge by simp
    have unat_S_True: "unat (Word.signed_cast x :: 'b word) = unat x + ?delta"
      using True unat_S by simp
    have unat_S_ge: "2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) \<le> unat (Word.signed_cast x :: 'b word)"
    proof -
      have la_pow_le: "(2 :: nat) ^ LENGTH('a) \<le> 2 ^ LENGTH('b)" using la_le_lb by simp
      have msb_pow_le_la_pow: "(2 :: nat) ^ ?MSB \<le> 2 ^ LENGTH('a)"
        using pow_la_eq by simp
      have msb_pow_pos: "(0 :: nat) < 2 ^ ?MSB" by simp
      \<comment> \<open>Key identity: with @{term \<open>2^LENGTH('a) = 2 * 2^?MSB\<close>}, we have
            @{term \<open>2^LENGTH('b) - 2^?MSB = 2^LENGTH('b) - 2^LENGTH('a) + 2^?MSB\<close>}.\<close>
      have arith_id: "(2::nat) ^ LENGTH('b) - 2 ^ ?MSB
                    = 2 ^ LENGTH('b) - 2 ^ LENGTH('a) + 2 ^ ?MSB"
        using la_pow_le pow_la_eq msb_pow_pos by linarith
      have "(2::nat) ^ LENGTH('b) - 2 ^ ?MSB \<le> unat x + ?delta"
        using arith_id ux_ge by linarith
      thus ?thesis using unat_S_True by simp
    qed
    have not_lt: "\<not> (Word.signed_cast x :: 'b word) < c_w"
      using unat_S_ge upper word_less_nat_alt[of "Word.signed_cast x :: 'b word" c_w]
      by simp
    have not_extr_0: "(smtlib_extract nm1 nm1 x :: 1 word) \<noteq> 0"
      using True extr_msb by simp
    show ?thesis using not_lt not_extr_0 by simp
  next
    case False
    have ux_lt_msb: "unat x < (2::nat) ^ ?MSB"
      using False bit_iff_unat_ge by linarith
    have unat_S_False: "unat (Word.signed_cast x :: 'b word) = unat x"
      using False unat_S by simp
    have lt: "unat (Word.signed_cast x :: 'b word) < unat c_w"
      using unat_S_False ux_lt_msb lower by simp
    have is_lt: "(Word.signed_cast x :: 'b word) < c_w"
      using lt word_less_nat_alt[of "Word.signed_cast x :: 'b word" c_w] by simp
    have is_extr_0: "(smtlib_extract nm1 nm1 x :: 1 word) = 0"
      using False extr_msb by simp
    show ?thesis using is_lt is_extr_0 by simp
  qed
qed


(*
(define-cond-rule bv-sign-extend-ult-const-3
  ((x ?BitVec) (m Int) (c Int) (nm Int) (nm1 Int))
  (def
    (n (@bvsize x))
    (clo (extract nm1 0 (@bv c nm)))
    (a (bvshl (@bv 1 nm) (@bv (- n 1) nm))) ; 1 << (n-1)
    (b (bvshl (bvnot (@bv 0 nm)) (@bv (- n 1) nm))) ; ~0 << (n-1)
  )
  (and (or (bvult (@bv c nm) a) (bvuge (@bv c nm) (bvnot a))) (= nm1 (- n 1)))
  (bvult (@bv c nm) (sign_extend m x))
  (bvult clo x))
*)

named_theorems rewrite_bv_sign_extend_ult_const_3 \<open>manually generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_3]:
  fixes x::"'a::len word" and m c n nm nm1 ::int
  shows "NO_MATCH cvc_a (undefined x m c n nm nm1) \<Longrightarrow>
  c_w = Word.Word c \<Longrightarrow>
  n = int LENGTH('a) \<Longrightarrow>
  nm = LENGTH('b) \<Longrightarrow>
  LENGTH('b) = LENGTH('a) + m \<Longrightarrow>
  m > 0 \<Longrightarrow>
  nm1 = n - 1 \<Longrightarrow>
  (c_w < ((2::'b::len word) ^ (LENGTH('a) - 1))
   \<or> not ((2::'b::len word) ^ (LENGTH('a) - 1)) \<le> c_w) \<Longrightarrow>
  (c_w < (Word.signed_cast x::'b::len word))
   =
  ((smtlib_extract nm1 0 c_w :: 'a::len word) < x)"
proof -
  assume n_eq: "n = int LENGTH('a)"
     and lb_a: "LENGTH('b) = LENGTH('a) + m"
     and m_pos: "m > 0"
     and nm1_eq: "nm1 = n - 1"
     and cond: "c_w < ((2::'b::len word) ^ (LENGTH('a) - 1))
              \<or> not ((2::'b::len word) ^ (LENGTH('a) - 1)) \<le> c_w"

  have la_lt_lb: "LENGTH('a) < LENGTH('b)" using lb_a m_pos by linarith
  have la_le_lb: "LENGTH('a) \<le> LENGTH('b)" using la_lt_lb by simp
  have msb_lt_b: "LENGTH('a) - 1 < LENGTH('b)" using la_lt_lb by linarith
  have nm1p1_nat: "nat (nm1 + 1) = LENGTH('a)" using nm1_eq n_eq by simp

  let ?MSB = "LENGTH('a) - Suc 0"
  let ?delta = "(2::nat) ^ LENGTH('b) - 2 ^ LENGTH('a)"
  let ?clo = "smtlib_extract nm1 0 c_w :: 'a::len word"

  have unat_S: "unat (Word.signed_cast x :: 'b word)
              = unat x + (if bit x ?MSB then ?delta else 0)"
    using unat_scast_widen_aux[OF la_le_lb, of x] .

  have ux_lt: "unat x < 2 ^ LENGTH('a)" by (simp add: unsigned_less)
  have ucw_lt: "unat c_w < 2 ^ LENGTH('b)" by (simp add: unsigned_less)

  have clo_bit: "\<And>i. i < LENGTH('a) \<Longrightarrow> bit ?clo i = bit c_w i"
  proof -
    fix i :: nat assume i_lt: "i < LENGTH('a)"
    have "?clo = slice 0 (take_bit LENGTH('a) (c_w :: 'b word) :: 'b word)"
      unfolding smtlib_extract_def using nm1p1_nat by simp
    moreover have "bit (slice 0 (take_bit LENGTH('a) (c_w :: 'b word) :: 'b word) :: 'a word) i
                  = bit c_w i"
      using i_lt la_le_lb
      by (simp add: bit_slice_iff bit_take_bit_iff min_def)
    ultimately show "bit ?clo i = bit c_w i" by simp
  qed

  have "int (unat ?clo) = int (unat c_w mod 2 ^ LENGTH('a))"
    proof -
      have "uint ?clo = take_bit LENGTH('a) (uint c_w)"
      proof (rule bit_eqI)
        fix i :: nat assume "possible_bit TYPE(int) i"
        show "bit (uint ?clo) i = bit (take_bit LENGTH('a) (uint c_w)) i"
        proof (cases "i < LENGTH('a)")
          case True
          have "bit (uint ?clo) i = bit ?clo i"
            using True by (simp add: bit_uint_iff)
          also have "\<dots> = bit c_w i" using True clo_bit by simp
          also have "\<dots> = bit (uint c_w) i"
            by (metis word_test_bit_def)
          also have "\<dots> = bit (take_bit LENGTH('a) (uint c_w)) i"
            using True by (simp add: bit_take_bit_iff)
          finally show ?thesis .
        next
          case False
          hence "\<not> bit (uint ?clo) i" by (simp add: bit_uint_iff)
          moreover have "\<not> bit (take_bit LENGTH('a) (uint c_w)) i"
            using False by (simp add: bit_take_bit_iff)
          ultimately show ?thesis by simp
        qed
      qed
      thus ?thesis
        by (metis Typedef_Morphisms.unat_of_nat Word.of_nat_unat unat_eq_nat_uint unsigned_ucast_eq)
    qed

  then have unat_clo: "unat ?clo = unat c_w mod 2 ^ LENGTH('a)"
  using nat_eq_iff[THEN iffD2] by force

  have pow_pos: "(0 :: 'b word) < (2 :: 'b word) ^ (LENGTH('a) - 1)"
  proof -
    have "(2 :: 'b word) ^ (LENGTH('a) - 1) \<noteq> 0" using msb_lt_b by simp
    thus ?thesis
      by (simp add: word_gt_0)
  qed
  have uint_pow: "uint ((2 :: 'b word) ^ (LENGTH('a) - 1)) = 2 ^ (LENGTH('a) - 1)"
    using pow_pos uint_2p by blast
  have pow_n_eq: "unat ((2 :: 'b word) ^ (LENGTH('a) - 1)) = 2 ^ (LENGTH('a) - 1)"
    using uint_pow by (simp add: unat_eq_nat_uint nat_power_eq)

  have pow_lt_b_int: "(2 :: int) ^ (LENGTH('a) - 1) < 2 ^ LENGTH('b)"
    using msb_lt_b by simp
  have pow_pos_int: "(0 :: int) < 2 ^ (LENGTH('a) - 1)" by simp
  have uint_neg: "uint (- ((2 :: 'b word) ^ (LENGTH('a) - 1)))
                = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
  proof -
    have "uint (- ((2 :: 'b word) ^ (LENGTH('a) - 1)))
        = - uint ((2 :: 'b word) ^ (LENGTH('a) - 1)) mod 2 ^ LENGTH('b)"
      by (rule uint_word_ariths(4))
    also have "\<dots> = - ((2 :: int) ^ (LENGTH('a) - 1)) mod 2 ^ LENGTH('b)"
      using uint_pow by simp
    also have "\<dots> = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
      using pow_pos_int pow_lt_b_int by (simp add: zmod_zminus1_eq_if)
    finally show ?thesis .
  qed
  have negpow_eq: "unat (- ((2 :: 'b word) ^ (LENGTH('a) - 1)))
                 = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
  proof -
    have pow_nn: "(0 :: int) \<le> 2 ^ (LENGTH('a) - 1)" by simp
    have pow_le_b: "(2 :: int) ^ (LENGTH('a) - 1) \<le> 2 ^ LENGTH('b)"
      using pow_lt_b_int by simp
    have "unat (- ((2 :: 'b word) ^ (LENGTH('a) - 1)))
        = nat (uint (- ((2 :: 'b word) ^ (LENGTH('a) - 1))))"
      by (rule unat_eq_nat_uint)
    also have "\<dots> = nat (2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1))" using uint_neg by simp
    also have "\<dots> = nat (2 ^ LENGTH('b)) - nat (2 ^ (LENGTH('a) - 1))"
      using pow_nn pow_le_b by (rule nat_diff_distrib)
    also have "\<dots> = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
      by (simp add: nat_power_eq)
    finally show ?thesis .
  qed

  have not_pow_eq: "unat (not ((2 :: 'b word) ^ (LENGTH('a) - 1)))
                 = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) - 1"
  proof -
    have pow_nz: "(2 :: 'b word) ^ (LENGTH('a) - 1) \<noteq> 0" using msb_lt_b by simp
    have neg_nz: "- ((2 :: 'b word) ^ (LENGTH('a) - 1)) \<noteq> 0" using pow_nz by simp
    have not_minus: "not ((2 :: 'b word) ^ (LENGTH('a) - 1)) = - ((2 :: 'b word) ^ (LENGTH('a) - 1)) - 1"
      by (simp add: not_eq_complement)
    have "unat (not ((2 :: 'b word) ^ (LENGTH('a) - 1)))
        = unat (- ((2 :: 'b word) ^ (LENGTH('a) - 1)) - 1)" using not_minus by simp
    also have "\<dots> = unat (- ((2 :: 'b word) ^ (LENGTH('a) - 1))) - 1"
      using neg_nz by (rule unat_minus_one)
    also have "\<dots> = 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) - 1" using negpow_eq by simp
    finally show ?thesis .
  qed

  have cond_unat: "unat c_w < 2 ^ (LENGTH('a) - 1)
                 \<or> 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) - 1 \<le> unat c_w"
    using cond pow_n_eq not_pow_eq word_less_nat_alt word_le_nat_alt by metis

  have la_eq: "LENGTH('a) = Suc ?MSB" by simp
  have pow_la_eq: "(2::nat) ^ LENGTH('a) = 2 * 2 ^ ?MSB"
    by (metis la_eq power_Suc)
  have pow_la_le_b: "(2::nat) ^ LENGTH('a) \<le> 2 ^ LENGTH('b)" using la_le_lb by simp
  have two_msb_le_b: "2 * (2::nat) ^ ?MSB \<le> 2 ^ LENGTH('b)" using pow_la_le_b pow_la_eq by simp
  have two_msb_lt_b: "2 * (2::nat) ^ ?MSB < 2 ^ LENGTH('b)"
  proof -
    have "LENGTH('a) < LENGTH('b)" using la_lt_lb .
    hence "(2::nat) ^ LENGTH('a) < 2 ^ LENGTH('b)" by simp
    thus ?thesis using pow_la_eq by simp
  qed

  have bit_iff_unat_ge: "bit x ?MSB \<longleftrightarrow> (2::nat) ^ ?MSB \<le> unat x"
  proof -
    have ux_lt_2msb: "unat x < 2 * 2 ^ ?MSB" using ux_lt pow_la_eq by simp
    have d_pos: "(0::nat) < 2 ^ ?MSB" by simp
    have div_lt2: "unat x div 2 ^ ?MSB < 2"
      using ux_lt_2msb by (simp add: less_mult_imp_div_less)
    hence div_01: "unat x div 2 ^ ?MSB = 0 \<or> unat x div 2 ^ ?MSB = 1" by linarith

    have "bit x ?MSB \<longleftrightarrow> bit (unat x :: nat) ?MSB"
      by (simp add: bit_unsigned_iff)
    also have "\<dots> \<longleftrightarrow> odd (unat x div 2 ^ ?MSB)"
      by (simp add: bit_iff_odd_drop_bit drop_bit_eq_div)
    also have "\<dots> \<longleftrightarrow> unat x div 2 ^ ?MSB = 1" using div_01 by auto
    also have "\<dots> \<longleftrightarrow> (2::nat) ^ ?MSB \<le> unat x"
    proof
      assume "unat x div 2 ^ ?MSB = 1"
      hence "0 < unat x div 2 ^ ?MSB" by simp
      thus "(2::nat) ^ ?MSB \<le> unat x"
        using d_pos div_greater_zero_iff by metis
    next
      assume "(2::nat) ^ ?MSB \<le> unat x"
      hence "0 < unat x div 2 ^ ?MSB"
        using d_pos div_greater_zero_iff by metis
      thus "unat x div 2 ^ ?MSB = 1" using div_lt2 by linarith
    qed
    finally show ?thesis .
  qed

  have unat_clo_low: "unat c_w < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> unat ?clo = unat c_w"
  proof -
    assume cw_low: "unat c_w < 2 ^ (LENGTH('a) - 1)"
    have "unat c_w < (2::nat) ^ LENGTH('a)" using cw_low pow_la_eq by simp
    thus ?thesis using unat_clo by simp
  qed

  have unat_clo_high: "(2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) - 1 \<le> unat c_w
       \<Longrightarrow> unat ?clo = unat c_w - ((2::nat) ^ LENGTH('b) - 2 ^ LENGTH('a))"
  proof -
    assume cw_high: "(2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) - 1 \<le> unat c_w"

    have power_split: "(2::nat) ^ LENGTH('b) = 2 ^ LENGTH('a) * 2 ^ (LENGTH('b) - LENGTH('a))"
      using la_le_lb by (metis le_add_diff_inverse power_add)

    have delta_mult: "?delta = (2 ^ (LENGTH('b) - LENGTH('a)) - 1) * (2::nat) ^ LENGTH('a)"
    proof -
      have "(2 ^ (LENGTH('b) - LENGTH('a)) - 1) * (2::nat) ^ LENGTH('a)
          = 2 ^ (LENGTH('b) - LENGTH('a)) * 2 ^ LENGTH('a) - 1 * 2 ^ LENGTH('a)"
        by (rule diff_mult_distrib)
      also have "\<dots> = 2 ^ ((LENGTH('b) - LENGTH('a)) + LENGTH('a)) - 2 ^ LENGTH('a)"
        by (simp add: power_add)
      also have "(LENGTH('b) - LENGTH('a)) + LENGTH('a) = LENGTH('b)" using la_le_lb by simp
      finally show ?thesis by simp
    qed

    have cw_ge_delta: "?delta \<le> unat c_w"
    proof -
      have msb_eq: "(2::nat) ^ (LENGTH('a) - 1) = 2 ^ ?MSB" by simp
      have msb_pos: "(1::nat) \<le> 2 ^ ?MSB" by simp
      have "?delta + 1 \<le> (2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
        using pow_la_eq two_msb_le_b msb_eq msb_pos by linarith
      hence "?delta \<le> (2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) - 1" by linarith
      thus ?thesis using cw_high by linarith
    qed

    have delta_plus_la: "?delta + (2::nat) ^ LENGTH('a) = 2 ^ LENGTH('b)"
      using pow_la_le_b by simp
    have diff_lt_la: "unat c_w - ?delta < (2::nat) ^ LENGTH('a)"
      using ucw_lt cw_ge_delta delta_plus_la by linarith

    have "unat c_w mod (2::nat) ^ LENGTH('a)
        = ((unat c_w - ?delta) + ?delta) mod 2 ^ LENGTH('a)"
      using cw_ge_delta by simp
    also have "\<dots> = ((unat c_w - ?delta) + (2 ^ (LENGTH('b) - LENGTH('a)) - 1) * 2 ^ LENGTH('a))
                       mod 2 ^ LENGTH('a)"
      using delta_mult by simp
    also have "\<dots> = (unat c_w - ?delta) mod 2 ^ LENGTH('a)"
      by (rule mod_mult_self1)
    also have "\<dots> = unat c_w - ?delta" using diff_lt_la by simp
    finally show ?thesis using unat_clo by simp
  qed

  show "(c_w < (Word.signed_cast x::'b::len word)) = (?clo < x)"
  proof (cases "bit x ?MSB")
    case False
    have ux_lt_msb: "unat x < (2::nat) ^ ?MSB"
      using False bit_iff_unat_ge by linarith
    have unat_S_eq: "unat (Word.signed_cast x :: 'b word) = unat x"
      using False unat_S by simp
    from cond_unat show ?thesis
    proof
      assume cw_low: "unat c_w < 2 ^ (LENGTH('a) - 1)"
      have unat_clo_eq: "unat ?clo = unat c_w" using cw_low unat_clo_low by simp
      have "(c_w < (Word.signed_cast x :: 'b word)) = (unat c_w < unat x)"
        using unat_S_eq word_less_nat_alt by metis
      also have "\<dots> = (unat ?clo < unat x)" using unat_clo_eq by simp
      also have "\<dots> = (?clo < x)" using word_less_nat_alt by metis
      finally show ?thesis .
    next
      assume cw_high: "(2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) - 1 \<le> unat c_w"
      have cw_ge_msb: "(2::nat) ^ ?MSB \<le> unat c_w"
      proof -
        have "(2::nat) ^ ?MSB + 1 \<le> (2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) - 1 + 1"
          using pow_la_eq two_msb_lt_b by auto
        thus ?thesis using cw_high by linarith
      qed
      have not_lhs: "\<not> c_w < (Word.signed_cast x :: 'b word)"
        using ux_lt_msb cw_ge_msb unat_S_eq word_less_nat_alt[of c_w "Word.signed_cast x :: 'b word"]
        by linarith
      have unat_clo_eq: "unat ?clo = unat c_w - ?delta" using cw_high unat_clo_high by simp
      have clo_ge_msb_m1: "(2::nat) ^ ?MSB - 1 \<le> unat ?clo"
      proof -
        have "?delta + (2::nat) ^ ?MSB - 1 \<le> 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) - 1"
          using pow_la_eq pow_la_le_b two_msb_lt_b by auto
        hence "?delta + (2::nat) ^ ?MSB - 1 \<le> unat c_w" using cw_high by linarith
        thus ?thesis using unat_clo_eq by linarith
      qed
      have not_rhs: "\<not> ?clo < x"
        using ux_lt_msb clo_ge_msb_m1 word_less_nat_alt[of ?clo x] by linarith
      show ?thesis using not_lhs not_rhs by simp
    qed
  next
    case True
    have ux_ge: "(2::nat) ^ ?MSB \<le> unat x" using True bit_iff_unat_ge by simp
    have unat_S_eq: "unat (Word.signed_cast x :: 'b word) = unat x + ?delta"
      using True unat_S by simp
    from cond_unat show ?thesis
    proof
      assume cw_low: "unat c_w < 2 ^ (LENGTH('a) - 1)"
      have unat_S_ge: "(2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) \<le> unat (Word.signed_cast x :: 'b word)"
      proof -
        have "(2::nat) ^ LENGTH('b) - 2 ^ ?MSB = ?delta + 2 ^ ?MSB"
          using pow_la_eq pow_la_le_b by linarith
        also have "\<dots> \<le> unat x + ?delta" using ux_ge by linarith
        finally show ?thesis using unat_S_eq by simp
      qed
      have cw_lt_high: "unat c_w < 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
        using cw_low pow_la_eq two_msb_lt_b by auto
      have is_lhs: "c_w < (Word.signed_cast x :: 'b word)"
        using unat_S_ge cw_lt_high word_less_nat_alt[of c_w "Word.signed_cast x :: 'b word"]
        by linarith
      have unat_clo_eq: "unat ?clo = unat c_w" using cw_low unat_clo_low by simp
      have is_rhs: "?clo < x"
      proof -
        have "unat ?clo < unat x" using unat_clo_eq cw_low ux_ge by auto
        thus ?thesis using word_less_nat_alt[of ?clo x] by simp
      qed
      show ?thesis using is_lhs is_rhs by simp
    next
      assume cw_high: "(2::nat) ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) - 1 \<le> unat c_w"
      have unat_clo_eq: "unat ?clo = unat c_w - ?delta" using cw_high unat_clo_high by simp
      have cw_ge_delta: "?delta \<le> unat c_w"
      proof -
        have "?delta + 1 \<le> 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1)"
          using pow_la_eq pow_la_le_b two_msb_lt_b
          using ux_lt by auto
        hence "?delta \<le> 2 ^ LENGTH('b) - 2 ^ (LENGTH('a) - 1) - 1" by linarith
        thus ?thesis using cw_high by linarith
      qed
      have "(c_w < (Word.signed_cast x :: 'b word)) = (unat c_w < unat x + ?delta)"
        using unat_S_eq word_less_nat_alt by metis
      also have "\<dots> = (unat c_w - ?delta < unat x)" using cw_ge_delta by linarith
      also have "\<dots> = (unat ?clo < unat x)" using unat_clo_eq by simp
      also have "\<dots> = (?clo < x)" using word_less_nat_alt by metis
      finally show ?thesis .
    qed
  qed
qed



(*
(define-cond-rule bv-sign-extend-ult-const-4
  ((x ?BitVec) (m Int) (c Int) (nm Int) (nm1 Int))
  (def
    (n (@bvsize x))
    (a (bvshl (@bv 1 nm) (@bv (- n 1) nm))) ; 1 << (n-1)
    (b (bvshl (bvnot (@bv 0 nm)) (@bv (- n 1) nm))) ; ~0 << (n-1)
  )
  (and (bvule (bvnot b) (@bv c nm)) (bvule (@bv c nm) (bvnot a)) (= nm1 (- n 1)))
  (bvult (@bv c nm) (sign_extend m x))
  (= (extract nm1 nm1 x) (@bv 1 1)))
*)






end
