theory BV_Rewrites_Simplification
  imports BV_Rewrites_Lemmas 
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
     "(smtlib_extract (int (LENGTH('a) - 1)) (int (LENGTH('a) - 1)) x :: 1 word) = 1"                            
     using smtlib_extract_msb_eq[of x] True by simp                                                              
   have lhs_ashr: "smtlib_bvashr x w_amount = not (smtlib_bvlshr (not x) w_amount)"                              
     unfolding smtlib_bvashr_def using msb_one by simp                                                           
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
     unfolding smtlib_bvashr_def using msb_zero by simp
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

    \<Longrightarrow> is_pow2 n = True
    \<Longrightarrow> exponent = (size - (floorlog 2 (nat n))) - 1
    \<Longrightarrow> u = size - e - 1

    \<Longrightarrow> (n_w::'b::len word) = Word.Word n
    \<Longrightarrow> LENGTH('a) + LENGTH('c) = LENGTH('b)
    \<Longrightarrow> LENGTH('c) = u + 1 \<Longrightarrow> u \<ge> 0
    \<Longrightarrow> exponent = int (LENGTH('a))
    \<Longrightarrow>
(cvc_list_left (*) xs (z * (cvc_list_right (*) n_w ys ::'b::len word)))
   = (word_cat (smtlib_extract u 0 (cvc_list_left (*) xs (cvc_list_right (*) z ys))::'c::len word) (0::'a::len word))"
  sorry


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



(*
(define-cond-rule bv-udiv-pow2-not-one
  ((x ?BitVec) (v Int) (n Int) (power Int) (nm1 Int))
  (and (int.ispow2 v) (> v 1) (= power (int.log2 v)) (= nm1 (- n 1)))
  (bvudiv x (@bv v n))
  (concat (@bv 0 power) (extract nm1 power x)))
*)



(*
(define-rule bv-udiv-zero
  ((x ?BitVec) (n Int))
  (bvudiv x (@bv 0 n))
  (bvnot (@bv 0 n)))

Note: Constraint LENGTH('a) = n is not needed so omitted

*)

named_theorems rewrite_bv_udiv_zero \<open>automatically_generated\<close>

(*This is an example where Isabelle and SMTLIB semantics are completely different*)

lemma [rewrite_bv_udiv_zero]:
  fixes x::"'a ::len word" and n::int
  shows  "NO_MATCH (cvc_a) (undefined x n)
 \<Longrightarrow> x div 0 = 0"
  by simp


(*
(define-rule bv-udiv-one ((x ?BitVec) (n Int))
  (bvudiv x (@bv 1 n))
  x)
*)


(*
(define-cond-rule bv-urem-pow2-not-one
  ((x ?BitVec) (v Int) (n Int) (nmp Int) (pm1 Int))
  (def (power (int.log2 v)))
  (and (int.ispow2 v) (> v 1) (= nmp (- n power)) (= pm1 (- power 1)))
  (bvurem x (@bv v n))
  (concat (@bv 0 nmp) (extract pm1 0 x)))
*)



(*
(define-rule bv-urem-one
  ((x ?BitVec) (n Int))
  (bvurem x (@bv 1 n))
  (@bv 0 n))
*)


(*
(define-cond-rule bv-urem-self
  ((x ?BitVec) (w Int))
  (= w (@bvsize x))
  (bvurem x x)
  (@bv 0 w))
*)


(*
(define-rule bv-shl-zero
  ((a ?BitVec) (n Int))
  (bvshl (@bv 0 n) a)
  (@bv 0 n))
*)


(*
(define-rule bv-lshr-zero
  ((a ?BitVec) (n Int))
  (bvlshr (@bv 0 n) a)
  (@bv 0 n))
*)


(*
(define-rule bv-ashr-zero
  ((a ?BitVec) (n Int))
  (bvashr (@bv 0 n) a)
  (@bv 0 n))
*)

named_theorems rewrite_bv_ashr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined a n) 
    \<Longrightarrow> signed_drop_bit (unat a) 0 = 0"
  by auto

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



(*
(define-rule bv-ult-one
  ((x ?BitVec) (n Int))
  (bvult x (@bv 1 n))
  (= x (@bv 0 n)))
*)


(*
(define-cond-rule bv-slt-zero
  ((x ?BitVec) (n Int) (nm1 Int))
  (= nm1 (- n 1))
  (bvslt x (@bv 0 n))
  (= (extract nm1 nm1 x) (@bv 1 1)))
*)



(*
(define-cond-rule bv-merge-sign-extend-1
  ((x ?BitVec) (i Int) (j Int) (k Int))
  (= k (+ i j))
  (sign_extend i (sign_extend j x))
  (sign_extend k x)
  )
*)


(*
(define-cond-rule bv-merge-sign-extend-2
  ((x ?BitVec) (i Int) (j Int) (k Int))
  (and (> j 0) (= k (+ i j)))
  (sign_extend i (zero_extend j x))
  (zero_extend k x)
  )
*)


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
*)


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
*)



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
*)


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
