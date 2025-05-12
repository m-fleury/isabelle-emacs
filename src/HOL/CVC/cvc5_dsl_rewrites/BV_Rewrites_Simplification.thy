theory BV_Rewrites_Simplification
  imports BV_Rewrites_Lemmas 
begin

(*Status May 2025: 70 rules total*)

(*
(define-rule bv-ite-equal-children ((c (_ BitVec 1)) (x ?BitVec)) (bvite c x x) x)
*)

named_theorems rewrite_bv_ite_equal_children \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_children]:
  fixes c::"1 word" and x::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined c x)
    \<Longrightarrow> (if bit c (0::nat) then x else x) = x"
  by auto


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
    \<Longrightarrow> (if bit c (0::nat) then Word.Word (0::int) else Word.Word (1::int)) = not c"
  by (metis (mono_tags, opaque_lifting) Word.of_nat_unat Word_eq_word_of_int add.group_left_neutral bit.compl_one bit.compl_zero bit_0_eq inc_le len_of_numeral_defs(2) mask_1 nat_int nle_le nth_0 take_bit_minus_one_eq_mask test_bit_1 ucast_id unsigned_1 unsigned_of_int word_neq_0_conv word_of_int_0 word_of_int_1 word_of_int_neg_1 word_order.extremum)


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
    \<Longrightarrow> (if bit c (0::nat) then Word.Word (1::int) else Word.Word (0::int)) = c"
  by (metis (mono_tags, opaque_lifting) Word.of_nat_unat add.group_left_neutral bit.compl_zero len_of_numeral_defs(2) mask_1 nat_int nth_0 one_word_def take_bit_minus_one_eq_mask ucast_id unsigned_1 unsigned_of_int word_and_1 word_ao_nth word_exists_nth word_of_int_neg_1 word_plus_and_or_coroll2 zero_word_def)


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
  by auto


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
  shows "(if bit c0 (0::nat) then t0 else if bit c0 (0::nat) then t1 else e1) =
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
  shows "(if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0
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
  shows "(if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else t1) =
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
  shows "(if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else e1) =
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
  shows "(if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t0 else e1) =
   (if bit (not (or c0 c1)) (0::nat) then e1 else t0)"
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
  shows "(if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t1 else t0) =
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
  shows "push_bit (unat (Word.Word (0::int))) x = x"
  by auto


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
  shows "NO_MATCH cvc_a (undefined x amount sz en)
    \<Longrightarrow> (amount < int(size x)) = True
    \<Longrightarrow> en = int (size x) - (1 + amount)
    \<Longrightarrow> LENGTH('b) = amount \<Longrightarrow> LENGTH('a) = LENGTH('c) + LENGTH('b) \<Longrightarrow> LENGTH('c) = en + 1
    \<Longrightarrow>
   (push_bit (nat amount) x ::'a::len word)=
   word_cat
    (smt_extract (nat en) (nat (0::int)) x::'c::len word)
    (0::'b::len word)"
  apply (subst word_unat_eq_iff)
  apply (simp only: unsigned_push_bit_eq unat_word_cat)
  apply (subst unat_smt_extract)
     apply simp_all
  apply (simp only: take_bit_push_bit)
  apply (rule arg_cong2[where f = push_bit])
   apply simp
  apply (rule arg_cong2[where f = take_bit])
   apply simp
  apply simp
  done

(*
(define-cond-rule bv-shl-by-const-2
  ((x ?BitVec) (amount Int) (sz Int) (w Int))
  (and (>= amount (@bvsize x)) (= w (@bvsize x)))
  (bvshl x (@bv amount sz))
  (@bv 0 w))
*)

named_theorems rewrite_bv_shl_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_2]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow> LENGTH('b) = sz \<longrightarrow> amount < 2^LENGTH('b) \<longrightarrow>
   push_bit (unat (Word.Word amount::'b::len word)) x = (Word.Word (0::int)::'a::len word)"
  by (simp add: take_bit_int_eq_self unsigned_of_int word_size)


(*
(define-rule bv-lshr-by-const-0
  ((x ?BitVec) (sz Int))
  (bvlshr x (@bv 0 sz))
  x)
*)

named_theorems rewrite_bv_lshr_by_const_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_0]:
  fixes x::"'a ::len word"  and sz::"int"
  shows "LENGTH('b) = sz \<longrightarrow>
   drop_bit (unat (Word.Word 0::'b::len word)) x = x"
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

lemma [rewrite_bv_lshr_by_const_1]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
   LENGTH('a) = LENGTH('b) + LENGTH('c) \<longrightarrow>
  (nat (int (size x) - (1::int))) < LENGTH('a) \<longrightarrow>
  0 \<le> amount \<longrightarrow>
(nat amount) \<le> (nat (int (size x) - (1::int))) \<longrightarrow>
  LENGTH('c) = 1 + ((nat (int (size x) - (1::int))) - (nat amount)) \<longrightarrow>
amount < 2^LENGTH('d) \<longrightarrow>
LENGTH('d) = sz \<longrightarrow>
   (drop_bit (unat (Word.Word amount::'d::len word)) x::'a::len word) =
   word_cat (Word.Word (0::int)::'b::len word)
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x::'c::len word)"
  apply rule+
proof-
  assume a0: "amount < int (size x)"
    "LENGTH('a) = LENGTH('b) + LENGTH('c)"
    "nat (int (size x) - (1::int)) < LENGTH('a)"
    "(0::int) \<le> amount"
    "nat amount \<le> nat (int (size x) - (1::int))"
    "LENGTH('c) = (1::nat) + (nat (int (size x) - (1::int)) - nat amount)"
    "amount < (2::int) ^ LENGTH('d)"
    "int LENGTH('d) = sz"
  have t0: "min (LENGTH('c::len) + nat amount) LENGTH('a) = LENGTH('a)"
    by (smt (verit, ccfv_SIG) a0(5) a0(6) add_diff_cancel_left' diff_add diff_diff_left less_le_not_le min.commute min.idem min.order_iff nat_minus_as_int nat_neq_iff of_nat_1 word_size)
   have t1: "(take_bit LENGTH('d) amount) = amount"
    apply (subst take_bit_int_eq_self[of amount "LENGTH('d)" ])
    apply (simp add: a0)
    using a0(7) apply auto[1]
    by auto

  have "(word_cat (Word.Word (0::int)::'b::len word)
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x::'c::len word)::'a::len word)
  = word_cat (0::'b::len word)
    (smt_extract (size x - 1) (nat amount) x::'c::len word)"
    by (metis nat_minus_as_int of_nat_1 zero_word_def)
  also have "...
  = word_cat (0::'b word) (slice (nat amount) (take_bit (size x) x)::'c::len word)"
    unfolding smt_extract_def
    by simp
  also have "...
  = word_cat (0::'b word) (slice (nat amount) x::'c::len word)"
    using take_bit_length_eq
    by (simp add: word_size)
  also have "...
  = word_cat (0::'b word) (slice1 (LENGTH('a::len) - nat amount) x::'c::len word)"
    using slice_def[of "nat amount"]
    by (simp add: slice_def)
 also have "...
  = word_cat (0::'b word) (ucast (drop_bit (LENGTH('a::len) - (LENGTH('a::len) - nat amount)) x)::'c::len word)"
   using slice1_def[of "(LENGTH('a::len) - nat amount)" x]
   by (smt (verit, del_insts) One_nat_def Suc_diff_1 a0(2) a0(5) a0(6) diff_add_inverse diff_less_mono2 len_gt_0 nat_diff_distrib' nat_int nat_one_as_int of_nat_0_le_iff ordered_cancel_comm_monoid_diff_class.add_diff_assoc plus_1_eq_Suc size_word.rep_eq)
 also have "...
  = word_cat (0::'b word) (ucast (drop_bit (nat amount) x)::'c::len word)"
   by (metis a0(1) diff_diff_cancel less_le_not_le nat_le_iff word_size)
 also have "...
  =  push_bit LENGTH('c::len) (ucast (0::'b word)) + ucast (ucast (drop_bit (nat amount) x)::'c::len word)"
   using word_cat_eq
   by blast
also have "...
  =  push_bit LENGTH('c::len) 0 + ucast (ucast (drop_bit (nat amount) x)::'c::len word)"
  using unsigned_ucast_eq[of "(drop_bit (nat amount) x)"]
  by auto
also have "...
  = ucast (ucast (drop_bit (nat amount) x)::'c::len word)"
  by simp
also have "...
  = (take_bit LENGTH('c::len) (unsigned (drop_bit (nat amount) x)::'a::len word))"
  using unsigned_ucast_eq[of "(drop_bit (nat amount) x)"]
  by (smt (verit, del_insts))
also have "...
  = (take_bit LENGTH('c::len) (drop_bit (nat amount) (take_bit LENGTH('a::len) (unsigned x))))"
  using unsigned_drop_bit_eq[of "nat amount" x] by simp
also have "...
  = drop_bit (nat amount) (take_bit (LENGTH('c::len) + nat amount) (take_bit LENGTH('a::len) (unsigned x)))"
  using take_bit_drop_bit[of "LENGTH('c)" "nat amount" "(take_bit LENGTH('a::len) (unsigned x))"]
  by blast
also have "...
  = drop_bit (nat amount) (take_bit LENGTH('a::len) (unsigned x))"
  using take_bit_take_bit
  by (smt (verit, ccfv_threshold) One_nat_def Suc_pred a0(5) a0(6) diff_add group_cancel.add1 int_ops(2) len_gt_0 nat_int_comparison(3) nat_minus_as_int plus_1_eq_Suc size_word.rep_eq take_bit_word_beyond_length_eq)
also have "...
  = drop_bit (nat amount) (unsigned x)"
  by force
  finally have "(word_cat (Word.Word (0::int)::'b::len word)
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x::'c::len word)::'a::len word)
  = drop_bit (nat amount) (unsigned x)"
    by blast

    then show "(drop_bit (unat (Word.Word amount::'d::len word)) x::'a::len word) =
   word_cat (Word.Word (0::int)::'b::len word)
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x::'c::len word)"
            by (simp add: a0(4) a0(7) unat_eq_nat_uint word_of_int_inverse)
        qed


(*
(define-cond-rule bv-lshr-by-const-2
  ((x ?BitVec) (amount Int) (sz Int))
  (>= amount (@bvsize x))
  (bvlshr x (@bv amount sz))
  (@bv 0 sz))
*)


(*
(define-rule bv-ashr-by-const-0
  ((x ?BitVec) (sz Int))
  (bvashr x (@bv 0 sz))
  x)
*)


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


(*
(define-cond-rule bv-ashr-by-const-2
  ((x ?BitVec) (amount Int) (sz Int) (nm1 Int) (rn Int))
  (and (>= amount (@bvsize x)) (= nm1 (- (@bvsize x) 1)) (= rn (@bvsize x)))
  (bvashr x (@bv amount sz))
  (repeat rn (extract nm1 nm1 x)))
*)



(*
(define-cond-rule bv-and-concat-pullup
  ((xs ?BitVec :list) (ws ?BitVec :list) (y ?BitVec)
   (z ?BitVec) (ys ?BitVec :list)
   (nxm1 Int) (ny Int) (nym1 Int))
  (def
    (nx (@bvsize (bvand xs ws)))
  )
  (and (= ny (@bvsize y)) (= nxm1 (- nx 1)) (= nym1 (- (@bvsize y) 1)))
  (bvand xs (concat ys z y) ws)
  (concat
    (bvand (extract nxm1 ny (bvand xs ws)) (concat ys z))
    (bvand (extract nym1 0 (bvand xs ws)) y)
  ))
*)

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

lemma [rewrite_bv_xor_concat_pullup]:
  fixes xs::"'a::len word" and amount::"int" and sz::"int" and en::"int"
  shows "NO_MATCH cvc_a (undefined x amount sz en)
    \<Longrightarrow> (amount < int(size x)) = True
    \<Longrightarrow> en = int (size x) - (1 + amount)
    \<Longrightarrow> LENGTH('b) = amount \<Longrightarrow> LENGTH('a) = LENGTH('c) + LENGTH('b) \<Longrightarrow> LENGTH('c) = en + 1
    \<Longrightarrow>
   (push_bit (nat amount) x ::'a::len word)=
   word_cat
    (smt_extract (nat en) (nat (0::int)) x::'c::len word)
    (0::'b::len word)"



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
*)


(*
(define-cond-rule bv-xor-ones ((xs ?BitVec :list) (zs ?BitVec :list) (n Int) (w Int))
  (= n (- (int.pow2 w) 1))
  (bvxor xs (@bv n w) zs)
  (bvnot (bvxor xs zs)))
*)


(*
(define-rule bv-xor-not ((x ?BitVec) (y ?BitVec))
  (bvxor (bvnot x) (bvnot y)) (bvxor x y))
*)


(*
(define-rule bv-not-idemp ((x ?BitVec))
  (bvnot (bvnot x)) x)
*)


(*
(define-rule bv-ult-zero-1
  ((x ?BitVec) (n Int))
  (bvult (@bv 0 n) x)
  (not (= x (@bv 0 n))))
*)


(*
(define-rule bv-ult-zero-2
  ((x ?BitVec) (n Int))
  (bvult x (@bv 0 n))
  false)
*)


(*
(define-rule bv-ult-self ((x ?BitVec)) (bvult x x) false)
*)


(*
(define-rule bv-lt-self ((x ?BitVec)) (bvslt x x) false)
*)


(*
(define-rule bv-ule-self ((x ?BitVec)) (bvule x x) true)
*)


(*
(define-rule bv-ule-zero
  ((x ?BitVec) (n Int))
  (bvule x (@bv 0 n))
  (= x (@bv 0 n)))
*)


named_theorems rewrite_bv_ule_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_zero]:
  fixes x::"'a ::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) 
    \<Longrightarrow> LENGTH('a) = n
    \<Longrightarrow> (x \<le> 0) = (x = 0)"
  by auto

(*
(define-rule bv-zero-ule
  ((x ?BitVec) (n Int))
  (bvule (@bv 0 n) x)
  true)
*)


(*
(define-rule bv-sle-self ((x ?BitVec)) (bvsle x x) true)
*)



(*
(define-cond-rule bv-ule-max ((x ?BitVec) (n Int) (w Int))
  (and (= w (@bvsize x)) (= n (- (int.pow2 (@bvsize x)) 1)))
  (bvule x (@bv n w)) true)
*)


(*
(define-rule bv-not-ult ((x ?BitVec) (y ?BitVec))
  (not (bvult x y))
  (bvule y x))
*)



(*
(define-cond-rule bv-mult-pow2-1
  ((xs ?BitVec :list) (ys ?BitVec :list) (z ?BitVec) (size Int) (n Int) (exponent Int) (u Int))
  (def (e (int.log2 n)))
  (and (int.ispow2 n) (= exponent e) (= u (- (- size e) 1)))
  (bvmul xs z (@bv n size) ys)
  (concat
    (extract u 0 (bvmul xs z ys))
    (@bv 0 exponent)))
*)


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
*)


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