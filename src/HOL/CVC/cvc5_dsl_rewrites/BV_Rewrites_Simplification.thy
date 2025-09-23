theory BV_Rewrites_Simplification
  imports BV_Rewrites_Lemmas 
begin

(*Status May 2025: 70 rules total*)

(*
(define-rule bv-ite-equal-children ((c (_ BitVec 1)) (x ?BitVec)) (bvite c x x) x)

TEST: NO
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

TEST: NO
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

TEST: NO
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

TEST: NO
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

TEST: NO
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

TEST: NO
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

TEST: NO
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

TEST: NO
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

TEST: NO
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

TEST: NO
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

TEST: YES
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

TEST: NO
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

TEST: YES
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

TEST: NO
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

TEST: NO
TEST: PROOF
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
  apply (simp add:unsigned_of_int)
  unfolding smt_extract_def
  apply (subst Suc_nat_eq_nat_zadd1)
   apply simp_all
  apply (subst word_size[of x])
  apply (subst take_bit_length_eq[of x])
  unfolding slice_def slice1_def
  sorry

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

fun word_cat_rbl_left :: "bool list list \<Rightarrow> 'a ::len word \<Rightarrow> 'b::len  word" where
  "word_cat_rbl_left xs y = word_cat (of_bl (concat xs)::'b:: len word) y"

lemma bit_foldr_xor:
"bit (foldr xor xs y) n = foldr (\<noteq>) (map (\<lambda>x. bit x n) xs) (bit y n)"
  apply (induction xs)
   apply simp_all
  by (simp add: bit_xor_iff)

fun is_singleton_ListVar:: "'a cvc_ListVar \<Rightarrow> bool" where
 "is_singleton_ListVar (ListVar xs) = (length xs = 1)"
fun is_empty_ListVar:: "'a cvc_ListVar \<Rightarrow> bool" where
 "is_empty_ListVar (ListVar xs) = (length xs = 0)"

fun word_cat_helper::"('a::len word) cvc_ListVar \<Rightarrow> 'a::len word" where
"word_cat_helper (ListVar [x]) = x"

fun word_cat_helper_left::"('a::len word) cvc_ListVar \<Rightarrow> 'b::len word \<Rightarrow> 'c::len word" where
"word_cat_helper_left (ListVar [x]) y = (word_cat x y)"

fun word_cat_helper_empty_left::"('a::len word) cvc_ListVar \<Rightarrow> 'b::len word \<Rightarrow> 'b::len word" where
"word_cat_helper_empty_left (ListVar []) y = y"

lemmas [cvc_evaluate_bv] = word_cat_helper_def (*is_singleton_ListVar.simps is_empty_ListVar.simps*)

lemmas word_cat_helper_def = word_cat_helper_left.simps word_cat_helper_empty_left.simps

lemma helper:
"n \<le> size y \<Longrightarrow> bit (xor xs (word_cat x y)) n = bit (xor xs y) n"
  unfolding bit_xor_iff bit_word_cat_iff
  by (simp add: word_size)

lemma helper3:
" (xor x (foldr xor xs y)) = (foldr xor (x # xs) y)"
  by simp

lemma helper3b:
" (xor (foldr xor xs y) x) = (foldr xor (xs @ [y]) x)"
  apply (induction xs)
   apply simp_all
  
  by (simp add: xor.assoc)


lemma helper4:
" (foldr xor xs (foldr xor ys y)) = (foldr xor (xs @ ys) y)"
  by simp

lemma helper5:
"(0::int) \<le> m \<Longrightarrow>  m \<le> n \<Longrightarrow> nat n < LENGTH('b) \<Longrightarrow> int LENGTH('a) = n + (1::int) - m \<Longrightarrow>
 (smt_extract (nat n) (nat m) (foldr xor xs (y::'b::len word)::'b ::len word)::'a::len word) = foldr xor (map (smt_extract (nat n) (nat m)) xs) (smt_extract (nat n) (nat m) y)"
  apply (induction xs)
  apply simp_all
  apply (subst rewrite_bv_extract_bitwise_xor)
      apply (simp_all add: word_size)
  done

lemma helper6: 
" (0::nat) = nat (0::int)"
  by simp



lemma case1: 
 fixes xs::"('a::len word) list"
    and x::"('a::len word)"
    and y::"'b::len word"
    and z::"'c::len word"
    and n::"nat"
  assumes "n < LENGTH('b)" and  "n < LENGTH('a)"
  shows "bit ((xor (word_cat z y::'a::len word) x)) n = 
bit (xor (smt_extract n 0 y ::'a::len word) (smt_extract n 0 x)) n"
  apply (simp add: bit_xor_iff bit_smt_extract)
  by (simp_all add: bit_word_cat_iff assms)

lemma yip1: "slice n (xor a b) = (xor (slice n a) (slice n b))"
  unfolding slice_def slice1_def
  by (simp add: unsigned_xor_eq)

lemma yip2: "
 smt_extract n (0::nat) (foldr xor xs y) = foldr xor (map (smt_extract n  (0::nat)) xs) (smt_extract n (0::nat) y) "
  apply (induction xs)
   apply simp_all
  unfolding smt_extract_def
  subgoal for x xss
    apply (subst take_bit_xor[of "(Suc n)" x])
    apply (subst yip1)
    by presburger
  done

lemma yip3:
"n < LENGTH('a::len) \<Longrightarrow> LENGTH('a)  < LENGTH('b) \<Longrightarrow>
(map ((\<lambda>x::'b ::len word. bit x n) \<circ> smt_extract (LENGTH('a) - Suc (0::nat)) (0::nat)) xs') = (map ((\<lambda>x::'b word. bit x n)) (xs'::'b::len word list))"
  apply (induction xs')
   apply simp_all
  unfolding bit_smt_extract
  by simp_all

lemma yip4:
"n < LENGTH('a::len) \<Longrightarrow> LENGTH('a) < LENGTH('b::len) \<Longrightarrow> (map (smt_extract (LENGTH('a)) 0) (x#xs)) = y#ys 
\<Longrightarrow> 
 bit (foldr xor xs (x::'a word)) n = bit (foldr xor ys (y::'b word)) n"
  apply (induction xs)
   apply simp_all
  oops

definition xor_bin where
 "xor_bin \<equiv> foldr (\<lambda>(x::bool) y::bool. x = (\<not> y))"


definition bit_map where
 "bit_map n \<equiv> map (\<lambda>x::'a ::len word. bit x n) "

lemma smt_extract_over:
"a - Suc 0< LENGTH('b::len) \<Longrightarrow> n \<le> a -Suc 0 \<Longrightarrow> bit (smt_extract (a-Suc 0) (0::nat) t1::'b::len word) n = bit (t1::'a::len word) n"
  unfolding smt_extract_def
  by (simp add: nth_slice bit_take_bit_iff)

lemma smt_extract_shift:
"n \<ge> LENGTH('b) \<Longrightarrow> n < LENGTH('b) + LENGTH('c) \<Longrightarrow> n - LENGTH('b) < LENGTH('d) \<Longrightarrow> bit (smt_extract (LENGTH('b::len) + LENGTH('c::len) - Suc (0::nat)) LENGTH('b) (t1::'a::len word)::'d::len word ) (n - LENGTH('b))
= bit t1 n
"
  unfolding smt_extract_def
  by (simp add: nth_slice bit_take_bit_iff)





lemma rewrite_bv_xor_concat_pullup_lemma0:
  fixes t1::"('a::len word) "
    and t2::"('d::len word)"
    and y::"'c::len word"
  shows "LENGTH('a::len) = LENGTH('d) + LENGTH('c)
\<Longrightarrow>
   (xor (word_cat t2 y ::'a::len word) t1)
   =    
  (word_cat
    (xor (smt_extract (LENGTH('a) - 1) (LENGTH('c)) t1 ::'d::len word) t2 ::'d::len word)
    (xor (smt_extract (LENGTH('c) - 1) (nat 0)      t1 ::'c::len word) y  ::'c::len word)
  ::'a word)
   "
  apply (simp add: bang_eq)
  apply (rule allI)
  subgoal for n
    apply (simp add: bit_xor_iff bit_word_cat_iff bit_smt_extract)
    apply (cases "n < LENGTH('c)")
     apply simp_all
     apply blast
    by (metis add_diff_inverse_nat bit_imp_le_length le_add1 less_diff_conv2)
  done

lemma rewrite_bv_xor_concat_pullup_lemma1:
  fixes t1::"('a::len word)"
    and y::"'b::len word"
    and z::"'c::len word"
  shows "LENGTH('a) = LENGTH('b) + LENGTH('c)
\<Longrightarrow> LENGTH('b) \<ge> 1 \<Longrightarrow> LENGTH('a) \<ge> 1
\<Longrightarrow>
   (xor (word_cat z y ::'a ::len word) t1::'a word)
= 
  (word_cat
    (xor (smt_extract ( LENGTH('a) - 1) (LENGTH('b)) (t1 ::'a::len word)::'c::len word) (z::'c::len word) ::'c::len word)
    (xor (smt_extract (LENGTH('b) - 1)  (nat 0)      (t1 ::'a::len word)::'b::len word) (y::'b::len word) ::'b::len word)
    ::'a word)
"
  using rewrite_bv_xor_concat_pullup_lemma0 
  by (metis add.commute)
  
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

size xs = size ws = size z + size y
xs \<rightarrow> 'a word
ws \<rightarrow> 'a word

z \<longrightarrow> 'c word
y \<longrightarrow> 'b word
(concat z y)  \<longrightarrow> 'a word = 'b word + 'c word
(bvxor xs (concat ys (concat z y)) ws) \<longrightarrow> 'a word
(@bvsize (bvxor xs ws)) \<longrightarrow> 'a word
(concat ys z) \<longrightarrow> 'c word
(extract (- (@bvsize (bvxor xs ws)) 1) (@bvsize y) (bvxor xs ws)) \<longrightarrow> 'c word = ('a word)  - ('b word)
(extract (- (@bvsize y) 1) 0 (bvxor xs ws)) \<longrightarrow> 'b word
(concat
    (bvxor (extract (- (@bvsize (bvxor xs ws)) 1) (@bvsize y) (bvxor xs ws)) (concat ys z))
    (bvxor (extract (- (@bvsize y) 1) 0 (bvxor xs ws)) y)
  )) \<longrightarrow> 'a word = 'c word + 'b word

*)

lemma fold_a:"foldr xor (xs' @ ys') x = foldr xor (ys' @ xs') x "
  apply (induction xs')
   apply simp_all
  apply (induction ys')
   apply simp_all
  by (metis (mono_tags, opaque_lifting) foldr_append helper3 helper3b xor.commute)

lemma fold_b: "foldr xor (xs' @ word_cat z y # butlast ws') (last ws') = foldr xor (word_cat z y # xs' @ butlast ws') (last ws') "
  by (metis append_Cons fold_a helper3)

lemma rewrite_bv_xor_concat_pullup_empty :
  fixes xs::"('a::len word) cvc_ListVar"
    and ws::"('a::len word) cvc_ListVar"
    and y::"'b::len word"
    and z::"'c::len word"
    and ys::"('e::len word) cvc_ListVar"
  shows "LENGTH('a) = LENGTH('b) + LENGTH('c)
\<Longrightarrow> xs \<noteq> (ListVar []) \<Longrightarrow> ws \<noteq> (ListVar []) \<Longrightarrow> is_empty_ListVar ys
\<Longrightarrow>
   (cvc_list_left xor xs
     (cvc_list_right xor
      (word_cat z y ::'a ::len word)
       ws
     ::'a word)
   ::'a word)
= 
  (word_cat
    ( xor
      (smt_extract ( LENGTH('a) - 1) (LENGTH('b)) (cvc_list_both' xor xs ws ::'a::len word)::'c::len word)
      (z::'c::len word)
    ::'c::len word)
    (xor (smt_extract (LENGTH('b) - 1) (nat 0) (cvc_list_both' xor xs ws ::'a word)::'b::len word) y ::'b word)
  ::'a word)
   "
apply (cases xs)
  apply (cases ws)
  apply (cases ys)
  apply simp
  subgoal for xs' ws' ys'
      unfolding cvc_list_left_transfer
      apply (subst cvc_list_right_transfer_2)
       apply simp
      unfolding cvc_list_both_transfer'
         apply (simp only: helper3 helper4 helper3b)
      apply (subst fold_b)
      apply simp
      apply (subst rewrite_bv_xor_concat_pullup_lemma1[of z y "(foldr xor xs' (foldr xor (butlast ws') (last ws')))"])
         apply (simp_all add: le_def)
      done
    done


lemma rewrite_bv_xor_concat_pullup1:
  fixes xs::"('a::len word) cvc_ListVar"
    and ws::"('a::len word) cvc_ListVar"
    and y::"'b::len word"
    and z::"'c::len word"
    and ys::"('e::len word) cvc_ListVar"
    and nxm1::int and ny::int and nym1::int
shows "NO_MATCH cvc_a (undefined xs ws y z ys nxm1 ny nym1)
\<Longrightarrow> LENGTH('a) = LENGTH('b) + LENGTH('c)
\<Longrightarrow> xs \<noteq> (ListVar []) \<Longrightarrow> ws \<noteq> (ListVar []) \<Longrightarrow> is_empty_ListVar ys
\<Longrightarrow>
   (cvc_list_left xor xs
     (cvc_list_right xor
       (word_cat_helper_empty_left 
         ys
         (word_cat z y ::'a ::len word)
       ::'a::len word)
       ws
     ::'a word)
   ::'a word)
= 
  (word_cat
    ( xor
      (smt_extract ( LENGTH('a) - 1) (LENGTH('b)) (cvc_list_both' xor xs ws ::'a::len word)::'c::len word)
      (word_cat_helper_empty_left ys (z::'c::len word)::'c::len word)
    ::'c::len word)
    (xor (smt_extract (LENGTH('b) - 1) (nat 0) (cvc_list_both' xor xs ws ::'a word)::'b::len word) y ::'b word)
  ::'a word)
   "
  apply (cases ys)
  apply simp
 
  using rewrite_bv_xor_concat_pullup_empty[of xs ws ys z y] 
  by fastforce


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

lemma rewrite_bv_xor_concat_pullup2 :
  fixes xs::"('a::len word) cvc_ListVar"
    and ws::"('a::len word) cvc_ListVar"
    and y::"'b::len word"
    and z::"'c::len word"
    and ys::"('e::len word) cvc_ListVar"
    and nxm1::int and ny::int and nym1::int
  shows "NO_MATCH cvc_a (undefined xs ws y z ys nxm1 ny nym1)
\<Longrightarrow>LENGTH('c) + LENGTH('b) = LENGTH('d)
\<Longrightarrow> LENGTH('e) + LENGTH('d) = LENGTH('a)
\<Longrightarrow> LENGTH('f) = LENGTH('a) - LENGTH('b)
\<Longrightarrow> LENGTH('f) = LENGTH('c) + LENGTH('e)
\<Longrightarrow> LENGTH('f) + LENGTH('b) = LENGTH('a)

\<Longrightarrow> xs \<noteq> (ListVar []) \<Longrightarrow> ws \<noteq> (ListVar []) \<Longrightarrow> is_singleton_ListVar ys
\<Longrightarrow>
   (cvc_list_left xor xs
     (cvc_list_right xor
       (word_cat_helper_left 
         ys
         (word_cat z y ::'d ::len word)
       ::'a::len word)
       ws
     ::'a word)
   ::'a word)
= 
  (word_cat
    ( xor
      (smt_extract ( LENGTH('a) - 1) (LENGTH('b)) (cvc_list_both' xor xs ws ::'a::len word)::'f::len word)
      (word_cat_helper_left ys (z::'c::len word)::'f::len word)
    ::'f::len word)
    (xor (smt_extract (LENGTH('b) - 1) (nat 0) (cvc_list_both' xor xs ws ::'a word)::'b::len word) y ::'b word)
  ::'a word)
   "
  apply (cases xs)
  apply (cases ws)
  apply (cases ys)
  apply simp
  subgoal for xs' ws' ys'
    apply (cases ys')
     apply simp_all
    subgoal for y1 ys1
    proof-
      assume  a0:
        "LENGTH('e) + LENGTH('d) = LENGTH('a)"
    "LENGTH('c) + LENGTH('e) = LENGTH('a) - LENGTH('b)"
    "LENGTH('f) = LENGTH('a) - LENGTH('b)"
    "LENGTH('a) - LENGTH('b) + LENGTH('b) = LENGTH('a)"
    "xs' \<noteq> []"
    "ws' \<noteq> []"
    "ys1 = []"
    "xs = ListVar xs'"
    "ws = ListVar ws'"
    "ys = ListVar [y1]"
    "ys' = [y1]"
      obtain t1 where t1_def: "t1 \<equiv>  (cvc_list_both' xor (ListVar xs') (ListVar ws'))"
        by blast
      obtain t2 where t2_def: "t2 \<equiv>  (word_cat y1 z::'f::len word)"
        by blast


      have "cvc_list_left xor (ListVar xs') (cvc_list_right xor (word_cat y1 (word_cat z y::'d::len word)) (ListVar ws')) =
(xor (word_cat y1 (word_cat z y::'d::len word)) (cvc_list_both' xor (ListVar xs') (ListVar ws')) )"
        by (metis (no_types, lifting) \<open>(ws'::'a::len word list) \<noteq> []\<close> \<open>(xs'::'a::len word list) \<noteq> []\<close> cvc_list_both_transfer' cvc_list_left_transfer cvc_list_right_transfer_2 fold_b helper3 helper4)
      then have "cvc_list_left xor (ListVar xs') (cvc_list_right xor (word_cat y1 (word_cat z y::'d::len word)) (ListVar ws')) =
(xor (word_cat y1 (word_cat z y::'d::len word)) t1 )"
          using t1_def by simp
 then have "cvc_list_left xor (ListVar xs') (cvc_list_right xor (word_cat y1 (word_cat z y::'d::len word)) (ListVar ws')) =
(xor (word_cat (word_cat y1 z::'f::len word) y ::'a::len word) t1 )"
   apply (subst word_cat_on_word_cat[symmetric,of y1 z y, where 'a='f and 'b='a and 'd='d])
   using a0
   apply (simp_all add: a0 word_size)
   using a0(2) apply presburger
   using a0(1) a0(2) a0(4) apply linarith
   by (metis (no_types, lifting) a0(5) a0(6) cvc_list_both_transfer' cvc_list_left_transfer cvc_list_right_transfer_2 fold_b helper3 helper4 t1_def)
    then have "cvc_list_left xor (ListVar xs') (cvc_list_right xor (word_cat y1 (word_cat z y::'d::len word)) (ListVar ws')) =
(xor (word_cat (t2::'f::len word) y ::'a::len word) t1 )"
      using t2_def by simp
 then have "cvc_list_left xor (ListVar xs') (cvc_list_right xor (word_cat y1 (word_cat z y::'d::len word)) (ListVar ws')) =
word_cat (xor (smt_extract (LENGTH('a::len) - (1::nat)) LENGTH('b::len) t1) t2) (xor (smt_extract (LENGTH('b::len) - (1::nat)) (nat (0::int)) t1) y)"
   by (simp add: a0 rewrite_bv_xor_concat_pullup_lemma0[of t2 y t1])


  then    show "cvc_list_left xor (ListVar xs') (cvc_list_right xor (word_cat y1 (word_cat z y::'d::len word)) (ListVar ws')) =
    word_cat (xor (smt_extract (LENGTH('a) - Suc (0::nat)) LENGTH('b) (cvc_list_both' xor (ListVar xs') (ListVar ws'))) (word_cat y1 z)::'f::len word)
     (xor (smt_extract (LENGTH('b) - Suc (0::nat)) (0::nat) (cvc_list_both' xor (ListVar xs') (ListVar ws'))) y)"

    by (simp add: t1_def t2_def)
qed
  done
  done


  
(*    foldr neq (map bit_n xs')
     (bit (xor (smt_extract n (0::nat) y) (foldr xor (map (smt_extract n (0::nat)) (butlast ws')) (smt_extract n (0::nat) (last ws')))) n)

 =
    foldr neq (map (bit_n \<circ> smt_extract (LENGTH('b) - Suc (0::nat)) (0::nat)) xs')
     (foldr (\<lambda>(x::bool) y::bool. x = (\<not> y)) (map ((\<lambda>x::'b word. bit x n) \<circ> smt_extract (LENGTH('b) - Suc (0::nat)) (0::nat)) (butlast ws'))
       (bit (xor (smt_extract (LENGTH('b) - Suc (0::nat)) (0::nat) (last ws')) y) n))*)

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

         ''bv-xor-concat-pullup''
         xs ListVar [27::8 word]        8 word
         ws ListVar []                  8 word
         y 0                                                  1 word
         z smt_extract (nat (6::int)) (nat 0) (v0__::8 word)  7 word
         ys ListVar []
         7::int
         1
         0
       proposition:
         (27::8 word) XOR word_cat (smt_extract (nat (6::int)) (nat 0) (v0__::8 word)) 0 =
         word_cat (smt_extract (nat (7::int)) (nat 1) (27::8 word) XOR smt_extract (nat (6::int)) (nat 0) v0__)
          (smt_extract (nat 0) (nat 0) (27::8 word) XOR 0)

  (bvxor xs (concat ys (concat z y)) ws) =
   xs' XOR (word_cat z y) 
   has length xs' = length z + length y


         word_cat 

(bvxor (extract (- (@bvsize (bvxor xs ws)) 1) (@bvsize y) (bvxor xs ws)) (concat ys z))
(smt_extract (- (@bvsize xs') 1) (@bvsize y) xs' XOR z
  has length z


    (bvxor (extract (- (@bvsize y) 1) 0 xs') 0)
          (smt_extract (nat (- (@bvsize y) 1)) (nat 0) (27::8 word) XOR 0)
    has length y

 *)
lemma rewrite_bv_xor_concat_pullup3[rewrite_bv_xor_concat_pullup]:
  fixes xs::"('a::len word) cvc_ListVar"
    and ws::"('a::len word) cvc_ListVar"
    and y::"'b::len word"
    and z::"'c::len word"
    and ys::"('e::len word) cvc_ListVar"
    and nxm1::int and ny::int and nym1::int
shows "NO_MATCH cvc_a (undefined xs ws y z ys nxm1 ny nym1)
\<Longrightarrow> is_singleton_ListVar xs \<Longrightarrow> ws = (ListVar []) \<Longrightarrow> is_empty_ListVar ys
\<Longrightarrow>LENGTH('a) = LENGTH('c) + LENGTH('b) \<Longrightarrow> 
   (cvc_list_left xor xs (word_cat z y ::'a ::len word) ::'a::len word)
= 
  (word_cat
    ( xor
      (smt_extract ( LENGTH('a) - 1) (LENGTH('a)) (word_cat_helper xs ::'a::len word)::'c::len word)
      (z::'c::len word)
    ::'c::len word)
    (xor (smt_extract (LENGTH('a) - 1) (nat 0) (word_cat_helper xs ::'a word)::'b::len word) y ::'b word)
  ::'a word)
   "
  apply (cases ys)
  apply simp_all
  sorry
















(*
lemma h1:
  fixes xs::"('a::len word) cvc_ListVar"
    and ws::"('a::len word) cvc_ListVar"
    and y::"'b::len word"
    and z::"'c::len word"
    and ys::"('e::len word) cvc_ListVar"
    and nxm1::"int" and ny::"int" and nym1::"int"
  shows "NO_MATCH cvc_a (undefined xs ws y z ys nxm1 ny nym1)
\<Longrightarrow> LENGTH('a) = LENGTH('b) + LENGTH('c)
\<Longrightarrow> LENGTH('c) = nat nxm1 - nat ny + 1
\<Longrightarrow> LENGTH('b) = nat nym1 + 1
\<Longrightarrow> LENGTH('b) + LENGTH('c) = LENGTH('a)
\<Longrightarrow> xs \<noteq> (ListVar []) \<Longrightarrow> ws \<noteq> (ListVar []) \<Longrightarrow> is_empty_ListVar ys
\<Longrightarrow> nxm1 \<ge> 0 \<Longrightarrow> ny \<ge> 0 \<Longrightarrow> nym1 \<ge> 0
\<Longrightarrow> n < LENGTH('c) \<Longrightarrow> n < LENGTH('a) \<Longrightarrow> n + nat ny < Suc (nat nxm1)
\<Longrightarrow>
   bit (cvc_list_left xor xs
     (cvc_list_right xor
      (word_cat z y ::'a ::len word)
       ws
     ::'a word)
   ::'a word) n
= 
  bit (
    ( xor
      (smt_extract (nat nxm1) (nat ny) (cvc_list_both' xor xs ws ::'a::len word)::'c::len word)
      (z::'c::len word)
    ::'c::len word)
    )  n
   "
  apply (cases xs)
  apply (cases ws)
  apply (cases ys)
  apply simp
  subgoal for xs' ws' ys'
      unfolding cvc_list_left_transfer
      apply (subst cvc_list_right_transfer_2)
       apply simp_all
      unfolding cvc_list_both_transfer'
unfolding bit_xor_iff bit_smt_extract
  proof-
    assume a0:
    "LENGTH('a) = Suc (Suc (nat nym1 + nat nxm1 - nat ny))"
    "LENGTH('c) = Suc (nat nxm1 - nat ny)"
    "LENGTH('b) = Suc (nat nym1)"
    "xs' \<noteq> [] "
    "ws' \<noteq> []"
    "ys' = []"
    "(0::int) \<le> nxm1"
    "(0::int) \<le> ny"
    "(0::int) \<le> nym1"
    "n < Suc (nat nxm1 - nat ny)"
    "n < Suc (Suc (nat nym1 + nat nxm1 - nat ny))"
    "n + nat ny < Suc (nat nxm1)"
    "xs = ListVar xs'"
    "ws = ListVar ws'"
    "ys = ListVar []"
    have "((n + nat ny < Suc (nat nxm1) \<and> bit (foldr xor xs' (foldr xor (butlast ws') (last ws'))) (n + nat ny)) \<and>
      n < LENGTH('c))
      = ((n + nat ny < Suc (nat nxm1) \<and> bit (foldr xor xs' (foldr xor (butlast ws') (last ws'))) (n + nat ny)))"
      using \<open>LENGTH('c::len) = Suc (nat (nxm1::int) - nat (ny::int))\<close> by linarith
    then have h1: "((n + nat ny < Suc (nat nxm1) \<and> bit (foldr xor xs' (foldr xor (butlast ws') (last ws'))) (n + nat ny)) \<and>
      n < LENGTH('c))
      = ((bit (foldr xor xs' (foldr xor (butlast ws') (last ws'))) (n + nat ny)))"
      using a0(12) by blast



    show "bit (foldr xor xs' (xor (word_cat z y) (foldr xor (butlast ws') (last ws')))) n =
    (((n + nat ny < Suc (nat nxm1) \<and> bit (foldr xor xs' (foldr xor (butlast ws') (last ws'))) (n + nat ny)) \<and>
      n < LENGTH('c)) \<noteq>
     bit z n)"
      apply (simp only: h1)

  
  apply simp
  apply (cases "n + nat ny < Suc (nat nxm1)")
   apply simp
       apply simp_all
       unfolding cvc_list_left_transfer
      apply (subst cvc_list_right_transfer_2)
       apply simp_all
       unfolding cvc_list_both_transfer'
 unfolding bit_foldr_xor bit_xor_iff
  unfolding bit_word_cat_iff
  apply simp


lemma [rewrite_bv_xor_concat_pullup]:
  fixes xs::"('a::len word) cvc_ListVar"
    and ws::"('a::len word) cvc_ListVar"
    and y::"'b::len word"
    and z::"'c::len word"
    and ys::"('e::len word) cvc_ListVar"
    and nxm1::"int" and ny::"int" and nym1::"int"
  shows "NO_MATCH cvc_a (undefined xs ws y z ys nxm1 ny nym1)
\<Longrightarrow> LENGTH('a) = LENGTH('b) + LENGTH('c)
\<Longrightarrow> LENGTH('c) = nat nxm1 - nat ny + 1
\<Longrightarrow> LENGTH('b) = nat nym1 + 1
\<Longrightarrow> LENGTH('b) + LENGTH('c) = LENGTH('a)
\<Longrightarrow> xs \<noteq> (ListVar []) \<Longrightarrow> ws \<noteq> (ListVar []) \<Longrightarrow> is_empty_ListVar ys
\<Longrightarrow> nxm1 \<ge> 0 \<Longrightarrow> ny \<ge> 0 \<Longrightarrow> nym1 \<ge> 0
\<Longrightarrow>
   (cvc_list_left xor xs
     (cvc_list_right xor
      (word_cat z y ::'a ::len word)
       ws
     ::'a word)
   ::'a word)
= 
  (word_cat
    ( xor
      (smt_extract (nat nxm1) (nat ny) (cvc_list_both' xor xs ws ::'a::len word)::'c::len word)
      (z::'c::len word)
    ::'c::len word)
    (xor (smt_extract (nat nym1) (nat 0) (cvc_list_both' xor xs ws ::'a word)::'b::len word) y ::'b word)
  ::'a word)
   "
  apply (cases xs)
  apply (cases ws)
  apply (cases ys)
  apply simp
  subgoal for xs' ws' ys'
      unfolding cvc_list_left_transfer
      apply (subst cvc_list_right_transfer_2)
       apply simp_all
      unfolding cvc_list_both_transfer'
      apply (simp only: helper3 helper4)

      unfolding word_cat_helper_left_def
      apply (simp only: bang_eq)
      apply (rule allI)
      subgoal for n
        apply (cases "n < LENGTH('b)")
         apply (simp_all add: bit_word_cat_iff)
        apply (simp_all add: bit_xor_iff bit_smt_extract)
  sorry


lemma 
  fixes xs::"('a::len word) cvc_ListVar"
    and ws::"('a::len word) cvc_ListVar"
    and y::"'b::len word"
    and z::"'c::len word"
    and ys::"('e::len word) cvc_ListVar"
    and nxm1::"int" and ny::"int" and nym1::"int"
  shows "NO_MATCH cvc_a (undefined xs ws y z ys nxm1 ny nym1)
\<Longrightarrow> LENGTH('d) = LENGTH('b) + LENGTH('c)
\<Longrightarrow> LENGTH('a) = LENGTH('d) + LENGTH('e)
\<Longrightarrow> LENGTH('f) = nat nxm1 - nat ny + 1
\<Longrightarrow> LENGTH('e) + LENGTH('c) = LENGTH('f)
\<Longrightarrow> LENGTH('b) = nat nym1 + 1
\<Longrightarrow> LENGTH('b) + LENGTH('f) = LENGTH('a)
\<Longrightarrow> xs \<noteq> (ListVar []) \<Longrightarrow> ws \<noteq> (ListVar []) \<Longrightarrow> is_singleton_ListVar ys
\<Longrightarrow> nxm1 \<ge> 0 \<Longrightarrow> ny \<ge> 0 \<Longrightarrow> nym1 \<ge> 0
\<Longrightarrow>
   (cvc_list_left xor xs
     (cvc_list_right xor
       (word_cat_helper_left
         ys
         (word_cat z y ::'d ::len word)
        ::'a word) ws
     ::'a word)
   ::'a word)
= 
  (word_cat
    ( xor
      (smt_extract (nat nxm1) (nat ny) (cvc_list_both' xor xs ws ::'a::len word)::'f::len word)
      (word_cat_helper_left ys z::'f::len word)
    ::'f::len word)
    (xor (smt_extract (nat nym1) 0 (cvc_list_both' xor xs ws ::'a word)::'b::len word) y ::'b word)
  ::'a word)
   "
  apply (cases xs)
  apply (cases ws)
  apply (cases ys)
  apply simp
  subgoal for xs' ws' ys'
      unfolding cvc_list_left_transfer
      apply (subst cvc_list_right_transfer_2)
       apply simp_all
      unfolding cvc_list_both_transfer'
      apply (cases ys') 
       apply simp_all
      subgoal for ys'' ys_empty
        apply (induction xs' arbitrary: xs)
         apply simp
        apply (induction ys' arbitrary: ys)
         apply simp
        apply simp


      unfolding word_cat_helper_left_def
       apply simp_all

        sorry


lemma
 fixes xs::"('a::len word) cvc_ListVar"
    and ws::"('a::len word) cvc_ListVar"
    and y::"'b::len word"
    and z::"'c::len word"
    and ys::"('e::len word) cvc_ListVar"
    and nxm1::"int" and ny::"int" and nym1::"int"
  shows
    "LENGTH('a) = LENGTH('d) + LENGTH('e)\<longrightarrow>
    LENGTH('f) = Suc (nat nxm1 - nat ny) \<longrightarrow>
    LENGTH('e) + LENGTH('c) = Suc (nat nxm1 - nat ny) \<longrightarrow>
    LENGTH('b) = Suc (nat nym1) \<longrightarrow>
    Suc (Suc (nat nym1 + (nat nxm1 - nat ny))) = LENGTH('d) + LENGTH('e) \<longrightarrow>
    xs' \<noteq> [] \<longrightarrow>
    ws' \<noteq> [] \<longrightarrow>
    ys_empty = [] \<longrightarrow>
    (0::int) \<le> nxm1 \<longrightarrow>
    (0::int) \<le> ny \<longrightarrow>
    (0::int) \<le> nym1 \<longrightarrow>
    xs = ListVar xs' \<longrightarrow>
    ws = ListVar ws' \<longrightarrow>
    ys = ListVar [ys''] \<longrightarrow>
    ys' = [ys''] \<longrightarrow>
    foldr xor xs' (xor (word_cat ys'' (word_cat z y::'d::len word)) (foldr xor (butlast ws') (last ws'))) =
    word_cat (xor (smt_extract (nat nxm1) (nat ny) (foldr xor xs' (foldr xor (butlast ws') (last ws')))) (word_cat ys'' z))
     (xor (smt_extract (nat nym1) (0::nat) (foldr xor xs' (foldr xor (butlast ws') (last ws')))) y)"


lemma
  fixes xs::"('a::len word) cvc_ListVar"
    and ws::"('a::len word) cvc_ListVar"
    and y::"'b::len word"
    and z::"'c::len word"
    and ys::"(bool list) list"
    and nxm1::"nat" and ny::"nat" and nym1::"nat"
  shows "NO_MATCH cvc_a (undefined xs ws y z ys nxm1 ny nym1)
\<Longrightarrow> length (concat ys) = LENGTH('e)
\<Longrightarrow> LENGTH('d) = LENGTH('b) + LENGTH('c)
\<Longrightarrow> LENGTH('a) = LENGTH('d) + LENGTH('e)
\<Longrightarrow> LENGTH('f) = nxm1 - ny + 1
\<Longrightarrow> LENGTH('e) + LENGTH('c) = LENGTH('f)
\<Longrightarrow> LENGTH('b) = nym1 + 1
\<Longrightarrow> LENGTH('b) + LENGTH('f) = LENGTH('a)
\<Longrightarrow> xs \<noteq> (ListVar []) \<Longrightarrow> ws \<noteq> (ListVar []) 
\<Longrightarrow>
   (cvc_list_left xor xs
     (cvc_list_right xor
       (word_cat
         (of_bl (concat ys)::'e::len word)
         (word_cat z y ::'d ::len word)
        ::'a word) ws
     ::'a word)
   ::'a word)
= 
  (word_cat
    ( xor
      (smt_extract nxm1 ny (cvc_list_both' xor xs ws ::'a::len word)::'f::len word)
      (word_cat (of_bl (concat ys)::'e::len word) z::'f::len word)
    ::'f::len word)
    (xor (smt_extract nym1 0 (cvc_list_both' xor xs ws ::'a word)::'b::len word) y ::'b word)
  ::'a word)
   "
  apply (cases xs)
  apply (cases ws)
  apply simp
  subgoal for xs' ws'
      unfolding cvc_list_left_transfer
      apply (subst cvc_list_right_transfer_2)
       apply simp_all
      unfolding cvc_list_both_transfer'
      apply (induction xs' arbitrary: xs)
      apply simp_all
      apply (induction ws' arbitrary: ws)
       apply simp_all
      apply (rule impI conjI)+
      sorry
    sorry
*)

lemma
  assumes  "(1::int) = int (size (0::1 word))" 
    and "(7::int) = int (size (27::8 word)) - (1::int)"
    and "(0::int) = int (size (0::1 word)) - (1::int)"
  shows "xor (27::8 word) (word_cat (smt_extract 6 0 (v0::8 word)::7 word) (0::1 word)::8 word) =
        word_cat
          (xor (smt_extract 7 1 (27::8 word)::7 word) (smt_extract 6 0 v0 :: 7 word) :: 7 word)
          (xor (smt_extract 0 0 (27::8 word)::1 word) (0::1 word) :: 1 word) "
  sorry


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

Simplified (without commutativity): 
(define-cond-rule bv-xor-ones ((w Int) (x ?BitVec))
  (= w (size x))
  (bvxor (@bv (- (int.pow2 w) 1) w) x)
  (bvnot x))


*)

lemma rewrite_bv_xor_ones_lemma: "foldr xor xs (not a) = not (foldr xor xs a)"
  apply (induction xs)
  by simp_all



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
  (and (int.ispow2 n) (= exponent (int.log2 n)) (= u (- (- size (int.log2 n)) 1)))
  (bvmul xs z (@bv n size) ys)
  (concat
    (extract u 0 (bvmul xs z ys))
    (@bv 0 exponent)))


     assumptions:
       is_pow2 (4::int) = True
       (2::int) = int (floorlog (nat (4::int)) (2::nat))
       1 = (4::int) - int (floorlog (nat (4::int)) (2::nat)) - 1
     prop: 
       (x::4 word) * (4::4 word) = word_cat (smt_extract (nat 1) (nat 0) x) 0 

   ''bv-mult-pow2-1''
         xs    ListVar []
         ys    ListVar []
         z     x::4 word
         size  4::int
         n     4::int
         exponent 2::int
         u     1
*)
named_theorems rewrite_bv_mult_pow2_1 \<open>manually generated\<close>


lemma [rewrite_bv_mult_pow2_1]:
  fixes xs ys :: "'b::len word cvc_ListVar"
    and z :: "'b::len word"
    and exponent size u :: int
    and n ::int
  shows "NO_MATCH (cvc_a) (undefined n_w xs ys z size n exponent u) 
    \<Longrightarrow> is_pow2 n
    \<Longrightarrow> (exponent = (floorlog (nat n) 2))
    \<Longrightarrow> (u = ((size - (floorlog (nat n) 2)) - 1))
    \<Longrightarrow> LENGTH('a) = nat exponent
    \<Longrightarrow> LENGTH('b) = nat size
    \<Longrightarrow> LENGTH('c) = nat u + 1
    \<Longrightarrow> n_w = (Word.Word n::'b::len word)
    \<Longrightarrow>
(cvc_list_left (*) xs (z *  (Word.Word n::'b::len word)))
   = (word_cat (smt_extract (nat u) (nat (0::int)) (cvc_list_left (*) xs (cvc_list_right (*) z ys))::'c::len word) (0::'a::len word))"
  sorry

thm rewrite_bv_mult_pow2_1[of _ "ListVar []" "ListVar []" "x::4 word" "4::int" "4::int" "2::int" 1]

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
