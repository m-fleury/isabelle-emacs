theory BV_Rewrites_Elimination
  imports BV_Rewrites_Lemmas 
begin

declare[[show_types,show_sorts]]
declare[[smt_expert_debug_alethe_level=0]]

(*
(define-rule bv-ugt-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvugt x y)
  (bvult y x))
*)

named_theorems rewrite_bv_ugt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined x y)
    \<Longrightarrow> (x < y) = (y > x)"
  by simp

(*
(define-rule bv-uge-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvuge x y)
  (bvule y x))
*)
named_theorems rewrite_bv_uge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_uge_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(y \<le> x) = (y \<le> x)"
  by auto

(*
(define-rule bv-sgt-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvsgt x y)
  (bvslt y x))
*)
named_theorems rewrite_bv_sgt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sgt_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(y <s x) = (y <s x)"
  by auto

(*
(define-rule bv-sge-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvsge x y)
  (bvsle y x))
*)
named_theorems rewrite_bv_sge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sge_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(y \<le>s x) = (y \<le>s x)"
  by auto

(*
(define-rule bv-sle-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvsle x y)
  (not (bvslt y x)))
*)
named_theorems rewrite_bv_slt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_slt_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(x <s y) =
   (x +
    push_bit (unat (Word.Word (int (size x) - (1::int))::'a::len word))
     (Word.Word (1::int)::'a::len word)
    < y +
      push_bit (unat (Word.Word (int (size x) - (1::int))::'a::len word))
       (Word.Word (1::int)::'a::len word))"
  apply transfer
  apply (simp add: signed_take_bit_eq_take_bit_shift)
  apply (cases \<open>LENGTH('a)\<close>)
  apply simp
  apply (simp add: iff_conv_conj_imp)
  apply (rule conjI impI)+
   apply (metis add.commute add_lessD1 n_less_equal_power_2 nat_int of_nat_take_bit plus_1_eq_Suc take_bit_nat_eq_self)
  by (metis add.commute add_lessD1 n_less_equal_power_2 nat_int of_nat_take_bit plus_1_eq_Suc take_bit_nat_eq_self)

(*
(define-cond-rule bv-redor-eliminate
  ((x ?BitVec) (w Int))
  (= w (@bvsize x))
  (bvredor x)
  (bvnot (bvcomp x (@bv 0 w))))
*)

named_theorems rewrite_bv_redor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redor_eliminate]:
  fixes x::"'a ::len word"
  shows "smt_redor x = not (smt_comp x (Word.Word (0::int)))"
  unfolding smt_redor_def by simp

(*
(define-cond-rule bv-redand-eliminate
  ((x ?BitVec) (w Int))
  (= w (@bvsize x))
  (bvredand x)
  (bvcomp x (bvnot (@bv 0 w))))
*)

named_theorems rewrite_bv_redand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redand_eliminate]:
  fixes x::"'a ::len word"
  shows "smt_redand x = smt_comp x (not (Word.Word (0::int)))"
  unfolding smt_redand_def by auto

(*
(define-rule bv-ule-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvule x y)
  (not (bvult y x)))
*)
named_theorems rewrite_bv_ule_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y)
    \<Longrightarrow> (x \<le> y) = (\<not>(y < x))"
  using word_le_not_less by simp

(*
(define-rule bv-comp-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvcomp x y)
  (ite (= x y) (@bv 1 1) (@bv 0 1)))
*)

named_theorems rewrite_bv_comp_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_comp_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "smt_comp x y = (if x = y then Word.Word (1::int) else Word.Word (0::int))"
  by (metis one_word.abs_eq smt_comp_def zero_word.abs_eq)


(*
(define-cond-rule bv-rotate-left-eliminate-1
  ((x ?BitVec) (amount Int) (u1 Int) (u2 Int) (l2 Int))
  (def (n (@bvsize x)) (a (mod amount n)))
  (and (not (= a 0)) (= u1 (- n (+ 1 a))) (= u2 (- n 1)) (= l2 (- n a)))
  (rotate_left amount x)
  (concat
    (extract u1 0 x)
    (extract u2 l2 x)))
*)


named_theorems rewrite_bv_rotate_left_eliminate_1 \<open>automatically_generated\<close>

(*lemma is somehow wrong*)
(*
lemma [rewrite_bv_rotate_left_eliminate_1]:
  fixes x::"'a::len word" and amount::"int"
  assumes "SMT.z3mod amount (int (size x)) \<noteq> (0::int)"
    "size x - (1 + SMT.z3mod amount (int (size x))) \<ge> 0"
    "size x - (1 + SMT.z3mod amount (int (size x))) < LENGTH('a)"
    "LENGTH('b) = size x - (1 + SMT.z3mod amount (int (size x))) + 1"
    "size x - SMT.z3mod amount (int (size x)) \<ge> 0"
    "size x - SMT.z3mod amount (int (size x)) \<le> size x -1"
    "size x - 1 < LENGTH('a)"
    "LENGTH('c) = SMT.z3mod amount (int (size x))"
    "LENGTH('a) = LENGTH('b) + LENGTH('c)"
    "amount \<ge> 0"
  shows "
  (word_rotl (nat amount) x::'a::len word) =
   word_cat
    (smt_extract
      (nat (int (size x) - ((1::int) + SMT.z3mod amount (int (size x)))))
      (nat (0::int)) x::'b::len word)
    (smt_extract (nat (int (size x) - (1::int)))
      (nat (int (size x) - SMT.z3mod amount (int (size x)))) x::'c::len word)"
proof -
  let ?n = "LENGTH('a)"
  define a where "a = LENGTH('c)"

  have size_eq: "size x = ?n" by (simp add: word_size)

  have z3mod_nneg: "0 \<le> SMT.z3mod amount (int (size x))"
    by (simp add: SMT.z3mod_def)

  have t0: "(0 \<le> amount mod (int LENGTH('b) + SMT.z3mod amount (int (size x))))"
    using  a_def assms(9) len_num1 n_not_Suc_n plus_1_eq_Suc
    unfolding SMT.z3mod_def 
    by (simp add: assms(10) nonneg_mod_div)
    
  text \<open>The rotation amount, reduced modulo \<open>?n\<close>, equals \<open>LENGTH('c)\<close>.\<close>
  have shift_mod: "nat amount mod (LENGTH('b) + LENGTH('c)) = LENGTH('c)"
    apply (simp add: nat_mod_as_int)
    apply (subst int_int_eq[symmetric])
    apply (subst assms(8))
    apply (subst assms(10))
    apply simp
    apply (simp add: t0)
    apply (simp add: assms(10))
    unfolding SMT.z3mod_def sorry
  have shift_eq: "nat amount mod ?n = a"
    using shift_mod assms(9) a_def by simp

  have b_eq: "LENGTH('b) = ?n - a"
    using assms(9) a_def by simp
  have a_lt_n: "a < ?n"
    using shift_eq[symmetric] by simp

  have z3mod_nat: "nat (SMT.z3mod amount (int (size x))) = a"
    using assms(10) size_eq shift_eq
    by (simp add: SMT.z3mod_def nat_mod_distrib flip: zmod_int)

  have a_pos: "0 < a"
    using assms(1) z3mod_nneg z3mod_nat by (metis nat_0 order_le_imp_less_or_eq)

  text \<open>Rewrite the integer-shaped indices in \<open>nat\<close> arithmetic.\<close>
  have idx_hi: "nat (int (size x) - (1 + SMT.z3mod amount (int (size x)))) = ?n - 1 - a"
    using z3mod_nat z3mod_nneg size_eq assms(2)
    by (simp add: nat_diff_distrib nat_add_distrib)
  have idx_top: "nat (int (size x) - 1) = ?n - 1"
    using size_eq by (simp add: nat_diff_distrib)
  have idx_lo: "nat (int (size x) - SMT.z3mod amount (int (size x))) = ?n - a"
    using z3mod_nat z3mod_nneg size_eq assms(5)
    by (simp add: nat_diff_distrib)

  show ?thesis
    unfolding idx_hi idx_top idx_lo
  proof (rule bit_word_eqI)
    fix k :: nat
    assume k_lt: "k < ?n"
    show "bit (word_rotl (nat amount) x) k =
          bit (word_cat
                 (smt_extract (?n - 1 - a) (nat 0) x :: 'b word)
                 (smt_extract (?n - 1) (?n - a) x :: 'c word) :: 'a word) k"
    proof (cases "k < a")
      case True
      with a_lt_n have add_lt: "k + (?n - a) < ?n" by linarith
      have lhs: "bit (word_rotl (nat amount) x) k = bit x (k + (?n - a))"
        using k_lt shift_eq add_lt by (simp add: bit_word_rotl_iff)
      have rhs: "bit (word_cat
                       (smt_extract (?n - 1 - a) (nat 0) x :: 'b word)
                       (smt_extract (?n - 1) (?n - a) x :: 'c word) :: 'a word) k
                  = bit x (k + (?n - a))"
        using True k_lt a_lt_n a_pos b_eq a_def add_lt
        by (auto simp: bit_word_cat_iff bit_smt_extract)
      from lhs rhs show ?thesis by simp
    next
      case False
      then have k_ge: "a \<le> k" by simp
      with k_lt a_lt_n have k_minus_lt: "k - a < ?n - a" by linarith
      have add_eq: "(k + (?n - a)) mod ?n = k - a"
      proof -
        have "k + (?n - a) = (k - a) + ?n"
          using k_ge a_lt_n by simp
        then show ?thesis using k_minus_lt by simp
      qed
      have lhs: "bit (word_rotl (nat amount) x) k = bit x (k - a)"
        using k_lt shift_eq add_eq by (simp add: bit_word_rotl_iff)
      have rhs: "bit (word_cat
                       (smt_extract (?n - 1 - a) (nat 0) x :: 'b word)
                       (smt_extract (?n - 1) (?n - a) x :: 'c word) :: 'a word) k
                  = bit x (k - a)"
        using False k_lt a_lt_n a_pos b_eq a_def k_minus_lt k_ge
        by (auto simp: bit_word_cat_iff bit_smt_extract)
      from lhs rhs show ?thesis by simp
    qed
  qed
qed
*)

(*
(define-cond-rule bv-rotate-left-eliminate-2
  ((x ?BitVec) (amount Int))
  (= (mod amount (@bvsize x)) 0)
  (rotate_left amount x)
  x)
*)


named_theorems rewrite_bv_rotate_left_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_2]:
  fixes x::"'a::len word" and amount::"int"
  shows "SMT.z3mod amount (int (size x)) = (0::int) \<longrightarrow>
   word_rotl (nat amount) x = x"
  unfolding SMT.z3mod_def
  apply (simp only: word_uint_eq_iff)
  apply (simp add: uint_word_rotl_eq)
  apply (simp add: unsigned_take_bit_eq)
  unfolding concat_bit_def
  by (simp add: bintr_uint nat_mod_as_int size_word.rep_eq)


(*
(define-cond-rule bv-rotate-right-eliminate-1
  ((x ?BitVec) (amount Int) (u1 Int) (u2 Int) (l2 Int))
  (def (n (@bvsize x)) (a (mod amount n)))
  (and (not (= a 0)) (= u1 (- a 1)) (= u2 (- n 1)) (= l2 a))
  (rotate_right amount x)
  (concat
    (extract u1 0 x)
    (extract u2 l2 x)))
*)

named_theorems rewrite_bv_rotate_right_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_1]:
  fixes x::"'a::len word" and amount::"int"
  shows "SMT.z3mod amount (int (size x)) \<noteq> (0::int) \<longrightarrow>
  LENGTH('a) = LENGTH('b) + LENGTH('c) \<longrightarrow>
  amount \<ge> 0 \<longrightarrow> 
  SMT.z3mod amount (int (size x)) - 1 \<ge> 0 \<longrightarrow>
  SMT.z3mod amount (int (size x)) - 1 < LENGTH('a) \<longrightarrow>
  LENGTH('b) = SMT.z3mod amount (int (size x)) \<longrightarrow>
  SMT.z3mod amount (int (size x)) \<ge> 0 \<longrightarrow>
  size x - 1 \<ge> SMT.z3mod amount (int (size x)) \<longrightarrow> 
  size x - 1 \<le> LENGTH('a) \<longrightarrow>
  LENGTH('c) = size x - SMT.z3mod amount (int (size x)) \<longrightarrow>
  (word_rotr (nat amount) x::'a::len word) =
   word_cat
    (smt_extract (nat (SMT.z3mod amount (int (size x)) - (1::int)))
      (nat (0::int)) x::'b::len word)
    (smt_extract (nat (int (size x) - (1::int)))
      (nat (SMT.z3mod amount (int (size x)))) x::'c::len word)"
(*  apply (rule impI)+
  apply (simp only: word_uint_eq_iff )
    apply (simp add: uint_word_rotr_eq)
  apply (simp add: concat_bit_eq uint_take_bit_eq)
  apply (subst uint_word_cat[of "(smt_extract (nat (SMT.z3mod amount (int (size x)) - (1::int)))
      0 x::'b::len word)" "(smt_extract (nat (int (size x) - (1::int)))
      (nat (SMT.z3mod amount (int (size x)))) x::'c::len word)", where 'c="'a"])
   apply simp
  apply (subst uint_smt_extract[of 0 "(nat (SMT.z3mod amount (int (size x)) - (1::int)))" x, where 'b="'b"])
     apply simp_all
  apply (subst uint_smt_extract[of "(nat (SMT.z3mod amount (int (size x))))" "(nat (int (size x) - (1::int)))" x, where 'b="'c"])
  apply simp_all
    apply (simp add: push_bit_take_bit)
  apply (simp add: drop_bit_take_bit)
  using Suc_diff_1
  unfolding SMT.z3mod_def
  apply (simp add:  nat_mod_as_int)*)
 (* by (smt (verit, ccfv_SIG) Suc_nat_eq_nat_zadd1 add.right_neutral diff_add_inverse group_cancel.add2 int_nat_eq nat_int plus_1_eq_Suc size_word.rep_eq zmod_int)
*)
  sorry
(*
(define-cond-rule bv-rotate-right-eliminate-2
  ((x ?BitVec) (amount Int))
  (= (mod amount (@bvsize x)) 0)
  (rotate_right amount x)
  x)

(define-rule bv-nand-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvnand x y)
  (bvnot (bvand x y)))
(define-rule bv-nor-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvnor x y)
  (bvnot (bvor x y)))
(define-rule bv-xnor-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvxnor x y)
  (bvnot (bvxor x y)))

(define-cond-rule bv-sdiv-eliminate
  ((x ?BitVec) (y ?BitVec) (nm1 Int))
  (def
    (xLt0 (= (extract nm1 nm1 x) (@bv 1 1)))
    (yLt0 (= (extract nm1 nm1 y) (@bv 1 1)))
    (rUdiv (bvudiv (ite xLt0 (bvneg x) x) (ite yLt0 (bvneg y) y)))
  )
  (= nm1 (- (@bvsize x) 1))
  (bvsdiv x y)
  (ite (xor xLt0 yLt0) (bvneg rUdiv) rUdiv))

(define-rule bv-zero-extend-eliminate
  ((x ?BitVec) (n Int))
  (zero_extend n x)
  (concat (@bv 0 n) x))

(define-cond-rule bv-uaddo-eliminate
  ((x ?BitVec) (y ?BitVec) (w Int))
  (= w (@bvsize x))
  (bvuaddo x y)
  (= (extract w w
      (bvadd (concat (@bv 0 1) x) (concat (@bv 0 1) y)))
    (@bv 1 1)
  ))
(define-cond-rule bv-saddo-eliminate
  ((x ?BitVec) (y ?BitVec) (wm1 Int))
  (def
    (xS (extract wm1 wm1 x))
    (yS (extract wm1 wm1 y))
    (aS (extract wm1 wm1 (bvadd x y)))
  )
  (= wm1 (- (@bvsize x) 1))
  (bvsaddo x y)
  (or
    (and (and (= xS (@bv 1 1)) (= yS (@bv 1 1))) (= aS (@bv 0 1)))
    (and (and (= xS (@bv 0 1)) (= yS (@bv 0 1))) (= aS (@bv 1 1)))
  ))
(define-cond-rule bv-sdivo-eliminate
  ((x ?BitVec) (y ?BitVec) (w Int) (wm1 Int))
  (and (= wm1 (- (@bvsize x) 1)) (= w (@bvsize y)))
  (bvsdivo x y)
  (and
    (= x (concat (@bv 1 1) (@bv 0 wm1)))
    (= y (bvnot (@bv 0 w)))
  ))
(define-cond-rule bv-smod-eliminate
  ((x ?BitVec) (y ?BitVec) (w Int) (wm1 Int))
  (def
    (xLt0 (= (extract wm1 wm1 x) (@bv 1 1)))
    (yLt0 (= (extract wm1 wm1 y) (@bv 1 1)))
    (nxLt0 (= (extract wm1 wm1 x) (@bv 0 1)))
    (nyLt0 (= (extract wm1 wm1 y) (@bv 0 1)))
    (xAbs (ite nxLt0 x (bvneg x)))
    (yAbs (ite nyLt0 y (bvneg y)))
    (u (bvurem xAbs yAbs))
  )
  (and (= w (@bvsize x)) (= wm1 (- (@bvsize x) 1)))
  (bvsmod x y)
  (ite (= u (@bv 0 w))
    u
    (ite (and nxLt0 nyLt0)
      u
      (ite (and xLt0 nyLt0)
        (bvadd (bvneg u) y)
        (ite (and nxLt0 yLt0)
          (bvadd u y)
          (bvneg u))))))

(define-cond-rule bv-srem-eliminate
  ((x ?BitVec) (y ?BitVec) (nm1 Int))
  (def
    (xLt0 (= (extract nm1 nm1 x) (@bv 1 1)))
    (yLt0 (= (extract nm1 nm1 y) (@bv 1 1)))
    (xAbs (ite xLt0 (bvneg x) x))
    (yAbs (ite yLt0 (bvneg y) y))
    (u (bvurem xAbs yAbs))
  )
  (= nm1 (- (@bvsize x) 1))
  (bvsrem x y)
  (ite xLt0 (bvneg u) u))

(define-cond-rule bv-usubo-eliminate
  ((x ?BitVec) (y ?BitVec) (n Int))
  (def
    (s (bvsub (zero_extend 1 x) (zero_extend 1 y)))
  )
  (= n (@bvsize x))
  (bvusubo x y)
  (= (extract n n s) (@bv 1 1)))
; Overflow occurs when
; 1. (N - P) = P
; 2. (P - N) = N
(define-cond-rule bv-ssubo-eliminate
  ((x ?BitVec) (y ?BitVec) (nm1 Int))
  (def
    (n (@bvsize x))
    (xe (extract nm1 nm1 x))
    (ye (extract nm1 nm1 y))
    (s (bvsub x y))
    (se (extract nm1 nm1 s))
  )
  (= nm1 (- n 1))
  (bvssubo x y)
  (or
    (and (and (= xe (@bv 1 1)) (= ye (@bv 0 1))) (= se (@bv 0 1)))
    (and (and (= xe (@bv 0 1)) (= ye (@bv 1 1))) (= se (@bv 1 1)))))

(define-cond-rule bv-nego-eliminate
  ((x ?BitVec) (n Int))
  (= n (- (@bvsize x) 1))
  (bvnego x)
  (= x (concat (@bv 1 1) (@bv 0 n))))*)
end