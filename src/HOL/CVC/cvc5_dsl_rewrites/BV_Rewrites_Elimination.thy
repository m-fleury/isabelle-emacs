theory BV_Rewrites_Elimination
  imports BV_Rewrites_Lemmas 
begin

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



end