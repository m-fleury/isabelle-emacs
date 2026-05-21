theory Alethe_UF_BV_Rewrites
  imports  "HOL-Library.Word" Word_Lib.More_Word "HOL-Library.Log_Nat" "HOL.Real" "HOL-Library.Sublist" 
HOL.SMT "Word_Lib.Signed_Division_Word" "Word_Lib.Reversed_Bit_Lists" SMT_Word
begin

declare[[show_sorts]]

declare[[smt_expert_debug_alethe_level=0]]


(*
(define-cond-rule uf-bv2nat-int2bv ((w Int) (t ?BitVec))
  (= (@bvsize t) w)
  (int_to_bv w (ubv_to_int t))
  t)
*)


named_theorems rewrite_uf_bv2nat_int2bv \<open>manually generated\<close>

lemma [rewrite_uf_bv2nat_int2bv]:
  fixes w::int and t::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined w t)
  \<Longrightarrow> int (size t) = w
  \<Longrightarrow> word_of_int (unsigned t::int) = t"
  by simp


(*
(define-cond-rule uf-bv2nat-int2bv-extend ((w Int) (t ?BitVec) (n Int))
  (and (> w (@bvsize t)) (= n (- w (@bvsize t))))
  (int_to_bv w (ubv_to_int t))
  (concat (@bv 0 n) t))

Note: Conditions LENGTH('c) = LENGTH('a) + LENGTH('b) and  LENGTH('b) = n are not necessary
*)

named_theorems rewrite_uf_bv2nat_int2bv_extend \<open>manually generated\<close>

lemma [rewrite_uf_bv2nat_int2bv_extend]:
  fixes w::int and t::"'a ::len word" and n::int
  shows "NO_MATCH cvc_a (undefined w t n)
  \<Longrightarrow> (int (size t) < w) = True
  \<Longrightarrow> n = w - int (size t)
  \<Longrightarrow> word_of_int (unsigned t::int) = (word_cat (0::'b::len word) t::'c::len word)"
  by simp

(*
(define-cond-rule uf-bv2nat-int2bv-extract ((w Int) (t ?BitVec) (wm1 Int))
  (and (< w (@bvsize t)) (= wm1 (- w 1)))
  (int_to_bv w (ubv_to_int t))
  (extract wm1 0 t))

Note: Condition wm1 \<ge> 0 and wm1 = w - 1 are not necessary
Premise   (w < int (size t)) = True is also not necessary
*)

named_theorems rewrite_uf_bv2nat_int2bv_extract \<open>manually generated\<close>

lemma [rewrite_uf_bv2nat_int2bv_extract]:
  fixes w::int and t::"'a ::len word" and wm1::int
  shows "NO_MATCH cvc_a (undefined w t wm1)
  \<Longrightarrow> LENGTH('c) = wm1 + 1 
  \<Longrightarrow> word_of_int (unsigned t::int) = (smtlib_extract wm1 0 t ::'c::len word)"
  unfolding smtlib_extract_def
  by (metis nat_int nat_zero_as_int ucast_eq ucast_slice
      unsigned_take_bit_eq word_ubin.Abs_norm)

(*
(define-rule uf-int2bv-bv2nat ((w Int) (t Int))
  (ubv_to_int (int_to_bv w t))
  (mod_total t (int.pow2 w)))
*)

named_theorems rewrite_uf_int2bv_bv2nat \<open>manually generated\<close>

lemma [rewrite_uf_int2bv_bv2nat]:
  fixes w::int and t::int
  shows "NO_MATCH cvc_a (undefined w t)
  \<Longrightarrow> LENGTH('a) = w
  \<Longrightarrow> (unsigned (word_of_int t::'a::len word)) = (SMT.z3mod t (int (2 ^ nat w)))"
  unfolding SMT.z3mod_def
  using uint_word_of_int by fastforce

(*
(define-cond-rule uf-bv2nat-geq-elim ((x ?BitVec) (n Int) (w Int))
  (= w (@bvsize x))
  (>= (ubv_to_int x) n)
  (ite (>= n (int.pow2 w)) false (ite (< n 0) true (bvuge x (int_to_bv w n)))))

*)
named_theorems rewrite_uf_bv2nat_geq_elim \<open>manually generated\<close>

lemma [rewrite_uf_bv2nat_geq_elim]:
  fixes x::"'a::len word" and n w::int
  shows "NO_MATCH cvc_a (undefined x n w)
  \<Longrightarrow> w = int (size x)
  \<Longrightarrow> (n \<le> (unsigned x::int)) = 
  (if int(2 ^ nat w) \<le> n then False else (if n < 0 then True else word_of_int n \<le> x))"
  apply (auto split: if_split)
  subgoal by (meson order_less_imp_not_less take_bit_int_greater_self_iff
      take_bit_int_less_self_iff)
  subgoal by (metis uint_lt_0 nle_le order_le_less_trans)
  subgoal by (meson linorder_not_less order.trans uint_range_size)
  subgoal by (metis leI nat_0_le nat_mono of_int_of_nat_eq
      unat_eq_nat_uint word_of_nat_le)
  subgoal by (simp add: uint_word_of_int word_le_def wsst_TYs(3))
  done

(*
(define-rule uf-int2bv-bvult-equiv ((t ?BitVec) (s ?BitVec))
  (bvult t s)
  (< (ubv_to_int t) (ubv_to_int s)))
*)
named_theorems rewrite_uf_int2bv_bvult_equiv \<open>manually generated\<close>

lemma [rewrite_uf_int2bv_bvult_equiv]:
  fixes t s::"'a::len word"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow>
  (t < s) = ((unsigned t::int) < (unsigned s::int))"
  using word_less_iff_unsigned by simp

(*

(define-rule uf-int2bv-bvule-equiv ((t ?BitVec) (s ?BitVec))
  (bvule t s)
  (<= (ubv_to_int t) (ubv_to_int s)))
*)
named_theorems rewrite_uf_int2bv_bvule_equiv \<open>manually generated\<close>

lemma [rewrite_uf_int2bv_bvule_equiv]:
  fixes t s::"'a::len word"
  shows "NO_MATCH cvc_a (undefined t s) \<Longrightarrow>
  (t \<le> s) = ((unsigned t::int) \<le> (unsigned s::int))"
  using word_less_eq_iff_unsigned by simp

(*
(define-cond-rule uf-sbv-to-int-elim ((t ?BitVec) (wm1 Int) (n Int))
  (and (= wm1 (- (@bvsize t) 1)) (= n (int.pow2 (@bvsize t))))
  (sbv_to_int t)
  (ite (= (extract wm1 wm1 t) (@bv 0 1)) (ubv_to_int t) (- (ubv_to_int t) n)))
*)

named_theorems rewrite_uf_sbv_to_int_elim \<open>manually generated\<close>

lemma [rewrite_uf_sbv_to_int_elim]:
  fixes t::"'a::len word" and wm1 n::int
  shows "NO_MATCH cvc_a (undefined t wm1 n) \<Longrightarrow>
  wm1 = int (size t) - 1 \<Longrightarrow> n = (int (2 ^ nat (int (size t)))) \<Longrightarrow> wm1 \<ge> 0 \<Longrightarrow>
  (signed t::int) = (if (smtlib_extract wm1 wm1 t) = (0::1 word) then unsigned t else (unsigned t) - n)"
proof -
  assume "NO_MATCH cvc_a (undefined t wm1 n)"
    and w: "wm1 = int (size t) - 1"
    and n: "n = int (2 ^ nat (int (size t)))"
    and "wm1 \<ge> 0"
  have wm1_eq: "wm1 = int (LENGTH('a) - 1)"
    using w
    by (metis One_nat_def Suc_lessI Suc_n_not_le_n add_diff_cancel_right' int_Suc
        less_eq_decr_length_iff order_refl size_word.rep_eq)
  have n_eq: "n = 2 ^ LENGTH('a)"
    using n by (simp add: word_size nat_int)
  have ext: "(smtlib_extract wm1 wm1 t :: 1 word) = (if bit t (LENGTH('a) - 1) then 1 else 0)"
    unfolding wm1_eq by (rule smtlib_extract_msb_eq)
  have sint_eq: "sint t = uint t - 2 ^ LENGTH('a) * of_bool (bit t (LENGTH('a) - 1))"
    by (simp add: sint_uint signed_take_bit_eq_take_bit_minus take_bit_int_eq_self bit_uint_iff)
  show "(signed t::int) = (if (smtlib_extract wm1 wm1 t) = (0::1 word) then unsigned t else (unsigned t) - n)"
  proof (cases "bit t (LENGTH('a) - 1)")
    case True
    then show ?thesis using ext sint_eq n_eq by simp
  next
    case False
    then show ?thesis using ext sint_eq n_eq by simp
  qed
qed

end