theory Alethe_BV_Rewrites_Elimination
  imports Alethe_BV_Rewrites_Lemmas 
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
    \<Longrightarrow> (y < x) = (y < x)"
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
  shows "NO_MATCH cvc_a (undefined x y)
    \<Longrightarrow> (y \<le> x) = (y \<le> x)"
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
  shows "NO_MATCH cvc_a (undefined x y)
    \<Longrightarrow> (y <s x) = (y <s x)"
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
  shows "NO_MATCH cvc_a (undefined x y)
    \<Longrightarrow> (y \<le>s x) = (y \<le>s x)"
  by auto

(*
(define-rule bv-sle-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvsle x y)
  (not (bvslt y x)))
*)
named_theorems rewrite_bv_sle_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined x y)
    \<Longrightarrow> (x \<le>s y) = (\<not>(y <s x))"
  by auto

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
  shows "NO_MATCH cvc_a (undefined x)
    \<Longrightarrow>smt_redor x = not (smt_comp x (Word.Word (0::int)))"
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
  shows "NO_MATCH cvc_a (undefined x)
    \<Longrightarrow>smt_redand x = smt_comp x (not (Word.Word (0::int)))"
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
  shows "NO_MATCH cvc_a (undefined x y)
    \<Longrightarrow> smt_comp x y = (if x = y then Word.Word (1::int) else Word.Word (0::int))"
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


lemma bit_smtlib_extract_aux:
  assumes "0 \<le> j"
  shows "bit (smtlib_extract j i x::'b::len word) n
    = ((n + nat i < Suc (nat j) \<and> bit x (n + nat i)) \<and> n < LENGTH('b::len))"
  unfolding smtlib_extract_def
  using nth_slice[of "nat i" "(take_bit (nat (j+1)) x)" n, where 'a="'b"]
        bit_take_bit_iff[of "nat (j+1)" x "n + nat i"] assms
  by (simp add: nat_add_distrib)

named_theorems rewrite_bv_rotate_left_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_1]:
  fixes x::"'a::len word" and amount u1 u2 l2::"int"
  shows "NO_MATCH cvc_a (undefined x amount u1 u2 l2)
    \<Longrightarrow> SMT.z3mod amount (int (size x)) \<noteq> (0::int)
    \<Longrightarrow> u1 = int (size x) - (1 + SMT.z3mod amount (int (size x)))
    \<Longrightarrow> u2 = int (size x) - 1
    \<Longrightarrow> l2 = int (size x) - SMT.z3mod amount (int (size x))
    \<Longrightarrow> LENGTH('b) = nat u1 + 1
    \<Longrightarrow> LENGTH('c) = nat u2 - nat l2 + 1
    \<Longrightarrow> LENGTH('a) = LENGTH('b) + LENGTH('c)
    \<Longrightarrow> amount \<ge> 0
    \<Longrightarrow>
   (word_rotl_lift amount x::'a::len word) =
   word_cat
    (smtlib_extract u1 0 x::'b::len word)
    (smtlib_extract u2 l2 x::'c::len word)"
proof -
  assume zne: "SMT.z3mod amount (int (size x)) \<noteq> 0"
     and u1_eq: "u1 = int (size x) - (1 + SMT.z3mod amount (int (size x)))"
     and u2_eq: "u2 = int (size x) - 1"
     and l2_eq: "l2 = int (size x) - SMT.z3mod amount (int (size x))"
     and lb: "LENGTH('b) = nat u1 + 1"
     and la: "LENGTH('a) = LENGTH('b) + LENGTH('c)"
     and amn: "amount \<ge> 0"
  have sz: "size x = LENGTH('a)" by (simp add: word_size)
  have sz_int: "int (size x) = int LENGTH('a)" using sz by simp
  have La_pos: "0 < LENGTH('a)" by (rule len_gt_0)
  have b_pos: "0 < LENGTH('b)" by (rule len_gt_0)
  have SucLa: "Suc (LENGTH('a) - 1) = LENGTH('a)" using La_pos by simp
  have SucLb: "Suc (LENGTH('b) - 1) = LENGTH('b)" using b_pos by simp
  have a_nn: "0 \<le> SMT.z3mod amount (int (size x))" by (simp add: SMT.z3mod_def)
  have a_pos: "0 < SMT.z3mod amount (int (size x))" using a_nn zne by simp
  have a_lt: "SMT.z3mod amount (int (size x)) < int LENGTH('a)"
    using sz_int La_pos by (simp add: SMT.z3mod_def)
  have u1_nn: "0 \<le> u1" using u1_eq a_lt sz_int by linarith
  have u2_nn: "0 \<le> u2" using u2_eq sz_int La_pos by linarith
  have lbE: "int LENGTH('b) = int (size x) - SMT.z3mod amount (int (size x))"
    using lb u1_eq u1_nn by simp
  have natu1: "nat u1 = LENGTH('b) - 1" using lb by simp
  have natl2: "nat l2 = LENGTH('b)" using l2_eq lbE by (metis nat_int)
  have natu2: "nat u2 = LENGTH('a) - 1"
    using u2_eq sz_int La_pos by (simp add: nat_diff_distrib)
  have lcE: "int LENGTH('c) = SMT.z3mod amount (int (size x))"
    using la lbE sz_int by simp
  \<comment> \<open>rotation amount, reduced modulo the width, as a nat\<close>
  have amod: "nat amount mod LENGTH('a) = LENGTH('c)"
  proof -
    have "SMT.z3mod amount (int (size x)) = amount mod int LENGTH('a)"
      using sz_int by (simp add: SMT.z3mod_def)
    with lcE have "int LENGTH('c) = amount mod int LENGTH('a)" by simp
    moreover have "nat (amount mod int LENGTH('a)) = nat amount mod LENGTH('a)"
      using amn by (simp add: nat_mod_distrib)
    ultimately show ?thesis by (metis nat_int)
  qed
  show "word_rotl_lift amount x =
        word_cat (smtlib_extract u1 0 x :: 'b word) (smtlib_extract u2 l2 x :: 'c word)"
    unfolding word_rotl_lift_def
  proof (rule bit_word_eqI)
    fix n :: nat assume n_lt: "n < LENGTH('a)"
    have lhs_bit: "bit (word_rotl (nat amount) x) n = bit x ((n + LENGTH('b)) mod LENGTH('a))"
    proof -
      have "LENGTH('a) - nat amount mod LENGTH('a) = LENGTH('b)" using amod la by simp
      thus ?thesis using n_lt by (simp add: bit_word_rotl_iff)
    qed
    show "bit (word_rotl (nat amount) x) n
            = bit (word_cat (smtlib_extract u1 0 x :: 'b word) (smtlib_extract u2 l2 x :: 'c word) :: 'a word) n"
    proof (cases "n < LENGTH('c)")
      case True
      have catbit: "bit (word_cat (smtlib_extract u1 0 x :: 'b word) (smtlib_extract u2 l2 x :: 'c word) :: 'a word) n
                      = bit (smtlib_extract u2 l2 x :: 'c word) n"
        using True n_lt by (simp add: bit_word_cat_iff)
      have nb_lt: "n + LENGTH('b) < LENGTH('a)" using True la by linarith
      have extbit: "bit (smtlib_extract u2 l2 x :: 'c word) n = bit x (n + LENGTH('b))"
        using True nb_lt u2_nn by (simp add: bit_smtlib_extract_aux natl2 natu2 SucLa)
      have modeq: "(n + LENGTH('b)) mod LENGTH('a) = n + LENGTH('b)" using nb_lt by simp
      show ?thesis using lhs_bit catbit extbit modeq by simp
    next
      case False
      hence n_ge: "LENGTH('c) \<le> n" by simp
      have catbit: "bit (word_cat (smtlib_extract u1 0 x :: 'b word) (smtlib_extract u2 l2 x :: 'c word) :: 'a word) n
                      = bit (smtlib_extract u1 0 x :: 'b word) (n - LENGTH('c))"
        using False n_lt by (simp add: bit_word_cat_iff)
      have klt: "n - LENGTH('c) < LENGTH('b)" using n_lt n_ge la by linarith
      have extbit: "bit (smtlib_extract u1 0 x :: 'b word) (n - LENGTH('c)) = bit x (n - LENGTH('c))"
        using klt u1_nn by (simp add: bit_smtlib_extract_aux natu1 SucLb)
      have ge: "LENGTH('a) \<le> n + LENGTH('b)" using n_ge la by linarith
      have modeq: "(n + LENGTH('b)) mod LENGTH('a) = n - LENGTH('c)"
      proof -
        have "(n + LENGTH('b)) mod LENGTH('a) = (n + LENGTH('b) - LENGTH('a)) mod LENGTH('a)"
          using ge by (simp add: le_mod_geq)
        moreover have "n + LENGTH('b) - LENGTH('a) = n - LENGTH('c)" using la by simp
        moreover have "(n - LENGTH('c)) mod LENGTH('a) = n - LENGTH('c)" using n_lt by simp
        ultimately show ?thesis by simp
      qed
      show ?thesis using lhs_bit catbit extbit modeq by simp
    qed
  qed
qed

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
  shows "NO_MATCH cvc_a (undefined x amount)
    \<Longrightarrow> SMT.z3mod amount (int (size x)) = (0::int)
    \<Longrightarrow> word_rotl_lift amount x = x"
  unfolding word_rotl_lift_def SMT.z3mod_def
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
  fixes x::"'a::len word" and amount u1 u2 l2::"int"
  shows "NO_MATCH cvc_a (undefined x amount u1 u2 l2)
    \<Longrightarrow> SMT.z3mod amount (int (size x)) \<noteq> (0::int)
    \<Longrightarrow> u1 = SMT.z3mod amount (int (size x)) - 1
    \<Longrightarrow> u2 = int (size x) - 1
    \<Longrightarrow> l2 = SMT.z3mod amount (int (size x))
    \<Longrightarrow> LENGTH('b) = nat u1 + 1
    \<Longrightarrow> LENGTH('c) = nat u2 - nat l2 + 1
    \<Longrightarrow> LENGTH('a) = LENGTH('b) + LENGTH('c)
    \<Longrightarrow> amount \<ge> 0
    \<Longrightarrow>
   (word_rotr_lift amount x::'a::len word) =
   word_cat
    (smtlib_extract u1 0 x::'b::len word)
    (smtlib_extract u2 l2 x::'c::len word)"
proof -
  assume zne: "SMT.z3mod amount (int (size x)) \<noteq> 0"
     and u1_eq: "u1 = SMT.z3mod amount (int (size x)) - 1"
     and u2_eq: "u2 = int (size x) - 1"
     and l2_eq: "l2 = SMT.z3mod amount (int (size x))"
     and lb: "LENGTH('b) = nat u1 + 1"
     and la: "LENGTH('a) = LENGTH('b) + LENGTH('c)"
     and amn: "amount \<ge> 0"
  have sz: "size x = LENGTH('a)" by (simp add: word_size)
  have La_pos: "0 < LENGTH('a)" by (rule len_gt_0)
  have b_pos: "0 < LENGTH('b)" by (rule len_gt_0)
  have SucLa: "Suc (LENGTH('a) - 1) = LENGTH('a)" using La_pos by simp
  have SucLb: "Suc (LENGTH('b) - 1) = LENGTH('b)" using b_pos by simp
  have a_nn: "0 \<le> SMT.z3mod amount (int (size x))" by (simp add: SMT.z3mod_def)
  have a_pos: "0 < SMT.z3mod amount (int (size x))" using a_nn zne by simp
  have u1_nn: "0 \<le> u1" using u1_eq a_pos by simp
  have u2_nn: "0 \<le> u2" using u2_eq sz La_pos by simp
  have lbE: "int LENGTH('b) = SMT.z3mod amount (int (size x))"
    using lb u1_eq u1_nn by simp
  have natu1: "nat u1 = LENGTH('b) - 1" using lb by simp
  have natl2: "nat l2 = LENGTH('b)" using l2_eq lbE by (metis nat_int)
  have natu2: "nat u2 = LENGTH('a) - 1"
    using u2_eq sz La_pos by (simp add: nat_diff_distrib)
  \<comment> \<open>rotation amount, reduced modulo the width, as a nat\<close>
  have amod: "nat amount mod LENGTH('a) = LENGTH('b)"
  proof -
    have "SMT.z3mod amount (int (size x)) = amount mod int LENGTH('a)"
      using sz by (simp add: SMT.z3mod_def)
    with lbE have "int LENGTH('b) = amount mod int LENGTH('a)" by simp
    moreover have "nat (amount mod int LENGTH('a)) = nat amount mod LENGTH('a)"
      using amn by (simp add: nat_mod_distrib)
    ultimately show ?thesis by (metis nat_int)
  qed
  show "word_rotr_lift amount x =
        word_cat (smtlib_extract u1 0 x :: 'b word) (smtlib_extract u2 l2 x :: 'c word)"
    unfolding word_rotr_lift_def
  proof (rule bit_word_eqI)
    fix n :: nat assume n_lt: "n < LENGTH('a)"
    have lhs_bit: "bit (word_rotr (nat amount) x) n = bit x ((n + LENGTH('b)) mod LENGTH('a))"
    proof -
      have "(n + nat amount) mod LENGTH('a) = (n + LENGTH('b)) mod LENGTH('a)"
        by (metis amod mod_add_right_eq)
      thus ?thesis using n_lt by (simp add: bit_word_rotr_iff)
    qed
    show "bit (word_rotr (nat amount) x) n
            = bit (word_cat (smtlib_extract u1 0 x :: 'b word) (smtlib_extract u2 l2 x :: 'c word) :: 'a word) n"
    proof (cases "n < LENGTH('c)")
      case True
      have catbit: "bit (word_cat (smtlib_extract u1 0 x :: 'b word) (smtlib_extract u2 l2 x :: 'c word) :: 'a word) n
                      = bit (smtlib_extract u2 l2 x :: 'c word) n"
        using True n_lt by (simp add: bit_word_cat_iff)
      have nb_lt: "n + LENGTH('b) < LENGTH('a)" using True la by linarith
      have extbit: "bit (smtlib_extract u2 l2 x :: 'c word) n = bit x (n + LENGTH('b))"
        using True nb_lt u2_nn by (simp add: bit_smtlib_extract_aux natl2 natu2 SucLa)
      have modeq: "(n + LENGTH('b)) mod LENGTH('a) = n + LENGTH('b)" using nb_lt by simp
      show ?thesis using lhs_bit catbit extbit modeq by simp
    next
      case False
      hence n_ge: "LENGTH('c) \<le> n" by simp
      have catbit: "bit (word_cat (smtlib_extract u1 0 x :: 'b word) (smtlib_extract u2 l2 x :: 'c word) :: 'a word) n
                      = bit (smtlib_extract u1 0 x :: 'b word) (n - LENGTH('c))"
        using False n_lt by (simp add: bit_word_cat_iff)
      have klt: "n - LENGTH('c) < LENGTH('b)" using n_lt n_ge la by linarith
      have extbit: "bit (smtlib_extract u1 0 x :: 'b word) (n - LENGTH('c)) = bit x (n - LENGTH('c))"
        using klt u1_nn by (simp add: bit_smtlib_extract_aux natu1 SucLb)
      have ge: "LENGTH('a) \<le> n + LENGTH('b)" using n_ge la by linarith
      have modeq: "(n + LENGTH('b)) mod LENGTH('a) = n - LENGTH('c)"
      proof -
        have "(n + LENGTH('b)) mod LENGTH('a) = (n + LENGTH('b) - LENGTH('a)) mod LENGTH('a)"
          using ge by (simp add: le_mod_geq)
        moreover have "n + LENGTH('b) - LENGTH('a) = n - LENGTH('c)" using la by simp
        moreover have "(n - LENGTH('c)) mod LENGTH('a) = n - LENGTH('c)" using n_lt by simp
        ultimately show ?thesis by simp
      qed
      show ?thesis using lhs_bit catbit extbit modeq by simp
    qed
  qed
qed
(*
(define-cond-rule bv-rotate-right-eliminate-2
  ((x ?BitVec) (amount Int))
  (= (mod amount (@bvsize x)) 0)
  (rotate_right amount x)
  x)
*)

named_theorems rewrite_bv_rotate_right_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_2]:
  fixes x::"'a::len word" and amount::"int"
  shows "NO_MATCH cvc_a (undefined x amount)
    \<Longrightarrow> SMT.z3mod amount (int (size x)) = (0::int)
    \<Longrightarrow> word_rotr_lift amount x = x"
  unfolding word_rotr_lift_def SMT.z3mod_def
  apply (simp only: word_uint_eq_iff)
  apply (simp add: uint_word_rotr_eq)
  apply (simp add: unsigned_take_bit_eq)
  unfolding concat_bit_def
  by (simp add: bintr_uint nat_mod_as_int size_word.rep_eq)

(*
(define-rule bv-nand-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvnand x y)
  (bvnot (bvand x y)))
*)

named_theorems rewrite_bv_nand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_nand_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y)
    \<Longrightarrow> not (and x y) = not (and x y)"
  by simp

(*
(define-rule bv-nor-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvnor x y)
  (bvnot (bvor x y)))
*)

named_theorems rewrite_bv_nor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_nor_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y)
    \<Longrightarrow> not (or x y) = not (or x y)"
  by simp

(*
(define-rule bv-xnor-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvxnor x y)
  (bvnot (bvxor x y)))
*)

named_theorems rewrite_bv_xnor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_xnor_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y)
    \<Longrightarrow> not (xor x y) = not (xor x y)"
  by simp

(*
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
*)

named_theorems rewrite_bv_sdiv_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sdiv_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word" and nm1::"int"
  shows "NO_MATCH cvc_a (undefined x y nm1)
    \<Longrightarrow> nm1 = int (size x) - 1
    \<Longrightarrow> smt_sdiv x y =
        (if (smtlib_extract nm1 nm1 x = (1::1 word)) \<noteq> (smtlib_extract nm1 nm1 y = (1::1 word))
         then - smt_udiv (if smtlib_extract nm1 nm1 x = (1::1 word) then - x else x)
                         (if smtlib_extract nm1 nm1 y = (1::1 word) then - y else y)
         else smt_udiv (if smtlib_extract nm1 nm1 x = (1::1 word) then - x else x)
                       (if smtlib_extract nm1 nm1 y = (1::1 word) then - y else y))"
proof -
  assume nm1: "nm1 = int (size x) - 1"
  have nm1': "nm1 = int (size x - 1)"
    using nm1
    by (simp add: le_def)
  have key: "(smtlib_extract nm1 nm1 z :: 1 word) = smt_extract (size x - 1) (size x - 1) z" for z :: "'a word"
  proof -
    have szlt: "size x - 1 < size (z::'a word)" by (simp add: word_size)
    have "(smtlib_extract nm1 nm1 z :: 1 word) = (if bit z (size x - 1) then 1 else 0)"
      unfolding nm1' using smtlib_extract_eq_iff[of "size x - 1" z] by simp
    moreover have "(smt_extract (size x - 1) (size x - 1) z :: 1 word) = (if bit z (size x - 1) then 1 else 0)"
      using smt_extract_bit[OF szlt] .
    ultimately show ?thesis by simp
  qed
  show "smt_sdiv x y =
        (if (smtlib_extract nm1 nm1 x = (1::1 word)) \<noteq> (smtlib_extract nm1 nm1 y = (1::1 word))
         then - smt_udiv (if smtlib_extract nm1 nm1 x = (1::1 word) then - x else x)
                         (if smtlib_extract nm1 nm1 y = (1::1 word) then - y else y)
         else smt_udiv (if smtlib_extract nm1 nm1 x = (1::1 word) then - x else x)
                       (if smtlib_extract nm1 nm1 y = (1::1 word) then - y else y))"
    unfolding smt_sdiv_def Let_def by (simp add: key)
qed

named_theorems rewrite_bv_zero_extend_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eliminate]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n)
    \<Longrightarrow> LENGTH('b) = nat n
    \<Longrightarrow> LENGTH('c) = LENGTH('a) + LENGTH('b)
    \<Longrightarrow> (ucast x :: 'c::len word) = word_cat (0::'b::len word) x"
proof -
  show "(ucast x :: 'c word) = word_cat (0::'b word) x"
  proof (rule bit_word_eqI)
    fix k :: nat assume "k < LENGTH('c)"
    thus "bit (ucast x :: 'c word) k = bit (word_cat (0::'b word) x :: 'c word) k"
      by (auto simp: bit_word_cat_iff bit_ucast_iff dest: bit_imp_le_length)
  qed
qed

(*
(define-cond-rule bv-uaddo-eliminate
  ((x ?BitVec) (y ?BitVec) (w Int))
  (= w (@bvsize x))
  (bvuaddo x y)
  (= (extract w w
      (bvadd (concat (@bv 0 1) x) (concat (@bv 0 1) y)))
    (@bv 1 1)
  ))
*)

named_theorems rewrite_bv_uaddo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_uaddo_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word" and w::"int"
  shows "NO_MATCH cvc_a (undefined x y w)
    \<Longrightarrow> w = int (size x)
    \<Longrightarrow> LENGTH('c) = LENGTH('a) + 1
    \<Longrightarrow> smt_uaddo TYPE('c::len) x y =
        (smtlib_extract w w
          (word_cat (0::1 word) x + word_cat (0::1 word) y :: 'c::len word) = (1::1 word))"
proof -
  assume w: "w = int (size x)" and lc: "LENGTH('c) = LENGTH('a) + 1"
  let ?S = "word_cat (0::1 word) x + word_cat (0::1 word) y :: 'c word"
  have szS: "size x < size ?S" using lc by (simp add: word_size)
  have e1: "(smtlib_extract w w ?S :: 1 word) = (if bit ?S (size x) then 1 else 0)"
    using w smtlib_extract_eq_iff[of "size x" ?S] by simp
  have e2: "(smt_extract (size x) (size x) ?S :: 1 word) = (if bit ?S (size x) then 1 else 0)"
    using smt_extract_bit[OF szS] .
  show "smt_uaddo TYPE('c) x y = (smtlib_extract w w ?S = (1::1 word))"
    unfolding smt_uaddo_def using e1 e2 by simp
qed

(*
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
*)

named_theorems rewrite_bv_saddo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_saddo_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word" and wm1::"int"
  shows "NO_MATCH cvc_a (undefined x y wm1)
    \<Longrightarrow> wm1 = int (size x) - 1
    \<Longrightarrow> smt_saddo TYPE('a) x y =
        (((smtlib_extract wm1 wm1 x = (1::1 word) \<and> smtlib_extract wm1 wm1 y = (1::1 word)) \<and> smtlib_extract wm1 wm1 (x + y) = (0::1 word))
       \<or> ((smtlib_extract wm1 wm1 x = (0::1 word) \<and> smtlib_extract wm1 wm1 y = (0::1 word)) \<and> smtlib_extract wm1 wm1 (x + y) = (1::1 word)))"
proof -
  assume wm1: "wm1 = int (size x) - 1"
  have wm1': "wm1 = int (size x - 1)"
    using wm1
    by (simp add: le_def)
  have key: "(smtlib_extract wm1 wm1 z :: 1 word) = smt_extract (size x - 1) (size x - 1) z" for z :: "'a word"
  proof -
    have szlt: "size x - 1 < size (z::'a word)" by (simp add: word_size)
    have "(smtlib_extract wm1 wm1 z :: 1 word) = (if bit z (size x - 1) then 1 else 0)"
      unfolding wm1' using smtlib_extract_eq_iff[of "size x - 1" z] by simp
    moreover have "(smt_extract (size x - 1) (size x - 1) z :: 1 word) = (if bit z (size x - 1) then 1 else 0)"
      using smt_extract_bit[OF szlt] .
    ultimately show ?thesis by simp
  qed
  show "smt_saddo TYPE('a) x y =
        (((smtlib_extract wm1 wm1 x = (1::1 word) \<and> smtlib_extract wm1 wm1 y = (1::1 word)) \<and> smtlib_extract wm1 wm1 (x + y) = (0::1 word))
       \<or> ((smtlib_extract wm1 wm1 x = (0::1 word) \<and> smtlib_extract wm1 wm1 y = (0::1 word)) \<and> smtlib_extract wm1 wm1 (x + y) = (1::1 word)))"
    unfolding smt_saddo_def Let_def by (simp add: key)
qed

(*
(define-cond-rule bv-usubo-eliminate
  ((x ?BitVec) (y ?BitVec) (n Int))
  (def
    (s (bvsub (zero_extend 1 x) (zero_extend 1 y)))
  )
  (= n (@bvsize x))
  (bvusubo x y)
  (= (extract n n s) (@bv 1 1)))
*)

named_theorems rewrite_bv_usubo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_usubo_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x y n)
    \<Longrightarrow> n = int (size x)
    \<Longrightarrow> LENGTH('c) = LENGTH('a) + 1
    \<Longrightarrow> smt_usubo TYPE('c::len) x y =
        (smtlib_extract n n
          (Word.cast x - Word.cast y :: 'c::len word) = (1::1 word))"
proof -
  assume n: "n = int (size x)" and lc: "LENGTH('c) = LENGTH('a) + 1"
  let ?S = "Word.cast x - Word.cast y :: 'c word"
  have szS: "size x < size ?S" using lc by (simp add: word_size)
  have e1: "(smtlib_extract n n ?S :: 1 word) = (if bit ?S (size x) then 1 else 0)"
    using n smtlib_extract_eq_iff[of "size x" ?S] by simp
  have e2: "(smt_extract (size x) (size x) ?S :: 1 word) = (if bit ?S (size x) then 1 else 0)"
    using smt_extract_bit[OF szS] .
  show "smt_usubo TYPE('c) x y = (smtlib_extract n n ?S = (1::1 word))"
    unfolding smt_usubo_def using e1 e2 by simp
qed

(*
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
*)

named_theorems rewrite_bv_ssubo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ssubo_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word" and nm1::"int"
  shows "NO_MATCH cvc_a (undefined x y nm1)
    \<Longrightarrow> nm1 = int (size x) - 1
    \<Longrightarrow> smt_ssubo x y =
        (((smtlib_extract nm1 nm1 x = (1::1 word) \<and> smtlib_extract nm1 nm1 y = (0::1 word)) \<and> smtlib_extract nm1 nm1 (x - y) = (0::1 word))
       \<or> ((smtlib_extract nm1 nm1 x = (0::1 word) \<and> smtlib_extract nm1 nm1 y = (1::1 word)) \<and> smtlib_extract nm1 nm1 (x - y) = (1::1 word)))"
proof -
  assume nm1: "nm1 = int (size x) - 1"
  have nm1': "nm1 = int (size x - 1)"
    using nm1
    by (simp add: le_def)
  have key: "(smtlib_extract nm1 nm1 z :: 1 word) = smt_extract (size x - 1) (size x - 1) z" for z :: "'a word"
  proof -
    have szlt: "size x - 1 < size (z::'a word)" by (simp add: word_size)
    have "(smtlib_extract nm1 nm1 z :: 1 word) = (if bit z (size x - 1) then 1 else 0)"
      unfolding nm1' using smtlib_extract_eq_iff[of "size x - 1" z] by simp
    moreover have "(smt_extract (size x - 1) (size x - 1) z :: 1 word) = (if bit z (size x - 1) then 1 else 0)"
      using smt_extract_bit[OF szlt] .
    ultimately show ?thesis by simp
  qed
  show "smt_ssubo x y =
        (((smtlib_extract nm1 nm1 x = (1::1 word) \<and> smtlib_extract nm1 nm1 y = (0::1 word)) \<and> smtlib_extract nm1 nm1 (x - y) = (0::1 word))
       \<or> ((smtlib_extract nm1 nm1 x = (0::1 word) \<and> smtlib_extract nm1 nm1 y = (1::1 word)) \<and> smtlib_extract nm1 nm1 (x - y) = (1::1 word)))"
    unfolding smt_ssubo_def Let_def by (simp add: key)
qed

(*
(define-cond-rule bv-sdivo-eliminate
  ((x ?BitVec) (y ?BitVec) (w Int) (wm1 Int))
  (and (= wm1 (- (@bvsize x) 1)) (= w (@bvsize y)))
  (bvsdivo x y)
  (and
    (= x (concat (@bv 1 1) (@bv 0 wm1)))
    (= y (bvnot (@bv 0 w)))
  ))
*)

named_theorems rewrite_bv_sdivo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sdivo_eliminate]:
  fixes x::"'a::len word" and y::"'b::len word" and w::"int" and wm1::"int"
  shows "NO_MATCH cvc_a (undefined x y w wm1)
    \<Longrightarrow> LENGTH('c) = nat wm1
    \<Longrightarrow> LENGTH('b) = nat w
    \<Longrightarrow> smt_sdivo TYPE('c::len) x y =
        (x = word_cat (1::1 word) (0::'c::len word) \<and> y = not (0::'b::len word))"
proof -
  have my: "(mask (size y)::'b word) = not (0::'b word)"
  proof (rule bit_word_eqI)
    fix k :: nat assume "k < LENGTH('b)"
    thus "bit (mask (size y)::'b word) k = bit (not (0::'b word)) k"
      by (simp add: bit_simps word_size)
  qed
  show "smt_sdivo TYPE('c) x y =
        (x = word_cat (1::1 word) (0::'c word) \<and> y = not (0::'b word))"
    unfolding smt_sdivo_def by (simp add: my)
qed

(*
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
*)

named_theorems rewrite_bv_smod_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_smod_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word" and w wm1::"int"
  shows "NO_MATCH cvc_a (undefined x y w wm1)
    \<Longrightarrow> wm1 = int (size x) - 1
    \<Longrightarrow> smt_smod x y =
        (if smt_urem (if smtlib_extract wm1 wm1 x = (0::1 word) then x else - x)
                     (if smtlib_extract wm1 wm1 y = (0::1 word) then y else - y) = (0::'a word)
         then smt_urem (if smtlib_extract wm1 wm1 x = (0::1 word) then x else - x)
                       (if smtlib_extract wm1 wm1 y = (0::1 word) then y else - y)
         else if smtlib_extract wm1 wm1 x = (0::1 word) \<and> smtlib_extract wm1 wm1 y = (0::1 word)
         then smt_urem (if smtlib_extract wm1 wm1 x = (0::1 word) then x else - x)
                       (if smtlib_extract wm1 wm1 y = (0::1 word) then y else - y)
         else if smtlib_extract wm1 wm1 x = (1::1 word) \<and> smtlib_extract wm1 wm1 y = (0::1 word)
         then - smt_urem (if smtlib_extract wm1 wm1 x = (0::1 word) then x else - x)
                         (if smtlib_extract wm1 wm1 y = (0::1 word) then y else - y) + y
         else if smtlib_extract wm1 wm1 x = (0::1 word) \<and> smtlib_extract wm1 wm1 y = (1::1 word)
         then smt_urem (if smtlib_extract wm1 wm1 x = (0::1 word) then x else - x)
                       (if smtlib_extract wm1 wm1 y = (0::1 word) then y else - y) + y
         else - smt_urem (if smtlib_extract wm1 wm1 x = (0::1 word) then x else - x)
                         (if smtlib_extract wm1 wm1 y = (0::1 word) then y else - y))"
proof -
  assume wm1: "wm1 = int (size x) - 1"
  have wm1': "wm1 = int (size x - 1)"
    using wm1
    by (simp add: le_def)
  have key: "(smtlib_extract wm1 wm1 z :: 1 word) = smt_extract (size x - 1) (size x - 1) z" for z :: "'a word"
  proof -
    have szlt: "size x - 1 < size (z::'a word)" by (simp add: word_size)
    have "(smtlib_extract wm1 wm1 z :: 1 word) = (if bit z (size x - 1) then 1 else 0)"
      unfolding wm1' using smtlib_extract_eq_iff[of "size x - 1" z] by simp
    moreover have "(smt_extract (size x - 1) (size x - 1) z :: 1 word) = (if bit z (size x - 1) then 1 else 0)"
      using smt_extract_bit[OF szlt] .
    ultimately show ?thesis by simp
  qed
  show "smt_smod x y =
        (if smt_urem (if smtlib_extract wm1 wm1 x = (0::1 word) then x else - x)
                     (if smtlib_extract wm1 wm1 y = (0::1 word) then y else - y) = (0::'a word)
         then smt_urem (if smtlib_extract wm1 wm1 x = (0::1 word) then x else - x)
                       (if smtlib_extract wm1 wm1 y = (0::1 word) then y else - y)
         else if smtlib_extract wm1 wm1 x = (0::1 word) \<and> smtlib_extract wm1 wm1 y = (0::1 word)
         then smt_urem (if smtlib_extract wm1 wm1 x = (0::1 word) then x else - x)
                       (if smtlib_extract wm1 wm1 y = (0::1 word) then y else - y)
         else if smtlib_extract wm1 wm1 x = (1::1 word) \<and> smtlib_extract wm1 wm1 y = (0::1 word)
         then - smt_urem (if smtlib_extract wm1 wm1 x = (0::1 word) then x else - x)
                         (if smtlib_extract wm1 wm1 y = (0::1 word) then y else - y) + y
         else if smtlib_extract wm1 wm1 x = (0::1 word) \<and> smtlib_extract wm1 wm1 y = (1::1 word)
         then smt_urem (if smtlib_extract wm1 wm1 x = (0::1 word) then x else - x)
                       (if smtlib_extract wm1 wm1 y = (0::1 word) then y else - y) + y
         else - smt_urem (if smtlib_extract wm1 wm1 x = (0::1 word) then x else - x)
                         (if smtlib_extract wm1 wm1 y = (0::1 word) then y else - y))"
    unfolding smt_smod_def Let_def by (simp add: key)
qed

(*
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
*)

named_theorems rewrite_bv_srem_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_srem_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word" and nm1::"int"
  shows "NO_MATCH cvc_a (undefined x y nm1)
    \<Longrightarrow> nm1 = int (size x) - 1
    \<Longrightarrow> smt_srem x y =
        (if smtlib_extract nm1 nm1 x = (1::1 word)
         then - smt_urem (if smtlib_extract nm1 nm1 x = (1::1 word) then - x else x)
                         (if smtlib_extract nm1 nm1 y = (1::1 word) then - y else y)
         else smt_urem (if smtlib_extract nm1 nm1 x = (1::1 word) then - x else x)
                       (if smtlib_extract nm1 nm1 y = (1::1 word) then - y else y))"
proof -
  assume nm1: "nm1 = int (size x) - 1"
  have nm1': "nm1 = int (size x - 1)"
    using nm1
    by (simp add: le_def)
  have e1: "(smtlib_extract nm1 nm1 z :: 1 word) = (if bit z (size x - 1) then 1 else 0)" for z :: "'a word"
    unfolding nm1' using smtlib_extract_eq_iff[of "size x - 1" z] by simp
  have e2: "(smt_extract (size x - 1) (size x - 1) z :: 1 word) = (if bit z (size x - 1) then 1 else 0)" for z :: "'a word"
  proof -
    have szlt: "size x - 1 < size (z::'a word)" by (simp add: word_size)
    show ?thesis using smt_extract_bit[OF szlt] .
  qed
  show "smt_srem x y =
        (if smtlib_extract nm1 nm1 x = (1::1 word)
         then - smt_urem (if smtlib_extract nm1 nm1 x = (1::1 word) then - x else x)
                         (if smtlib_extract nm1 nm1 y = (1::1 word) then - y else y)
         else smt_urem (if smtlib_extract nm1 nm1 x = (1::1 word) then - x else x)
                       (if smtlib_extract nm1 nm1 y = (1::1 word) then - y else y))"
    unfolding smt_srem_def Let_def
    by (cases "bit x (size x - 1)"; cases "bit y (size x - 1)"; simp add: e1 e2)
qed

(*
(define-cond-rule bv-usubo-eliminate
  ((x ?BitVec) (y ?BitVec) (n Int))
  (def
    (s (bvsub (zero_extend 1 x) (zero_extend 1 y)))
  )
  (= n (@bvsize x))
  (bvusubo x y)
  (= (extract n n s) (@bv 1 1)))


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