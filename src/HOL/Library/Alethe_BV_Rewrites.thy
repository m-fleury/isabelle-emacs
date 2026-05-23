theory Alethe_BV_Rewrites
  imports Alethe_BV_Rewrites_Lemmas 
begin
declare[[show_types,show_sorts]]

declare[[smt_expert_debug_alethe_level=0]]

(*
(define-cond-rule bv-concat-extract-merge
  ((xs ?BitVec :list)
   (s ?BitVec)
   (ys ?BitVec :list)
   (i Int) (j Int) (j1 Int) (k Int)
  )
  (= j1 (+ j 1))
  (concat xs (extract k j1 s) (extract j i s) ys)
  (concat xs (extract k i s) ys))

If xs and ys are not empty they are parsed in as list of bitlists. So we don't use word_cat directly
but a wrapper.
*)



(*First prove without xs to make it easier:*)


lemma  bv_concat_extract_merge_helper:
  fixes s::"'a::len word" and ys::"bool list list" and i j j1 k ::"int"
  assumes a0: "j1 = j + 1"
  shows "
int LENGTH('b) = j - i + 1 \<Longrightarrow> j \<ge> i \<Longrightarrow> i \<ge> 0 \<Longrightarrow>
int LENGTH('c) = k - j1 + 1 \<Longrightarrow> k \<ge> j1 \<Longrightarrow> j1 \<ge> 0 \<Longrightarrow>
int LENGTH('d) = k - i + 1 \<Longrightarrow> k \<ge> i \<Longrightarrow> i \<ge> 0 \<Longrightarrow> LENGTH('d) = LENGTH('b) + LENGTH('c) \<Longrightarrow>
word_cat_length ys = LENGTH('e::len) \<Longrightarrow>
LENGTH('e) + LENGTH('b) = LENGTH('g) \<Longrightarrow>
LENGTH('g) + LENGTH('c) = LENGTH('f) \<Longrightarrow> 

(word_cat (smtlib_extract k j1 s::'c::len word) (word_cat_rbl_right (smtlib_extract j i s::'b::len word) ys TYPE('e)::'g::len word)::'f::len word)
=
(word_cat_rbl_right (smtlib_extract k i s::'d::len word) ys TYPE('e))
"
  apply (subst word_cat_rbl_right_comm[of "(smtlib_extract k j1 s::'c::len word)" "(smtlib_extract j i s::'b::len word)" ys,where 'c='e and 'd='g and 'e='f and 'f='d])
     apply simp_all
    apply (simp add: a0)
   (* apply (subst word_cat_smtlib_extract[of i "j" k s])
     apply standard+
      apply simp
   apply simp
  by simp*)
  sorry
    
lemma rewrite_bv_concat_extract_merge:
  fixes s::"'a::len word" and ys::"bool list list" and i j j1 k ::"int"
  assumes a0: "j1 = j + 1"
  shows "
int LENGTH('b) = j - i + 1 \<Longrightarrow> j \<ge> i \<Longrightarrow> i \<ge> 0 \<Longrightarrow>
int LENGTH('c) = k - j1 + 1 \<Longrightarrow> k \<ge> j1 \<Longrightarrow> j1 \<ge> 0 \<Longrightarrow>
int LENGTH('d) = k - i + 1 \<Longrightarrow> k \<ge> i \<Longrightarrow> i \<ge> 0 \<Longrightarrow> LENGTH('d) = LENGTH('b) + LENGTH('c) \<Longrightarrow>
word_cat_length ys = LENGTH('e::len) \<Longrightarrow>
LENGTH('e) + LENGTH('b) = LENGTH('g) \<Longrightarrow>
LENGTH('g) + LENGTH('c) = LENGTH('f) \<Longrightarrow> 
word_cat_length xs = LENGTH('h::len) \<Longrightarrow>
LENGTH('i) = LENGTH('h) + LENGTH ('f) \<Longrightarrow>
(word_cat_rbl_left xs (word_cat (smtlib_extract k j1 s::'c::len word) (word_cat_rbl_right (smtlib_extract j i s::'b::len word) ys TYPE('e)::'g::len word)::'f::len word) TYPE('h::len) ::'i::len word)
=
(word_cat_rbl_left xs (word_cat_rbl_right (smtlib_extract k i s::'d::len word) ys TYPE('e)::'f::len word) TYPE('h::len))
"
  apply (subst bv_concat_extract_merge_helper)
  by simp_all


















(*
; x[i..j][k..l] = x[i+k..i+l]
; note: could be fixed-point but we don't permit conditional fixed point
(define-cond-rule bv-extract-extract
  ((x ?BitVec) (i Int) (j Int) (k Int) (l Int) (ll Int) (kk Int))
  (and (= ll (+ i l)) (= kk (+ i k)))
  (extract l k (extract j i x))
  (extract ll kk x))
*)



named_theorems rewrite_bv_extract_extract \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_extract]:
  fixes x::"'a::len word" and i j k l ll kk ::int
  shows "NO_MATCH cvc_a (undefined x i j k l ll kk) \<Longrightarrow>
ll = i + l \<Longrightarrow> kk = i + k \<Longrightarrow>
LENGTH('b) = ll + 1 - kk \<Longrightarrow> ll \<ge> kk \<Longrightarrow> kk \<ge> 0 \<Longrightarrow>
LENGTH('c) = j + 1 - i \<Longrightarrow> j \<ge> i \<Longrightarrow> i \<ge> 0 \<Longrightarrow>
LENGTH('b) = l + 1 - k \<Longrightarrow> l \<ge> k \<Longrightarrow> k \<ge> 0 \<Longrightarrow>
l + 1 \<le> int LENGTH('c::len) \<Longrightarrow>
(smtlib_extract l k (smtlib_extract j i x::'c::len word)) = (smtlib_extract ll kk x::'b::len word)
"
proof -
  assume ll_eq: "ll = i + l"
  assume kk_eq: "kk = i + k"
  assume b_eq_l: "int LENGTH('b::len) = l + 1 - k"
  assume c_eq: "int LENGTH('c::len) = j + 1 - i"
  assume ij: "i \<le> j"
  assume i_nn: "0 \<le> i"
  assume lk: "k \<le> l"
  assume k_nn: "0 \<le> k"
  assume l_lt_c: "l + 1 \<le> int LENGTH('c::len)"

  from ij i_nn have j_nn: "0 \<le> j" by linarith
  from lk k_nn have l_nn: "0 \<le> l" by linarith
  from i_nn l_nn ll_eq have ll_nn: "0 \<le> ll" by linarith
  from i_nn k_nn kk_eq have kk_nn: "0 \<le> kk" by linarith

  let ?ni = "nat i" and ?nj = "nat j"
  let ?nk = "nat k" and ?nl = "nat l"
  let ?nll = "nat ll" and ?nkk = "nat kk"

  have nll_eq: "?nll = ?ni + ?nl"
    using ll_eq i_nn l_nn by (simp add: nat_add_distrib)
  have nkk_eq: "?nkk = ?ni + ?nk"
    using kk_eq i_nn k_nn by (simp add: nat_add_distrib)

  have ni_le_nj: "?ni \<le> ?nj" using ij i_nn by (simp add: nat_mono)
  have nk_le_nl: "?nk \<le> ?nl" using lk k_nn by (simp add: nat_mono)

  have b_nat: "LENGTH('b::len) = Suc ?nl - ?nk"
  proof -
    have "LENGTH('b::len) = nat (int LENGTH('b::len))" by simp
    also have "\<dots> = nat (l + 1 - k)" using b_eq_l by simp
    also have "\<dots> = Suc ?nl - ?nk"
      using k_nn lk l_nn by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed

  have c_nat: "LENGTH('c::len) = Suc ?nj - ?ni"
  proof -
    have "LENGTH('c::len) = nat (int LENGTH('c::len))" by simp
    also have "\<dots> = nat (j + 1 - i)" using c_eq by simp
    also have "\<dots> = Suc ?nj - ?ni"
      using i_nn ij j_nn by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed

  have nl_ni_le_nj: "?nl + ?ni \<le> ?nj"
  proof -
    from l_lt_c c_eq have li_le_j: "l + i \<le> j" by simp
    have "nat (l + i) \<le> ?nj"
      using li_le_j j_nn by (simp add: nat_mono)
    moreover have "nat (l + i) = ?nl + ?ni"
      using l_nn i_nn by (simp add: nat_add_distrib)
    ultimately show ?thesis by simp
  qed

  have e_inner: "(smtlib_extract j i x :: 'c::len word) = smt_extract ?nj ?ni x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='c and j="?nj" and i="?ni"]
          j_nn i_nn by (metis int_nat_eq)
  have e_outer: "(smtlib_extract l k (smt_extract ?nj ?ni x :: 'c::len word) :: 'b::len word)
                  = smt_extract ?nl ?nk (smt_extract ?nj ?ni x :: 'c::len word)"
    using smtlib_extract_eq_smt_extract[where 'a='c and 'b='b and j="?nl" and i="?nk"]
          l_nn k_nn by (metis int_nat_eq)
  have e_rhs: "(smtlib_extract ll kk x :: 'b::len word) = smt_extract ?nll ?nkk x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='b and j="?nll" and i="?nkk"]
          ll_nn kk_nn by (metis int_nat_eq)

  show "(smtlib_extract l k (smtlib_extract j i x::'c::len word)::'b::len word)
        = (smtlib_extract ll kk x::'b::len word)"
    unfolding e_inner e_outer e_rhs
  proof (rule bit_word_eqI)
    fix n :: nat
    assume n_lt: "n < LENGTH('b::len)"
    have n_nk_le_nl: "n + ?nk \<le> ?nl"
      using n_lt b_nat nk_le_nl by linarith
    have n_nk_ni_le_nj: "n + ?nk + ?ni \<le> ?nj"
      using n_nk_le_nl nl_ni_le_nj by linarith
    have n_nk_lt_c: "n + ?nk < LENGTH('c::len)"
      using n_nk_ni_le_nj c_nat ni_le_nj by linarith
    show "bit (smt_extract ?nl ?nk (smt_extract ?nj ?ni x :: 'c::len word) :: 'b::len word) n
        = bit (smt_extract ?nll ?nkk x :: 'b::len word) n"
      using n_lt n_nk_le_nl n_nk_ni_le_nj n_nk_lt_c nll_eq nkk_eq
      sorry
  qed
qed

(*

(define-cond-rule bv-extract-whole
  ((x ?BitVec) (n Int))
  (>= n (- (@bvsize x) 1))
  (extract n 0 x)
  x)
*)
named_theorems rewrite_bv_extract_whole \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_whole]:
  fixes x::"'a::len word" and n ::int
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow>
(int (size x) - 1 \<le> n) = True \<Longrightarrow> n \<ge> 0 \<Longrightarrow>
(smtlib_extract n 0 x) = x"
  unfolding smtlib_extract_def
  by (metis (mono_tags, opaque_lifting) add_nonneg_nonneg eq_diff_eq le_nat_iff linorder_not_le nat_zero_as_int slice_id take_bit_word_beyond_length_eq word_size zero_le_one zle_diff1_eq)

(*
; Case 1: (< j n) so the extract is self contained
(define-cond-rule bv-extract-concat-1
  ((x ?BitVec) (xs ?BitVec :list) (y ?BitVec)
  (i Int) (j Int))
  (<= j (@bvsize x))
  (extract j i (concat xs y x)) ; (concat ...) needs at least 2 children
  (extract j i x))

(step t484 (cl (= (extract 3 0 (concat (@bv 0 12) (extract 15 12 vptr$))) (extract 3 0 (extract 15 12 vptr$)))) :rule rare_rewrite :premises (t483) :args ("bv-extract-concat-1" (extract 15 12 vptr$) rare-list (@bv 0 12) 0 3))

*)


named_theorems rewrite_bv_extract_concat_1 \<open>automatically_generated\<close>

(*xs is empty*)
lemma [rewrite_bv_extract_concat_1]:
  fixes x::"'a::len word" and xs::"'c cvc_ListVar" and y::"'b::len word" and i::int and j::int
  shows "NO_MATCH cvc_a (undefined x xs y i j) \<Longrightarrow>
j + 1 \<le> int LENGTH('a::len) \<Longrightarrow>


LENGTH('a::len) + LENGTH('b::len) = LENGTH('d::len) \<Longrightarrow>
int LENGTH('e::len) = j + 1 - i \<Longrightarrow> j \<ge> i \<Longrightarrow> i \<ge> 0 \<Longrightarrow>
(smtlib_extract j i (word_cat y x::'d::len word)::'e::len word)
=
(smtlib_extract j i x)"
proof -
  assume nm: "NO_MATCH cvc_a (undefined x xs y i j)"
  assume jbound: "j + 1 \<le> int LENGTH('a::len)"
  assume d_len: "LENGTH('a::len) + LENGTH('b::len) = LENGTH('d::len)"
  assume e_len: "int LENGTH('e::len) = j + 1 - i"
  assume ij: "i \<le> j"
  assume i_nn: "0 \<le> i"

  from ij i_nn have j_nn: "0 \<le> j" by linarith

  let ?ni = "nat i" and ?nj = "nat j"

  have ni_le_nj: "?ni \<le> ?nj" using ij i_nn by (simp add: nat_mono)
  have nj_lt_a: "?nj < LENGTH('a::len)" using jbound j_nn by linarith

  have e_nat: "LENGTH('e::len) = Suc ?nj - ?ni"
  proof -
    have "LENGTH('e::len) = nat (int LENGTH('e::len))" by simp
    also have "\<dots> = nat (j + 1 - i)" using e_len by simp
    also have "\<dots> = Suc ?nj - ?ni"
      using i_nn ij j_nn by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed

  have e_x: "(smtlib_extract j i x :: 'e::len word) = smt_extract ?nj ?ni x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='e and j="?nj" and i="?ni"]
          j_nn i_nn by (metis int_nat_eq)
  have e_yx: "(smtlib_extract j i (word_cat y x :: 'd::len word) :: 'e::len word)
              = smt_extract ?nj ?ni (word_cat y x :: 'd::len word)"
    using smtlib_extract_eq_smt_extract[where 'a='d and 'b='e and j="?nj" and i="?ni"]
          j_nn i_nn by (metis int_nat_eq)

  show "(smtlib_extract j i (word_cat y x::'d::len word)::'e::len word)
          = smtlib_extract j i x"
    unfolding e_x e_yx
  proof (rule bit_word_eqI)
    fix n :: nat
    assume n_lt: "n < LENGTH('e::len)"
    from n_lt e_nat ni_le_nj have n_ni_le_nj: "n + ?ni \<le> ?nj" by linarith
    hence n_ni_lt_a: "n + ?ni < LENGTH('a::len)" using nj_lt_a by linarith
    have n_ni_lt_d: "n + ?ni < LENGTH('d::len)"
      using n_ni_lt_a d_len by linarith
    from n_lt n_ni_le_nj n_ni_lt_a n_ni_lt_d
    show "bit (smt_extract ?nj ?ni (word_cat y x :: 'd::len word) :: 'e::len word) n
        = bit (smt_extract ?nj ?ni x :: 'e::len word) n"
      by (auto simp: bit_smt_extract bit_word_cat_iff)
  qed
qed



(*xs is non empty and its element have different bit-widths*)
lemma [rewrite_bv_extract_concat_1]:
  fixes x::"'a::len word" and xs::"bool list list" and y::"'b::len word" and i::int and j::int
  shows "NO_MATCH cvc_a (undefined x xs y i j) \<Longrightarrow>
j + 1 \<le> int LENGTH('a::len) \<Longrightarrow>

word_cat_length xs = LENGTH('c::len) \<Longrightarrow>
LENGTH('a::len) + LENGTH('b::len) = LENGTH('d::len) \<Longrightarrow>
LENGTH('c::len) + LENGTH('d::len) = LENGTH('h::len) \<Longrightarrow>
0 \<le> i \<Longrightarrow> int LENGTH('e::len) = j + 1 - i \<Longrightarrow>
(smtlib_extract j i
   (word_cat_rbl_left xs (word_cat y x::'d::len word) TYPE('c)::'h::len word)
 ::'e::len word)
=
(smtlib_extract j i x)"
proof -
  assume jbound: "j + 1 \<le> int LENGTH('a::len)"
  assume i_nn: "0 \<le> i"
  assume xs_len: "word_cat_length xs = LENGTH('c::len)"
  assume d_len: "LENGTH('a::len) + LENGTH('b::len) = LENGTH('d::len)"
  assume h_len: "LENGTH('c::len) + LENGTH('d::len) = LENGTH('h::len)"
  assume e_len: "int LENGTH('e::len) = j + 1 - i"

  from jbound i_nn have ij: "i \<le> j"
    by (metis diff_gt_0_iff_gt e_len int_eq_iff len_gt_0 nat_less_iff of_nat_0_eq_iff
        zle_add1_eq_le)
  from ij i_nn have j_nn: "0 \<le> j" by linarith

  let ?ni = "nat i" and ?nj = "nat j"

  have ni_le_nj: "?ni \<le> ?nj" using ij i_nn by (simp add: nat_mono)
  have nj_lt_a: "?nj < LENGTH('a::len)"
    using jbound j_nn by linarith

  have e_nat: "LENGTH('e::len) = Suc ?nj - ?ni"
  proof -
    have "LENGTH('e::len) = nat (int LENGTH('e::len))" by simp
    also have "\<dots> = nat (j + 1 - i)" using e_len by simp
    also have "\<dots> = Suc ?nj - ?ni"
      using i_nn ij j_nn by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed

  have e_x: "(smtlib_extract j i x :: 'e::len word) = smt_extract ?nj ?ni x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='e and j="?nj" and i="?ni"]
          j_nn i_nn by (metis int_nat_eq)
  have e_concat:
    "(smtlib_extract j i
        (word_cat (of_bl (concat xs) :: 'c::len word)
                  (word_cat y x::'d::len word) :: 'h::len word)
      :: 'e::len word)
       = smt_extract ?nj ?ni
           (word_cat (of_bl (concat xs) :: 'c::len word)
                     (word_cat y x::'d::len word) :: 'h::len word)"
    using smtlib_extract_eq_smt_extract[where 'a='h and 'b='e and j="?nj" and i="?ni"]
          j_nn i_nn by (metis int_nat_eq)

  show "(smtlib_extract j i
           (word_cat_rbl_left xs (word_cat y x::'d::len word) TYPE('c)
            ::'h::len word) :: 'e::len word)
       = smtlib_extract j i x"
    unfolding word_cat_rbl_left_def e_x e_concat
  proof (rule bit_word_eqI)
    fix n :: nat
    assume n_lt: "n < LENGTH('e::len)"
    from n_lt e_nat ni_le_nj have n_ni_le_nj: "n + ?ni \<le> ?nj" by linarith
    hence n_ni_lt_a: "n + ?ni < LENGTH('a::len)" using nj_lt_a by linarith
    have n_ni_lt_d: "n + ?ni < LENGTH('d::len)"
      using n_ni_lt_a d_len by linarith
    have n_ni_lt_h: "n + ?ni < LENGTH('h::len)"
      using n_ni_lt_d h_len by linarith
    from n_lt n_ni_le_nj n_ni_lt_a n_ni_lt_d n_ni_lt_h
    show "bit (smt_extract ?nj ?ni
                 (word_cat (of_bl (concat xs) :: 'c::len word)
                           (word_cat y x::'d::len word) :: 'h::len word)
              :: 'e::len word) n
        = bit (smt_extract ?nj ?ni x :: 'e::len word) n"
      by (auto simp: bit_smt_extract bit_word_cat_iff)
  qed
qed



(*
; Case 2: (< i n) but (>= j n), the extract crosses the boundary into the next one.
; Note that we do not know the size of the element after x, so we leave it in (extract ... (concat ...)) form
(define-cond-rule bv-extract-concat-2
  ((x ?BitVec) (xs ?BitVec :list) (y ?BitVec) (i Int) (j Int) (u1 Int) (u2 Int))
  (and (< i (@bvsize x)) (>= j (@bvsize x)) (= u1 (- j (@bvsize x))) (= u2 (- (@bvsize x) 1)))
  (extract j i (concat xs y x))
  (concat
    (extract u1 0 (concat xs y))
    (extract u2 i x)))
*)
(*
; Case 3: (>= i n) and (>= j n), extract elides x
(define-cond-rule bv-extract-concat-3
  ((x ?BitVec) (y ?BitVec) (xs ?BitVec :list) (i Int) (j Int) (u2 Int) (l2 Int))
  (and (>= i (@bvsize x)) (= u2 (- j (@bvsize x))) (= l2 (- i (@bvsize x))))
  (extract j i (concat xs y x))
  (extract u2 l2 (concat xs y)))
*)
(*
; Case 4: Elision from the higher portion
(define-cond-rule bv-extract-concat-4
  ((x ?BitVec) (y ?BitVec) (xs ?BitVec :list) (i Int) (j Int))
  (< j (- (@bvsize (concat x y xs)) (@bvsize x)))
  (extract j i (concat x xs y))
  (extract j i (concat xs y)))
*)

(*
; Motivated by TheoryBv::ppAssert, which turns an equality involving
; extract into a solved form for the variable we are extracting from.
(define-cond-rule bv-eq-extract-elim1
  ((x ?BitVec) (y ?BitVec) (i Int) (j Int) (wm1 Int) (jp1 Int) (im1 Int))
  (and (= wm1 (- (@bvsize x) 1)) (= jp1 (+ j 1)) (= im1 (- i 1)) (> wm1 j) (> i 0))
  (= (extract j i x) y)
  (= x (concat (extract wm1 jp1 x) y (extract im1 0 x))))

         (2::int) = int (size (c::3 word)) - 1
         (2::int) = 1 + 1
         0 = 1 - 1
         (1 < (2::int)) = True
         (0 < 1) = True
*)

named_theorems rewrite_bv_eq_extract_elim1 \<open>automatically_generated\<close>

lemma [rewrite_bv_eq_extract_elim1]:
  fixes x::"'a::len word" and y::"'b::len word" and i j wm1 jp1 im1 ::int
  shows "NO_MATCH cvc_a (undefined x y i j wm1 jp1 im1) \<Longrightarrow>
LENGTH('b) = j + 1 - i \<Longrightarrow> j \<ge> i \<Longrightarrow>
LENGTH('c) = im1 + 1 \<Longrightarrow>
LENGTH('c) + LENGTH('b) = LENGTH('d) \<Longrightarrow>
LENGTH('e) = wm1 + 1 - jp1 \<Longrightarrow>
wm1 = int (size x) - 1 \<Longrightarrow> jp1 = j + 1 \<Longrightarrow> im1 = i - 1 \<Longrightarrow> (j < wm1) = True \<Longrightarrow> (0 < i) = True \<Longrightarrow>
((smtlib_extract j i x) = y) = (x = (word_cat (smtlib_extract wm1 jp1 x::'e::len word) (word_cat y (smtlib_extract im1 0 x::'c::len word)::'d::len word)))"
proof -
  assume b_int: "int LENGTH('b::len) = j + 1 - i"
     and ij: "i \<le> j"
     and c_int: "int LENGTH('c::len) = im1 + 1"
     and d_eq: "LENGTH('c::len) + LENGTH('b::len) = LENGTH('d::len)"
     and e_int: "int LENGTH('e::len) = wm1 + 1 - jp1"
     and wm1_size: "wm1 = int (size x) - 1"
     and jp1_eq: "jp1 = j + 1"
     and im1_eq: "im1 = i - 1"
     and wm1_gt_j: "(j < wm1) = True"
     and i_pos': " (0 < i) = True"

  from i_pos' have i_pos: "1 \<le> i"
    by simp
  from i_pos' have i_nn: "0 \<le> i" by simp
  from im1_eq i_pos have im1_nn: "0 \<le> im1" by linarith
  from ij i_pos have j_nn: "0 \<le> j" by linarith
  from wm1_gt_j jp1_eq have wm1_jp1: "jp1 \<le> wm1" by simp
  from jp1_eq j_nn have jp1_nn: "0 \<le> jp1" by linarith
  from wm1_size have a_int: "int LENGTH('a::len) = wm1 + 1" by (simp add: word_size)
  from wm1_jp1 jp1_nn have wm1_nn: "0 \<le> wm1" by linarith

  let ?ni = "nat i" and ?nj = "nat j" and ?nwm1 = "nat wm1"
        and ?nim1 = "nat im1" and ?njp1 = "nat jp1"

  have ni_le_nj: "?ni \<le> ?nj" using ij i_nn j_nn by (simp add: nat_mono)

  have nim1_eq: "Suc ?nim1 = ?ni"
    using im1_eq i_pos im1_nn by (simp add: nat_diff_distrib)
  have njp1_eq: "?njp1 = Suc ?nj"
    using jp1_eq j_nn by (simp add: nat_add_distrib)

  have c_nat: "LENGTH('c::len) = ?ni"
  proof -
    have "int LENGTH('c::len) = int ?ni"
      using c_int im1_eq i_nn by simp
    thus ?thesis by linarith
  qed

  have b_nat: "LENGTH('b::len) = Suc ?nj - ?ni"
  proof -
    have "LENGTH('b::len) = nat (int LENGTH('b::len))" by simp
    also have "\<dots> = nat (j + 1 - i)" using b_int by simp
    also have "\<dots> = Suc ?nj - ?ni"
      using i_nn ij j_nn by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed

  have d_nat: "LENGTH('d::len) = Suc ?nj"
    using d_eq c_nat b_nat ni_le_nj by linarith

  have Snj_le_nwm1: "Suc ?nj \<le> ?nwm1"
    using wm1_jp1 jp1_eq j_nn wm1_nn by linarith

  have e_nat: "LENGTH('e::len) = ?nwm1 - ?nj"
  proof -
    have "LENGTH('e::len) = nat (int LENGTH('e::len))" by simp
    also have "\<dots> = nat (wm1 + 1 - jp1)" using e_int by simp
    also have "\<dots> = ?nwm1 - ?nj"
      using jp1_nn wm1_jp1 wm1_nn jp1_eq j_nn by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed

  have a_nat: "LENGTH('a::len) = Suc ?nwm1"
  proof -
    have "int LENGTH('a::len) = int (Suc ?nwm1)"
      using a_int wm1_nn by simp
    thus ?thesis by linarith
  qed

  have ext_b: "(smtlib_extract j i x :: 'b::len word) = smt_extract ?nj ?ni x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='b and j="?nj" and i="?ni"]
          j_nn i_nn by (metis int_nat_eq)

  have ext_e: "(smtlib_extract wm1 jp1 x :: 'e::len word) = smt_extract ?nwm1 (Suc ?nj) x"
  proof -
    have "(smtlib_extract wm1 jp1 x :: 'e::len word) = smt_extract ?nwm1 ?njp1 x"
      using smtlib_extract_eq_smt_extract[where 'a='a and 'b='e and j="?nwm1" and i="?njp1"]
            wm1_nn jp1_nn by (metis int_nat_eq)
    with njp1_eq show ?thesis by simp
  qed

  have ext_c: "(smtlib_extract im1 0 x :: 'c::len word) = smt_extract ?nim1 0 x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='c and j="?nim1" and i="0::nat"]
          im1_nn by simp

  show "((smtlib_extract j i x :: 'b::len word) = y)
        = (x = word_cat (smtlib_extract wm1 jp1 x :: 'e::len word)
                       (word_cat y (smtlib_extract im1 0 x :: 'c::len word) :: 'd::len word))"
    unfolding ext_b ext_e ext_c
  proof (rule iffI)
    assume H: "(smt_extract ?nj ?ni x :: 'b::len word) = y"
    show "x = word_cat (smt_extract ?nwm1 (Suc ?nj) x :: 'e::len word)
                      (word_cat y (smt_extract ?nim1 0 x :: 'c::len word) :: 'd::len word)"
    proof (rule bit_word_eqI)
      fix n :: nat
      assume n_lt_a: "n < LENGTH('a::len)"
      have n_lt_Snwm1: "n < Suc ?nwm1" using n_lt_a a_nat by simp
      show "bit x n
          = bit (word_cat (smt_extract ?nwm1 (Suc ?nj) x :: 'e::len word)
                  (word_cat y (smt_extract ?nim1 0 x :: 'c::len word) :: 'd::len word)
                 :: 'a::len word) n"
      proof (cases "n < LENGTH('d::len)")
        case d_in: True
        hence n_lt_Snj: "n < Suc ?nj" using d_nat by simp
        show ?thesis
        proof (cases "n < LENGTH('c::len)")
          case c_in: True
          hence n_lt_ni: "n < ?ni" using c_nat by simp
          have "bit (smt_extract ?nim1 0 x :: 'c::len word) n = bit x n"
            using n_lt_ni c_nat nim1_eq by (simp add: bit_smt_extract)
          thus ?thesis
            using c_in d_in n_lt_a by (simp add: bit_word_cat_iff)
        next
          case c_out: False
          hence ni_le_n: "?ni \<le> n" using c_nat by simp
          have y_bit: "bit y (n - LENGTH('c::len)) = bit x n"
          proof -
            have nc: "n - LENGTH('c::len) = n - ?ni" using c_nat by simp
            have lt_b: "n - ?ni < LENGTH('b::len)"
              using n_lt_Snj b_nat ni_le_n by linarith
            from H have "bit y (n - ?ni) = bit (smt_extract ?nj ?ni x :: 'b::len word) (n - ?ni)"
              by simp
            also have "\<dots> = bit x n"
              using lt_b ni_le_n n_lt_Snj by (simp add: bit_smt_extract)
            finally show ?thesis using nc by simp
          qed
          thus ?thesis
            using c_out d_in n_lt_a by (simp add: bit_word_cat_iff)
        qed
      next
        case d_out: False
        hence Snj_le_n: "Suc ?nj \<le> n" using d_nat by simp
        have e_bit: "bit (smt_extract ?nwm1 (Suc ?nj) x :: 'e::len word)
                         (n - LENGTH('d::len)) = bit x n"
        proof -
          have nd: "n - LENGTH('d::len) = n - Suc ?nj" using d_nat by simp
          have plus_back: "n - Suc ?nj + Suc ?nj = n" using Snj_le_n by simp
          have lt_e: "n - Suc ?nj < LENGTH('e::len)"
            using e_nat Snj_le_n n_lt_Snwm1 Snj_le_nwm1 by linarith
          show ?thesis
            using plus_back lt_e n_lt_Snwm1 nd by (simp add: bit_smt_extract)
        qed
        thus ?thesis
          using d_out n_lt_a by (simp add: bit_word_cat_iff)
      qed
    qed
  next
    assume H: "x = word_cat (smt_extract ?nwm1 (Suc ?nj) x :: 'e::len word)
                            (word_cat y (smt_extract ?nim1 0 x :: 'c::len word)
                             :: 'd::len word)"
    show "(smt_extract ?nj ?ni x :: 'b::len word) = y"
    proof (rule bit_word_eqI)
      fix n :: nat
      assume n_lt_b: "n < LENGTH('b::len)"
      have n_plus_ni_lt_Snj: "n + ?ni < Suc ?nj"
        using n_lt_b b_nat ni_le_nj by linarith
      have n_plus_ni_ge_c: "LENGTH('c::len) \<le> n + ?ni" using c_nat by simp
      have n_plus_ni_lt_d: "n + ?ni < LENGTH('d::len)"
        using d_nat n_plus_ni_lt_Snj by simp
      have n_plus_ni_lt_a: "n + ?ni < LENGTH('a::len)"
        using a_nat n_plus_ni_lt_Snj Snj_le_nwm1 by linarith
      have "bit (smt_extract ?nj ?ni x :: 'b::len word) n = bit x (n + ?ni)"
        using n_plus_ni_lt_Snj n_lt_b by (simp add: bit_smt_extract)
      also from H have "\<dots> = bit (word_cat (smt_extract ?nwm1 (Suc ?nj) x :: 'e::len word)
                            (word_cat y (smt_extract ?nim1 0 x :: 'c::len word)
                             :: 'd::len word) :: 'a::len word) (n + ?ni)"
        by simp
      also have "\<dots> = bit y n"
        using n_plus_ni_lt_d n_plus_ni_lt_a n_plus_ni_ge_c c_nat
        by (simp add: bit_word_cat_iff)
      finally show "bit (smt_extract ?nj ?ni x :: 'b::len word) n = bit y n" .
    qed
  qed
qed




(*
(define-cond-rule bv-eq-extract-elim2
  ((x ?BitVec) (y ?BitVec) (j Int) (wm1 Int) (jp1 Int))
  (and (= wm1 (- (@bvsize x) 1)) (= jp1 (+ j 1)) (> wm1 j))
  (= (extract j 0 x) y)

*)

named_theorems rewrite_bv_eq_extract_elim2 \<open>automatically_generated\<close>

lemma [rewrite_bv_eq_extract_elim2]:
  fixes x::"'a::len word" and y::"'b::len word" and j wm1 jp1 ::int
  shows "NO_MATCH cvc_a (undefined x y j wm1 jp1) \<Longrightarrow>
LENGTH('b) = j + 1 \<Longrightarrow> j \<ge> 0 \<Longrightarrow>
LENGTH('e) = wm1 + 1 - jp1 \<Longrightarrow> wm1 \<ge> jp1 \<Longrightarrow> jp1 \<ge> 0 \<Longrightarrow>
LENGTH('a) = LENGTH('e) + LENGTH('b) \<Longrightarrow>

wm1 = int(size x) - 1 \<Longrightarrow> jp1 = j + 1 \<Longrightarrow> (j <  wm1)  = True \<Longrightarrow>
((smtlib_extract j 0 x) = y) = (x = (word_cat (smtlib_extract wm1 jp1 x::'e::len word) y))"
proof -
  assume b_int: "int LENGTH('b::len) = j + 1"
     and j_nn: "0 \<le> j"
     and e_int: "int LENGTH('e::len) = wm1 + 1 - jp1"
     and wm1_jp1: "jp1 \<le> wm1"
     and jp1_nn: "0 \<le> jp1"
     and a_eq: "LENGTH('a::len) = LENGTH('e::len) + LENGTH('b::len)"
  and "wm1 = int(size x) - 1"
     and jp1_eq: "jp1 = j + 1" and "(j <  wm1)  = True"

  from wm1_jp1 jp1_nn have wm1_nn: "0 \<le> wm1" by linarith

  let ?nj = "nat j" and ?nwm1 = "nat wm1" and ?njp1 = "nat jp1"

  have njp1_eq: "?njp1 = Suc ?nj"
    using jp1_eq j_nn by (simp add: nat_add_distrib)

  have b_nat: "LENGTH('b::len) = Suc ?nj"
  proof -
    have "LENGTH('b::len) = nat (int LENGTH('b::len))" by simp
    also have "\<dots> = nat (j + 1)" using b_int by simp
    also have "\<dots> = Suc ?nj" using j_nn by simp
    finally show ?thesis .
  qed

  have Snj_le_nwm1: "Suc ?nj \<le> ?nwm1"
    using wm1_jp1 jp1_eq j_nn wm1_nn by linarith

  have e_nat: "LENGTH('e::len) = ?nwm1 - ?nj"
  proof -
    have "LENGTH('e::len) = nat (int LENGTH('e::len))" by simp
    also have "\<dots> = nat (wm1 + 1 - jp1)" using e_int by simp
    also have "\<dots> = ?nwm1 - ?nj"
      using jp1_nn wm1_jp1 wm1_nn jp1_eq j_nn by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed

  have a_nat: "LENGTH('a::len) = Suc ?nwm1"
    using a_eq e_nat b_nat Snj_le_nwm1 by linarith

  have ext_b: "(smtlib_extract j 0 x :: 'b::len word) = smt_extract ?nj 0 x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='b and j="?nj" and i="0::nat"]
          j_nn by simp

  have ext_e: "(smtlib_extract wm1 jp1 x :: 'e::len word) = smt_extract ?nwm1 (Suc ?nj) x"
  proof -
    have "(smtlib_extract wm1 jp1 x :: 'e::len word) = smt_extract ?nwm1 ?njp1 x"
      using smtlib_extract_eq_smt_extract[where 'a='a and 'b='e and j="?nwm1" and i="?njp1"]
            wm1_nn jp1_nn by (metis int_nat_eq)
    with njp1_eq show ?thesis by simp
  qed

  show "((smtlib_extract j 0 x) = y) = (x = (word_cat (smtlib_extract wm1 jp1 x::'e::len word) y))"
    unfolding ext_b ext_e
  proof (rule iffI)
    assume H: "(smt_extract (nat j) 0 x :: 'b::len word) = y"
    show "x = (word_cat (smt_extract (nat wm1) (Suc (nat j))  x :: 'e::len word) y :: 'a::len word)"
    proof (rule bit_word_eqI)
      fix n :: nat
      assume n_lt_a: "n < LENGTH('a::len)"
      have n_lt_Snwm1: "n < Suc ?nwm1" using n_lt_a a_nat by simp
      show "bit x n = bit (word_cat (smt_extract ?nwm1 (Suc ?nj) x :: 'e::len word) y
                            :: 'a::len word) n"
      proof (cases "n < LENGTH('b::len)")
        case b_in: True
        hence n_lt_Snj: "n < Suc ?nj" using b_nat by simp
        have "bit y n = bit x n"
        proof -
          from H have "bit y n = bit (smt_extract ?nj 0 x :: 'b::len word) n"
            by simp
          also have "\<dots> = bit x n"
            using n_lt_Snj b_in by (simp add: bit_smt_extract)
          finally show ?thesis .
        qed
        thus ?thesis
          using b_in n_lt_a by (simp add: bit_word_cat_iff)
      next
        case b_out: False
        hence Snj_le_n: "Suc ?nj \<le> n" using b_nat by simp
        have e_bit: "bit (smt_extract ?nwm1 (Suc ?nj) x :: 'e::len word)
                         (n - LENGTH('b::len)) = bit x n"
        proof -
          have nb: "n - LENGTH('b::len) = n - Suc ?nj" using b_nat by simp
          have plus_back: "n - Suc ?nj + Suc ?nj = n" using Snj_le_n by simp
          have lt_e: "n - Suc ?nj < LENGTH('e::len)"
            using e_nat Snj_le_n n_lt_Snwm1 Snj_le_nwm1 by linarith
          show ?thesis
            using plus_back lt_e n_lt_Snwm1 nb by (simp add: bit_smt_extract)
        qed
        thus ?thesis
          using b_out n_lt_a by (simp add: bit_word_cat_iff)
      qed
    qed
  next
    assume H: "x = word_cat (smt_extract (nat wm1) (Suc (nat j)) x :: 'e::len word) y"               
    show "(smt_extract ?nj 0 x :: 'b::len word) = y"
    proof (rule bit_word_eqI)
      fix n :: nat
      assume n_lt_b: "n < LENGTH('b::len)"
      have n_lt_Snj: "n < Suc ?nj" using n_lt_b b_nat by simp
      have n_lt_a: "n < LENGTH('a::len)"
        using a_nat n_lt_Snj Snj_le_nwm1 by linarith
      have "bit (smt_extract ?nj 0 x :: 'b::len word) n = bit x n"
        using n_lt_Snj n_lt_b by (simp add: bit_smt_extract)
      also from H have "\<dots> = bit (word_cat (smt_extract ?nwm1 (Suc ?nj) x :: 'e::len word) y
                            :: 'a::len word) n"
        by simp
      also have "\<dots> = bit y n"
        using n_lt_b n_lt_a by (simp add: bit_word_cat_iff)
      finally show "bit (smt_extract ?nj 0 x :: 'b::len word) n = bit y n" .
    qed
  qed
qed


(*
(define-cond-rule bv-eq-extract-elim3
  ((x ?BitVec) (y ?BitVec) (i Int) (j Int) (im1 Int))
  (and (= j (- (@bvsize x) 1)) (= im1 (- i 1)) (> i 0))
  (= (extract j i x) y)
  (= x (concat y (extract im1 0 x))))

 TODO: use assumptions:
         (15::int) = int (size (x::16 word)) - 1
         (14::int) = (15::int) - 1
         (0 < (15::int)) = True
*)

named_theorems rewrite_bv_eq_extract_elim3 \<open>automatically_generated\<close>

lemma [rewrite_bv_eq_extract_elim3]:
  fixes x::"'a::len word" and y::"'b::len word" and i j im1 ::int
  shows "NO_MATCH cvc_a (undefined x y i j im1) \<Longrightarrow>
LENGTH('b) = j + 1 - i \<Longrightarrow> j \<ge> i \<Longrightarrow> i \<ge> 0 \<Longrightarrow>
LENGTH('c) = im1 + 1 \<Longrightarrow> im1 \<ge> 0 \<Longrightarrow> im1 = i - 1 \<Longrightarrow>
LENGTH('a) = LENGTH('b) + LENGTH('c) \<Longrightarrow>
((smtlib_extract j i x) = y) = (x = (word_cat y (smtlib_extract im1 0 x::'c::len word) :: 'a::len word))"
proof -
  assume b_int: "int LENGTH('b::len) = j + 1 - i"
     and ij: "i \<le> j"
     and i_nn: "0 \<le> i"
     and c_int: "int LENGTH('c::len) = im1 + 1"
     and im1_nn: "0 \<le> im1"
     and im1_eq: "im1 = i - 1"
     and a_eq: "LENGTH('a::len) = LENGTH('b::len) + LENGTH('c::len)"

  from im1_eq im1_nn have i_pos: "1 \<le> i" by linarith
  from ij i_pos have j_nn: "0 \<le> j" by linarith

  let ?ni = "nat i" and ?nj = "nat j" and ?nim1 = "nat im1"

  have ni_le_nj: "?ni \<le> ?nj" using ij i_nn j_nn by (simp add: nat_mono)

  have nim1_eq: "Suc ?nim1 = ?ni"
    using im1_eq i_pos im1_nn by (simp add: nat_diff_distrib)

  have c_nat: "LENGTH('c::len) = ?ni"
  proof -
    have "int LENGTH('c::len) = int ?ni"
      using c_int im1_eq i_nn by simp
    thus ?thesis by linarith
  qed

  have b_nat: "LENGTH('b::len) = Suc ?nj - ?ni"
  proof -
    have "LENGTH('b::len) = nat (int LENGTH('b::len))" by simp
    also have "\<dots> = nat (j + 1 - i)" using b_int by simp
    also have "\<dots> = Suc ?nj - ?ni"
      using i_nn ij j_nn by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed

  have a_nat: "LENGTH('a::len) = Suc ?nj"
    using a_eq c_nat b_nat ni_le_nj by linarith

  have ext_b: "(smtlib_extract j i x :: 'b::len word) = smt_extract ?nj ?ni x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='b and j="?nj" and i="?ni"]
          j_nn i_nn by (metis int_nat_eq)

  have ext_c: "(smtlib_extract im1 0 x :: 'c::len word) = smt_extract ?nim1 0 x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='c and j="?nim1" and i="0::nat"]
          im1_nn by simp

  show "((smtlib_extract j i x :: 'b::len word) = y)
        = (x = (word_cat y (smtlib_extract im1 0 x :: 'c::len word) :: 'a::len word))"
    unfolding ext_b ext_c
  proof (rule iffI)
    assume H: "(smt_extract ?nj ?ni x :: 'b::len word) = y"
    show "x = (word_cat y (smt_extract ?nim1 0 x :: 'c::len word) :: 'a::len word)"
    proof (rule bit_word_eqI)
      fix n :: nat
      assume n_lt_a: "n < LENGTH('a::len)"
      have n_lt_Snj: "n < Suc ?nj" using n_lt_a a_nat by simp
      show "bit x n = bit (word_cat y (smt_extract ?nim1 0 x :: 'c::len word)
                            :: 'a::len word) n"
      proof (cases "n < LENGTH('c::len)")
        case c_in: True
        hence n_lt_ni: "n < ?ni" using c_nat by simp
        have "bit (smt_extract ?nim1 0 x :: 'c::len word) n = bit x n"
          using n_lt_ni c_nat nim1_eq by (simp add: bit_smt_extract)
        thus ?thesis
          using c_in n_lt_a by (simp add: bit_word_cat_iff)
      next
        case c_out: False
        hence ni_le_n: "?ni \<le> n" using c_nat by simp
        have y_bit: "bit y (n - LENGTH('c::len)) = bit x n"
        proof -
          have nc: "n - LENGTH('c::len) = n - ?ni" using c_nat by simp
          have lt_b: "n - ?ni < LENGTH('b::len)"
            using n_lt_Snj b_nat ni_le_n by linarith
          from H have "bit y (n - ?ni) = bit (smt_extract ?nj ?ni x :: 'b::len word) (n - ?ni)"
            by simp
          also have "\<dots> = bit x n"
            using lt_b ni_le_n n_lt_Snj by (simp add: bit_smt_extract)
          finally show ?thesis using nc by simp
        qed
        thus ?thesis
          using c_out n_lt_a by (simp add: bit_word_cat_iff)
      qed
    qed
  next
    assume H: "x = (word_cat y (smt_extract ?nim1 0 x :: 'c::len word) :: 'a::len word)"
    show "(smt_extract ?nj ?ni x :: 'b::len word) = y"
    proof (rule bit_word_eqI)
      fix n :: nat
      assume n_lt_b: "n < LENGTH('b::len)"
      have n_plus_ni_lt_Snj: "n + ?ni < Suc ?nj"
        using n_lt_b b_nat ni_le_nj by linarith
      have n_plus_ni_ge_c: "LENGTH('c::len) \<le> n + ?ni" using c_nat by simp
      have n_plus_ni_lt_a: "n + ?ni < LENGTH('a::len)"
        using a_nat n_plus_ni_lt_Snj by simp
      have "bit (smt_extract ?nj ?ni x :: 'b::len word) n = bit x (n + ?ni)"
        using n_plus_ni_lt_Snj n_lt_b by (simp add: bit_smt_extract)
      also from H have "\<dots> = bit (word_cat y (smt_extract ?nim1 0 x :: 'c::len word)
                            :: 'a::len word) (n + ?ni)"
        by simp
      also have "\<dots> = bit y n"
        using n_plus_ni_lt_a n_plus_ni_ge_c c_nat
        by (simp add: bit_word_cat_iff)
      finally show "bit (smt_extract ?nj ?ni x :: 'b::len word) n = bit y n" .
    qed
  qed
qed
(*
(define-rule bv-extract-not
  ((x ?BitVec) (i Int) (j Int))
  (extract j i (bvnot x))
  (bvnot (extract j i x)))
*)
(*
(define-cond-rule bv-extract-sign-extend-1
  ((x ?BitVec) (low Int) (high Int) (k Int))
  (< high (@bvsize x))
  (extract high low (sign_extend k x))
  (extract high low x))
*)
(*
(define-cond-rule bv-extract-sign-extend-2
  ((x ?BitVec) (low Int) (high Int) (k Int) (nm1 Int) (sn Int))
  (def (n (@bvsize x)))
  (and (< low n) (>= high n) (= nm1 (- n 1)) (= sn (+ 1 (- high n))))
  (extract high low (sign_extend k x))
  (sign_extend
    sn
    (extract nm1 low x)))
*)
(*
(define-cond-rule bv-extract-sign-extend-3
  ((x ?BitVec) (low Int) (high Int) (k Int) (rn Int) (nm1 Int))
  (def (n (@bvsize x)))
  (and (>= low n) (= rn (+ 1 (- high low))) (= nm1 (- n 1)))
  (extract high low (sign_extend k x))
  (repeat rn (extract nm1 nm1 x)))
*)
(*
(define-rule bv-not-xor
  ((x1 ?BitVec) (x2 ?BitVec) (xs ?BitVec :list))
  (bvnot (bvxor x1 x2 xs))
  (bvxor (bvnot x1) x2 xs))
*)

(*
(define-cond-rule bv-and-simplify-1
  ((xs ?BitVec :list) (ys ?BitVec :list) (zs ?BitVec :list) (x ?BitVec) (w Int))
  (= w (@bvsize x))
  (bvand xs (bvnot x) ys x zs)
  (@bv 0 w))
*)
(*
(define-cond-rule bv-and-simplify-2
  ((xs ?BitVec :list) (ys ?BitVec :list) (zs ?BitVec :list) (x ?BitVec) (w Int))
  (= w (@bvsize x))
  (bvand xs x ys (bvnot x) zs)
  (@bv 0 w))
*)
(*
(define-cond-rule bv-or-simplify-1
  ((xs ?BitVec :list) (ys ?BitVec :list) (zs ?BitVec :list) (x ?BitVec) (w Int))
  (= w (@bvsize x))
  (bvor xs (bvnot x) ys x zs)
  (bvnot (@bv 0 w)))
*)
(*
(define-cond-rule bv-or-simplify-2
  ((xs ?BitVec :list) (ys ?BitVec :list) (zs ?BitVec :list) (x ?BitVec) (w Int))
  (= w (@bvsize x))
  (bvor xs x ys (bvnot x) zs)
  (bvnot (@bv 0 w)))
*)

(*
(define-rule* bv-xor-simplify-1
  ((xs ?BitVec :list) (ys ?BitVec :list) (zs ?BitVec :list) (x ?BitVec))
  (bvxor xs x ys x zs)
  (bvxor xs ys zs))
*)
(*
(define-rule bv-xor-simplify-2
  ((xs ?BitVec :list) (ys ?BitVec :list) (zs ?BitVec :list) (x ?BitVec))
  (bvxor xs x ys (bvnot x) zs)
  (bvnot (bvxor xs ys zs)))
*)
(*
(define-rule bv-xor-simplify-3
  ((xs ?BitVec :list) (ys ?BitVec :list) (zs ?BitVec :list) (x ?BitVec))
  (bvxor xs (bvnot x) ys x zs)
  (bvnot (bvxor xs ys zs)))
*)

(*
; x < ys + 1 + zs <=> (not (ys + zs) < x) and (ys + zs) != 1...1
; we use ys, zs as lists so that 1 may appear on the left or the right of the bvadd term.
(define-cond-rule bv-ult-add-one
  ((x ?BitVec) (ys ?BitVec :list) (zs ?BitVec :list) (c1 ?BitVec) (w Int))
  (and (= c1 (@bv 1 w)) (= w (@bvsize x)))
  (bvult x (bvadd ys c1 zs))
  (and
    (not (= (bvadd ys zs) (bvnot (@bv 0 w))))
    (not (bvult (bvadd ys zs) x))))
*)
(*
(define-cond-rule bv-mult-slt-mult-1
  ((x ?BitVec) (y ?BitVec) (a ?BitVec) (n Int) (m Int) (tn Int) (an Int))
  (and (= tn (@bvsize x)) (= an (@bvsize a)))
  (bvslt
    (bvmul (sign_extend n y) (sign_extend m a))
    (bvmul (sign_extend n x) (sign_extend m a))
  )
  (and
    (not (= (bvsub y x) (@bv 0 tn)))
    (not (= a (@bv 0 an)))
    (= (bvslt y x) (bvsgt a (@bv 0 an)))))
*)

(*
(define-cond-rule bv-mult-slt-mult-2
  ((x ?BitVec) (y ?BitVec) (a ?BitVec) (n Int) (m Int) (tn Int) (an Int))
  (and (= tn (@bvsize x)) (= an (@bvsize a)))
  (bvslt
    (bvmul (zero_extend n y) (sign_extend m a))
    (bvmul (zero_extend n x) (sign_extend m a))
  )
  (and
    (not (= (bvsub y x) (@bv 0 tn)))
    (not (= a (@bv 0 an)))
    (= (bvult y x) (bvsgt a (@bv 0 an)))))
*)

(*
(define-rule bv-commutative-xor ((x ?BitVec) (y ?BitVec))
  (bvxor x y) (bvxor y x))
*)

(*
(define-rule bv-commutative-comp ((x ?BitVec) (y ?BitVec))
  (bvcomp x y) (bvcomp y x))
*)
(*
(define-rule bv-zero-extend-eliminate-0
  ((x ?BitVec))
  (zero_extend 0 x)
  x)
*)
(*
(define-rule bv-sign-extend-eliminate-0
  ((x ?BitVec))
  (sign_extend 0 x)
  x)
*)

(*
(define-cond-rule bv-not-neq ((x ?BitVec))
  (> (@bvsize x) 0)
  (= x (bvnot x))
  false)
*)
(*
(define-cond-rule bv-ult-ones ((x ?BitVec) (n Int) (w Int))
  (= n (- (int.pow2 w) 1))
  (bvult x (@bv n w))
  (distinct x (@bv n w)))
*)

(*

(define-cond-rule bv-concat-merge-const
  ((xs ?BitVec :list)
   (n1 Int) (w1 Int) (n2 Int) (w2 Int) (ww Int)
   (zs ?BitVec :list))
  (= ww (+ w1 w2))
  (concat xs (@bv n1 w1) (@bv n2 w2) zs)
  (concat xs (@bv (+ (\* n1 (int.pow2 w2)) (mod n2 (int.pow2 w2))) ww) zs))

*)


(*

(define-rule bv-extract-not
  ((x ?BitVec) (i Int) (j Int))
  (extract j i (bvnot x))
  (bvnot (extract j i x)))
*)

named_theorems rewrite_bv_extract_not \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_not]:
  fixes x::"'a::len word" and i j ::int
  shows "NO_MATCH cvc_a (undefined x i j) \<Longrightarrow>
LENGTH('b) = j + 1 - i \<Longrightarrow> j \<ge> i \<Longrightarrow> i \<ge> 0 \<Longrightarrow> j < int (size x) \<Longrightarrow>
(smtlib_extract j i (not x)::'b::len word) = not (smtlib_extract j i x)"
proof -
  assume b_int: "int LENGTH('b::len) = j + 1 - i"
     and ij: "i \<le> j"
     and i_nn: "0 \<le> i"
     and j_lt_size: "j < int (size x)"

  from ij i_nn have j_nn: "0 \<le> j" by linarith
  have j_lt_a: "j < int LENGTH('a::len)" using j_lt_size by (simp add: word_size)

  let ?ni = "nat i" and ?nj = "nat j"

  have ni_le_nj: "?ni \<le> ?nj" using ij i_nn by (simp add: nat_mono)
  have nj_lt_a: "?nj < LENGTH('a::len)" using j_lt_a j_nn by linarith

  have b_nat: "LENGTH('b::len) = Suc ?nj - ?ni"
  proof -
    have "LENGTH('b::len) = nat (int LENGTH('b::len))" by simp
    also have "\<dots> = nat (j + 1 - i)" using b_int by simp
    also have "\<dots> = Suc ?nj - ?ni"
      using i_nn ij j_nn by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed

  have ext_not: "(smtlib_extract j i (not x) :: 'b::len word) = smt_extract ?nj ?ni (not x)"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='b and j="?nj" and i="?ni"]
          j_nn i_nn by (metis int_nat_eq)
  have ext: "(smtlib_extract j i x :: 'b::len word) = smt_extract ?nj ?ni x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='b and j="?nj" and i="?ni"]
          j_nn i_nn by (metis int_nat_eq)

  show "(smtlib_extract j i (not x) :: 'b::len word) = not (smtlib_extract j i x)"
    unfolding ext_not ext
  proof (rule bit_word_eqI)
    fix n :: nat
    assume n_lt_b: "n < LENGTH('b::len)"
    have n_ni_le_nj: "n + ?ni \<le> ?nj" using n_lt_b b_nat ni_le_nj by linarith
    have n_ni_lt_a: "n + ?ni < LENGTH('a::len)"
      using n_ni_le_nj nj_lt_a by linarith
    show "bit (smt_extract ?nj ?ni (not x) :: 'b::len word) n
        = bit (not (smt_extract ?nj ?ni x :: 'b::len word)) n"
      using n_lt_b n_ni_le_nj n_ni_lt_a
      by (simp add: bit_smt_extract bit_not_iff)
  qed
qed


(*(define-cond-rule bv-extract-sign-extend-1
  ((x ?BitVec) (low Int) (high Int) (k Int))
  (< high (@bvsize x))
  (extract high low (sign_extend k x))
  (extract high low x))

Goal: "rare_rewrite"
       assumptions:
         ((7::int) < int (size (isabelle_internal_T1_10896::8 word))) = True
       arguments:
         ''bv-extract-sign-extend-1''
         isabelle_internal_T1_10896::8 word
         0
         7::int
         8::int
       proposition:
         smtlib_extract (7::int) 0 (Word.signed_cast (isabelle_internal_T1_10896::8 word)) =
         smtlib_extract (7::int) 0 isabelle_internal_T1_10896 
*)


named_theorems rewrite_bv_extract_sign_extend_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_1]:
  fixes x::"'a::len word" and low high k ::int
  shows "NO_MATCH cvc_a (undefined x low high k) \<Longrightarrow>
 (high < int (size x)) = True \<Longrightarrow>

int LENGTH('b) = k + int LENGTH('a) \<Longrightarrow>
int LENGTH('c) = high + 1 - low \<Longrightarrow> high \<ge> low \<Longrightarrow> low \<ge> 0 \<Longrightarrow> k \<ge> 0 \<Longrightarrow>

(smtlib_extract high low (Word.signed_cast x::'b::len word)::'c::len word) = (smtlib_extract high low x)"
proof -
  assume high_lt_size: "(high < int (size x)) = True"
     and b_int: "int LENGTH('b::len) = k + int LENGTH('a::len)"
     and c_int: "int LENGTH('c::len) = high + 1 - low"
     and lh: "low \<le> high"
     and low_nn: "0 \<le> low"
     and k_nn: "0 \<le> k"
  from high_lt_size have high_lt_a: "high < int LENGTH('a::len)"
    by (simp add: word_size)
  from lh low_nn have high_nn: "0 \<le> high" by linarith

  let ?ni = "nat low" and ?nj = "nat high"

  have ni_le_nj: "?ni \<le> ?nj" using lh low_nn by (simp add: nat_mono)
  have nj_lt_a: "?nj < LENGTH('a::len)" using high_lt_a high_nn by linarith
  have a_le_b: "LENGTH('a::len) \<le> LENGTH('b::len)"
    using b_int k_nn by simp

  have c_nat: "LENGTH('c::len) = Suc ?nj - ?ni"
  proof -
    have "LENGTH('c::len) = nat (int LENGTH('c::len))" by simp
    also have "\<dots> = nat (high + 1 - low)" using c_int by simp
    also have "\<dots> = Suc ?nj - ?ni"
      using low_nn lh high_nn by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed

  have ext_l: "(smtlib_extract high low (scast x::'b::len word) :: 'c::len word)
               = smt_extract ?nj ?ni (scast x::'b::len word)"
    using smtlib_extract_eq_smt_extract[where 'a='b and 'b='c and j="?nj" and i="?ni"]
          high_nn low_nn by (metis int_nat_eq)
  have ext_r: "(smtlib_extract high low x :: 'c::len word) = smt_extract ?nj ?ni x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='c and j="?nj" and i="?ni"]
          high_nn low_nn by (metis int_nat_eq)

  show "(smtlib_extract high low (Word.signed_cast x::'b::len word) :: 'c::len word)
         = (smtlib_extract high low x)"
    unfolding ext_l ext_r
  proof (rule bit_word_eqI)
    fix n :: nat
    assume n_lt_c: "n < LENGTH('c::len)"
    have n_ni_le_nj: "n + ?ni \<le> ?nj" using n_lt_c c_nat ni_le_nj by linarith
    have n_ni_lt_a: "n + ?ni < LENGTH('a::len)"
      using n_ni_le_nj nj_lt_a by linarith
    have n_ni_lt_b: "n + ?ni < LENGTH('b::len)"
      using n_ni_lt_a a_le_b by linarith
    show "bit (smtlib_extract high low (Word.signed_cast x::'b::len word) :: 'c::len word) n
        = bit (smt_extract (nat high) (nat low)  x :: 'c::len word) n"
      using n_lt_c n_ni_le_nj n_ni_lt_a n_ni_lt_b
      apply (simp add: bit_smt_extract bit_word_scast_iff)
      sorry
  qed
qed

(*

       arguments:
         ''bv-extract-sign-extend-2''
         if not (and (v1::4 word) (v2::4 word)) =
            word_cat 0
             (smt_comp (word_cat (4::3 word) (if (8::4 word) < v1 then 0 else 1))
               (scast (if (8::4 word) < v1 then 0 else 1)))
         then 0 else 1
         0
         1
         3::int
         0
         1
       proposition:
         smtlib_extract 1 0
          (scast
            x) =
         scast
          (smtlib_extract 0 0
            x) 
 (0 < int (size x)) = True
 (int (size x) \<le> 1) = True
0 = int (size x) -1
1 =1 + (1 - int (size x))

(define-cond-rule bv-extract-sign-extend-2
  ((x ?BitVec) (low Int) (high Int) (k Int) (nm1 Int) (sn Int))
  (def (n (@bvsize x)))
  (and (< low n) (>= high n) (= nm1 (- n 1)) (= sn (+ 1 (- high n))))
  (extract high low (sign_extend k x))
  (sign_extend
    sn
    (extract nm1 low x)))*)



named_theorems rewrite_bv_extract_sign_extend_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_2]:
  fixes x::"'a::len word" and low high k nm1 sn ::int
  shows "NO_MATCH cvc_a (undefined x low high k nm1 sn) \<Longrightarrow>
(low < int (size x)) = True \<Longrightarrow> (int (size x) \<le> high) = True \<Longrightarrow> nm = n - 1 \<Longrightarrow>
sn = 1 + (high - int(size x)) \<Longrightarrow>

int LENGTH('b) = k \<Longrightarrow>
int LENGTH('c) = high + 1 - low \<Longrightarrow> high \<ge> low \<Longrightarrow> low \<ge> 0 \<Longrightarrow>
int LENGTH('d) = nm1 + 1 -low \<Longrightarrow> nm1 \<ge> low \<Longrightarrow>
LENGTH('d) + sn = LENGTH('c) \<Longrightarrow>
(smtlib_extract high low (scast x::'b::len word)::'c::len word) = (scast (smtlib_extract nm1 low x::
'd::len word))"
  sorry

(*(define-cond-rule bv-extract-sign-extend-3
  ((x ?BitVec) (low Int) (high Int) (k Int) (rn Int) (nm1 Int))
  (def (n (@bvsize x)))
  (and (>= low n) (= rn (+ 1 (- high low))) (= nm1 (- n 1)))
  (extract high low (sign_extend k x))
  (repeat rn (extract nm1 nm1 x)))
*)

(*
(define-rule bv-not-xor
  ((x1 ?BitVec) (x2 ?BitVec) (xs ?BitVec :list))
  (bvnot (bvxor x1 x2 xs))
  (bvxor (bvnot x1) x2 xs))*)













(*(define-rule* bv-concat-flatten
  ((xs ?BitVec :list)
   (s ?BitVec)
   (ys ?BitVec :list)
   (zs ?BitVec :list))
  (concat xs (concat (concat s ys) zs))
  (concat xs (concat s (concat ys zs)))

*)















  










named_theorems rewrite_bv_sle_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(x \<le>s y) = (\<not> y <s x)"
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

named_theorems rewrite_bv_repeat_eliminate_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_1]:
  fixes x::"'a ::len word" and n::"int"
  assumes "1 < n" "LENGTH('c) = (n-1) * LENGTH('a)" "LENGTH('b) = n * LENGTH('a)"
  shows "(smt_repeat (nat n) x::'b::len word) = (word_cat x (smt_repeat (nat (n - (1::int))) x::'c::len word)::'b::len word)"
proof- 
  have t0: "LENGTH('c::len) = (nat n - (1::nat)) * size (x::'a::len word)"
    apply (simp add: assms)
    by (metis One_nat_def assms(1) assms(2) int_one_le_iff_zero_less mult.commute nat_diff_distrib' nat_int nat_mult_distrib of_nat_0_le_iff of_nat_1 order_less_imp_le wsst_TYs(3))

  have "unat (word_repeat (nat n) x::'b::len word) = replicate_nat (nat n) (size x) * unat x"
    apply (subst word_repeat_prop[of "nat n" x, where 'b='b])
    using assms(1) apply auto[1]
     apply (metis assms(3) mult.commute nat_int nat_mult_distrib of_nat_0_le_iff size_word.rep_eq)
    by simp
  also have "... =
 (replicate_nat (nat n - (1::nat)) (size x) + (2::nat) ^ ((nat n - (1::nat)) * size x)) * unat x"
    using replicate_nat_Suc[of "nat n - 1" "size x"] add_0 assms(1) by fastforce
  also have "... = replicate_nat (nat n - (1::nat)) (size x) * unat x + (2::nat) ^ ((nat n - (1::nat)) * size x) * unat x"
    by (metis distrib_left mult.commute)
  also have "... = unat (word_repeat (nat n-1) x::'c::len word) + (2::nat) ^ ((nat n - (1::nat)) * size x) * unat x"
    apply (subst word_repeat_prop[symmetric,of "nat n-1" x, where 'b='c])
    using assms(1) apply linarith
      apply (metis assms(1,2) int_minus int_one_le_iff_zero_less int_ops(2) less_le_not_le mult.commute nat_0_le nat_int nat_mult_distrib of_nat_0_le_iff wsst_TYs(3))
    by blast
  also have "... = push_bit LENGTH('c::len) (unat x) + unat (word_repeat (nat n-1) x::'c::len word)"
    by (simp add: push_bit_eq_mult t0)
  also have "... = unat (word_cat x (smt_repeat (nat (n - (1::int))) x::'c::len word)::'b::len word)"
    apply (subst unat_word_cat[of x "(smt_repeat (nat (n - (1::int))) x::'c::len word)", where 'c='b])
    using assms(2,3) int_distrib(3) apply auto[1]
    sorry  finally show ?thesis
    sorry
qed

named_theorems rewrite_bv_repeat_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_2]:
  fixes x::"'a ::len word"
  shows "smt_repeat (nat (1::int)) x = x"
  unfolding smt_repeat_def word_repeat_def replicate_nat_def
  by (simp add: size_word.rep_eq the_equality word_eq_unatI)


named_theorems rewrite_bv_rotate_right_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_2]:
  fixes x::"'a::len word" and amount::"int"
  shows "SMT.z3mod amount (int (size x)) = (0::int) \<longrightarrow>
   word_rotr (nat amount) x = x"
  unfolding SMT.z3mod_def
  apply (simp only: word_uint_eq_iff)
  apply (simp add: uint_word_rotr_eq)
  apply (simp add: unsigned_take_bit_eq)
  unfolding concat_bit_def
  by (simp add: bintr_uint nat_mod_as_int size_word.rep_eq)

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

named_theorems rewrite_bv_sign_extend_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eliminate]:
  fixes x::"'a::len word" and n::"nat"
  assumes "LENGTH('b) = n" "LENGTH('c) = LENGTH('a) + LENGTH('b)"
  shows "
(Word.signed_cast x ::'c::len word) =
   word_cat
    (smt_repeat n (smt_extract (LENGTH('a)-1) (LENGTH('a)-1) x::1 word)::'b::len word)
    x"
proof(cases "bit x (LENGTH('a::len) - (1::nat))")
  assume a0: "bit x (LENGTH('a) - (1::nat))"
  have t0: "(smt_extract (LENGTH('a)-1) (LENGTH('a)-1) x::1 word) = (1::1 word)"
    using smt_extract_bit[of "LENGTH('a)-1" x]
    by (meson a0 test_bit_size)
  show "
(Word.signed_cast x ::'c::len word) =
   word_cat
    (smt_repeat n (smt_extract (LENGTH('a)-1) (LENGTH('a)-1) x::1 word)::'b::len word)
    x"
    using a0
    apply (subst t0)
    apply (simp add: bang_eq)
    apply (rule allI)
    subgoal for i
      apply(simp add: bit_word_scast_iff)
      apply(simp add: bit_word_cat_iff)
      apply(cases " i < LENGTH('a)")
       apply simp_all
      apply (cases "i < LENGTH('c)")
       apply simp_all
      apply (subst smt_repeat_ones_mask)
      using assms(1) apply blast
      using assms(1) apply blast
      apply (simp add: bit_mask_iff)
      apply (rule conjI)
      using assms(2) apply linarith
      by (simp add: assms(1) assms(2))
    done
next
  assume a0: "\<not> bit x (LENGTH('a) - (1::nat))"
  have t0: "(smt_extract (LENGTH('a)-1) (LENGTH('a)-1) x::1 word) = (0::1 word)"
    using smt_extract_bit[of "LENGTH('a)-1" x]
    by (metis One_nat_def a0 decr_length_less_iff dual_order.refl word_size)
  show "
(Word.signed_cast x ::'c::len word) =
   word_cat
    (smt_repeat n (smt_extract (LENGTH('a)-1) (LENGTH('a)-1) x::1 word)::'b::len word)
    x"
using a0
    apply (subst t0)
    apply (simp add: bang_eq)
    apply (rule allI)
    subgoal for i
      apply(simp add: bit_word_scast_iff)
      apply(simp add: bit_word_cat_iff)
      apply(cases " i < LENGTH('a)")
       apply simp_all
      apply (cases "i < LENGTH('c)")
       apply simp_all
      apply (subst smt_repeat_zeros)
      using assms(1) apply blast
      using assms(1) apply blast
      apply (simp add: bit_mask_iff)
      using bit_imp_le_length by auto
    done
qed

(*named_theorems rewrite_bv_saddo_eliminate \<open>automatically_generated\<close>

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
*)

named_theorems rewrite_bv_sdivo_eliminate \<open>automatically_generated\<close>

(*TODO: (itself::'c itself) instead of (itself::'c ::len itself) is printed
when you print without types it works ^^*)
lemma [rewrite_bv_sdivo_eliminate]:
  fixes x::"'a ::len word" and y::"'b ::len word"
  shows "LENGTH('c) = LENGTH('a) - 1  \<longrightarrow> smt_sdivo TYPE('c::len) x y =
   (x = word_cat (Word.Word (1::int):: 1 word) (Word.Word (0::int)::'c::len word) \<and>
    y = not (Word.Word (0::int)::'b::len word))"
    using smt_sdivo_def[of x y, where 'c="'c"] 
mask_full[where 'a="'b"]
    by (metis bit.compl_zero one_word_def word_size zero_word_def)

named_theorems rewrite_bv_srem_eliminate_fewer_bitwise_ops \<open>automatically_generated\<close>

lemma [rewrite_bv_srem_eliminate_fewer_bitwise_ops]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "
LENGTH('a) = LENGTH('b) + 1 \<longrightarrow>
smt_srem x y =
   (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> x
    then - smt_urem
            (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> x
             then - x else x)
            (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> y
             then - y else y)
    else smt_urem
          (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> x
           then - x else x)
          (if word_cat (Word.Word (1::int):: 1 word) (Word.Word (0::int)::'b::len word) \<le> y
           then - y else y))"
  unfolding smt_srem_def Let_def
  apply (cases "word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> x")
   apply simp_all
   apply (cases "word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> y")
    apply simp_all
  oops

named_theorems rewrite_bv_usubo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_usubo_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "LENGTH('b) = LENGTH('a) + 1 
\<Longrightarrow> smt_usubo (TYPE('b::len)) x y =
   (smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int)))
     ((Word.cast x::'b::len word) - Word.cast y) =
    (Word.Word (1::int):: 1 word))"
  unfolding smt_usubo_def
  by (simp add: nat_minus_as_int word_size)






(*


(define-cond-rule bv-shl-by-const-1
  ((x ?BitVec) (amount Int) (sz Int))
  (< amount (bvsize x))
  (bvshl x (bv amount sz))
  (concat (extract (- (bvsize x) (+ 1 amount)) 0 x) (bv 0 amount)))

size (bv 0 amount) = amount
size (extract (- (bvsize x) (+ 1 amount)) 0 x) = (1 + (((bvsize x) - (1 + amount)) - 0)) =  (bvsize x) - amount)
size (concat (extract (- (bvsize x) (+ 1 amount)) 0 x) (bv 0 amount))) = bvsize x
size (bvshl x (bv amount sz)) = bvsize x

(bvsize x) - amount \<ge> 0
amount \<ge> 0 
(bvsize x) \<ge> 0
sz \<ge> 0*)

(*TODO: I needed to add amount < (2::int) ^ LENGTH('d). Is this implicit in cvc5? Probably*)





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

named_theorems rewrite_bv_neg_idemp \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_idemp]:
  fixes x::"'a ::len word"
  shows "- (- x) = x"
  by auto

named_theorems rewrite_bv_udiv_pow2_2p \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_2p]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "v = 1 \<longrightarrow> x div Word.Word v = x"
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
  sorry



named_theorems rewrite_bv_zero_ult \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ult]:
  fixes x::"'a ::len word"
  shows "(Word.Word 0 < x) = (x \<noteq> Word.Word 0)"
  using word_neq_0_conv by auto

named_theorems rewrite_bv_merge_sign_extend_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_3]:
  fixes x::"'a ::len word" and i::"int"
  shows "signed_take_bit (nat i) (push_bit (nat 0) x) = signed_take_bit (nat i) x"
  by auto

lemma help1: "b <= a --> (nat (int a - b)) = a - b"
  using nat_minus_as_int by presburger
lemma help2: "1 \<le> m \<longrightarrow> (nat (int (size x) + ((m::int) - (1::int)))) = size x + nat m - 1"
  using Nat.diff_add_assoc One_nat_def nat_1 nat_add_distrib nat_int nat_mono by fastforce

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

  have t0: "unat (smt_extract (nat i) (nat j) (semiring_bit_operations_class.xor x y)::'b::len word)
 = drop_bit (nat j) (take_bit (Suc (nat i)) (semiring_bit_operations_class.xor (unat x) (unat y)))"
  proof-
    have "unat (smt_extract (nat i) (nat j) (semiring_bit_operations_class.xor x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (unat (semiring_bit_operations_class.xor x y)))"
      using unat_smt_extract[of "nat j" "nat i" "(semiring_bit_operations_class.xor x y)", where 'b="'b"]  
      by (metis Suc_as_int Suc_eq_plus1 a0 a1 a2 a3 int_nat_eq nat_diff_distrib' nat_int nat_mono not_less_eq_eq order_trans word_size)
    then show "unat (smt_extract (nat i) (nat j) (semiring_bit_operations_class.xor x y)::'b::len word)
 = drop_bit (nat j) (take_bit (Suc (nat i)) (semiring_bit_operations_class.xor (unat x) (unat y)))"
      using unsigned_xor_eq by metis
  qed
  moreover have "unat (semiring_bit_operations_class.xor ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
  = (semiring_bit_operations_class.xor (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    proof-
      have "unat (semiring_bit_operations_class.xor ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
        = (semiring_bit_operations_class.xor (unat ((smt_extract (nat i) (nat j) x)::'b::len word)) (unat ((smt_extract (nat i) (nat j) y)::'b::len word)))"
    using unsigned_xor_eq by blast
    moreover have " nat (j::int) \<le> nat (i::int) \<and> nat i < size (x::'a::len word) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j "
      using a0 a1 a2 a3 by force
    moreover have "nat i < size (y::'a::len word)"
      by (metis a1 size_word.rep_eq)
    ultimately show t1: "unat (semiring_bit_operations_class.xor ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
    = (semiring_bit_operations_class.xor (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    using unat_smt_extract[of "nat j" "nat i" "x", where 'b="'b"]
    using unat_smt_extract[of "nat j" "nat i" "y", where 'b="'b"]
    by presburger
  qed
  moreover have  "drop_bit (nat j) (take_bit (Suc (nat i)) (semiring_bit_operations_class.xor (unat x) (unat y)))
  = (semiring_bit_operations_class.xor (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    by auto
  ultimately show "(smt_extract (nat i) (nat j) (semiring_bit_operations_class.xor x y)::'b::len word) =
   semiring_bit_operations_class.xor ((smt_extract (nat i) (nat j) x)::'b::len word) 
    ((smt_extract (nat i) (nat j) y)::'b::len word)"
    by (metis unsigned_word_eqI)
qed

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
    sorry
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
    sorry
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
    sorry
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
    sorry
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
    sorry
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
    sorry
  done

named_theorems rewrite_bv_ult_add_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_add_one]:
  fixes x::"'a ::len word" and y::"'a ::len word" and n::"int"
  shows "(x < y + (Word.Word (1::int)::'a::len word)) =
   (\<not> y < x \<and> y \<noteq> not (Word.Word 0))"
  apply simp
  by (metis ab_left_minus word_Suc_le word_not_le word_not_simps(1))

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

named_theorems rewrite_bv_or_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_or_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "or x (Word.Word (0::int)) = x"
  by auto

named_theorems rewrite_bv_mul_one \<open>automatically_generated\<close>

lemma [rewrite_bv_mul_one]:
  fixes x::"'a::len word" and n::"int"
  shows "x * Word.Word (1::int) = x"
  by auto

named_theorems rewrite_bv_mul_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_mul_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "x * Word.Word (0::int) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_add_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_add_zero]:
  fixes x::"'a::len word" and n::"int"
  shows "x + Word.Word (0::int) = x"
  by auto

named_theorems rewrite_bv_add_two \<open>automatically_generated\<close>

lemma [rewrite_bv_add_two]:
  fixes x::"'a::len word"
  shows "x + x = x * Word.Word (2::int)"
  by auto

named_theorems rewrite_bv_zero_extend_eliminate_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eliminate_0]:
  fixes x::"'a::len word"
  shows "Word.cast x = x"
  by auto

named_theorems rewrite_bv_sign_extend_eliminate_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eliminate_0]:
  fixes x::"'a::len word"
  shows "Word.signed_cast x = x"
  by auto

named_theorems rewrite_bv_not_neq \<open>automatically_generated\<close>

lemma [rewrite_bv_not_neq]:
  fixes x::"'a::len word"
  shows "(0::int) < int (size x) \<longrightarrow> (x = not x) = False"
  by (metis lsb0)

named_theorems rewrite_bv_ult_ones \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_ones]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "y = not (Word.Word (0::int)) \<longrightarrow> (x < y) = (x \<noteq> y)"
  using word_order.not_eq_extremum by auto


end