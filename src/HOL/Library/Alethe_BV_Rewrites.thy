theory Alethe_BV_Rewrites
  imports Alethe_BV_Rewrites_Lemmas
begin
declare[[show_types,show_sorts]]

declare[[smt_expert_debug_alethe_level=0]]

lemma bit_smtlib_extract:
  assumes "0 \<le> j"
  shows "bit (smtlib_extract j i x::'b::len word) n
    = ((n + nat i < Suc (nat j) \<and> bit x (n + nat i)) \<and> n < LENGTH('b::len))"
  unfolding smtlib_extract_def
  using nth_slice[of "nat i" "(take_bit (nat (j+1)) x)" n, where 'a="'b"]
        bit_take_bit_iff[of "nat (j+1)" x "n + nat i"] assms
  by (simp add: nat_add_distrib)

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

  have kk_nn: "0 \<le> kk" using kk_eq i_nn k_nn by linarith

  show "(smtlib_extract l k (smtlib_extract j i x::'c::len word)::'b::len word)
        = (smtlib_extract ll kk x::'b::len word)"
  proof (rule bit_word_eqI)
    fix n :: nat
    assume n_lt: "n < LENGTH('b::len)"
    have n_nk_lt_Snl: "n + ?nk < Suc ?nl"
      using n_lt b_nat nk_le_nl by linarith
    have n_nk_ni_lt_Snj: "n + ?nk + ?ni < Suc ?nj"
      using n_nk_lt_Snl nl_ni_le_nj by linarith
    have n_nk_lt_c: "n + ?nk < LENGTH('c::len)"
      using n_nk_ni_lt_Snj c_nat ni_le_nj by linarith
    have n_nkk_lt_Snll: "n + ?nkk < Suc ?nll"
      using n_nk_lt_Snl nll_eq nkk_eq by linarith
    have n_nkk_eq: "n + ?nk + ?ni = n + ?nkk"
      using nkk_eq by simp
    show "bit (smtlib_extract l k (smtlib_extract j i x::'c::len word) :: 'b::len word) n
        = bit (smtlib_extract ll kk x :: 'b::len word) n"
      using n_lt n_nk_lt_Snl n_nk_ni_lt_Snj n_nk_lt_c n_nkk_lt_Snll n_nkk_eq j_nn l_nn ll_nn
      by (metis bit_smtlib_extract)
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

  show "(smtlib_extract j i (word_cat y x::'d::len word)::'e::len word)
          = smtlib_extract j i x"
  proof (rule bit_word_eqI)
    fix n :: nat
    assume n_lt: "n < LENGTH('e::len)"
    from n_lt e_nat ni_le_nj have n_ni_le_nj: "n + ?ni \<le> ?nj" by linarith
    hence n_ni_lt_a: "n + ?ni < LENGTH('a::len)" using nj_lt_a by linarith
    have n_ni_lt_d: "n + ?ni < LENGTH('d::len)"
      using n_ni_lt_a d_len by linarith
    from n_lt n_ni_le_nj n_ni_lt_a n_ni_lt_d
    show "bit (smtlib_extract j i (word_cat y x :: 'd::len word) :: 'e::len word) n
        = bit (smtlib_extract j i x :: 'e::len word) n"
      by (auto simp: bit_smtlib_extract bit_word_cat_iff j_nn)
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

  show "(smtlib_extract j i
           (word_cat_rbl_left xs (word_cat y x::'d::len word) TYPE('c)
            ::'h::len word) :: 'e::len word)
       = smtlib_extract j i x"
    unfolding word_cat_rbl_left_def
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
    show "bit (smtlib_extract j i
                 (word_cat (of_bl (concat xs) :: 'c::len word)
                           (word_cat y x::'d::len word) :: 'h::len word)
              :: 'e::len word) n
        = bit (smtlib_extract j i x :: 'e::len word) n"
      by (auto simp: bit_smtlib_extract bit_word_cat_iff j_nn)
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

  show "((smtlib_extract j i x :: 'b::len word) = y)
        = (x = word_cat (smtlib_extract wm1 jp1 x :: 'e::len word)
                       (word_cat y (smtlib_extract im1 0 x :: 'c::len word) :: 'd::len word))"
  proof (rule iffI)
    assume H: "(smtlib_extract j i x :: 'b::len word) = y"
    show "x = word_cat (smtlib_extract wm1 jp1 x :: 'e::len word)
                      (word_cat y (smtlib_extract im1 0 x :: 'c::len word) :: 'd::len word)"
    proof (rule bit_word_eqI)
      fix n :: nat
      assume n_lt_a: "n < LENGTH('a::len)"
      have n_lt_Snwm1: "n < Suc ?nwm1" using n_lt_a a_nat by simp
      show "bit x n
          = bit (word_cat (smtlib_extract wm1 jp1 x :: 'e::len word)
                  (word_cat y (smtlib_extract im1 0 x :: 'c::len word) :: 'd::len word)
                 :: 'a::len word) n"
      proof (cases "n < LENGTH('d::len)")
        case d_in: True
        hence n_lt_Snj: "n < Suc ?nj" using d_nat by simp
        show ?thesis
        proof (cases "n < LENGTH('c::len)")
          case c_in: True
          hence n_lt_ni: "n < ?ni" using c_nat by simp
          have "bit (smtlib_extract im1 0 x :: 'c::len word) n = bit x n"
            using n_lt_ni c_nat nim1_eq by (simp add: bit_smtlib_extract im1_nn)
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
            from H have "bit y (n - ?ni) = bit (smtlib_extract j i x :: 'b::len word) (n - ?ni)"
              by simp
            also have "\<dots> = bit x n"
              using lt_b ni_le_n n_lt_Snj by (simp add: bit_smtlib_extract j_nn)
            finally show ?thesis using nc by simp
          qed
          thus ?thesis
            using c_out d_in n_lt_a by (simp add: bit_word_cat_iff)
        qed
      next
        case d_out: False
        hence Snj_le_n: "Suc ?nj \<le> n" using d_nat by simp
        have e_bit: "bit (smtlib_extract wm1 jp1 x :: 'e::len word)
                         (n - LENGTH('d::len)) = bit x n"
        proof -
          have nd: "n - LENGTH('d::len) = n - Suc ?nj" using d_nat by simp
          have plus_back: "n - Suc ?nj + Suc ?nj = n" using Snj_le_n by simp
          have lt_e: "n - Suc ?nj < LENGTH('e::len)"
            using e_nat Snj_le_n n_lt_Snwm1 Snj_le_nwm1 by linarith
          show ?thesis
            using plus_back lt_e n_lt_Snwm1 nd njp1_eq by (simp add: bit_smtlib_extract wm1_nn)
        qed
        thus ?thesis
          using d_out n_lt_a by (simp add: bit_word_cat_iff)
      qed
    qed
  next
    assume H: "x = word_cat (smtlib_extract wm1 jp1 x :: 'e::len word)
                            (word_cat y (smtlib_extract im1 0 x :: 'c::len word)
                             :: 'd::len word)"
    show "(smtlib_extract j i x :: 'b::len word) = y"
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
      have "bit (smtlib_extract j i x :: 'b::len word) n = bit x (n + ?ni)"
        using n_plus_ni_lt_Snj n_lt_b by (simp add: bit_smtlib_extract j_nn)
      also from H have "\<dots> = bit (word_cat (smtlib_extract wm1 jp1 x :: 'e::len word)
                            (word_cat y (smtlib_extract im1 0 x :: 'c::len word)
                             :: 'd::len word) :: 'a::len word) (n + ?ni)"
        by simp
      also have "\<dots> = bit y n"
        using n_plus_ni_lt_d n_plus_ni_lt_a n_plus_ni_ge_c c_nat
        by (simp add: bit_word_cat_iff)
      finally show "bit (smtlib_extract j i x :: 'b::len word) n = bit y n" .
    qed
  qed
qed

(*
(define-cond-rule bv-eq-extract-elim2
  ((x ?BitVec) (y ?BitVec) (j Int) (wm1 Int) (jp1 Int))
  (and (= wm1 (- (@bvsize x) 1)) (= jp1 (+ j 1)) (> wm1 j))
  (= (extract j 0 x) y)
  (= x (concat (extract wm1 jp1 x) y)))
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

(*
(define-cond-rule bv-extract-sign-extend-1
  ((x ?BitVec) (low Int) (high Int) (k Int))
  (< high (@bvsize x))
  (extract high low (sign_extend k x))
  (extract high low x))
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

  have nat_high1: "nat (high + 1) = Suc ?nj" using high_nn by linarith

  show "(smtlib_extract high low (Word.signed_cast x::'b::len word) :: 'c::len word)
         = (smtlib_extract high low x)"
  proof (rule bit_word_eqI)
    fix n :: nat
    assume n_lt_c: "n < LENGTH('c::len)"
    have n_ni_le_nj: "n + ?ni \<le> ?nj" using n_lt_c c_nat ni_le_nj by linarith
    have n_ni_lt_a: "n + ?ni < LENGTH('a::len)"
      using n_ni_le_nj nj_lt_a by linarith
    have n_ni_lt_b: "n + ?ni < LENGTH('b::len)"
      using n_ni_lt_a a_le_b by linarith
    have ni_le_a: "?ni \<le> LENGTH('a::len)" using n_ni_lt_a by linarith
    have ni_le_b: "?ni \<le> LENGTH('b::len)" using n_ni_lt_b by linarith
    have n_lt_a_minus_ni: "n < LENGTH('a::len) - ?ni"
      using n_ni_lt_a by linarith
    have n_lt_b_minus_ni: "n < LENGTH('b::len) - ?ni"
      using n_ni_lt_b by linarith
    have n_ni_lt_high1: "n + ?ni < nat (high + 1)"
      using n_ni_le_nj nat_high1 by linarith
    show "bit (smtlib_extract high low (Word.signed_cast x::'b::len word) :: 'c::len word) n
        = bit (smtlib_extract high low x :: 'c::len word) n"
      unfolding smtlib_extract_def
      using n_lt_c n_ni_lt_a n_ni_lt_b ni_le_a ni_le_b
            n_lt_a_minus_ni n_lt_b_minus_ni n_ni_lt_high1
      by (auto simp: bit_slice_iff bit_take_bit_iff bit_word_scast_iff)
  qed
qed

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

named_theorems rewrite_bv_extract_sign_extend_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_2]:
  fixes x::"'a::len word" and low high k nm1 sn ::int
  shows "NO_MATCH cvc_a (undefined x low high k nm1 sn) \<Longrightarrow>
    (low < int (size x)) = True \<Longrightarrow>
    (int (size x) \<le> high) = True \<Longrightarrow>
    nm1 = int (size x) - 1 \<Longrightarrow>
    sn = 1 + (high - int (size x)) \<Longrightarrow>
    int LENGTH('b) = k + int LENGTH('a) \<Longrightarrow>
    int LENGTH('c) = high + 1 - low \<Longrightarrow> high \<ge> low \<Longrightarrow> low \<ge> 0 \<Longrightarrow> k \<ge> 0 \<Longrightarrow>
    int LENGTH('d) = nm1 + 1 - low \<Longrightarrow> nm1 \<ge> low \<Longrightarrow>
    int LENGTH('d) + sn = int LENGTH('c) \<Longrightarrow>
    high + 1 \<le> int LENGTH('b) \<Longrightarrow>
    (smtlib_extract high low (scast x::'b::len word)::'c::len word)
      = (scast (smtlib_extract nm1 low x::'d::len word) :: 'c::len word)"
proof -
  assume low_lt_size: "(low < int (size x)) = True"
     and high_ge_size: "(int (size x) \<le> high) = True"
     and nm1_eq: "nm1 = int (size x) - 1"
     and b_int: "int LENGTH('b::len) = k + int LENGTH('a::len)"
     and c_int: "int LENGTH('c::len) = high + 1 - low"
     and lh: "low \<le> high"
     and low_nn: "0 \<le> low"
     and k_nn: "0 \<le> k"
     and d_int: "int LENGTH('d::len) = nm1 + 1 - low"
     and nm1_low: "low \<le> nm1"
     and high1_le_b: "high + 1 \<le> int LENGTH('b::len)"

  from low_lt_size have low_lt_a: "low < int LENGTH('a::len)"
    by (simp add: word_size)
  from high_ge_size have a_le_high: "int LENGTH('a::len) \<le> high"
    by (simp add: word_size)
  from low_nn lh have high_nn: "0 \<le> high" by linarith
  from low_nn nm1_low have nm1_nn: "0 \<le> nm1" by linarith
  from nm1_eq have nm1_size: "nm1 = int LENGTH('a::len) - 1"
    by (simp add: word_size)

  let ?nlow = "nat low" and ?nhigh = "nat high" and ?nnm1 = "nat nm1"

  have nlow_lt_a: "?nlow < LENGTH('a::len)" using low_lt_a low_nn by linarith
  have a_le_b: "LENGTH('a::len) \<le> LENGTH('b::len)" using b_int k_nn by linarith
  have nat_high1: "nat (high + 1) = Suc ?nhigh" using high_nn by linarith
  have nat_nm11: "nat (nm1 + 1) = LENGTH('a::len)"
    using nm1_size by linarith
  have d_nat: "LENGTH('d::len) = LENGTH('a::len) - ?nlow"
  proof -
    have "int LENGTH('d::len) = int LENGTH('a::len) - low"
      using d_int nm1_size by linarith
    hence "LENGTH('d::len) = nat (int LENGTH('a::len) - low)" by linarith
    also have "\<dots> = LENGTH('a::len) - ?nlow"
      using low_nn nlow_lt_a by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed
  have d_pos: "0 < LENGTH('d::len)" using d_nat nlow_lt_a by linarith
  have d_le_a_minus_nlow: "LENGTH('d::len) \<le> LENGTH('a::len) - ?nlow" using d_nat by simp
  have nhigh1_le_b: "Suc ?nhigh \<le> LENGTH('b::len)"
    using high1_le_b nat_high1 by linarith

  show "(smtlib_extract high low (scast x::'b::len word) :: 'c::len word)
        = (scast (smtlib_extract nm1 low x :: 'd::len word) :: 'c::len word)"
  proof (rule bit_word_eqI)
    fix n :: nat
    assume n_lt_c: "n < LENGTH('c::len)"
    have c_nat: "LENGTH('c::len) = Suc ?nhigh - ?nlow"
    proof -
      have "LENGTH('c::len) = nat (int LENGTH('c::len))" by simp
      also have "\<dots> = nat (high + 1 - low)" using c_int by simp
      also have "\<dots> = Suc ?nhigh - ?nlow"
        using low_nn lh high_nn by (simp add: nat_diff_distrib)
      finally show ?thesis .
    qed
    have nlow_le_nhigh: "?nlow \<le> ?nhigh" using lh low_nn by (simp add: nat_mono)
    have n_nlow_le_nhigh: "n + ?nlow \<le> ?nhigh"
      using n_lt_c c_nat nlow_le_nhigh by linarith
    have n_nlow_lt_high1: "n + ?nlow < nat (high + 1)"
      using n_nlow_le_nhigh nat_high1 by linarith
    have n_nlow_lt_b: "n + ?nlow < LENGTH('b::len)"
      using n_nlow_le_nhigh nhigh1_le_b by linarith
    have nlow_le_b: "?nlow \<le> LENGTH('b::len)" using n_nlow_lt_b by linarith
    have n_lt_b_minus_nlow: "n < LENGTH('b::len) - ?nlow" using n_nlow_lt_b by linarith
    show "bit (smtlib_extract high low (scast x::'b::len word) :: 'c::len word) n
        = bit (scast (smtlib_extract nm1 low x :: 'd::len word) :: 'c::len word) n"
      unfolding smtlib_extract_def
    proof (cases "n + ?nlow < LENGTH('a::len)")
      case in_a: True
      hence n_lt_d: "n < LENGTH('d::len)" using d_nat by linarith
      have lhs: "bit (slice ?nlow (take_bit (nat (high + 1)) (scast x :: 'b::len word))
                    :: 'c::len word) n
                 = bit x (n + ?nlow)"
        using n_lt_c n_nlow_lt_high1 n_nlow_lt_b nlow_le_b n_lt_b_minus_nlow in_a a_le_b
        by (auto simp: bit_slice_iff bit_take_bit_iff bit_word_scast_iff)
      have rhs: "bit (scast (slice ?nlow (take_bit (nat (nm1 + 1)) x) :: 'd::len word)
                    :: 'c::len word) n
                 = bit x (n + ?nlow)"
        using n_lt_c n_lt_d d_nat nat_nm11 nlow_lt_a in_a
        by (auto simp: bit_slice_iff bit_take_bit_iff bit_word_scast_iff)
      from lhs rhs show "bit (slice ?nlow (take_bit (nat (high + 1)) (scast x :: 'b::len word))
                            :: 'c::len word) n
                       = bit (scast (slice ?nlow (take_bit (nat (nm1 + 1)) x) :: 'd::len word)
                            :: 'c::len word) n"
        by simp
    next
      case out_a: False
      hence a_le_n_nlow: "LENGTH('a::len) \<le> n + ?nlow" by simp
      hence d_le_n: "LENGTH('d::len) \<le> n" using d_nat by linarith
      have lhs_sign: "bit (slice ?nlow (take_bit (nat (high + 1)) (scast x :: 'b::len word))
                          :: 'c::len word) n
                      = bit x (LENGTH('a::len) - Suc 0)"
        using n_lt_c n_nlow_lt_high1 n_nlow_lt_b nlow_le_b n_lt_b_minus_nlow
              out_a a_le_n_nlow a_le_b
        by (auto simp: bit_slice_iff bit_take_bit_iff bit_word_scast_iff
                 dest: bit_imp_le_length)
      have idx_eq: "LENGTH('d::len) - Suc 0 + ?nlow = LENGTH('a::len) - Suc 0"
        using d_nat nlow_lt_a d_pos by linarith
      have inner_sign:
        "bit (slice ?nlow (take_bit (nat (nm1 + 1)) x) :: 'd::len word)
             (LENGTH('d::len) - Suc 0)
         = bit x (LENGTH('a::len) - Suc 0)"
        using d_pos d_nat nat_nm11 idx_eq nlow_lt_a
        by (auto simp: bit_slice_iff bit_take_bit_iff)
      have rhs_sign: "bit (scast (slice ?nlow (take_bit (nat (nm1 + 1)) x) :: 'd::len word)
                          :: 'c::len word) n
                      = bit x (LENGTH('a::len) - Suc 0)"
        using n_lt_c d_le_n inner_sign
        by (auto simp: bit_word_scast_iff dest: bit_imp_le_length)
      from lhs_sign rhs_sign show "bit (slice ?nlow (take_bit (nat (high + 1)) (scast x :: 'b::len word))
                                      :: 'c::len word) n
                                 = bit (scast (slice ?nlow (take_bit (nat (nm1 + 1)) x) :: 'd::len word)
                                      :: 'c::len word) n"
        by simp
    qed
  qed
qed

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

named_theorems rewrite_bv_not_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_not_xor]:
  fixes x::"'a ::len word" and xs::"'a ::len word cvc_ListVar"
  shows "not (cvc_list_right semiring_bit_operations_class.xor x xs) =
   cvc_list_right semiring_bit_operations_class.xor (not x) xs"
  apply (cases xs)
  subgoal for xss
    sorry
  done

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

(*
(define-cond-rule bv-or-simplify-2
  ((xs ?BitVec :list) (ys ?BitVec :list) (zs ?BitVec :list) (x ?BitVec) (w Int))
  (= w (@bvsize x))
  (bvor xs x ys (bvnot x) zs)
  (bvnot (@bv 0 w)))
*)

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

(*
(define-rule* bv-xor-simplify-1
  ((xs ?BitVec :list) (ys ?BitVec :list) (zs ?BitVec :list) (x ?BitVec))
  (bvxor xs x ys x zs)
  (bvxor xs ys zs))
*)

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

(*
(define-rule bv-xor-simplify-2
  ((xs ?BitVec :list) (ys ?BitVec :list) (zs ?BitVec :list) (x ?BitVec))
  (bvxor xs x ys (bvnot x) zs)
  (bvnot (bvxor xs ys zs)))
*)

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

(*
(define-rule bv-xor-simplify-3
  ((xs ?BitVec :list) (ys ?BitVec :list) (zs ?BitVec :list) (x ?BitVec))
  (bvxor xs (bvnot x) ys x zs)
  (bvnot (bvxor xs ys zs)))
*)

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

named_theorems rewrite_bv_ult_add_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_add_one]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow>
    (x < y + (Word.Word (1::int)::'a::len word)) =
    (\<not> y < x \<and> y \<noteq> not (Word.Word 0))"
  using Alethe_BV_Rewrites_Lemmas.rewrite_bv_ult_add_one by blast

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

named_theorems rewrite_bv_commutative_xor \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_xor]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "semiring_bit_operations_class.xor x y =
   semiring_bit_operations_class.xor y x"
  by (simp add: xor.commute)

(*
(define-rule bv-commutative-comp ((x ?BitVec) (y ?BitVec))
  (bvcomp x y) (bvcomp y x))
*)

named_theorems rewrite_bv_commutative_comp \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_comp]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> smt_comp x y = smt_comp y x"
  by (simp add: smt_comp_def eq_commute)

(*
(define-rule bv-zero-extend-eliminate-0
  ((x ?BitVec))
  (zero_extend 0 x)
  x)
*)

named_theorems rewrite_bv_zero_extend_eliminate_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eliminate_0]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (Word.cast x :: 'a::len word) = x"
  by (simp add: ucast_id)

(*
(define-rule bv-sign-extend-eliminate-0
  ((x ?BitVec))
  (sign_extend 0 x)
  x)
*)

named_theorems rewrite_bv_sign_extend_eliminate_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eliminate_0]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow> (Word.signed_cast x :: 'a::len word) = x"
  by (simp add: scast_id)

(*
(define-cond-rule bv-not-neq ((x ?BitVec))
  (> (@bvsize x) 0)
  (= x (bvnot x))
  false)
*)

named_theorems rewrite_bv_not_neq \<open>automatically_generated\<close>

lemma [rewrite_bv_not_neq]:
  fixes x::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x) \<Longrightarrow>
    (0::int) < int (size x) \<longrightarrow> (x = not x) = False"
  by (metis bit_not_iff len_gt_0 possible_bit_word)

(*
(define-cond-rule bv-ult-ones ((x ?BitVec) (n Int) (w Int))
  (= n (- (int.pow2 w) 1))
  (bvult x (@bv n w))
  (distinct x (@bv n w)))
*)

named_theorems rewrite_bv_ult_ones \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_ones]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow>
    y = not (Word.Word (0::int)) \<longrightarrow> (x < y) = (x \<noteq> y)"
  by (metis bit.compl_zero word_order.not_eq_extremum order_less_irrefl
            word_of_int_neg_1 zero_word_def)

(* Collapse rules *)

(*
(define-cond-rule bv-concat-merge-const
  ((xs ?BitVec :list)
   (n1 Int) (w1 Int) (n2 Int) (w2 Int) (ww Int)
   (zs ?BitVec :list))
  (= ww (+ w1 w2))
  (concat xs (@bv n1 w1) (@bv n2 w2) zs)
  (concat xs (@bv (+ (\* n1 (int.pow2 w2)) (mod n2 (int.pow2 w2))) ww) zs))
*)

(* These rules should be subsumed by ARITH_POLY_NORM, but removing them increases the number of holes *)

(*
(define-rule bv-commutative-add ((x ?BitVec) (y ?BitVec))
  (bvadd x y) (bvadd y x))
*)

named_theorems rewrite_bv_commutative_add \<open>automatically_generated\<close>

lemma [rewrite_bv_commutative_add]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> x + y = y + x"
  by (simp add: add.commute)

(*
(define-rule bv-sub-eliminate
  ((x ?BitVec) (y ?BitVec))
  (bvsub x y)
  (bvadd x (bvneg y)))
*)

named_theorems rewrite_bv_sub_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sub_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow> x - y = x + - y"
  by auto

(*
(define-rule bv-ite-width-one ((x ?BitVec))
  (ite (= x (@bv 1 1)) (@bv 1 1) (@bv 0 1))
  x)
*)

named_theorems rewrite_bv_ite_width_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_width_one]:
  fixes x::"1 word"
  shows "NO_MATCH cvc_a (undefined x)
    \<Longrightarrow> (if x = (1::1 word) then (1::1 word) else (0::1 word)) = x"
  apply (cases "x = (1:: 1 word)")
   apply simp
  by (metis One_nat_def Word.mask_Suc_0 and.right_neutral and_one_neq_simps(2) len_of_numeral_defs(2)
      max_word_mask)

(*
(define-rule bv-ite-width-one-not ((x ?BitVec))
  (ite (= x (@bv 0 1)) (@bv 1 1) (@bv 0 1))
  (bvnot x))
*)

named_theorems rewrite_bv_ite_width_one_not \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_width_one_not]:
  fixes x::"1 word"
  shows "NO_MATCH cvc_a (undefined x)
    \<Longrightarrow> (if x = (0::1 word) then (1::1 word) else (0::1 word)) = not x"
  by (metis (no_types, lifting) One_nat_def Word.mask_Suc_0 and.right_neutral and_one_neq_simps(2) bit.compl_zero len_of_numeral_defs(2) max_word_mask
      word_bitwise_m1_simps(1))

(*
(define-rule bv-eq-xor-solve ((x ?BitVec) (y ?BitVec) (z ?BitVec))
  (= (= (bvxor x y) z) (= x (bvxor z y)))
  true)
*)

named_theorems rewrite_bv_eq_xor_solve \<open>automatically_generated\<close>

lemma [rewrite_bv_eq_xor_solve]:
  fixes x::"'a::len word" and y::"'a::len word" and z::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y z) \<Longrightarrow>
    ((semiring_bit_operations_class.xor x y = z)
      = (x = semiring_bit_operations_class.xor z y)) = True"
  by (metis word_bw_comms(3) swap_with_xor)

(*
(define-rule bv-eq-not-solve ((x ?BitVec) (y ?BitVec))
  (= (= (bvnot x) y) (= x (bvnot y)))
  true)
*)

named_theorems rewrite_bv_eq_not_solve \<open>automatically_generated\<close>

lemma [rewrite_bv_eq_not_solve]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "NO_MATCH cvc_a (undefined x y) \<Longrightarrow>
    ((not x = y) = (x = not y)) = True"
  by auto

end
