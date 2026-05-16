theory BV_Rewrites
  imports BV_Rewrites_Lemmas 
begin
declare[[show_types,show_sorts]]
(* This is a theory automatically created from a RARE file! All that remains to do is to prove
any lemma whose provided proof fails and to to import this file in SMT.thy (if you want to use it
for proof reconstruction).*)



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
    apply (subst word_cat_smtlib_extract[of i "j" k s])
     apply standard+
      apply simp
   apply simp
  by simp
    
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



(*

(define-cond-rule bv-extract-whole
  ((x ?BitVec) (n Int))
  (>= n (- (@bvsize x) 1))
  (extract n 0 x)
  x)
*)
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
*)

(*
(define-cond-rule bv-eq-extract-elim2
  ((x ?BitVec) (y ?BitVec) (j Int) (wm1 Int) (jp1 Int))
  (and (= wm1 (- (@bvsize x) 1)) (= jp1 (+ j 1)) (> wm1 j))
  (= (extract j 0 x) y)
  (= x (concat (extract wm1 jp1 x) y)))
*)
(*
(define-cond-rule bv-eq-extract-elim3
  ((x ?BitVec) (y ?BitVec) (i Int) (j Int) (im1 Int))
  (and (= j (- (@bvsize x) 1)) (= im1 (- i 1)) (> i 0))
  (= (extract j i x) y)
  (= x (concat y (extract im1 0 x))))
*)
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
When a RARE rule is parsed in 


(concat x ys)    is     (concat_bvs x (of_bl (concat_list (map to_bl ys))))



During reconstruction

E.g. ys=[y1,y2,y3] x=x1

(concat x1 (concat y1 (concat y2 (concat y3))))


Instantiate  (concat_bvs x (of_bl (concat_list (map to_bl ys))))
= (concat_bvs x (of_bl (to_bl y1 @ to_bl y2 @ to_bl y3)))











Make function that concatenates bv that are expressed as natural numbers

nat \<Rightarrow> nat \<Rightarrow> nat

*)

























fun word_concat_left :: "nat \<Rightarrow> 'b::len word \<Rightarrow> 'c::len word" where (*TODO: Bitwidth of the result*)
"word_concat_left n y = (THE z::'c::len word.  uint z = concat_bit (LENGTH('c)) n (unat y)) "

fun word_concat_right :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'c::len word" where (*TODO: Bitwidth of the result*)
"word_concat_right x m = (THE z::'c::len word.  uint z = concat_bit (LENGTH('c)) (unat x) m) "

(*(define-rule* bv-concat-flatten
  ((xs ?BitVec :list)
   (s ?BitVec)
   (ys ?BitVec :list)
   (zs ?BitVec :list))
  (concat xs (concat (concat s ys) zs))
  (concat xs (concat s (concat ys zs)))

*)

(*First fold concat_bit over list, get natural number. Then apply word_concat_right *)

(*fun cvc_nary_op_fold :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a" where
 cvc_nary_op_fold_Nil: "cvc_nary_op_fold op [x] = x" |
 cvc_nary_op_fold_Cons: "cvc_nary_op_fold op (x#xs) = (op x (cvc_nary_op_fold op xs))"
*)

(*Use reversed bit list?

Dann kann ich bitvectoren als (to_bl x) einparsen

Die Funktion nimmt dann eine bl und ein word

Erster Schritt concat zwei blists, ergebnis ist ein Wort. Dann immer eine bl ein Wort mit concat_left. Am Ende kommt ein Wort raus, das andere word wird vorne 
drangehangen. 

Geht whrs nicht wegen den Typen. Aber erst ganze Liste auf nats ausrollen?! Gibt es dann nicht probleme das Lemma bei der Rekonstruktion zu benutzen?

*)
(*fun test :: "nat list \<Rightarrow> nat"

term "cvc_nary_op_fold concat_bit

fun cvc_bin_op2' :: "('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b cvc_ListVar \<Rightarrow> 'a" where
 "cvc_bin_op2' op1 op2 op3 y (ListVar xs) = (if xs = [] then y else op3 y (cvc_nary_op_fold' op1 op2 xs))"

definition cvc_list_right' where "cvc_list_right' op1 op2 op3 y lv = cvc_bin_op2' op1 op2 op3 y lv"





(*"(nat \<Rightarrow> word \<Rightarrow> word) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> word) \<Rightarrow> (word \<Rightarrow> word \<Rightarrow> word)*)
definition word_concat_cvc_list_right' where
 "word_concat_cvc_list_right' y lv = cvc_list_right' op1 op2 op3 y lv"



lemma test:
  fixes xs::"nat cvc_ListVar" and zs::"nat cvc_ListVar" and s::"'a::len word"
  shows "(cvc_list_left word_concat_left xs (cvc_list_right word_concat_right (cvc_list_right word_concat_right s ys) zs))
= (cvc_list_left word_concat_left xs (cvc_list_right word_concat_right s (cvc_list_both concat_bit ys zs)))"






lemma test:
  fixes xs::"nat cvc_ListVar" and zs::"nat cvc_ListVar" and s::"'a::len word"
  assumes "\<not>(ys = (ListVar []) \<and> zs = (ListVar []))"
  shows "(cvc_list_left word_concat_list_left xs (cvc_list_right' word_concat_list_right (0::'a::len word) s ys))
= (cvc_list_left word_concat_list_left xs (word_cat s (cvc_list_both word_concat_list_both (0::'a::len word) ys zs)))"
  oops


*)


declare[[show_types,show_sorts]]

(*  "to_bl (of_bl bl::'a::len word) =*)
















  




value "(concat_smt [[True,False],[True,True]])::4 word" (*concat 10 11 = 1011  \<rightarrow> 11*)

(*
  (concat xs ((concat s ys) zs))
  (concat xs (s (ys zs)))
*)

lemma "
LENGTH('a) = size (s::'f1::len word) + size (t::'f2::len word) \<Longrightarrow>
LENGTH('b) = LENGTH('a) + size (q::'f3::len word) \<Longrightarrow>
LENGTH('d) = size t + size q \<Longrightarrow>
LENGTH('b) = size s + LENGTH('d) \<Longrightarrow>
(word_cat (word_cat s t::'a::len word) q::'b::len word) = word_cat s (word_cat t q::'d::len word)"
  apply (simp only: word_unat_eq_iff)
  apply (subst unat_word_cat[of "(word_cat s t::'a::len word)" q, where 'c='b] )
  using word_size apply auto[1]
  apply (subst unat_word_cat[of s t, where 'c='a])
   apply (simp add: word_size)
  apply (subst unat_word_cat[of s "(word_cat t q::'d::len word)", where 'c='b])
   apply (simp add: word_size)
  apply (subst unat_word_cat)
   apply (simp add: word_size)
  by (simp add: add.commute push_bit_add size_word.rep_eq)




lemma test:
  fixes xs::"(bool list) list" and ys::"(bool list) list" 
    and zs::"(bool list) list" and s::"'a::len word"
  assumes a0: "(c_s_ys_1::'f1::len word) = (word_cat s (concat_smt ys::'b::len word))"
      and a1: "LENGTH('f1) = LENGTH('a) + LENGTH('b)"
      and a2: "(c_1_zs_2::'f2::len word) = (word_cat c_s_ys_1 (concat_smt zs::'c::len word))"
      and a3: "LENGTH('f2) = LENGTH('f1) + LENGTH('c)"
      and a4: "(c_xs_2_3::'f3::len word) = (word_cat (concat_smt xs::'d::len word) c_1_zs_2)"
      and a5: "LENGTH('f3) = LENGTH('d) + LENGTH('f2)"
      and a6: "(c_ys_zs_4::'f4::len word) = (word_cat (concat_smt ys::'b::len word) (concat_smt zs::'c::len word))"
      and a7: "LENGTH('f4) = LENGTH('b) + LENGTH('c)"
      and a8: "(c_s_4_5::'f2::len word) = (word_cat s c_ys_zs_4)"
      and a9: "LENGTH('f2) = LENGTH('a) + LENGTH('f4)"
      and a10: "(c_xs_5_6::'f3::len word) = (word_cat (concat_smt xs::'d::len word) c_s_4_5)"
      and a11: "LENGTH('f3) = LENGTH('d) + LENGTH('f2)"
      and "xs \<noteq> []" and "ys \<noteq> []" and "zs \<noteq> []" and "list_length_0 xs" and "list_length_0 ys" and "list_length_0 zs"
    shows "c_xs_2_3 = c_xs_5_6"
  unfolding a4 a10
  apply (subst  arg_cong[of c_1_zs_2 c_s_4_5 "\<lambda>k. word_cat (concat_smt xs::'d::len word) k::'f3::len word"])
  subgoal
    unfolding a2 a8 a0 a6
    using word_cat_on_word_cat 
  proof -
    have "len_of (TYPE('f4)::'f4 itself) = len_of (TYPE('b)::'b itself) + len_of (TYPE('c)::'c itself) \<and> len_of (TYPE('f2)::'f2 itself) = len_of (TYPE('f1)::'f1 itself) + len_of (TYPE('c)::'c itself) \<and> len_of (TYPE('f1)::'f1 itself) = len_of (TYPE('a)::'a itself) + len_of (TYPE('b)::'b itself)"
      using a1 a3 a7 by blast
    then show "(word_cat (word_cat s (concat_smt ys::'b word)::'f1 word) (concat_smt zs::'c word)::'f2 word) = word_cat s (word_cat (concat_smt ys::'b word) (concat_smt zs::'c word)::'f4 word)"
      by (simp add: word_cat_on_word_cat word_size)
  qed
  apply simp
  done














(*

Alle Vorkommen von xs ausserhalb von concat muessten mit (foldr of_bl xs) und eigenen Variablen ersetzt werden, was nur funktioniert
wenn sie alle diesselbe Laenge haben

Fuer concat ersetzen wir Vorkommen von concat xs y mit (concat (concat_smt xs) y). concat_smt nimmt eine Liste von bl listen 
und gibt die Concatenation als bitvector. Durch die implicit assumptions wird size  (concat (concat_smt xs) y) als summe
gesetzt. Aber wir koennen es auch selbst hinzufuegen. Muessen wir vielleicht sogar weil beide listen leer sein koennen


  (concat xs (concat s ys) zs)
  (concat xs s ys zs))


*)

named_theorems rewrite_bv_extract_whole \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_whole]:
  fixes x::"'a::len word" and n::"int"
  shows "NO_MATCH cvc_a (undefined x n) \<Longrightarrow>
int (size x) - (1::int) \<le> n \<Longrightarrow>
   smtlib_extract n 0 x = x"
  unfolding smtlib_extract_def
  apply (cases "n = int (size x)")
  apply (simp add: size_word.rep_eq slice_id smt_extract_def take_bit_word_eq_self)
  by (simp add: size_word.rep_eq slice_id smt_extract_def take_bit_word_eq_self)

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

named_theorems rewrite_bv_udiv_zero \<open>automatically_generated\<close>


(*This is an example where Isabelle and SMTLIB semantics are completely different*)

lemma [rewrite_bv_udiv_zero]:
  fixes x::"'a ::len word"
  shows "x div Word.Word (0::int) =  (Word.Word (0::int))"
  by simp

named_theorems rewrite_bv_udiv_one \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_one]:
  fixes x::"'a ::len word"
  shows "x div Word.Word (1::int) = x"
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

named_theorems rewrite_bv_urem_one \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_one]:
  fixes x::"'a ::len word"
  shows "smt_urem x (Word.Word (1::int)) = Word.Word (0::int)"
  unfolding smt_urem_def
  apply simp
  by (simp add: unsigned_eq_0_iff)

named_theorems rewrite_bv_urem_self \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_self]:
  fixes x::"'a ::len word"
  shows "x> 0 \<longrightarrow> smt_urem x x = Word.Word (0::int)"
  unfolding smt_urem_def
  apply simp
  using unat_eq_zero by auto

named_theorems rewrite_bv_shl_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "push_bit (unat a) (Word.Word (0::int)) = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_lshr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "drop_bit (unat a) (Word.Word (0::int)) = Word.Word (0::int)"
  by auto


named_theorems rewrite_bv_ugt_urem \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_urem]:
  fixes y::"'a ::len word" and x::"'a ::len word"
  shows "(x < smt_urem y x) =
   (Word.Word (0::int) < y \<and> x = Word.Word (0::int))"
  unfolding smt_urem_def
  apply simp
  by (metis not_less_iff_gr_or_eq unat_gt_0 word_arith_nat_mod word_gt_a_gt_0 word_mod_by_0 word_mod_less_divisor)

named_theorems rewrite_bv_ult_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_one]:
  fixes x::"'a ::len word"
  shows "(x < Word.Word (1::int)) = (x = Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_slt_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_slt_zero]:
  fixes x::"'a ::len word"
  shows "LENGTH('a) > 1 \<longrightarrow> (x <s (Word.Word (0::int)::'a::len word)) =
   (smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) x =
    (Word.Word (1::int)::1 word))"
proof
  assume "(1::nat) < LENGTH('a)"
  have "sint (smt_extract (nat (int (size x) - (1::int))) (nat (int (size x) - (1::int))) x::1 word)
      = sint (smt_extract (size x - 1) (size x - 1) x::1 word)"
    by (simp add: nat_minus_as_int)
  then have "sint (smt_extract (nat (int (size x) - (1::int))) (nat (int (size x) - (1::int))) x::1 word)
      = signed_take_bit (LENGTH(1) - Suc (0::nat)) (drop_bit (size x - (1::nat)) (take_bit (Suc (size x - (1::nat))) (uint x)))"
    using sint_smt_extract[of "size x - 1" "size x - 1" x, where 'b="1"]
    by (metis Suc_pred' add_diff_cancel_left' le_refl len_num1 lessI word_size_gt_0)
  then have "sint (smt_extract (nat (int (size x) - (1::int))) (nat (int (size x) - (1::int))) x::1 word)
      = signed_take_bit 0 (drop_bit (size x - (1::nat)) (take_bit (Suc (size x - (1::nat))) (uint x)))"
    using One_nat_def diff_self_eq_0 len_num1 by presburger
  moreover have "sint (1::1 word) = -1"
    by simp


   have t3: "(size x - (size x - Suc (0::nat))) = 1"
    by (metis One_nat_def Suc_diff_1 add_implies_diff plus_1_eq_Suc word_size_gt_0)

  have "(sint x < (0::int))
      = (signed_take_bit 0 (drop_bit (size x - (1::nat)) (take_bit (Suc (size x - (1::nat))) (uint x))) = -1)"
    apply simp
    apply (simp add: drop_bit_take_bit)
    unfolding drop_bit_eq_div take_bit_eq_mod
    apply (simp add: sint_uint)
    apply (simp add: t3 bit_iff_odd)
    apply (simp add: word_size)
    by (simp add: odd_iff_mod_2_eq_one)

   then show "(x <s Word.Word (0::int)) =
    (smt_extract (nat (int (size x) - (1::int))) (nat (int (size x) - (1::int))) x = (Word.Word (1::int)::1 word))"
    apply (simp add: word_sless_alt)
  by (metis \<open>(sint (x::'a::len word) < (0::int)) = (signed_take_bit (0::nat) (drop_bit (size x - (1::nat)) (take_bit (Suc (size x - (1::nat))) (uint x))) = - (1::int))\<close> calculation len_num1 signed_1 word_eq_iff_signed)
qed

named_theorems rewrite_bv_zero_ult \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ult]:
  fixes x::"'a ::len word"
  shows "(Word.Word 0 < x) = (x \<noteq> Word.Word 0)"
  using word_neq_0_conv by auto

named_theorems rewrite_bv_merge_sign_extend_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_1]:
  fixes x::"'a::len word" and i::"int" and j::"int"
  shows "LENGTH('b) = LENGTH('a) + j \<longrightarrow> LENGTH('c) = LENGTH('b) + i \<longrightarrow> LENGTH('c) = LENGTH('a) + (i + j) \<longrightarrow>
i \<ge> 0 \<longrightarrow> j \<ge> 0 \<longrightarrow> 
 (Word.signed_cast (Word.signed_cast x::'b::len word)::'c::len word) = Word.signed_cast x"
  using scast_up_scast_id[of x]
  by (simp add: is_up.rep_eq scast_up_scast)

named_theorems rewrite_bv_merge_sign_extend_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_merge_sign_extend_2]:
  fixes x::"'a::len word" and i::"int" and j::"int"
  shows "(1::int) < j \<longrightarrow> LENGTH('c) = LENGTH('b) + i \<longrightarrow> i \<ge> 0 \<longrightarrow>
    j \<ge> 0 \<longrightarrow> LENGTH('b) = LENGTH('a) + j \<longrightarrow> LENGTH('c) = LENGTH('a) + (i + j) \<longrightarrow> 
   (Word.signed_cast (Word.cast x::'b::len word)::'c::len word) = Word.cast x"
  apply (rule impI)+
  apply transfer
  by (simp add: signed_take_bit_take_bit)

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