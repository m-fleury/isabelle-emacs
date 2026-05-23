theory Alethe_BV_Rewrites_Lemmas
  imports  "HOL-Library.Word" Word_Lib.More_Word "HOL-Library.Log_Nat" "HOL.Real" "HOL-Library.Sublist" 
HOL.SMT "Word_Lib.Signed_Division_Word" "Word_Lib.Reversed_Bit_Lists" CVC_Word
begin

lemma word_cat_smt_extract: "i \<le> j \<and> j + 1 \<le> k \<and> i \<ge> 0 \<and> k < size x 
 \<and> LENGTH('b::len) = k + (1::nat) - Suc j
 \<and> LENGTH('d::len) = k + (1::nat) - i
 \<and> LENGTH('c::len) = j + (1::nat) - i
\<longrightarrow> word_cat ((smt_extract k (j+1) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) = ((smt_extract k i x)::'d::len word)"
  apply (rule impI)+
  apply (simp add: bang_eq)
  apply (rule allI)+
  subgoal for n
    apply (simp add: bit_word_cat_iff)
    apply (cases "n < Suc j - i")
    apply (simp_all add: bit_smt_extract bit_word_cat_iff)
     apply (cases "n < Suc k - i")
      apply simp_all
    apply linarith
     apply (cases "n < Suc k - i")
     apply simp_all
    apply (cases "n + i - Suc 0 < k")
    apply simp_all
    apply (cases "n + i < Suc k ")
     apply simp_all
    apply (cases "n + i - Suc j < k - j")
     apply simp_all
    by (metis Suc_pred diff_Suc_1' diff_Suc_Suc diff_add_0 len_gt_0 zero_less_iff_neq_zero)
  done

lemma smtlib_extract_eq_smt_extract:
  fixes w :: "'a::len word"
  shows "(smtlib_extract (int j) (int i) w :: 'b::len word) = smt_extract j i w"
  unfolding smtlib_extract_def smt_extract_def
  by (metis nat_int.Rep_inverse Suc_as_int)
declare[[show_types,show_sorts]]

lemma word_cat_smtlib_extract: "
j \<ge> i \<and> i \<ge> 0 \<and> int LENGTH('c::len) = j + 1 - i \<and>
k \<ge> j + 1 \<and> j + 1 \<ge> 0 \<and> int LENGTH('b::len) = k - j 
 \<and> LENGTH('b) + LENGTH('c) = LENGTH('d)
\<longrightarrow> word_cat ((smtlib_extract k (j+1) (x::'a::len word))::'b::len word) ((smtlib_extract j i x)::'c::len word) = ((smtlib_extract k i x)::'d::len word)"
proof (rule impI)
  assume A: "j \<ge> i \<and> i \<ge> 0 \<and> int LENGTH('c::len) = j + 1 - i \<and>
             k \<ge> j + 1 \<and> j + 1 \<ge> 0 \<and> int LENGTH('b::len) = k - j
             \<and> LENGTH('b::len) + LENGTH('c::len) = LENGTH('d::len)"

  from A have ij: "i \<le> j" and i_nn: "0 \<le> i"
      and c_eq_int: "int LENGTH('c::len) = j + 1 - i"
      and jk: "j + 1 \<le> k"
      and b_eq_int: "int LENGTH('b::len) = k - j"
      and d_eq: "LENGTH('b::len) + LENGTH('c::len) = LENGTH('d::len)"
    by auto
  from ij i_nn have j_nn: "0 \<le> j" by linarith
  from jk j_nn have k_nn: "0 \<le> k" by linarith

  let ?ni = "nat i" and ?nj = "nat j" and ?nk = "nat k"

  have ni_le_nj: "?ni \<le> ?nj" using ij i_nn by (simp add: nat_mono)
  have Snj_le_nk: "Suc ?nj \<le> ?nk"
    using jk j_nn k_nn by linarith

  have c_nat: "LENGTH('c::len) = Suc ?nj - ?ni"
  proof -
    have "LENGTH('c::len) = nat (int LENGTH('c::len))" by simp
    also have "\<dots> = nat (j + 1 - i)" using c_eq_int by simp
    also have "\<dots> = Suc ?nj - ?ni"
      using i_nn ij j_nn by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed
  have b_nat: "LENGTH('b::len) = ?nk - ?nj"
  proof -
    have "LENGTH('b::len) = nat (int LENGTH('b::len))" by simp
    also have "\<dots> = nat (k - j)" using b_eq_int by simp
    also have "\<dots> = ?nk - ?nj"
      using j_nn jk by (simp add: nat_diff_distrib)
    finally show ?thesis .
  qed
  have d_nat: "LENGTH('d::len) = Suc ?nk - ?ni"
    using d_eq b_nat c_nat Snj_le_nk ni_le_nj by linarith

  text \<open>Rewrite each smtlib_extract to a corresponding smt_extract.\<close>
  have eb: "(smtlib_extract k (j+1) x :: 'b::len word) = smt_extract ?nk (Suc ?nj) x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='b and j="?nk" and i="Suc ?nj"]
          k_nn j_nn
    by (simp add: add.commute)
  have ec: "(smtlib_extract j i x :: 'c::len word) = smt_extract ?nj ?ni x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='c and j="?nj" and i="?ni"]
          j_nn i_nn
    by (metis int_nat_eq)
  have ed: "(smtlib_extract k i x :: 'd::len word) = smt_extract ?nk ?ni x"
    using smtlib_extract_eq_smt_extract[where 'a='a and 'b='d and j="?nk" and i="?ni"]
          k_nn i_nn
    by (metis int_nat_eq)

  show "word_cat (smtlib_extract k (j+1) x :: 'b::len word)
                 (smtlib_extract j i x :: 'c::len word)
        = (smtlib_extract k i x :: 'd::len word)"
    unfolding eb ec ed
  proof (rule bit_word_eqI)
    fix n :: nat
    assume n_lt: "n < LENGTH('d::len)"
    from n_lt d_nat ni_le_nj Snj_le_nk
    have n_ni_le_nk: "n + ?ni \<le> ?nk" by linarith
    show "bit (word_cat (smt_extract ?nk (Suc ?nj) x :: 'b::len word)
                        (smt_extract ?nj ?ni x :: 'c::len word) :: 'd::len word) n
        = bit (smt_extract ?nk ?ni x :: 'd::len word) n"
    proof (cases "n < LENGTH('c::len)")
      case True
      with c_nat ni_le_nj n_lt d_nat n_ni_le_nk
      show ?thesis
        apply (simp add: bit_word_cat_iff bit_smt_extract)
        by linarith
    next
      case False
      hence c_le: "LENGTH('c::len) \<le> n" by simp
      have m_def: "(n - LENGTH('c::len)) + Suc ?nj = n + ?ni"
        using c_le c_nat ni_le_nj Snj_le_nk by linarith
      have m_bound: "n - LENGTH('c::len) < LENGTH('b::len)"
        using c_le c_nat n_lt d_nat ni_le_nj Snj_le_nk b_nat by linarith
      have n_ni_lt_Snk: "n + ?ni < Suc ?nk"
        using n_ni_le_nk by linarith
      from c_le m_def m_bound n_ni_lt_Snk n_lt
      show ?thesis
        by (simp add: bit_word_cat_iff bit_smt_extract)
    qed
  qed
qed

lemma word_cat_smt_extract_2:
  fixes x::"'a::len word" and t1 :: "'b::len word" and t2 :: "'c::len word" and t3 :: "'d::len word"
  and i j k :: "int"
  shows  "i \<le> j \<and> j + 1 \<le> k \<and> i \<ge> 0 \<and> k < int (size x)
 \<and> t1 = ((smt_extract (nat k) (nat (j+1)) (x::'a::len word))::'b::len word)
 \<and> t2 = ((smt_extract (nat j) (nat i) x)::'c::len word)
 \<and> t3 = ((smt_extract (nat k) (nat i) x)::'d::len word)
 \<and> int (size t1) = k - j
 \<and> int (size t3) = k + (1::int) - i
 \<and> int (size t2) = j + (1::int) - i
\<longrightarrow> word_cat t1 t2 = t3"
proof
  assume a0: "((i \<le> j) \<and>
      (((j + (1::int)) \<le> k) \<and>
       (((0::int) \<le> i) \<and>
        ((k < (int (size x))) \<and>
         ((t1 = (smt_extract (nat k) (nat (j + (1::int))) x)) \<and>
          ((t2 = (smt_extract (nat j) (nat i) x)) \<and>
           ((t3 = (smt_extract (nat k) (nat i) x)) \<and>
            (((int (size t1)) = (k - j)) \<and> (((int (size t3)) = ((k + (1::int)) - i)) \<and> ((int (size t2)) = ((j + (1::int)) - i)))))))))))"
  have "(nat (i::int)) \<le> (nat (j::int))"
    by (simp add: a0 nat_mono)
  moreover have "(nat j) + (1::nat) \<le> (nat (k::int))"
    using Suc_nat_eq_nat_zadd1 a0 nat_mono by auto
  moreover have "(0::nat) \<le> (nat i)"
    by simp
  moreover have "(nat k) < (size (x::'a::len word))"
    using a0 nat_less_iff by auto
  moreover have "LENGTH('a::len) = (size x)"
    by (simp add: word_size)
  moreover have "LENGTH('b::len) = (((nat k) + (1::nat)) - (Suc (nat j)))"
    by (metis Nat.diff_cancel Suc_eq_plus1 a0 add.commute bot_nat_0.extremum_uniqueI calculation(1)
        calculation(2) int_eq_iff int_nat_eq nat_diff_distrib' nat_eq_iff nat_int_comparison(3)
        not_less_eq_eq word_size)
  moreover have "LENGTH('d::len) = (((nat k) + (1::nat)) - (nat i))"
    sorry  moreover have "LENGTH('c::len) = (((nat j) + (1::nat)) - (nat i))"
    sorry  ultimately show "(word_cat t1 t2) = t3"
    using word_cat_smt_extract[of "nat i" "nat j" "nat k" x, where 'b="'b", where 'd="'d", where 'c="'c"]
      sorry
  qed
    
lemma 
  fixes s::"'a ::len word" and i::"int" and j::"int" and k::"int"
  and x_c1 :: "'d :: len word" and x_c0 :: "'c ::len word" and  x_c2 x_c3 :: "'b ::len word"
  shows 
  "x_c3 = smt_extract (nat k) (nat i) s \<and>
   x_c2 = word_cat x_c0 x_c1 \<and>
   x_c1 = smt_extract (nat j) (nat i) s \<and>
   x_c0 = smt_extract (nat k) (nat (j + 1)) s \<and>
   int (size x_c3) = 1 + (k - i) \<and>
   int (size x_c2) = int (size x_c0) + int (size x_c1) \<and>
   int (size x_c1) = 1 + (j - i) \<and>
   int (size x_c0) = 1 + (k - (j + 1)) \<and>
   i \<le> k \<and> k < int (size s) \<and>
   i \<le> j \<and>
   0 \<le> i \<and>
   j + 1 \<le> k \<and> 0 \<le> j + 1 \<longrightarrow>
   x_c2 = x_c3"
proof
  assume a0: "x_c3 = smt_extract (nat k) (nat i) s \<and>
   x_c2 = word_cat x_c0 x_c1 \<and>
   x_c1 = smt_extract (nat j) (nat i) s \<and>
   x_c0 = smt_extract (nat k) (nat (j + 1)) s \<and>
   int (size x_c3) = 1 + (k - i) \<and>
   int (size x_c2) = int (size x_c0) + int (size x_c1) \<and>
   int (size x_c1) = 1 + (j - i) \<and>
   int (size x_c0) = 1 + (k - (j + 1)) \<and>
   i \<le> k \<and> k < int (size s) \<and>
   i \<le> j \<and>
   0 \<le> i \<and>
   j + 1 \<le> k \<and> 0 \<le> j + 1"
  have "nat (i::int) \<le> (nat (j::int))" 
    using a0 nat_mono by presburger
  moreover have "((nat j) + (1::nat)) \<le> (nat (k::int))"
    using Suc_nat_eq_nat_zadd1 a0 nat_mono by auto
  moreover have "(0::nat) \<le> (nat i)"
    by auto
  moreover have "(nat k) < (size (s::'a::len word))"
    by (metis a0 not_less_iff_gr_or_eq split_nat word_size_gt_0 zless_nat_eq_int_zless)
  moreover have "(x_c0::'c::len word) = (smt_extract (nat k) ((nat j) + (1::nat)) s)"
    using a0 nat_add_distrib by auto
  moreover have "(x_c1::'d::len word) = (smt_extract (nat j) (nat i) s)"
    using a0 by blast
  moreover have "(x_c3::'b::len word) = (smt_extract (nat k) (nat i) s)"
    using a0 by force
  moreover have "(size x_c0) = (((nat k) + (1::nat)) - (Suc (nat j)))"
    sorry
  moreover have "(size x_c3) = (((nat k) + (1::nat)) - (nat i))"
    sorry
  moreover have "(size x_c1) = (((nat j) + (1::nat)) - (nat i))"
    sorry
  ultimately show "x_c2 = x_c3"
    by (metis a0 word_cat_smt_extract word_size)
qed


lemma rewrite_bv_ult_add_one:
  fixes x::"'a ::len word" and y::"'a ::len word" and n::"int"
  shows "(x < y + (Word.Word (1::int)::'a::len word)) =
   (\<not> y < x \<and> y \<noteq> not (Word.Word 0))"
  apply simp
  by (metis ab_left_minus word_Suc_le word_not_le word_not_simps(1))


lemma not_int_div_pow2: "not (x div (2::int)^j) = not x div 2^j"
  apply (induction j)
   apply simp_all
  using not_int_div_2 
  by (metis drop_bit_Suc drop_bit_eq_div drop_bit_half power_Suc)

lemma not_drop_bit: "(not (drop_bit (nat j) (uint x))) = (drop_bit (nat j) (not (uint x)))"
  apply (simp_all add: take_bit_eq_mod drop_bit_eq_div bit_or_iff mask_eq_exp_minus_1)
  using not_int_div_pow2[of "uint x" "nat j"]
  using not_int_rec[of "(uint x div (2::int) ^ nat j)"]
  by simp


 (* apply (rule impI)+
proof-
  assume a0: "(0::int) \<le> j" and a1: "j \<le> i" and a2: "i < int (size x)"
    and a3: "int LENGTH('b) = i + (1::int) - j"

  have t0: "uint (smt_extract (nat i) (nat j) (not x)::'b::len word)
  = drop_bit (nat j) (take_bit (Suc (nat i)) (not (unsigned x)))"
  proof-
  have "nat (j::int) \<le> nat (i::int) \<and> nat i < size (not (x::'a::len word)) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j"
    by (metis Suc_eq_plus1_left Suc_nat_eq_nat_zadd1 a0 a1 a2 a3 add.commute diff_ge_0_iff_ge int_eq_iff nat_diff_distrib nat_less_iff nat_mono order_trans word_size)
  then have "uint (smt_extract (nat i) (nat j) (not x)::'b::len word)
  = drop_bit (nat j) (take_bit (Suc (nat i)) (uint (not x)))"
  using uint_smt_extract[of "nat j" "nat i" "not x", where 'b="'b"]
  by blast
  then have t0: "uint (smt_extract (nat i) (nat j) (not x)::'b::len word)
  = drop_bit (nat j) (take_bit (Suc (nat i)) (take_bit LENGTH('a::len) (not (unsigned x))))"
    using unsigned_not_eq[of x] by metis
  moreover have "(min (Suc (nat i)) LENGTH('a::len)) = Suc (nat i)"
    by (metis Suc_leI \<open>nat (j::int) \<le> nat (i::int) \<and> nat i < size (not (x::'a::len word)) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j\<close> min.orderE word_size)
  ultimately show "uint (smt_extract (nat i) (nat j) (not x)::'b::len word)
  = drop_bit (nat j) (take_bit (Suc (nat i)) (not (unsigned x)))"
    by auto
  qed

 moreover have t1: "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
drop_bit (nat j) (take_bit (nat (i + (1::int))) (not (uint x)))"
proof-
  have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) =
take_bit LENGTH('b::len) (not (unsigned (smt_extract (nat i) (nat j) x::'b::len word)))"
    using unsigned_not_eq[of "(smt_extract (nat i) (nat j) x::'b::len word)"]
    by blast
  moreover have "nat (j::int) \<le> nat (i::int) \<and> nat i < size (not (x::'a::len word)) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j"
    by (metis Suc_eq_plus1_left Suc_nat_eq_nat_zadd1 a0 a1 a2 a3 add.commute diff_ge_0_iff_ge int_eq_iff nat_diff_distrib nat_less_iff nat_mono order_trans word_size)
  moreover have "nat (j::int) \<le> nat (i::int) \<and> nat i < size (x::'a::len word) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j"
    by (metis \<open>nat (j::int) \<le> nat (i::int) \<and> nat i < size (not (x::'a::len word)) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j\<close> word_size)
  ultimately have t1: "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
take_bit LENGTH('b::len) (not (drop_bit (nat j) (take_bit (Suc (nat i)) (uint x))))"
    using uint_smt_extract[of "nat j" "nat i" x, where 'b="'b"] 
    by presburger
  then have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
take_bit LENGTH('b::len) (not (take_bit (Suc (nat i) - nat j) (drop_bit (nat j) (uint x))))"
    using drop_bit_take_bit[of "nat j" "Suc (nat i)" "uint x"]
    by presburger
 then have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
take_bit LENGTH('b::len) (not (take_bit (LENGTH('b)) (drop_bit (nat j) (uint x))))"
   using Suc_eq_plus1 \<open>nat (j::int) \<le> nat (i::int) \<and> nat i < size (x::'a::len word) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j\<close> by presburger
then have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
take_bit LENGTH('b::len) (not (drop_bit (nat j) (uint x)))"
  using take_bit_not_take_bit[of "LENGTH('b)" "(drop_bit (nat j) (uint x))"]
  by presburger
then have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
take_bit LENGTH('b::len) (not (drop_bit (nat j) (uint x)))"
  using take_bit_not_take_bit[of "LENGTH('b)" "(drop_bit (nat j) (uint x))"]
  by presburger
then have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
take_bit LENGTH('b::len) (drop_bit (nat j) (not (uint x)))"
  using not_drop_bit[of j x] by simp
then have "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
drop_bit (nat j) (take_bit (nat (i + (1::int) - j) + nat j) (not (uint x)))"
  using take_bit_drop_bit[of "LENGTH('b)" "nat j" "not (uint x)"]
  by (metis a3 nat_int)
then show "uint (not (smt_extract (nat i) (nat j) x::'b::len word)) = 
drop_bit (nat j) (take_bit (nat (i + (1::int))) (not (uint x)))"
  using a0 a1 nat_diff_distrib' by auto
qed
  

lemma rewrite_bv_extract_bitwise_and:
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
qed*)


lemma rewrite_bv_extract_bitwise_or:
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



lemma rewrite_bv_extract_bitwise_xor:
  fixes x::"'a ::len word" and y::"'a ::len word" and i::"int" and j::"int"
  shows "0 \<le> j \<longrightarrow> nat i < size x \<longrightarrow> int LENGTH('b) = i + 1 - j \<longrightarrow> j \<le> i \<longrightarrow>
smt_extract (nat i) (nat j) (semiring_bit_operations_class.xor x y) =
semiring_bit_operations_class.xor (smt_extract (nat i) (nat j) x::'b::len word)
    (smt_extract (nat i) (nat j) y::'b::len word)"
  apply (rule impI)+
proof-
  assume a0: "0 \<le> j" and a1: "nat i < size x" and a2: "int LENGTH('b) = i + 1 - j" and a3: "j \<le> i"

  have t0: "unat (smt_extract (nat i) (nat j) (semiring_bit_operations_class.xor x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (semiring_bit_operations_class.xor (unat x) (unat y)))"
  proof-
    have "unat (smt_extract (nat i) (nat j) (semiring_bit_operations_class.xor x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (unat (semiring_bit_operations_class.xor x y)))"
      using unat_smt_extract[of "nat j" "nat i" "(semiring_bit_operations_class.xor x y)", where 'b="'b"]  
      by (metis Suc_as_int Suc_eq_plus1 a0 a1 a2 a3 int_nat_eq nat_diff_distrib' nat_int nat_mono not_less_eq_eq order_trans word_size)
    then show "unat (smt_extract (nat i) (nat j) (semiring_bit_operations_class.xor x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (semiring_bit_operations_class.xor (unat x) (unat y)))"
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



lemma rewrite_bv_slt_eliminate_lemma:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(x <s y) =
   (x +
    push_bit (unat (Word.Word (int (size x) - (1::int))::'a::len word))
     (Word.Word (1::int)::'a::len word)
    < y +
      push_bit (unat (Word.Word (int (size x) - (1::int))::'a::len word))
       (Word.Word (1::int)::'a::len word))"
  apply transfer
  apply simp
  apply (simp add: signed_take_bit_eq_take_bit_shift)
  apply (cases \<open>LENGTH('a)\<close>)
  apply simp_all
  apply (simp add: iff_conv_conj_imp)
  apply (rule conjI impI)+
   apply (metis add.commute add_lessD1 n_less_equal_power_2 nat_int of_nat_take_bit plus_1_eq_Suc take_bit_nat_eq_self)
  by (metis add.commute add_lessD1 n_less_equal_power_2 nat_int of_nat_take_bit plus_1_eq_Suc take_bit_nat_eq_self)

end
