theory BV_Rewrites
  imports BV_Rewrites_Lemmas HOL.SMT "Word_Lib.Signed_Division_Word"
begin

(* This is a theory automatically created from a RARE file! All that remains to do is to prove
any lemma whose provided proof fails and to to import this file in SMT.thy (if you want to use it
for proof reconstruction).*)



(*lift_definition word_cat :: \<open>'a::len word \<Rightarrow> 'b::len word \<Rightarrow> 'c::len word\<close>
  is \<open>\<lambda>k l. concat_bit LENGTH('b) l (take_bit LENGTH('a) k)\<close>
  by (simp add: bit_eq_iff bit_concat_bit_iff bit_take_bit_iff)

definition concat_bit :: \<open>nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>concat_bit n k l = take_bit n k OR push_bit n l\<close>*)

(* (concat xs (concat s ys) zs)
  (concat xs s ys zs))

definition word_repeat :: \<open>nat \<Rightarrow> 'a :: len word \<Rightarrow> 'b :: len word\<close> where
 \<open>word_repeat i n = (THE x :: 'b::len word. LENGTH('b) = i * size n \<and> unat x = replicate_nat i (size n) * (unat n))\<close>

definition smt_repeat :: "nat \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word" where
  \<open>smt_repeat i x = (if i = 0 then (ucast x::'b::len word) else word_repeat i x)\<close>*)

(*
definition concat_nat:: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
 \<open>concat_nat x y l = concat_bit l x y\<close>


definition word_concat :: \<open>'a :: len word \<Rightarrow> 'b :: len word \<Rightarrow> 'c :: len word\<close> where
 \<open>word_concat x y = (THE z :: 'c::len word. LENGTH('c) = LENGTH('a) + LENGTH('b) \<and> uint z = concat_nat (LENGTH('c)) (unat x) (unat y))\<close>

fun word_concat_left :: "nat \<Rightarrow> 'b::len word \<Rightarrow> 'c::len word" where
"word_concat_left n y = (THE z::'c::len word. LENGTH('c) = size(of_nat n::'a::len word) + LENGTH('b) \<and>  uint z = concat_nat (LENGTH('c)) n (unat y)) "

fun word_concat_list_left :: "nat list \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word" where
"word_concat_list_left [] y = (ucast y)" |
"word_concat_list_left (x#xs) y = word_concat (word_concat_list_left xs y) y"


definition word_concat_list_right :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'b::len word" where
"word_concat_list_right y x = (ucast y)"

definition word_concat_list_both :: "nat \<Rightarrow> nat \<Rightarrow> 'b::len word" where
"word_concat_list_both y x = (2)"


lemma test:
  fixes xs::"nat cvc_ListVar" and zs::"nat cvc_ListVar" and s::"'a::len word"
  assumes "\<not>(ys = (ListVar []) \<and> zs = (ListVar []))"
  shows "(cvc_list_left word_concat_list_left xs (cvc_list_right' word_concat_list_right (0::'a::len word) s ys))
= (cvc_list_left word_concat_list_left xs (word_cat s (cvc_list_both word_concat_list_both (0::'a::len word) ys zs)))"
  oops
*)
declare[[show_types,show_sorts]]


named_theorems rewrite_bv_extract_extract \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_extract]:
  fixes x::"'a::len word" and i::"int" and j::"int" and k::"int" and l::"int"
  assumes "i \<ge> 0" "i \<le> j" "j < size x" "LENGTH('b) = j + 1 - i"
   "k \<ge> 0" "k \<le> l" "l < size (smt_extract (nat j) (nat i) x::'b::len word)" "LENGTH('c) = l + 1 - k"
   "(i+k) \<ge> 0" "(i+k) \<le> (i+l)" "(i+l) < size x" "LENGTH('c) = (i+l) + 1 - (i+k)"
  shows "
   (smt_extract (nat l) (nat k) (smt_extract (nat j) (nat i) x::'b::len word)::'c::len word) =
   smt_extract (nat (i + l)) (nat (i + k)) x"
  using assms
  apply (simp add: word_unat_eq_iff)
  apply (subst unat_smt_extract[of "nat k" "nat l" "(smt_extract (nat j) (nat i) x::'b::len word)", where 'b="'c"])
  apply (simp_all add: nat_mono)
  apply (subst unat_smt_extract[of "nat i" "nat j" x, where 'b="'b"])
  apply (simp_all add: nat_mono)
  apply (subst unat_smt_extract[of "nat (i+k)" "nat (i+l)" x, where 'b="'c"])
  apply (simp_all add: nat_mono)
  apply (simp add: take_bit_drop_bit)
  apply (simp add: nat_add_distrib add.commute)
  by (simp add: word_size)

named_theorems rewrite_bv_extract_whole \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_whole]:
  fixes x::"'a::len word" and n::"int"
  shows "int (size x) - (1::int) \<le> n \<longrightarrow>
   smt_extract (nat n) (nat (0::int)) x = x"
  apply (cases "n = int (size x)")
  apply (simp add: size_word.rep_eq slice_id smt_extract_def take_bit_word_eq_self)
  by (simp add: size_word.rep_eq slice_id smt_extract_def take_bit_word_eq_self)

named_theorems rewrite_bv_ugt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ugt_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(y < x) = (y < x)"
  by auto

named_theorems rewrite_bv_uge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_uge_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(y \<le> x) = (y \<le> x)"
  by auto

named_theorems rewrite_bv_sgt_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sgt_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(y <s x) = (y <s x)"
  by auto

named_theorems rewrite_bv_sge_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sge_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(y \<le>s x) = (y \<le>s x)"
  by auto

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

named_theorems rewrite_bv_sle_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(x \<le>s y) = (\<not> y <s x)"
  by auto

named_theorems rewrite_bv_redor_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redor_eliminate]:
  fixes x::"'a ::len word"
  shows "smt_redor x = not (smt_comp x (Word.Word (0::int)))"
  unfolding smt_redor_def by simp

named_theorems rewrite_bv_redand_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_redand_eliminate]:
  fixes x::"'a ::len word"
  shows "smt_redand x = smt_comp x (not (Word.Word (0::int)))"
  unfolding smt_redand_def by auto

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

named_theorems rewrite_bv_comp_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_comp_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "smt_comp x y = (if x = y then Word.Word (1::int) else Word.Word (0::int))"
  by (metis one_word.abs_eq smt_comp_def zero_word.abs_eq)

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
    by (metis assms(1) int_one_le_iff_zero_less len_gt_0 less_le_not_le mult_zero_left nat_diff_distrib' nat_int of_nat_0_le_iff of_nat_1 smt_repeat_def t0)
  finally show ?thesis
    by (metis assms(1) less_nat_zero_code one_less_nat_eq smt_repeat_def word_unat_eq_iff)
qed

named_theorems rewrite_bv_repeat_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_repeat_eliminate_2]:
  fixes x::"'a ::len word"
  shows "smt_repeat (nat (1::int)) x = x"
  unfolding smt_repeat_def word_repeat_def replicate_nat_def
  by (simp add: size_word.rep_eq the_equality word_eq_unatI)

named_theorems rewrite_bv_rotate_left_eliminate_1 \<open>automatically_generated\<close>

(*This had a nicer smt proof before but to include in Reconstruction it we need to do without*)
lemma [rewrite_bv_rotate_left_eliminate_1]:
  fixes x::"'a::len word" and amount::"int"
  assumes "SMT.z3mod amount (int (size x)) \<noteq> (0::int)"
    "size x - (1 + SMT.z3mod amount (int (size x))) \<ge> 0"
    "size x - (1 + SMT.z3mod amount (int (size x))) < LENGTH('a)"
    "LENGTH('b) = size x - (1 + SMT.z3mod amount (int (size x))) + 1"
    "size x - SMT.z3mod amount (int (size x)) \<ge> 0"
    "size x - SMT.z3mod amount (int (size x)) \<le> size x -1"
    "size x - 1 < LENGTH('a)"
    "LENGTH('c) = size x - 1 + 1 - (size x - SMT.z3mod amount (int (size x)))"
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
proof-
  have t0: "(nat amount mod (LENGTH('b) + LENGTH('c))) = LENGTH('c)"
    apply (simp add: nat_mod_as_int assms)
    apply (simp add: int_int_eq[symmetric])
    apply (subst assms(8))
    unfolding SMT.z3mod_def
    by simp
  have t1: "(Suc (LENGTH('c) + nat (int (size x) - (1 + SMT.z3mod amount (int (size x)))))) = LENGTH('b) + LENGTH('c)"
    apply (simp add: nat_mod_as_int assms)
    apply (subst int_int_eq[symmetric])
    apply (subst assms(4))
    unfolding SMT.z3mod_def
    apply simp
    by (metis Euclidean_Rings.pos_mod_bound add.commute add1_zle_eq bot_nat_0.extremum_strict leI nat_0_iff
        nat_int_comparison(2) nat_less_eq_zless of_nat_0_le_iff word_size_gt_0)
  have t2: "(Suc (nat (int (size x) - 1)) - nat (int (size x) - SMT.z3mod amount (int (size x)))) = (nat amount mod (LENGTH('b) + LENGTH('c)))"
    apply (simp add: nat_mod_as_int assms)
    unfolding SMT.z3mod_def
    apply simp
    by (metis Suc_pred' assms(10) assms(9) diff_add_inverse diff_add_inverse2 int_ops(2) len_gt_0 nat_0_le nat_int nat_minus_as_int of_nat_mod size_word.rep_eq t0)
  have t3: "(LENGTH('b) + LENGTH('c) - nat amount mod (LENGTH('b) + LENGTH('c)))= (nat (int (size x) - SMT.z3mod amount (int (size x))))"
    apply (simp add: nat_mod_as_int assms)
    unfolding SMT.z3mod_def
    apply simp
    by (metis assms(10) assms(9) nat_0_le nat_int nat_minus_as_int t0 word_size zmod_int)


  show ?thesis
    using assms
  apply (simp only: word_uint_eq_iff)
  apply (simp add: uint_word_rotl_eq)
  apply (simp add: concat_bit_eq uint_take_bit_eq)
  apply (subst uint_word_cat[of "(smt_extract
      (nat (int (size x) - ((1::int) + SMT.z3mod amount (int (size x)))))
      0 x::'b::len word)" "(smt_extract (nat (int (size x) - (1::int)))
      (nat (int (size x) - SMT.z3mod amount (int (size x)))) x::'c::len word)", where 'c="'a"])
   apply simp
  apply (subst uint_smt_extract[of 0 "(nat (int (size x) - ((1::int) + SMT.z3mod amount (int (size x)))))" x, where 'b="'b"])
     apply simp_all
  apply (subst uint_smt_extract[of "(nat (int (size x) - SMT.z3mod amount (int (size x))))" "(nat (int (size x) - (1::int)))" x, where 'b="'c"])
     apply simp_all
    apply (simp add: push_bit_take_bit)
    apply (simp add: drop_bit_take_bit)
    apply (simp add: add.commute)
    apply (subst add_mono_thms_linordered_semiring(4)
[of "take_bit (LENGTH('b) + LENGTH('c)) (push_bit (nat amount mod (LENGTH('b) + LENGTH('c))) (uint x))"
"take_bit (Suc (LENGTH('c) + nat (int (size x) - (1 + SMT.z3mod amount (int (size x)))))) (push_bit LENGTH('c) (uint x))"
"take_bit (nat amount mod (LENGTH('b) + LENGTH('c)))
     (drop_bit (LENGTH('b) + LENGTH('c) - nat amount mod (LENGTH('b) + LENGTH('c))) (uint x))"
"take_bit (Suc (nat (int (size x) - 1)) - nat (int (size x) - SMT.z3mod amount (int (size x))))
     (drop_bit (nat (int (size x) - SMT.z3mod amount (int (size x)))) (uint x))"])
    apply simp_all
    apply (rule conjI)
    using t0 t1 apply presburger
    using t2 t3
    by (simp add: nat_minus_as_int)
qed

named_theorems rewrite_bv_rotate_left_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_left_eliminate_2]:
  fixes x::"'a::len word" and amount::"int"
  shows "SMT.z3mod amount (int (size x)) = (0::int) \<longrightarrow>
   word_rotl (nat amount) x = x"
  unfolding SMT.z3mod_def
  apply (simp only: word_uint_eq_iff)
  apply (simp add: uint_word_rotl_eq)
  apply (simp add: uint_take_bit_eq)
  unfolding concat_bit_def
  by (simp add: bintr_uint nat_mod_as_int size_word.rep_eq)

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
  apply (rule impI)+
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
  apply (simp add:  nat_mod_as_int)
  by (smt (verit, ccfv_SIG) Suc_nat_eq_nat_zadd1 add.right_neutral diff_add_inverse group_cancel.add2 int_nat_eq nat_int plus_1_eq_Suc size_word.rep_eq zmod_int)

named_theorems rewrite_bv_rotate_right_eliminate_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_rotate_right_eliminate_2]:
  fixes x::"'a::len word" and amount::"int"
  shows "SMT.z3mod amount (int (size x)) = (0::int) \<longrightarrow>
   word_rotr (nat amount) x = x"
  unfolding SMT.z3mod_def
  apply (simp only: word_uint_eq_iff)
  apply (simp add: uint_word_rotr_eq)
  apply (simp add: uint_take_bit_eq)
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

named_theorems rewrite_bv_zero_extend_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eliminate]:
  fixes x::"'a::len word" and n::"int"
  shows "LENGTH('c) = LENGTH('b) + LENGTH('a) \<longrightarrow>
   (Word.cast x::'c::len word) = word_cat (Word.Word (0::int)::'b::len word) x"
  apply (simp add: word_uint_eq_iff)
  using uint_word_cat[of 0 x, where 'd1="'b", where 'c="'c"]
  apply simp
  by (simp add: word_cat_bin')

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


named_theorems rewrite_bv_uaddo_eliminate \<open>automatically_generated\<close>

(*TODO: Change smt_uaddo in SMT.thy *)
lemma [rewrite_bv_uaddo_eliminate]:
  fixes x::"'a ::len word" and y::"'b ::len word"
  shows "LENGTH('c) = LENGTH('a) + 1
       \<and> LENGTH('c) = LENGTH('b) + 1 \<and> int (size x) > 0 \<and> int (size y) > 0 
\<longrightarrow> smt_uaddo (TYPE('c::len)) x y =
   (smt_extract (nat (int (size x))) (nat (int (size x)))
     (word_cat (Word.Word (0::int)::1 word) x
 + word_cat (Word.Word (0::int)::1 word) y :: 'c ::len word) =
    (Word.Word (1::int):: 1 word))"
    using smt_uaddo_def[of x y, where 'c="'c"]
    sorry 
<<<<<<< HEAD
=======

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
>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)

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

named_theorems rewrite_bv_smod_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_smod_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "size x > 1 \<longrightarrow> smt_smod x y =
   (if smt_urem
        (if smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) x =
           (Word.Word (1::int)::1 word)
         then - x else x)
        (if smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) y =
            (Word.Word (1::int)::1 word)
         then - y else y) =
       Word.Word (0::int)
    then smt_urem
          (if smt_extract (nat (int (size x) - (1::int)))
               (nat (int (size x) - (1::int))) x =
              (Word.Word (1::int)::1 word)
           then - x else x)
          (if smt_extract (nat (int (size x) - (1::int)))
               (nat (int (size x) - (1::int))) y =
              (Word.Word (1::int)::1 word)
           then - y else y)
    else if smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) x \<noteq>
            (Word.Word (1::int)::1 word) \<and>
            smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) y \<noteq>
            (Word.Word (1::int)::1 word)
         then smt_urem
               (if smt_extract (nat (int (size x) - (1::int)))
                    (nat (int (size x) - (1::int))) x =
                   (Word.Word (1::int)::1 word)
                then - x else x)
               (if smt_extract (nat (int (size x) - (1::int)))
                    (nat (int (size x) - (1::int))) y =
                   (Word.Word (1::int)::1 word)
                then - y else y)
         else if smt_extract (nat (int (size x) - (1::int)))
                  (nat (int (size x) - (1::int))) x =
                 (Word.Word (1::int)::1 word) \<and>
                 smt_extract (nat (int (size x) - (1::int)))
                  (nat (int (size x) - (1::int))) y \<noteq>
                 (Word.Word (1::int)::1 word)
              then - smt_urem
                      (if smt_extract (nat (int (size x) - (1::int)))
                           (nat (int (size x) - (1::int))) x =
                          (Word.Word (1::int)::1 word)
                       then - x else x)
                      (if smt_extract (nat (int (size x) - (1::int)))
                           (nat (int (size x) - (1::int))) y =
                          (Word.Word (1::int)::1 word)
                       then - y else y) +
                   y
              else if smt_extract (nat (int (size x) - (1::int)))
                       (nat (int (size x) - (1::int))) x \<noteq>
                      (Word.Word (1::int)::1 word) \<and>
                      smt_extract (nat (int (size x) - (1::int)))
                       (nat (int (size x) - (1::int))) y =
                      (Word.Word (1::int)::1 word)
                   then smt_urem
                         (if smt_extract (nat (int (size x) - (1::int)))
                              (nat (int (size x) - (1::int))) x =
                             (Word.Word (1::int)::1 word)
                          then - x else x)
                         (if smt_extract (nat (int (size x) - (1::int)))
                              (nat (int (size x) - (1::int))) y =
                             (Word.Word (1::int)::1 word)
                          then - y else y) +
                        y
                   else - smt_urem
                           (if smt_extract
                                (nat (int (size x) - (1::int)))
                                (nat (int (size x) - (1::int))) x =
                              (Word.Word (1::int)::1 word)
                            then - x else x)
                           (if smt_extract
                                (nat (int (size x) - (1::int)))
                                (nat (int (size x) - (1::int))) y =
                               (Word.Word (1::int)::1 word)
                            then - y else y))"
  unfolding smt_smod_def[of x y] 
  unfolding Let_def
  apply (cases " smt_urem
        (if smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) x =
           (Word.Word (1::int)::1 word)
         then - x else x)
        (if smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) y =
            (Word.Word (1::int)::1 word)
         then - y else y) =
       Word.Word (0::int)")
   apply simp
  apply (smt (verit, best) One_nat_def int_ops(2) len_num1 nat_minus_as_int signed_1 sint_1_cases zero_neq_one)
  apply (cases "smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) x \<noteq>
            (Word.Word (1::int)::1 word) \<and>
            smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) y \<noteq>
            (Word.Word (1::int)::1 word)")
   apply simp
  apply (smt (verit, ccfv_threshold) len_num1 nat_1 nat_diff_distrib' nat_int nat_neq_iff of_nat_0_le_iff sint_1_cases)
  sorry

named_theorems rewrite_bv_smod_eliminate_fewer_bitwise_ops \<open>automatically_generated\<close>

lemma [rewrite_bv_smod_eliminate_fewer_bitwise_ops]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "LENGTH('b) + 1 = LENGTH('a) \<Longrightarrow> smt_smod x y =
   (if smt_urem
        (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> x
         then - x else x)
        (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> y
         then - y else y) =
       Word.Word (0::int)
    then smt_urem
          (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> x
           then - x else x)
          (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> y
           then - y else y)
    else if \<not> word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word)
                   \<le> x \<and>
            \<not> word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word)
                   \<le> y
         then smt_urem
               (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word)
                   \<le> x
                then - x else x)
               (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word)
                   \<le> y
                then - y else y)
         else if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word)
                 \<le> x \<and>
                 \<not> word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word)
                        \<le> y
              then - smt_urem
                      (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word)
                          \<le> x
                       then - x else x)
                      (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word)
                          \<le> y
                       then - y else y) +
                   y
              else if \<not> word_cat (Word.Word (1::int)::1 word)
                              (Word.Word (0::int)::'b::len word)
                             \<le> x \<and>
                      word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word)
                      \<le> y
                   then smt_urem
                         (if word_cat (Word.Word (1::int)::1 word)
                              (Word.Word (0::int)::'b::len word)
                             \<le> x
                          then - x else x)
                         (if word_cat (Word.Word (1::int)::1 word)
                              (Word.Word (0::int)::'b::len word)
                             \<le> y
                          then - y else y) +
                        y
                   else - smt_urem
                           (if word_cat (Word.Word (1::int)::1 word)
                                (Word.Word (0::int)::'b::len word)
                               \<le> x
                            then - x else x)
                           (if word_cat (Word.Word (1::int)::1 word)
                                (Word.Word (0::int)::'b::len word)
                               \<le> y
                            then - y else y))"
  unfolding smt_smod_def Let_def
  apply (cases "smt_urem
        (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> x
         then - x else x)
        (if word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> y
         then - y else y) =
       Word.Word (0::int)")
   apply simp
  subgoal
    apply (cases "word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> x")
    apply simp_all
       apply (cases "word_cat (Word.Word (1::int)::1 word) (Word.Word (0::int)::'b::len word) \<le> y")
      apply simp_all
    sorry
  sorry
    
named_theorems rewrite_bv_srem_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_srem_eliminate]:
  fixes x::"'a::len word" and y::"'a::len word"
  shows "smt_srem x y =
   (if bit (smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) x::1 word)
        (0::nat)
    then - smt_urem
            (if bit (smt_extract (nat (int (size x) - (1::int)))
                      (nat (int (size x) - (1::int))) x:: 1 word)
                 (0::nat)
             then - x else x)
            (if bit (smt_extract (nat (int (size x) - (1::int)))
                      (nat (int (size x) - (1::int))) y:: 1 word)
                 (0::nat)
             then - y else y)
    else smt_urem
          (if bit (smt_extract (nat (int (size x) - (1::int)))
                    (nat (int (size x) - (1::int))) x::1 word)
               (0::nat)
           then - x else x)
          (if bit (smt_extract (nat (int (size x) - (1::int)))
                    (nat (int (size x) - (1::int))) y::1 word)
               (0::nat)
           then - y else y))"
  unfolding smt_srem_def Let_def
  apply (cases "bit (smt_extract (nat (int (size x) - (1::int)))
             (nat (int (size x) - (1::int))) x::1 word)  (0::nat)")
   apply auto
                      apply (simp_all add: nat_minus_as_int; fail)+
                      apply (simp add: bit_smt_extract nat_minus_as_int smt_extract_bit test_bit_size)
                      apply (metis (full_types) One_nat_def dvd_0_right len_num1 nat_minus_as_int of_nat_1 one_neq_neg_one signed_1 sint_1_cases)
                      apply (metis (full_types) One_nat_def dvd_0_right len_num1 nat_minus_as_int of_nat_1 one_neq_neg_one signed_1 sint_1_cases)
                      apply (metis (full_types) One_nat_def dvd_0_right len_num1 nat_minus_as_int of_nat_1 one_neq_neg_one signed_1 sint_1_cases)
                      apply (simp add: nat_minus_as_int; fail)+
                      apply (simp add: bit_smt_extract nat_minus_as_int smt_extract_bit test_bit_size; fail)
                      apply (simp add: bit_smt_extract nat_minus_as_int smt_extract_bit test_bit_size; fail)
(*                      apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
                      apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
                      apply (simp add: nat_minus_as_int; fail)+
                     apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
                    apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
                   apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
                  apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
                 apply (simp add: nat_minus_as_int; fail)+
                apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
               apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
              apply (smt (verit, ccfv_threshold) bit_1_0 smt_extract_bit word_size_gt_0)
             apply (smt (verit, ccfv_threshold) bit_1_0 smt_extract_bit word_size_gt_0)
            apply (smt (verit, ccfv_threshold) bit_1_0 smt_extract_bit word_size_gt_0)
           apply (smt (verit, ccfv_threshold) bit_1_0 smt_extract_bit word_size_gt_0)
          apply (smt (verit, ccfv_threshold) bit_1_0 smt_extract_bit word_size_gt_0)
         apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
        apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
       apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
      apply (smt (verit, ccfv_threshold) bit_1_0 smt_extract_bit word_size_gt_0)
     apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
    apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
   apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))
  apply (smt (verit, ccfv_SIG) smt_extract_bit word_size_gt_0 wsst_TYs(3))*)
  sorry

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

named_theorems rewrite_bv_ssubo_eliminate \<open>automatically_generated\<close>

lemma [rewrite_bv_ssubo_eliminate]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "smt_ssubo x y =
   (smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) x =
    (Word.Word (1::int)::1 word) \<and>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) y \<noteq>
    (Word.Word (1::int)::1 word) \<and>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) (x - y) \<noteq>
    (Word.Word (1::int)::1 word) \<or>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) x \<noteq>
    (Word.Word (1::int)::1 word) \<and>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) y =
    (Word.Word (1::int)::1 word) \<and>
    smt_extract (nat (int (size x) - (1::int)))
     (nat (int (size x) - (1::int))) (x - y) =
    (Word.Word (1::int)::1 word))"
  unfolding smt_ssubo_def Let_def
  apply simp
  apply (cases "smt_extract (size x - Suc (0::nat)) (size x - Suc (0::nat)) x = (1::1 word)")
   apply simp_all
   apply (case_tac [!] "smt_extract (size x - Suc (0::nat)) (size x - Suc (0::nat)) y = (1::1 word)")
     apply simp_all
  apply (simp add: nat_minus_as_int)
    apply (simp add: nat_diff_distrib')
    apply (simp add: nat_minus_as_int)
  sorry
<<<<<<< HEAD
=======

>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)

named_theorems rewrite_bv_ite_equal_children \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_children]:
  fixes c::"1  word" and x::"'a ::len word"
  shows "(if bit c (0::nat) then x else x) = x"
  by auto

named_theorems rewrite_bv_ite_const_children_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_1]:
  fixes c::"1  word"
  shows "(if bit c (0::nat) then Word.Word (0::int) else Word.Word (1::int)) =
   not c"
  by (metis (mono_tags, opaque_lifting) Word.of_nat_unat Word_eq_word_of_int add.group_left_neutral bit.compl_one bit.compl_zero bit_0_eq inc_le len_of_numeral_defs(2) mask_1 nat_int nle_le nth_0 take_bit_minus_one_eq_mask test_bit_1 ucast_id unsigned_1 unsigned_of_int word_neq_0_conv word_of_int_0 word_of_int_1 word_of_int_neg_1 word_order.extremum)

named_theorems rewrite_bv_ite_const_children_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_const_children_2]:
  fixes c::"1 word"
  shows "(if bit c (0::nat) then Word.Word (1::int) else Word.Word (0::int)) = c"
  by (metis (mono_tags, opaque_lifting) Word.of_nat_unat add.group_left_neutral bit.compl_zero len_of_numeral_defs(2) mask_1 nat_int nth_0 one_word_def take_bit_minus_one_eq_mask ucast_id unsigned_1 unsigned_of_int word_and_1 word_ao_nth word_exists_nth word_of_int_neg_1 word_plus_and_or_coroll2 zero_word_def)

named_theorems rewrite_bv_ite_equal_cond_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_1]:
  fixes c0::"1 word" and t0::"'a ::len word" and e0::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto

named_theorems rewrite_bv_ite_equal_cond_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_2]:
  fixes c0::"1 word" and t0::"'a ::len word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 (0::nat) then t0 else if bit c0 (0::nat) then t1 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto

named_theorems rewrite_bv_ite_equal_cond_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_equal_cond_3]:
  fixes c0::"1 word" and t0::"'a ::len word" and e0::"'a ::len word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 (0::nat) then if bit c0 (0::nat) then t0 else e0
    else if bit c0 (0::nat) then t1 else e1) =
   (if bit c0 (0::nat) then t0 else e1)"
  by auto

named_theorems rewrite_bv_ite_merge_then_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_if]:
  fixes c0::"1 word" and c1::"1  word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else t1) =
   (if bit (and c0 (not c1)) (0::nat) then e1 else t1)"
  by (metis lsb0)

named_theorems rewrite_bv_ite_merge_else_if \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_if]:
  fixes c0::"1 word" and c1::"1 word" and t1::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 (0::nat) then if bit c1 (0::nat) then t1 else e1 else e1) =
   (if bit (and c0 c1) (0::nat) then t1 else e1)"
  by (metis word_ao_nth)

named_theorems rewrite_bv_ite_merge_then_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_then_else]:
  fixes c0::"1 word" and c1::"1 word" and t0::"'a ::len word" and e1::"'a ::len word"
  shows "(if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t0 else e1) =
   (if bit (not (or c0 c1)) (0::nat) then e1 else t0)"
  by (metis lsb0)

named_theorems rewrite_bv_ite_merge_else_else \<open>automatically_generated\<close>

lemma [rewrite_bv_ite_merge_else_else]:
  fixes c0::"1  word" and c1::"1 word" and t1::"'a ::len word" and t0::"'a ::len word"
  shows "(if bit c0 (0::nat) then t0 else if bit c1 (0::nat) then t1 else t0) =
   (if bit (and (not c0) c1) (0::nat) then t1 else t0)"
  by (metis lsb0)

named_theorems rewrite_bv_shl_by_const_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_0]:
  fixes x::"'a::len word" and sz::"int"
  shows "push_bit (unat (Word.Word (0::int))) x = x"
  by auto

named_theorems rewrite_bv_shl_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_1]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
LENGTH('b) = amount \<longrightarrow>
size x - (1 + amount) \<ge> 0 \<longrightarrow>
size x - (1 + amount) < size x \<longrightarrow> 
LENGTH('c) = size x - (1 + amount) - 1 \<longrightarrow>
LENGTH('a) = LENGTH('b) + LENGTH('c) \<longrightarrow>
   (push_bit (unat (Word.Word amount)) x ::'a::len word)=
   word_cat
    (smt_extract (nat (int (size x) - ((1::int) + amount)))
      (nat (0::int)) x::'c::len word)
    (Word.Word (0::int)::'b::len word)"
  by (simp add: size_word.rep_eq)

<<<<<<< HEAD
=======
named_theorems rewrite_bv_shl_by_const_1' \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_1]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
(int (size x)) - (amount + 1) \<ge> 0 \<longrightarrow> (int (size x)) - (amount + 1) \<le> (int (size x)) \<longrightarrow> 
LENGTH('b) = (size x - (1 + amount)) + 1  \<longrightarrow>
LENGTH('c) + LENGTH('b) = LENGTH('a) \<longrightarrow>  
   (push_bit (unat (Word.Word amount::'d::len word)) x::'a::len word) =
   word_cat
    (smt_extract (nat (int (size x) - ((1::int) + amount))) 0 x::'b::len word)
    (Word.Word (0::int)::'c::len word)"
  apply (rule impI)+
  sorry

>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)
named_theorems rewrite_bv_shl_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_2]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow>
   push_bit (unat (Word.Word amount)) x = Word.Word (0::int)"
  sorry

named_theorems rewrite_bv_lshr_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_1]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
   drop_bit (unat (Word.Word amount)) x =
   word_cat (Word.Word (0::int))
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x)"
  sorry

named_theorems rewrite_bv_lshr_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_2]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow>
   drop_bit (unat (Word.Word amount)) x = Word.Word (0::int)"
  sorry

named_theorems rewrite_bv_ashr_by_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_by_const_1]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
   drop_bit (unat (Word.Word amount)) x =
   word_cat
    (smt_repeat (nat amount)
      (smt_extract (nat (int (size x) - (1::int)))
        (nat (int (size x) - (1::int))) x))
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x)"
  sorry

named_theorems rewrite_bv_ashr_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_by_const_2]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow>
   drop_bit (unat (Word.Word amount)) x =
   smt_repeat (nat (int (size x)))
    (smt_extract (nat (int (size x) - (1::int)))
      (nat (int (size x) - (1::int))) x)"
  sorry

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

named_theorems rewrite_bv_or_one \<open>automatically_generated\<close>

lemma [rewrite_bv_or_one]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "y = not (Word.Word 0) \<longrightarrow> or x y = not (Word.Word 0)"
  by auto

named_theorems rewrite_bv_xor_duplicate \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_duplicate]:
  fixes x::"'a ::len word"
  shows "semiring_bit_operations_class.xor x x = Word.Word (0::int)"
  by auto

named_theorems rewrite_bv_xor_ones \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_ones]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "y = not (Word.Word 0) \<longrightarrow>
   semiring_bit_operations_class.xor x y = not x"
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

named_theorems rewrite_bv_xor_not \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_not]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "semiring_bit_operations_class.xor (not x) (not y) =
   semiring_bit_operations_class.xor x y"
  by auto

named_theorems rewrite_bv_not_idemp \<open>automatically_generated\<close>

lemma [rewrite_bv_not_idemp]:
  fixes x::"'a ::len word"
  shows "not (not x) = x"
  by auto

named_theorems rewrite_bv_ult_zero_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_1]:
  fixes x::"'a ::len word"
  shows "(Word.Word (0::int) < x) = (Word.Word (0::int) \<noteq> x)"
  using word_neq_0_conv by auto

named_theorems rewrite_bv_ult_zero_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_zero_2]:
  fixes x::"'a ::len word"
  shows "(x < Word.Word (0::int)) = False"
  by auto

named_theorems rewrite_bv_ult_self \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_self]:
  fixes x::"'a ::len word"
  shows "(x < x) = False"
  by auto

named_theorems rewrite_bv_lt_self \<open>automatically_generated\<close>

lemma [rewrite_bv_lt_self]:
  fixes x::"'a ::len word"
  shows "(x <s x) = False"
  by auto

named_theorems rewrite_bv_ule_self \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_self]:
  fixes x::"'a ::len word"
  shows "(x \<le> x) = True"
  by auto

named_theorems rewrite_bv_ule_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_zero]:
  fixes x::"'a ::len word"
  shows "(x \<le> Word.Word (0::int)) = (x = Word.Word (0::int))"
  by auto

named_theorems rewrite_bv_zero_ule \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_ule]:
  fixes x::"'a ::len word"
  shows "(Word.Word (0::int) \<le> x) = True"
  by auto

named_theorems rewrite_bv_sle_self \<open>automatically_generated\<close>

lemma [rewrite_bv_sle_self]:
  fixes x::"'a ::len word"
  shows "(x \<le>s x) = True"
  by auto

named_theorems rewrite_bv_ule_max \<open>automatically_generated\<close>

lemma [rewrite_bv_ule_max]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "y = not (Word.Word (0::int)) \<longrightarrow> (x \<le> y) = True"
  by auto

named_theorems rewrite_bv_not_ult \<open>automatically_generated\<close>

lemma [rewrite_bv_not_ult]:
  fixes x::"'a ::len word" and y::"'a ::len word"
  shows "(\<not> x < y) = (y \<le> x)"
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

named_theorems rewrite_bv_extract_mult_leading_bit \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_mult_leading_bit]:
  fixes high::"int" and low::"int" and x1i::"int" and x1in::"int" and x2::"'a ::len word" and y1i::"int" and y1in::"int" and y2::"'b ::len word"
  shows "(64::int) < x1in + int (size x2) \<and>
   low
   < (2::int) * (x1in + int (size x2)) -
     ((if x1i = (0::int) then x1in
       else x1in - int (floorlog (nat x1i) (2::nat))) +
      (if y1i = (0::int) then y1in
       else y1in - int (floorlog (nat y1i) (2::nat)))) \<longrightarrow>
   smt_extract (nat high) (nat low)
    (word_cat (Word.Word x1i) x2 * word_cat (Word.Word y1i) y2) =
   Word.Word (0::int)"
  apply (cases "x1i = (0::int)")
  apply (case_tac [!] "y1i = (0::int)")
     apply simp_all
  sorry

named_theorems rewrite_bv_neg_idemp \<open>automatically_generated\<close>

lemma [rewrite_bv_neg_idemp]:
  fixes x::"'a ::len word"
  shows "- (- x) = x"
  by auto

named_theorems rewrite_bv_udiv_pow2_1p \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_1p]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "True \<and> (1::int) < v \<longrightarrow>
   x div Word.Word v =
   word_cat (Word.Word (0::int))
    (smt_extract (nat (n - (1::int)))
      (nat (int (floorlog (nat v) (2::nat)))) x)"
  sorry

named_theorems rewrite_bv_udiv_pow2_1n \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_1n]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "True \<and> v < - (1::int) \<longrightarrow>
   x div Word.Word v =
   - word_cat (Word.Word (0::int))
      (smt_extract (nat (n - (1::int)))
        (nat (int (floorlog (nat (- v)) (2::nat)))) x)"
  sorry
<<<<<<< HEAD
=======

>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)

named_theorems rewrite_bv_udiv_pow2_2p \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_2p]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "v = 1 \<longrightarrow> x div Word.Word v = x"
  by auto

named_theorems rewrite_bv_udiv_pow2_2n \<open>automatically_generated\<close>

lemma [rewrite_bv_udiv_pow2_2n]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "v = - 1 \<longrightarrow> x div Word.Word v = - x"
  sorry

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

named_theorems rewrite_bv_urem_pow2_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_pow2_1]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "is_pow2 v \<and> 1 < v \<longrightarrow>
   smt_urem x (Word.Word v) =
   word_cat (Word.Word 0)
    (smt_extract (nat (int (floorlog (nat v) 2) - 1)) (nat 0) x)"
  sorry

named_theorems rewrite_bv_urem_pow2_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_urem_pow2_2]:
  fixes x::"'a ::len word" and v::"int" and n::"int"
  shows "is_pow2 (- v) \<and> v < - 1 \<longrightarrow>
   smt_urem x (Word.Word v) =
   word_cat (Word.Word 0)
    (smt_extract (nat (int (floorlog (nat (- v)) 2) - 1)) (nat 0) x)"
  unfolding is_pow2_def smt_urem_def
  apply simp
  by force

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

named_theorems rewrite_bv_ashr_zero \<open>automatically_generated\<close>

lemma [rewrite_bv_ashr_zero]:
  fixes n::"int" and a::"'a ::len word"
  shows "signed_drop_bit (unat a) (Word.Word (0::int)) = Word.Word (0::int)"
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

named_theorems rewrite_bv_sign_extend_eq_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eq_const_1]:
  fixes x::"'a::len word" and m::"int" and c::"int" and nm::"int"
  shows "LENGTH('b::len) = nat nm \<longrightarrow> LENGTH('c::len) = nat m + 1 \<longrightarrow> 
  size x - 1 \<ge> 0 \<longrightarrow> nm  - 1 \<ge> size x - 1 \<longrightarrow> nm - 1 < LENGTH('b::len) \<longrightarrow> LENGTH('c::len) = nm - (size x - 1) \<longrightarrow> 
  size x - 1 < LENGTH('b::len) \<longrightarrow> LENGTH('a::len) = size x \<longrightarrow> 
  m \<ge> 0 \<longrightarrow> LENGTH('b) = LENGTH('a) + m \<longrightarrow>
 (Word.signed_cast x = (Word.Word c ::'b::len word)) =
   (((smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int))) (Word.Word c::'b::len word)::'c::len word) = (Word.Word (0::int)::'c::len word)
   \<or>
     (smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int))) (Word.Word c::'b::len word)::'c::len word) = not (Word.Word (0::int)::'c::len word))
  \<and>
    x = smt_extract (nat (int (size x) - (1::int))) (nat (0::int)) (Word.Word c::'b::len word))"
  apply (rule impI)+
  sorry
<<<<<<< HEAD

=======
(*
>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)
named_theorems rewrite_bv_sign_extend_eq_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_eq_const_2]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "(Word.Word c = signed_take_bit (nat m) x) =
   ((smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
      (Word.Word c) =
     Word.Word (0::int) \<or>
     smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
      (Word.Word c) =
     not (Word.Word (0::int))) \<and>
    x =
    smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
     (Word.Word c))"
  sorry

named_theorems rewrite_bv_zero_extend_eq_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eq_const_1]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "
LENGTH('b) =  m \<longrightarrow>
 LENGTH('c) =  nm \<longrightarrow>
size x - 1 \<ge> 0 \<longrightarrow>
LENGTH('a) = size x \<longrightarrow>
nm -1 \<ge> size x -1 \<longrightarrow>
nm -1 < LENGTH('c) \<longrightarrow>
LENGTH('b) = nm -1 + 1 - (size x -1) \<longrightarrow>
((Word.cast x::'c::len word) = (Word.Word c::'c::len word)) =
   (smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
     (Word.Word c::'c::len word) =
    (Word.Word (0::int)::'b::len word) \<and>
    x =
    (smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
     (Word.Word c::'c::len word)::'a::len word))"
  apply (rule impI)+
  apply (simp add: word_uint_eq_iff)
  apply (subst uint_up_ucast)
  apply (simp add: is_up.rep_eq)
  apply (subst uint_smt_extract[of "(nat (int (size x) - (1::int)))" "(nat (nm - (1::int)))" "(word_of_int c::'c::len word)", where 'b="'b"])
     apply simp_all
  apply (metis dual_order.refl len_gt_0 nat_less_iff of_nat_0_less_iff size_word.rep_eq zle_diff1_eq)
  apply (subst uint_smt_extract[of 0 "(nat (int (size x) - (1::int)))" "(word_of_int c::'c::len word)" ])
     apply simp_all
    apply (metis One_nat_def int_minus int_ops(2) nat_int_comparison(2) word_size)
  apply (metis Suc_diff_1 nat_minus_as_int of_nat_1 word_size_gt_0)
  apply (simp add: uint_word_of_int_eq[of c, where 'a="'c"])
  sorry



named_theorems rewrite_bv_zero_extend_eq_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_eq_const_2]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "(Word.Word c = push_bit (nat m) x) =
   (smt_extract (nat (nm - (1::int))) (nat (int (size x) - (1::int)))
     (Word.Word c) =
    Word.Word (0::int) \<and>
    x =
    smt_extract (nat (int (size x) - (1::int))) (nat (0::int))
     (Word.Word c))"
  sorry


named_theorems rewrite_bv_sign_extend_ult_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_1]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "Word.Word c
   \<le> push_bit (unat (Word.Word 1)) (Word.Word (int (size x) - 1)) \<or>
   push_bit (unat (not (Word.Word 0))) (Word.Word (int (size x) - 1))
   \<le> Word.Word c \<longrightarrow>
   (signed_take_bit (nat m) x < Word.Word c) =
   (x < smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c))"
  sorry

named_theorems rewrite_bv_sign_extend_ult_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_2]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "push_bit (unat (Word.Word 1)) (Word.Word (int (size x) - 1))
   < Word.Word c \<and>
   Word.Word c
   \<le> push_bit (unat (not (Word.Word 0)))
          (Word.Word (int (size x) - 1)) \<longrightarrow>
   (signed_take_bit (nat m) x < Word.Word c) =
   (smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1)) x =
    Word.Word 0)"
  sorry

named_theorems rewrite_bv_sign_extend_ult_const_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_3]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "Word.Word c
   < push_bit (unat (Word.Word 1)) (Word.Word (int (size x) - 1)) \<or>
   not (push_bit (unat (Word.Word 1)) (Word.Word (int (size x) - 1)))
   \<le> Word.Word c \<longrightarrow>
   (Word.Word c < signed_take_bit (nat m) x) =
   (smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) < x)"
  sorry

named_theorems rewrite_bv_sign_extend_ult_const_4 \<open>automatically_generated\<close>

lemma [rewrite_bv_sign_extend_ult_const_4]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "not (push_bit (unat (not (Word.Word 0))) (Word.Word (int (size x) - 1)))
   \<le> Word.Word c \<and>
   Word.Word c
   \<le> not (push_bit (unat (Word.Word 1))
               (Word.Word (int (size x) - 1))) \<longrightarrow>
   (Word.Word c < signed_take_bit (nat m) x) =
   (smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1)) x =
    Word.Word 0)"
  sorry

named_theorems rewrite_bv_zero_extend_ult_const_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_ult_const_1]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "smt_extract (nat (nm - 1)) (nat (int (size x))) (Word.Word c) =
   Word.Word 0 \<longrightarrow>
   (push_bit (nat m) x < Word.Word c) =
   (x < smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c))"
  sorry

named_theorems rewrite_bv_zero_extend_ult_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_zero_extend_ult_const_2]:
  fixes x::"'a ::len word" and m::"int" and c::"int" and nm::"int"
  shows "smt_extract (nat (nm - 1)) (nat (int (size x))) (Word.Word c) =
   Word.Word 0 \<longrightarrow>
   (Word.Word c < push_bit (nat m) x) =
   (smt_extract (nat (int (size x) - 1)) (nat 0) (Word.Word c) < x)"
  sorry

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

named_theorems rewrite_bv_extract_not \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_not]:
  fixes x::"'a ::len word" and i::"int" and j::"int"
  shows "j \<ge> 0 \<longrightarrow> i \<ge> j \<longrightarrow> i < int (size x) \<longrightarrow> int (LENGTH('b)) = i + 1 - j \<longrightarrow>
   (smt_extract (nat i) (nat j) (not x)::'b::len word) =
   not (smt_extract (nat i) (nat j) x::'b::len word)"
  apply (rule impI)+
  apply (simp add: word_uint_eq_iff)
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

  moreover have "drop_bit (nat j) (take_bit (Suc (nat i)) (not (unsigned x)))
= drop_bit (nat j) (take_bit (nat (i + (1::int))) (not (uint x)))"
    by (metis Suc_nat_eq_nat_zadd1 a0 a1 add.commute order_trans)

  ultimately show "uint (smt_extract (nat i) (nat j) (not x)::'b::len word) = uint (not (smt_extract (nat i) (nat j) x ::'b::len word))"
    by presburger
qed

<<<<<<< HEAD
named_theorems rewrite_bv_extract_sign_extend_1 \<open>automatically_generated\<close>


=======
*)

named_theorems rewrite_bv_extract_sign_extend_1 \<open>automatically_generated\<close>

(*
(define-cond-rule bv-extract-sign-extend-1
  ((x ?BitVec) (low Int) (high Int) (k Int))
  (< high (bvsize x))
  (extract high low (sign_extend k x))
  (extract high low x)
  )
*)
(*
>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)
lemma [rewrite_bv_extract_sign_extend_1]:
  fixes x::"'a ::len word" and low::"int" and high::"int" and k::"int"
  shows "
LENGTH('a) > 0 \<and> 
LENGTH('b) = k + LENGTH('a) \<and> k \<ge> 0
\<and> LENGTH('c) = high + 1 - low 
\<and> low \<ge> 0 \<and> high \<ge> low \<and> LENGTH('a) > high 
 \<and> LENGTH('b) > high 
\<Longrightarrow> high < size x
 \<Longrightarrow>
   (smt_extract (nat high) (nat low) (Word.signed_cast x::'b::len word)::'c::len word) =
   smt_extract (nat high) (nat low) x" 
proof-
  assume a0: " (0::nat) < LENGTH('a) \<and>
    LENGTH('b) = k + LENGTH('a) \<and> k \<ge> 0
\<and> LENGTH('c) = high + 1 - low 
\<and> low \<ge> 0 \<and> high \<ge> low \<and> LENGTH('a) > high 
 \<and> LENGTH('b) > high "
and a1: "high < size x"
  have "nat (low::int) \<le> nat (high::int) \<and> LENGTH('c::len) = nat high + (1::nat) - nat low"
    using a0 by linarith
  moreover have "nat high < size (Word.signed_cast (x::'a::len word)::'b::len word)"
    by (metis a0 len_gt_0 nat_int size_word.rep_eq zless_nat_conj)
  ultimately have "sint (smt_extract (nat high) (nat low) (Word.signed_cast x::'b::len word)::'c::len word) =
signed_take_bit (LENGTH('c::len) - Suc (0::nat))
   (drop_bit (nat low) (take_bit (Suc (nat high)) (uint (Word.signed_cast x::'b::len word))))" 
  using sint_smt_extract[of "nat low" "nat high" "(Word.signed_cast x::'b::len word)", where 'b="'c"]
  by blast
then have "sint (smt_extract (nat high) (nat low) (Word.signed_cast x::'b::len word)::'c::len word) =
signed_take_bit (LENGTH('c) - Suc (0::nat))
     (drop_bit (nat low) (take_bit (Suc (nat high)) (uint (word_of_int (signed_take_bit (LENGTH('a) - Suc (0::nat)) (Word.rep x))::'b::len word))))" 
  by (metis (no_types, opaque_lifting) One_nat_def Suc_eq_plus1 Word.signed_cast_def Word_eq_word_of_int \<open>nat (low::int) \<le> nat (high::int) \<and> LENGTH('c::len) = nat high + (1::nat) - nat low\<close> drop_bit_take_bit map_fun_def o_apply signed.rep_eq sint_uint the_signed_int.rep_eq uint_word_of_int_eq)
then have "sint (smt_extract (nat high) (nat low) (Word.signed_cast x::'b::len word)::'c::len word) =
signed_take_bit (LENGTH('c) - Suc (0::nat))
     (drop_bit (nat low) (take_bit (Suc (nat high)) (take_bit LENGTH('b::len) (signed_take_bit (LENGTH('a) - Suc (0::nat)) (Word.rep x)))))" 
  using uint_word_of_int_eq by metis
  moreover have 
"(take_bit LENGTH('b::len) (signed_take_bit (LENGTH('a) - Suc (0::nat)) (Word.rep x)))
= uint x"
    sorry
  moreover have "sint (smt_extract (nat high) (nat low) x::'c::len word)
 = signed_take_bit (LENGTH('c::len) - Suc (0::nat))
     (drop_bit (nat low) (take_bit (Suc (nat high)) (uint x)))"
  using sint_smt_extract[of "nat low" "nat high" "x", where 'b="'c"]
  by (metis \<open>nat (low::int) \<le> nat (high::int) \<and> LENGTH('c::len) = nat high + (1::nat) - nat low\<close> a0 len_gt_0 nat_0_iff nat_less_iff nle_le size_word.rep_eq)
  ultimately show "(smt_extract (nat high) (nat low) (Word.signed_cast x::'b::len word)::'c::len word) =
   smt_extract (nat high) (nat low) x"
    apply (simp add: signed_cast.abs_eq)
    sorry
qed

<<<<<<< HEAD
=======

named_theorems rewrite_bv_extract_sign_extend_1 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_1]:
  fixes x::"'a::len ::len word" and low::"int" and high::"int" and k::"int"
  shows "high < int (size x) \<longrightarrow>
   SMT.smt_extract (nat high) (nat low) (Word.signed_cast x) =
   SMT.smt_extract (nat high) (nat low) x"
 sorry
  

>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)
named_theorems rewrite_bv_extract_sign_extend_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_2]:
  fixes x::"'a ::len word" and low::"int" and high::"int" and k::"int"
  shows "low < int (size x) \<and> int (size x) \<le> high \<longrightarrow>
   smt_extract (nat high) (nat low) (signed_take_bit (nat k) x) =
   signed_take_bit (nat (1 + (high - int (size x))))
    (smt_extract (nat (int (size x) - 1)) (nat low) x)"
<<<<<<< HEAD
  sorry

=======
  by auto
*)
>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)
named_theorems rewrite_bv_extract_sign_extend_3 \<open>automatically_generated\<close>

lemma [rewrite_bv_extract_sign_extend_3]:
  fixes x::"'a ::len word" and low::"int" and high::"int" and k::"int"
  shows "int (size x) \<le> low \<longrightarrow>
   smt_extract (nat high) (nat low) (signed_take_bit (nat k) x) =
   smt_repeat (nat (1 + (high - low)))
    (smt_extract (nat (int (size x) - 1)) (nat (int (size x) - 1)) x)"
  sorry

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
    by (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
  done

named_theorems rewrite_bv_and_simplify_1 \<open>automatically_generated\<close>
<<<<<<< HEAD

=======
(*
(*TODO: I would have to add assumption during parsing*)
>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)
lemma [rewrite_bv_and_simplify_1]:
  fixes xs::"'b::len word cvc_ListVar" and ys::"'b::len word cvc_ListVar" and zs::"'b::len word cvc_ListVar" and x::"'b::len word"
  shows "\<not> (xs = (ListVar []) \<and> ys = (ListVar [])) \<Longrightarrow>
     cvc_list_right and
    (and (cvc_list_right and (cvc_list_left and xs x) ys) x) zs =
   cvc_list_right and (cvc_list_right and (cvc_list_left and xs x) ys) zs"
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
    sorry
  done

named_theorems rewrite_bv_and_simplify_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_and_simplify_2]:
  fixes xs::"'a::len word cvc_ListVar" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar" and x::"'a::len word"
  shows "ListVar ys' = ys \<and> ys' \<noteq> [] \<longrightarrow>
ListVar zs' = zs \<and> zs' \<noteq> [] \<longrightarrow>
cvc_list_right and
    (and (cvc_list_right and (cvc_list_left and xs x) ys) (not x)) zs =
   Word.Word (0::int)"
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
    apply (simp add: or.left_commute word_bw_assocs(2))
    by (simp add: word_bw_assocs(2))
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
      apply (simp add: or.assoc word_bw_lcs(2))
     apply (metis or.left_commute word_bw_assocs(2) word_or_max)
    by (simp add: or.assoc)
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
      apply (simp add: word_bw_assocs(3) xor.left_commute)
    apply (simp add: xor.commute)
    by (simp add: word_bw_assocs(3))
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
      apply (simp add: word_bw_assocs(3) xor.left_commute)
    apply (simp add: xor.commute)
    by (simp add: word_bw_assocs(3))
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
      apply (simp add: word_bw_assocs(3) xor.left_commute)
    apply (simp add: xor.commute)
    by (simp add: word_bw_assocs(3))
  done

named_theorems rewrite_bv_ult_add_one \<open>automatically_generated\<close>

lemma [rewrite_bv_ult_add_one]:
  fixes x::"'a ::len word" and y::"'a ::len word" and n::"int"
  shows "(x < y + (Word.Word (1::int)::'a::len word)) =
   (\<not> y < x \<and> y \<noteq> not (Word.Word 0))"
  apply simp
  by (metis ab_left_minus word_Suc_le word_not_le word_not_simps(1))

named_theorems rewrite_bv_concat_to_mult \<open>automatically_generated\<close>

lemma [rewrite_bv_concat_to_mult]:
  fixes x::"'a ::len word" and i::"int" and m::"int"
  shows "(1::int) + i + m = int (size x)
   \<longrightarrow> LENGTH('b) = nat i + 1
   \<longrightarrow> LENGTH('b) + LENGTH('c) = LENGTH('a)
   \<longrightarrow> int (LENGTH('c)) = m
   \<longrightarrow> 
   (word_cat (smt_extract (nat i) (nat (0::int)) x :: 'b:: len word) (Word.Word (0::int):: 'c::len word) ::'a::len word) =
   x * (push_bit (unat (Word.Word m :: 'a::len word)) (Word.Word (1::int)::'a::len word)::'a::len word)"
  using BV_Rewrites_Lemmas.rewrite_bv_concat_to_mult by blast

<<<<<<< HEAD

named_theorems rewrite_bv_mult_slt_mult_1 \<open>automatically_generated\<close>

(*TODO: bvslt needs to generate conditions for its extracts. Proofsketch in sdiv*)
=======
*)


named_theorems rewrite_bv_mult_slt_mult_1 \<open>automatically_generated\<close>

(*(define-rule bv-mult-slt-mult-1 ((x ?BitVec) (t ?BitVec) (a ?BitVec) (n Int) (m Int))
 (def (tn (bvsize t)) (an (bvsize a)) )
 (bvslt (bvmul (sign_extend n (bvadd x t)) (sign_extend m a)) (bvmul (sign_extend n x) (sign_extend m a)))
 (and (not (= t (bv 0 tn))) (not (= a (bv 0 an))) (= (bvslt (bvadd x t) x) (bvsgt a (bv 0 an)))))
*)
(*TODO: bvslt needs to generate conditions for its extracts.*)
(*
>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)
lemma [rewrite_bv_mult_slt_mult_1]:
  fixes x::"'a ::len word" and t::"'a ::len word" and a::"'a ::len word" and n::"int" and m::"int"
  shows "nat n < LENGTH('a) \<Longrightarrow> LENGTH('a) > 1 \<Longrightarrow> 
    (signed_take_bit (nat n) (x + t) * signed_take_bit (nat m) a
    <s signed_take_bit (nat n) x * signed_take_bit (nat m) a) =
   (t \<noteq> (Word.Word 0::'a::len word) \<and>
    a \<noteq> (Word.Word 0::'a::len word) \<and>
   (x + t <s x) = (Word.Word 0 <s a))"
<<<<<<< HEAD
  sorry

=======
  apply (cases "t = (Word.Word 0::'a::len word)")
   apply simp
  apply (cases "a = (Word.Word 0::'a::len word)")
   apply simp
  apply (cases "(x + t <s x) = (Word.Word 0 <s a)")
   apply simp_all
proof-
  assume a00: "nat n < LENGTH('a)" and a01: " Suc (0::nat) < LENGTH('a)" and a0: "t \<noteq> (0::'a word)"
  and a1: "a \<noteq> (0::'a word)"
  and a2: "(x + t <s x) = ((0::'a word) <s a)"

have t0: "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x))
       (signed_take_bit (LENGTH('a) - 1) ((if (bit x (nat n)) then 1 else 0)
   * signed_take_bit LENGTH('a::len) (not (signed (mask (nat n)::'a::len word))))))"
proof-
  have "sint (signed_take_bit (nat n) x) =
   sint (or (take_bit (nat n) x) (of_bool (bit x (nat n)) * not (mask (nat n))))"
    using signed_take_bit_def[of "nat n" "x"] signed_or_eq
    by simp
  then have "sint (signed_take_bit (nat n) x) =
   (or (sint (take_bit (nat n) x::'a::len word)) (sint (of_bool (bit x (nat n)) * not (mask (nat n))::'a::len word)))"
    using signed_or_eq by simp
 then have "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x)) (sint (of_bool (bit x (nat n)) * not (mask (nat n))::'a::len word)))"
  using signed_take_bit_eq[of "nat n" "x"] a00 by simp
then have "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x)) (sint ((if (bit x (nat n)) then 1 else 0) * not (mask (nat n))::'a::len word)))"
  using of_bool_def by simp
then have "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x))
       (signed_take_bit (LENGTH('a) - 1) (sint (if (bit x (nat n)) then 1 else 0::'a::len word) * sint (not (mask (nat n))::'a::len word))))"
  by (simp add: sint_word_ariths(3))
then have "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x))
       (signed_take_bit (LENGTH('a) - 1) ( (if (bit x (nat n)) then sint (1::'a::len word) else sint (0::'a::len word)) * sint (not (mask (nat n))::'a::len word))))"
  by simp
  moreover have "sint (1::'a::len word) = (1::int)"
    using a01 by fastforce
  moreover have "sint (0::'a::len word) = (0::int)"
    by simp
  ultimately have "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x))
       (signed_take_bit (LENGTH('a) - 1) ((if (bit x (nat n)) then 1 else 0) * sint (not (mask (nat n))::'a::len word))))"
    by presburger
then have "sint (signed_take_bit (nat n) x) =
   (or (take_bit (nat n) (sint x))
       (signed_take_bit (LENGTH('a) - 1) ((if (bit x (nat n)) then 1 else 0)
   * signed_take_bit LENGTH('a::len) (not (signed (mask (nat n)::'a::len word))))))"
  using signed_not_eq[of "mask (nat n)"] by metis
  then show ?thesis 
    by blast
qed

 have t1: "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t)))
       (signed_take_bit (LENGTH('a) - 1) ((if (bit (x + t) (nat n)) then 1 else 0)
   * signed_take_bit LENGTH('a::len) (not (signed (mask (nat n)::'a::len word))))))"
proof-
  have "sint (signed_take_bit (nat n) (x + t) * signed_take_bit (nat m) a) =
   signed_take_bit (LENGTH('a::len) - (1::nat)) (sint (signed_take_bit (nat n) (x + t)) * sint (signed_take_bit (nat m) a))"
    using sint_word_ariths(3) by simp
  have "sint (signed_take_bit (nat n) (x + t)) =
   sint (or (take_bit (nat n) (x + t)) (of_bool (bit (x + t) (nat n)) * not (mask (nat n))))"
    using signed_take_bit_def[of "nat n" "x+t"] signed_or_eq
    by simp
  then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (sint (take_bit (nat n) (x + t)::'a::len word)) (sint (of_bool (bit (x + t) (nat n)) * not (mask (nat n))::'a::len word)))"
    using signed_or_eq by simp
 then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (sint (x + t))) (sint (of_bool (bit (x + t) (nat n)) * not (mask (nat n))::'a::len word)))"
  using signed_take_bit_eq[of "nat n" "x+t"] a00 by simp
then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t))) (sint (of_bool (bit (x + t) (nat n)) * not (mask (nat n))::'a::len word)))"
  using sint_word_ariths(1) by metis
then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t))) (sint ((if (bit (x + t) (nat n)) then 1 else 0) * not (mask (nat n))::'a::len word)))"
  using of_bool_def by simp
then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t)))
       (signed_take_bit (LENGTH('a) - 1) (sint (if (bit (x + t) (nat n)) then 1 else 0::'a::len word) * sint (not (mask (nat n))::'a::len word))))"
  by (simp add: sint_word_ariths(3))
then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t)))
       (signed_take_bit (LENGTH('a) - 1) ( (if (bit (x + t) (nat n)) then sint (1::'a::len word) else sint (0::'a::len word)) * sint (not (mask (nat n))::'a::len word))))"
  by simp
  moreover have "sint (1::'a::len word) = (1::int)"
    using a01 by fastforce
  moreover have "sint (0::'a::len word) = (0::int)"
    by simp
  ultimately have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t)))
       (signed_take_bit (LENGTH('a) - 1) ((if (bit (x + t) (nat n)) then 1 else 0) * sint (not (mask (nat n))::'a::len word))))"
    by presburger
then have "sint (signed_take_bit (nat n) (x + t)) =
   (or (take_bit (nat n) (signed_take_bit (LENGTH('a) - 1) (sint x + sint t)))
       (signed_take_bit (LENGTH('a) - 1) ((if (bit (x + t) (nat n)) then 1 else 0)
   * signed_take_bit LENGTH('a::len) (not (signed (mask (nat n)::'a::len word))))))"
  using signed_not_eq[of "mask (nat n)"] by metis
  then show ?thesis 
    by blast
qed

  show " signed_take_bit (nat n) (x + t) * signed_take_bit (nat m) a <s signed_take_bit (nat n) x * signed_take_bit (nat m) a"
    apply (simp add: word_sless_alt)
    apply (simp add: sint_word_ariths(3))
    apply (simp add: t0 t1)
    apply (cases "bit (x + t) (nat n)")
    apply (case_tac "bit x (nat n)")
      apply simp_all
    unfolding take_bit_eq_mod bit_or_iff
    apply simp
qed



*)
>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)

named_theorems rewrite_bv_mult_slt_mult_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_mult_slt_mult_2]:
  fixes x::"'a ::len word" and t::"'a ::len word" and a::"'a ::len word" and n::"int" and m::"int"
  shows "(push_bit (nat n) (x + t) * signed_take_bit (nat m) a
    <s push_bit (nat n) x * signed_take_bit (nat m) a) =
   (t \<noteq> Word.Word 0 \<and>
    a \<noteq> Word.Word 0 \<and> (x + t < x) = (Word.Word 0 <s a))"
  sorry

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

<<<<<<< HEAD

=======
(*
>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)
named_theorems rewrite_bv_or_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_or_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len  word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "cvc_list_right or (cvc_list_left or xs (cvc_list_right or s ys)) zs =
   cvc_list_right or (cvc_list_right or (cvc_list_left or xs s) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (induction zss arbitrary: zs)
      apply simp_all
    sorry
    done

<<<<<<< HEAD
=======
  done*)
(*
>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)

named_theorems rewrite_bv_xor_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_xor_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "cvc_list_right semiring_bit_operations_class.xor
    (cvc_list_left semiring_bit_operations_class.xor xs
      (cvc_list_right semiring_bit_operations_class.xor s ys))
    zs =
   cvc_list_right semiring_bit_operations_class.xor
    (cvc_list_right semiring_bit_operations_class.xor
      (cvc_list_left semiring_bit_operations_class.xor xs s) ys)
    zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    apply (induction yss arbitrary: ys)
     apply simp_all
    apply (induction xss arbitrary: xs)
     apply simp_all
    apply (induction zss arbitrary: zs)
     apply simp_all
     apply (metis (no_types, opaque_lifting) bit.xor_left_self word_bw_assocs(3))
    unfolding bit_xor_iff
    sorry
  done
<<<<<<< HEAD


=======
*)
(*
>>>>>>> de9dcaa151 (Restructuring and proofing additional lemmas)
named_theorems rewrite_bv_and_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_and_flatten]:
  fixes xs::"'a::len word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len  word cvc_ListVar"
  shows "cvc_list_right and (cvc_list_left and xs (cvc_list_right and s ys)) zs =
   cvc_list_right and (cvc_list_right and (cvc_list_left and xs s) ys) zs"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    sorry
  done
*)




named_theorems rewrite_bv_mul_flatten \<open>automatically_generated\<close>

lemma [rewrite_bv_mul_flatten]:
  fixes xs::"'a::len  word cvc_ListVar" and s::"'a::len word" and ys::"'a::len word cvc_ListVar" and zs::"'a::len word cvc_ListVar"
  shows "cvc_list_right (*) (cvc_list_left (*) xs (cvc_list_right (*) s ys)) zs =
   cvc_list_right (*) (cvc_list_right (*) (cvc_list_left (*) xs s) ys) zs"
  apply (cases zs)
  apply (cases ys) 
  apply (cases xs)
  subgoal for zss yss xss 
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
    sorry
  done



end
