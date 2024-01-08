theory BV_Rewrites
  imports BV_Rewrites_Lemmas 
begin

(* This is a theory automatically created from a RARE file! All that remains to do is to prove
any lemma whose provided proof fails and to to import this file in SMT.thy (if you want to use it
for proof reconstruction).*)


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

(*
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
*)
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
lemma [rewrite_bv_shl_by_const_1]:
  fixes x::"'a::len word" and amount::"int" and sz::"int"
  shows "amount < int (size x) \<longrightarrow>
LENGTH('b) = amount \<longrightarrow>
size x - (1 + amount) \<ge> 0 \<longrightarrow>
size x - (1 + amount) < size x \<longrightarrow> 
amount \<ge> 0 \<longrightarrow>
LENGTH('c) = 1 + ((size x - (1 + amount)) - 0) \<longrightarrow>
LENGTH('a) = LENGTH('b) + LENGTH('c) \<longrightarrow>
LENGTH('d) = sz \<longrightarrow>
amount < (2::int) ^ LENGTH('d) \<longrightarrow>
   (push_bit (unat (Word.Word amount::'d::len word)) x ::'a::len word)=
   word_cat
    (smt_extract (nat (int (size x) - ((1::int) + amount)))
      (nat (0::int)) x::'c::len word)
    (Word.Word (0::int)::'b::len word)"
  apply rule+
proof-
  assume a0:
    "amount < int (size x)"
    "int LENGTH('b) = amount"
    "(0::int) \<le> int (size x) - ((1::int) + amount)"
    "int (size x) - ((1::int) + amount) < int (size x)"
    "amount \<ge> 0"
    "int LENGTH('c) = (1::int) + (int (size x) - ((1::int) + amount) - (0::int))"
    "LENGTH('a) = LENGTH('b) + LENGTH('c)"
    "int LENGTH('d) = sz"
    "amount < (2::int) ^ LENGTH('d)"
  have t0: "(nat (int (size x) - ((1::int) + amount))) = (size x - 1 - nat amount::nat)"
    using a0(3) a0(4) by auto
  have t1: "(unat (Word.Word amount::'d::len word)) = nat amount"
    apply simp
    apply (simp add: unsigned_of_int)
    apply (subst take_bit_int_eq_self)
    by (simp_all add: a0)

  have "word_cat
    (smt_extract (nat (int (size x) - ((1::int) + amount)))
      (nat (0::int)) x::'c::len word)
    (Word.Word (0::int)::'b::len word)
  = word_cat (smt_extract (size x - 1 - nat amount) 0 x::'c::len word) (0::'b::len word)"
    using t0 by simp
  also have "...
  = word_cat (slice (0::nat) (take_bit (Suc (size x - (1::nat) - nat amount)) x::'a::len word)::'c::len word) (0::'b ::len word)"
    unfolding smt_extract_def by simp
  also have "...
  = word_cat (slice (0::nat) (take_bit (size x - nat amount) x::'a::len word)::'c::len word) (0::'b ::len word)"
    using Suc_diff_Suc a0(1) a0(4) by force
 also have "...
  = word_cat (ucast (take_bit (size x - nat amount) x::'a::len word)::'c::len word) (0::'b ::len word)"
   by (simp add: ucast_slice)
   also have "...
  =  push_bit LENGTH('b::len) (ucast (ucast (take_bit (size x - nat amount) x::'a::len word)::'c::len word)::'a::len word) + (ucast (0::'b::len word)::'a::len word)"
     using word_cat_eq[of "(ucast (take_bit (size x - nat amount) x::'a::len word)::'c::len word)" "(0::'b ::len word)"]
     by simp
 also have "...
  =  push_bit LENGTH('b::len) (ucast (ucast (take_bit (size x - nat amount) x::'a::len word)::'c::len word)::'a::len word)"
   by auto
 also have "...
  =  push_bit (unat (Word.Word amount::'d::len word)) (ucast (ucast (take_bit (size x - nat amount) x::'a::len word)::'c::len word)::'a::len word)"
   using t1 a0(2) by force
 also have "...
  =  push_bit (unat (Word.Word amount::'d::len word)) (take_bit LENGTH('c::len) (unsigned (take_bit (size x - nat amount) x::'a::len word)::'a::len word))"
   apply (subst unsigned_ucast_eq[of "(take_bit (size x - nat amount) x::'a::len word)"])
   by simp
also have "...
  =  push_bit (unat (Word.Word amount::'d::len word)) (take_bit LENGTH('c::len) (take_bit (size x - nat amount) (unsigned x::'a::len word)))"
  by (simp add: unsigned_take_bit_eq)
also have "...
  =  (push_bit (unat (Word.Word amount::'d::len word)) (take_bit (size x - nat amount) (unsigned x::'a::len word))::'a::len word)"
  using take_bit_take_bit
  by (metis a0(2) a0(5) a0(7) nat_eq_iff2 push_bit_take_bit t1 take_bit_length_eq)
also have "...
  =  (push_bit (unat (Word.Word amount::'d::len word)) x::'a::len word)"
  by (metis t1 take_bit_length_eq take_bit_push_bit ucast_id word_size)

  finally  show "(push_bit (unat (Word.Word amount::'d::len word)) x ::'a::len word)=
   word_cat
    (smt_extract (nat (int (size x) - ((1::int) + amount)))
      (nat (0::int)) x::'c::len word)
    (Word.Word (0::int)::'b::len word)"
    by presburger
qed


named_theorems rewrite_bv_shl_by_const_2 \<open>automatically_generated\<close>

lemma [rewrite_bv_shl_by_const_2]:
  fixes x::"'a ::len word" and amount::"int" and sz::"int"
  shows "int (size x) \<le> amount \<longrightarrow> LENGTH('b) = sz \<longrightarrow> amount < 2^LENGTH('b) \<longrightarrow>
   push_bit (unat (Word.Word amount::'b::len word)) x = (Word.Word (0::int)::'a::len word)"
  by (simp add: take_bit_int_eq_self unsigned_of_int word_size)

named_theorems rewrite_bv_lshr_by_const_0 \<open>automatically_generated\<close>

lemma [rewrite_bv_lshr_by_const_0]:
  fixes x::"'a ::len word"  and sz::"int"
  shows "LENGTH('b) = sz \<longrightarrow>
   drop_bit (unat (Word.Word 0::'b::len word)) x = x"
  by force
(*
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
proof-
  assume a0: "amount < int (size x)"
    "LENGTH('a) = LENGTH('b) + LENGTH('c)"
    "nat (int (size x) - (1::int)) < LENGTH('a)"
    "(0::int) \<le> amount"
    "nat amount \<le> nat (int (size x) - (1::int))"
    "LENGTH('c) = (1::nat) + (nat (int (size x) - (1::int)) - nat amount)"
    "amount < (2::int) ^ LENGTH('d)"
    "int LENGTH('d) = sz"
  have t0: "min (LENGTH('c::len) + nat amount) LENGTH('a) = LENGTH('a)"
    by (smt (verit, ccfv_SIG) a0(5) a0(6) add_diff_cancel_left' diff_add diff_diff_left less_le_not_le min.commute min.idem min.order_iff nat_minus_as_int nat_neq_iff of_nat_1 word_size)
   have t1: "(take_bit LENGTH('d) amount) = amount"
    apply (subst take_bit_int_eq_self[of amount "LENGTH('d)" ])
    apply (simp add: a0)
    using a0(7) apply auto[1]
    by auto

  have "(word_cat (Word.Word (0::int)::'b::len word)
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x::'c::len word)::'a::len word)
  = word_cat (0::'b::len word)
    (smt_extract (size x - 1) (nat amount) x::'c::len word)"
    by (metis nat_minus_as_int of_nat_1 zero_word_def)
  also have "...
  = word_cat (0::'b word) (slice (nat amount) (take_bit (size x) x)::'c::len word)"
    unfolding smt_extract_def
    by simp
  also have "...
  = word_cat (0::'b word) (slice (nat amount) x::'c::len word)"
    using take_bit_length_eq
    by (simp add: word_size)
  also have "...
  = word_cat (0::'b word) (slice1 (LENGTH('a::len) - nat amount) x::'c::len word)"
    using slice_def[of "nat amount"]
    by (simp add: slice_def)
 also have "...
  = word_cat (0::'b word) (ucast (drop_bit (LENGTH('a::len) - (LENGTH('a::len) - nat amount)) x)::'c::len word)"
   using slice1_def[of "(LENGTH('a::len) - nat amount)" x]
   by (smt (verit, del_insts) One_nat_def Suc_diff_1 a0(2) a0(5) a0(6) diff_add_inverse diff_less_mono2 len_gt_0 nat_diff_distrib' nat_int nat_one_as_int of_nat_0_le_iff ordered_cancel_comm_monoid_diff_class.add_diff_assoc plus_1_eq_Suc size_word.rep_eq)
 also have "...
  = word_cat (0::'b word) (ucast (drop_bit (nat amount) x)::'c::len word)"
   by (metis a0(1) diff_diff_cancel less_le_not_le nat_le_iff word_size)
 also have "...
  =  push_bit LENGTH('c::len) (ucast (0::'b word)) + ucast (ucast (drop_bit (nat amount) x)::'c::len word)"
   using word_cat_eq
   by blast
also have "...
  =  push_bit LENGTH('c::len) 0 + ucast (ucast (drop_bit (nat amount) x)::'c::len word)"
  using unsigned_ucast_eq[of "(drop_bit (nat amount) x)"]
  by auto
also have "...
  = ucast (ucast (drop_bit (nat amount) x)::'c::len word)"
  by simp
also have "...
  = (take_bit LENGTH('c::len) (unsigned (drop_bit (nat amount) x)::'a::len word))"
  using unsigned_ucast_eq[of "(drop_bit (nat amount) x)"]
  by (smt (verit, del_insts))
also have "...
  = (take_bit LENGTH('c::len) (drop_bit (nat amount) (take_bit LENGTH('a::len) (unsigned x))))"
  using unsigned_drop_bit_eq[of "nat amount" x] by simp
also have "...
  = drop_bit (nat amount) (take_bit (LENGTH('c::len) + nat amount) (take_bit LENGTH('a::len) (unsigned x)))"
  using take_bit_drop_bit[of "LENGTH('c)" "nat amount" "(take_bit LENGTH('a::len) (unsigned x))"]
  by blast
also have "...
  = drop_bit (nat amount) (take_bit LENGTH('a::len) (unsigned x))"
  using take_bit_take_bit
  by (smt (verit, ccfv_threshold) One_nat_def Suc_pred a0(5) a0(6) diff_add group_cancel.add1 int_ops(2) len_gt_0 nat_int_comparison(3) nat_minus_as_int plus_1_eq_Suc size_word.rep_eq take_bit_word_beyond_length_eq)
also have "...
  = drop_bit (nat amount) (unsigned x)"
  by force
  finally have "(word_cat (Word.Word (0::int)::'b::len word)
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x::'c::len word)::'a::len word)
  = drop_bit (nat amount) (unsigned x)"
    by blast

    then show "(drop_bit (unat (Word.Word amount::'d::len word)) x::'a::len word) =
   word_cat (Word.Word (0::int)::'b::len word)
    (smt_extract (nat (int (size x) - (1::int))) (nat amount) x::'c::len word)"
            by (simp add: a0(4) a0(7) unat_eq_nat_uint word_of_int_inverse)
        qed

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
    by (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer_op)
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
*)

end