theory SMT_Word
  imports "HOL-Library.Word" Word_Lib.More_Word "HOL-Library.Log_Nat"
   "Word_Lib.Reversed_Bit_Lists" Dsl_Nary_Ops "Alethe_BV_Reconstruction"
begin
(*Erstmal diese Theory Afp abhaengig sein
Soll zweiten bv_term_parser enthalten, der alle cvc5 bv definitionen enthaelt

BV_Rewrite muss hiervon erben

SMT.thy  

*)

declare  [[smt_cvc_lethe = true]]

subsection \<open>Tool support\<close>

(*imported from various places*)

(*IEEE_Float_Extend_Integer*)
lemma nat_add_offset_less:
  fixes x :: nat
  assumes yv: "y < 2 ^ n"
  and     xv: "x < 2 ^ m"
  and     mn: "sz = m + n"
  shows   "x * 2 ^ n + y < 2 ^ sz"
proof (subst mn)
  from yv obtain qy where "y + qy = 2 ^ n" and "0 < qy"
    by (auto dest: less_imp_add_positive)

  have "x * 2 ^ n + y < x * 2 ^ n + 2 ^ n" by simp fact+
  also have "\<dots> = (x + 1) * 2 ^ n" by simp
  also have "\<dots> \<le> 2 ^ (m + n)" using xv
    by (subst power_add) (rule mult_le_mono1, simp)
  finally show "x * 2 ^ n + y < 2 ^ (m + n)" .
qed

lemma nat_bit_shift_add_bound:
  fixes e f :: nat
  assumes LF: "f<2^F"
      and LE: "e<2^E"
  shows "f+e*2^F < 2^(E+F)"
proof -
  from LE have "e \<le> 2^E - 1" by simp
  hence "e*2^F \<le> (2^E - 1) * 2^F" by simp
  also have "\<dots> = 2^(E+F) - 2^F" by (simp add: power_add algebra_simps)
  finally have "e * 2 ^ F \<le> 2 ^ (E + F) - 2 ^ F" .
  thus ?thesis using LF
    by (metis LE add.commute nat_add_offset_less)
qed

lemma int_bit_shift_add_bound:
  fixes e f :: int
  assumes LF: "f<2^F"
      and LE: "e<2^E"
  shows "f+e*2^F < 2^(E+F)"
proof -
  from LE have "e \<le> 2^E - 1" by simp
  hence "e*2^F \<le> (2^E - 1) * 2^F" by simp
  also have "\<dots> = 2^(E+F) - 2^F" by (simp add: power_add algebra_simps)
  finally have "e * 2 ^ F \<le> 2 ^ (E + F) - 2 ^ F" .
  thus ?thesis using LF by linarith
qed
  
lemma uint_bit_shift_add_bound:
  fixes f :: "'f::len word"
    and e :: "'e::len word"
  shows "uint (f) + uint (e) * 2 ^ LENGTH('f) < 2^(LENGTH('e) + LENGTH('f))"
  apply (rule int_bit_shift_add_bound)
  by auto

lemma unat_bit_shift_add_bound:
  fixes f :: "'f::len word"
    and e :: "'e::len word"
  shows "unat (f) + unat (e) * 2 ^ LENGTH('f) < 2^(LENGTH('e) + LENGTH('f))"
  apply (rule nat_bit_shift_add_bound)
  by auto

lemma unat_pow_le_intro:
  "LENGTH('a) \<le> n \<Longrightarrow> unat (x :: 'a :: len word) < 2 ^ n"
  by (metis lt2p_lem not_le of_nat_le_iff of_nat_numeral semiring_1_class.of_nat_power uint_nat)

lemma unat_word_cat_eq:
  fixes w\<^sub>1 :: "'l\<^sub>1::len word"
  fixes w\<^sub>2 :: "'l\<^sub>2::len word"
  assumes "LENGTH('l\<^sub>1) + LENGTH('l\<^sub>2) \<le> LENGTH('l\<^sub>3)"
  shows "unat (word_cat w\<^sub>1 w\<^sub>2 :: 'l\<^sub>3::len word) = unat w\<^sub>2 + unat w\<^sub>1 * 2^LENGTH('l\<^sub>2)"  
proof -
  have [simp]: "LENGTH('l\<^sub>2) < LENGTH('l\<^sub>3)"
    using assms 
    by (metis add_diff_cancel_right' add_leD2 diff_is_0_eq' le_neq_implies_less len_not_eq_0)
  then have B2: "unat w\<^sub>2 + unat w\<^sub>1 * unat ((2::'l\<^sub>3 word) ^ LENGTH('l\<^sub>2)) < 2 ^ LENGTH('l\<^sub>3)"
    apply simp
    apply (rule order.strict_trans2[OF unat_bit_shift_add_bound])
    using assms by simp
  have B1: "unat w\<^sub>1 * unat ((2::'l\<^sub>3 word) ^ LENGTH('l\<^sub>2)) < 2 ^ LENGTH('l\<^sub>3)" 
    using B2 by linarith
          
  show ?thesis  
    apply (simp add: word_cat_eq' concat_bit_eq take_bit_eq_mod push_bit_eq_mult)
    apply (simp add: unat_word_ariths unat_ucast_upcast B1 B2)
    by (metis B2 \<open>LENGTH('l\<^sub>2) < LENGTH('l\<^sub>3)\<close> add.commute add_leD2 add_lessD1 assms nat_mod_eq'
        unat_pow_le_intro unat_power_lower unat_ucast)
qed

(*end of stolen*)

(* SMT-LIB bit-vector definitions *)

definition smt_extract :: "nat \<Rightarrow> nat \<Rightarrow> 'a ::len word \<Rightarrow> 'b::len word" where
  \<open>smt_extract j i w = slice i (take_bit (Suc j) w)\<close>


value "smt_extract (7) 1 (1::4 word)::1 word"
value "slice 3 (4::8 word)::8 word"

lemma "i+1-j < LENGTH('a) \<Longrightarrow> size (smt_extract j i w::'a::len word) = i+1-j"
  oops

lemma unat_smt_extract:
  fixes x::"'a::len word"
  shows  "i \<le> j \<Longrightarrow> j < size x \<Longrightarrow> LENGTH('b) = j + 1 - i
 \<Longrightarrow> unat ((smt_extract j i (x::'a::len word))::'b::len word)
   = drop_bit i (take_bit (Suc j) (unat x))"
  apply (cases "i=0")
proof-
  assume a0: "i = (0::nat)" and a1: "i \<le> j" "j < size x" "LENGTH('b) = j + 1 - i"
  then have t0: "LENGTH('b) \<le> LENGTH('a)"
    by (simp add: size_word.rep_eq)
  have "unat (smt_extract j i x::'b::len word) = unat (ucast (take_bit (Suc j) x ::'a::len word)::'b::len word)"
   unfolding smt_extract_def slice_def slice1_def
   by (simp add: a0)
  also have "... = unat (take_bit (Suc j) x ::'a::len word)"
    by (simp add: a1 a0 unsigned_take_bit_eq unsigned_ucast_eq)
  also have "... = take_bit (Suc j) (unsigned x)" 
    using Word.semiring_bit_operations_class.unsigned_take_bit_eq
    by auto
  finally show "unat ((smt_extract j i (x::'a::len word))::'b::len word) = drop_bit i (take_bit (Suc j) (unat x))"
    using a0 by force
next
  assume a0: "i \<noteq> (0::nat)" and a1: "i \<le> j" "j < size x" "LENGTH('b) = j + 1 - i"
  then have t0: "LENGTH('b) \<le> LENGTH('a)"
    by (metis Suc_eq_plus1 Suc_leI diff_le_self le_trans size_word.rep_eq)
  have t1: "i < LENGTH('a)"
    by (metis a1(1,2) dual_order.strict_trans2 size_word.rep_eq)
  have "unat (smt_extract j i x::'b::len word) = unat (ucast (drop_bit i (take_bit (Suc j) x))::'b::len word)"
    unfolding smt_extract_def slice_def slice1_def
    using a0 t1 by force
  also have "... = unat (drop_bit i (take_bit (Suc j) x))"
    by (metis (no_types, lifting) Suc_eq_plus1 a1(3) drop_bit_take_bit min.idem take_bit_take_bit unsigned_take_bit_eq unsigned_ucast_eq)
  also have "... = drop_bit i (unsigned (take_bit (Suc j) x))" 
    using unat_drop_bit_eq by blast
  also have "... = drop_bit i (take_bit (Suc j) (unsigned x))" 
    by (simp add: unsigned_take_bit_eq)
  finally show "unat ((smt_extract j i (x::'a::len word))::'b::len word) = drop_bit i (take_bit (Suc j) (unat x))"
    by simp
qed

lemma uint_smt_extract:
  fixes x::"'a::len word"
  shows  "i \<le> j \<Longrightarrow> j < size x \<Longrightarrow> LENGTH('b) = j + 1 - i
 \<Longrightarrow> uint ((smt_extract j i (x::'a::len word))::'b::len word)
   = drop_bit i (take_bit (Suc j) (unsigned x))"
  apply (subst uint_nat)
  apply (simp add: unat_smt_extract)
  by (metis Word.of_nat_unat of_nat_drop_bit take_bit_of_nat)

lemma sint_smt_extract:
  fixes x::"'a::len word"
  shows  "i \<le> j \<and> j < size x \<and> LENGTH('b) = j + 1 - i
 \<Longrightarrow> sint ((smt_extract j i (x::'a::len word))::'b::len word)
= signed_take_bit (LENGTH('b::len) - Suc (0::nat)) (drop_bit i (take_bit (Suc j) (unsigned x)))"
  apply (subst sint_uint)
  by (simp add: uint_smt_extract)

lemma smt_extract_bit: "k < size (x::'a::len word) \<Longrightarrow> (smt_extract k k x::1 word) = (if bit x k then 1 else 0)" 
  apply (simp add: bang_eq)
  unfolding smt_extract_def
  apply (simp_all add: nth_slice bit_take_bit_iff)
  by (metis add_0 bot_nat_0.not_eq_extremum)

lemma bit_smt_extract: "bit (smt_extract j i x::'b::len word) n = ((n + i < Suc j \<and> bit x (n + i)) \<and> n < LENGTH('b::len))"
  unfolding smt_extract_def
  using nth_slice[of i "(take_bit (Suc j) x)" n, where 'a="'b"] bit_take_bit_iff[of "Suc j" x "n+i"]
  by simp

definition replicate_nat :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat\<close> where
 \<open>replicate_nat i s = (\<Sum>k=0..(i-1). 2^(s*k))\<close>

lemma replicate_nat_Suc[simp]:
  \<open>i > 0 \<Longrightarrow> replicate_nat (Suc i) s = replicate_nat i s + (2::nat) ^ (i*s)\<close>
  by (cases i) (auto simp: replicate_nat_def)

definition word_repeat :: \<open>nat \<Rightarrow> 'a :: len word \<Rightarrow> 'b :: len word\<close> where
 \<open>word_repeat i n = (THE x :: 'b::len word. LENGTH('b) = i * size n \<and> unat x = replicate_nat i (size n) * (unat n))\<close>

lemma ex_unat_nat: "n < 2^ (LENGTH('a)) \<Longrightarrow> \<exists>x :: 'a:: len word. unat x = n"
  using of_nat_inverse by blast

lemma replicate_nat_le: \<open>i \<ge> 1 \<Longrightarrow> replicate_nat i (size n) * unat n < 2 ^ (i * size n)\<close>
  apply (induction i)
  subgoal by auto
  subgoal for i
    apply (cases i)
    apply (auto simp: replicate_nat_def)
    apply (simp add: wsst_TYs(3))
    by (simp add: distrib_left mult.commute nat_bit_shift_add_bound wsst_TYs(3))
  done

lemma word_repeat_unique:
  \<open>LENGTH('b) = i * size n \<and> unat a = replicate_nat i (size n) * unat n \<Longrightarrow>
  LENGTH('b::len) = i * size n \<and> unat x = replicate_nat i (size n) * unat n \<Longrightarrow>
  x = a\<close>
  using word_eq_iff_unsigned
  by metis

lemma ex_word_repeat:
  fixes n :: \<open>'a :: len word\<close>
  assumes \<open>LENGTH('b) = i * size n\<close> "i \<ge> 1" 
  shows \<open>\<exists>x::'b::len word. unat x = replicate_nat i (size n) * (unat n)\<close>
  using assms apply -
  by (rule ex_unat_nat) (auto intro: replicate_nat_le)

lemma word_repeat_prop:
  \<open>i\<ge>1 \<Longrightarrow> LENGTH('b) = i * size n \<Longrightarrow> unat ((word_repeat i n) :: 'b :: len word) = replicate_nat i (size n) * (unat n)\<close>
  using ex_word_repeat[of i n, where 'b='b]
    theI[where P = \<open>\<lambda>x :: 'b::len word. LENGTH('b) = i * size n \<and> unat x = replicate_nat i (size n) * (unat n)\<close>,
    unfolded word_repeat_def[symmetric]]
    word_repeat_unique[where 'b='b]
  by fast

lemma word_repeat_alt_def:
  assumes \<open>LENGTH('b) = i * size n\<close> \<open>i \<ge> 1\<close>
  shows \<open>word_repeat i n = (a::'b ::len word) \<longleftrightarrow> (unat a = replicate_nat i (size n) * unat n)\<close>
proof -
  have \<open>LENGTH('b) = i * size n \<Longrightarrow> i \<ge> 1 \<Longrightarrow>  word_repeat i n = (a::'b ::len word) \<longleftrightarrow> (LENGTH('b) = i * size n \<and> unat a = replicate_nat i (size n) * unat n)\<close>
    apply (subst eq_commute[of _ a])
    apply (subst theI_unique[where P = \<open>\<lambda>x :: 'b::len word. LENGTH('b) = i * size n \<and> unat x = replicate_nat i (size n) * (unat n)\<close>,
      unfolded word_repeat_def[symmetric], of a])
    subgoal
      apply (subst Ex1_def)
      using
        ex_word_repeat[of i n, where 'b='b]
        word_repeat_unique[of i n, where 'b='b]
      by blast
    subgoal by auto
    done
  then show ?thesis
    using assms by fast
qed

lemma word_repeat_word_cat:
  fixes n :: "'a :: len word"
  assumes \<open>LENGTH('b::len) = Suc i * size n\<close> \<open>i > 0\<close>
    \<open>LENGTH('c::len) = i * size n\<close>
  shows \<open>(word_repeat (Suc i) n :: 'b word) = word_cat (n :: 'a word) (word_repeat i n :: 'c word)\<close>
  supply [[show_sorts,show_types]]
  apply (subst word_repeat_alt_def)
  subgoal using assms by auto
  subgoal by auto
    apply (subst unat_word_cat_eq)
    subgoal using assms by (auto simp: word_size)
    apply (subst word_repeat_prop)
    subgoal using assms by auto
    subgoal using assms by auto
      apply (subst replicate_nat_Suc)
    subgoal using assms by auto
    subgoal using assms by (auto simp: algebra_simps word_size)
    done

definition smt_repeat :: "nat \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word" where
  \<open>smt_repeat i x = (if i = 0 then (ucast x::'b::len word) else word_repeat i x)\<close>

lemma smt_repeat_zeros: "n = LENGTH('a) \<Longrightarrow> n > 0 \<Longrightarrow> (smt_repeat n (0::1 word)::'a::len word) = 0"
  unfolding smt_repeat_def
  unfolding word_repeat_def
  apply simp
  by (metis (mono_tags, lifting) One_nat_def ex_unat_nat len_num1 less_2_cases_iff less_numeral_extra(3) nat_zero_less_power_iff size_word.rep_eq the_equality unat_gt_0)

lemma smt_repeat_ones_mask: "n = LENGTH('a) \<Longrightarrow> n > 0 \<Longrightarrow> (smt_repeat n (1::1 word)::'a::len word) = mask (Suc n)"
  unfolding smt_repeat_def
  unfolding word_repeat_def
  apply simp
proof
  show "n = LENGTH('a) \<Longrightarrow> Suc (0::nat) = size (1::1 word) \<and> unat (mask (Suc LENGTH('a))::'a word) = replicate_nat LENGTH('a) (size (1::1 word))"
    unfolding replicate_nat_def mask_eq_exp_minus_1
    apply simp
    apply (rule conjI)
    apply (simp add: size_word.rep_eq)
    apply (simp add: unat_minus_one_word)
    apply (simp add: size_word.rep_eq)
    by (metis Suc_pred atLeast0AtMost bot_nat_0.not_eq_extremum len_not_eq_0 lessThan_Suc_atMost lessThan_def mask_eq_sum_exp_nat)
next
  show "\<And>x::'a word. n = LENGTH('a) \<Longrightarrow>
       Suc (0::nat) = size (1::1 word) \<and> unat x = replicate_nat LENGTH('a) (size (1::1 word)) \<Longrightarrow> x = mask (Suc LENGTH('a))"
    subgoal for x
      unfolding replicate_nat_def mask_eq_exp_minus_1
      apply simp
    apply (simp add: size_word.rep_eq)
      by (metis One_nat_def Suc_pred' atLeast0AtMost len_gt_0 lessThan_Suc_atMost lessThan_def mask_eq_sum_exp_nat unat_minus_one_word word_unat_eq_iff)
  done
qed

definition smt_comp :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 1 word" where
  \<open>smt_comp x y = (if (x = y) then 1 else 0)\<close>

lemma smt_comp_cast_0 [simp]:
  assumes "x = y"
  shows "unat (smt_comp x y) = 1"
        "uint (smt_comp x y) = 1"
        "sint (smt_comp x y) = -1"
  by (simp_all add: smt_comp_def assms)

lemma smt_comp_cast_1 [simp]:
  assumes "x \<noteq> y"
  shows "unat (smt_comp x y) = 0"
        "uint (smt_comp x y) = 0"
        "sint (smt_comp x y) = 0"
  by (simp_all add: smt_comp_def assms)

definition smt_redor :: "'a::len word \<Rightarrow> 1 word" where
  \<open>smt_redor x = not (smt_comp x 0)\<close>

lemma smt_redor_cast_0 [simp]:
  assumes "x = 0"
  shows "unat (smt_redor x) = 0"
        "uint (smt_redor x) = 0"
        "sint (smt_redor x) = 0"
  by (simp_all add: smt_redor_def smt_comp_def assms)

lemma smt_redor_cast_1 [simp]:
  assumes "x \<noteq> 0"
  shows "unat (smt_redor x) = 1"
        "uint (smt_redor x) = 1"
        "sint (smt_redor x) = -1"
    apply (simp_all add: smt_redor_def smt_comp_def assms)
  by (simp_all add: unsigned_minus_1_eq_mask)

definition smt_redand :: "'a::len word \<Rightarrow> 1 word" where
  \<open>smt_redand x = smt_comp x (not (0::'a word))\<close>

lemma smt_redand_cast_0 [simp]:
  assumes "x \<noteq> -1"
  shows "unat (smt_redand x) = 0"
        "uint (smt_redand x) = 0"
        "sint (smt_redand x) = 0"
  by (simp_all add: smt_redand_def smt_comp_def assms)

lemma smt_redand_cast_1 [simp]:
  assumes "x = -1"
  shows "unat (smt_redand x) = 1"  
        "uint (smt_redand x) = 1"
        "sint (smt_redand x) = -1"
  by (simp_all add: smt_redand_def smt_comp_def assms)

(*'c is 'a + 1*)
definition smt_uaddo :: "'c::len itself \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word \<Rightarrow> bool" where
"smt_uaddo TYPE('c) x y = (smt_extract (size x - 1) (size x - 1)
 ((Word.word_cat (0::1 word) x) + (Word.word_cat (0::1 word) y) :: 'c::len word) = (1:: 1 word))"

definition smt_saddo :: "'a::len itself \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word \<Rightarrow> bool" where
"smt_saddo TYPE('a) x y = 
(let sign0=smt_extract (size x - 1) (size x - 1) x in
 let sign1=smt_extract (size x - 1) (size x - 1) y in
 let signa=smt_extract (size x - 1) (size x - 1) (x+y) in
 let both_neg=((sign0 = (1::1 word)) \<and> (sign1 = (1::1 word))) in
 let both_pos=((sign0 = (0::1 word)) \<and> (sign1 = (0::1 word))) in
 let result_neg=(signa = (1::1 word)) in
 let result_pos=(signa = (0::1 word)) in 
((both_neg \<and> result_pos) \<or> (both_pos \<and> result_neg))
)"

definition smt_sdivo :: "'c::len itself \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word \<Rightarrow> bool" where
"smt_sdivo TYPE('c) x y = (x = (word_cat (1::1 word) (0::'c::len word)::'a word) \<and> y = (mask (size y)::'b word))"

definition smt_usubo :: "'c::len itself \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word \<Rightarrow> bool" where
"smt_usubo TYPE('c) x y = ((smt_extract ((size x)-1) ((size y)-1) ((Word.cast x::'c::len word) - Word.cast y)) = (1::1 word))"

definition smt_ssubo :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> bool" where
"smt_ssubo x y = 
(let sign0=smt_extract (size x - 1) (size x - 1) x in
 let sign1=smt_extract (size x - 1) (size x - 1) y in
 let signs=smt_extract (size x - 1) (size x - 1) (x-y) in
 let neg_pos=((sign0 = (1::1 word)) \<and> (sign1 = (0::1 word))) in
 let pos_neg=((sign0 = (0::1 word)) \<and> (sign1 = (1::1 word))) in
 let result_neg=(signs = (1::1 word)) in
 let result_pos=(signs = (0::1 word)) in 
((neg_pos \<and> result_pos) \<or> (pos_neg \<and> result_neg))
)"

definition smt_urem :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
"smt_urem s t = (if (unat s = 0) then s else of_nat ((unat s) mod (unat t)))"

lemma uint_smt_urem:
 "uint (smt_urem s t) = (if (s = 0) then (uint s) else int ((unat s) mod (unat t)))"
 "unat (smt_urem s t) = (if (s = 0) then (unat s) else ((unat s) mod (unat t)))"
  unfolding smt_urem_def
  apply (case_tac "s=0")
    apply simp_all
   apply (metis Word.of_nat_unat semiring_1_class.of_nat_0 uint_mod_distrib word_arith_nat_mod zmod_int)
  by (metis unat_mod word_arith_nat_mod)

(* Should be done with bit instead of extract? *)
definition smt_smod :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
"smt_smod s t =
(let size_s = size s in
(let msb_s = smt_extract (size_s-1) (size_s-1) s in 
(let msb_t = smt_extract (size_s-1) (size_s-1) t in 
(let abs_s = (if (msb_s = (0::1 word)) then s else -s) in 
(let abs_t = (if (msb_t = (0::1 word)) then t else -t) in 
(let u = (smt_urem abs_s abs_t) in 
(if (u = (0::'a word)) then u
 else if ((msb_s = (0::1 word)) \<and> (msb_t = (0::1 word))) then u
 else if ((msb_s = (1::1 word)) \<and> (msb_t = (0::1 word))) then (-u + t)
 else if ((msb_s = (0::1 word)) \<and> (msb_t = (1::1 word))) then (u + t)
 else -u)))))))
"

definition smt_srem :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
"smt_srem s t =
(let size_s = size s in
(let msb_s = (smt_extract (size_s-1) (size_s-1) s::1 word) in
(let msb_t = (smt_extract (size_s-1) (size_s-1) t::1 word) in 
(if ((msb_s = (0::1 word)) \<and> (msb_t = (0::1 word)))
 then (smt_urem s t)
 else (if ((msb_s = 1) \<and> (msb_t = 0))
 then (- (smt_urem (-s) t))
 else (if ((msb_s = 0) \<and> (msb_t = 1))
 then (smt_urem s (-t))
 else (- (smt_urem (-s) (-t)))
))))))
"

lemma uint_smt_srem:
"uint (smt_srem s t) =
 (if ((smt_extract (size s-1) (size s-1) s = (0::1 word)) \<and> (smt_extract (size s-1) (size s-1) t = (0::1 word)))
 then uint (smt_urem s t)
 else (if ((smt_extract (size s-1) (size s-1) s = (1::1 word)) \<and> (smt_extract (size s-1) (size s-1) t = (0::1 word)))
 then take_bit (size s) (- uint (smt_urem (-s) t))
 else (if ((smt_extract (size s-1) (size s-1) s = (0::1 word)) \<and> (smt_extract (size s-1) (size s-1) t = (1::1 word)))
 then uint (smt_urem s (-t))
 else take_bit (size s) (- uint (smt_urem (-s) (-t)))
)))"
  unfolding smt_srem_def Let_def
  by (simp add: uint_word_arith_bintrs(4) wsst_TYs(3))

definition is_pow2 :: "int \<Rightarrow> bool" where
  \<open>is_pow2 i \<equiv> (i = 0) \<and> (and i (i-1) = 0)\<close>

definition smt_udiv :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
"smt_udiv s t =
(if (unat t) = 0 then (mask (size s)) else s div t)
"


lemma uint_word_rotl_eq:
  \<open>uint (word_rotl n w) = concat_bit (n mod LENGTH('a))
    (drop_bit (LENGTH('a) - n mod LENGTH('a)) (uint w))
    (uint (take_bit (LENGTH('a) - n mod LENGTH('a)) w))\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp add: take_bit_concat_bit_eq)

lemma unat_word_cat: "LENGTH('c) = LENGTH('a) + LENGTH('b) \<Longrightarrow>
  unat (word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
    = push_bit LENGTH('b::len) (unat x) + unat y"
proof-
  assume a0: "LENGTH('c) = LENGTH('a) + LENGTH('b)"
  then have "unat (word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
    = unat ((push_bit LENGTH('b::len) (ucast x::'c::len word)::'c::len word) + (ucast y::'c::len word)::'c::len word)"
    using word_cat_eq[of x y] by metis
  then have "unat (word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
    = ((unat (push_bit LENGTH('b::len) (ucast x::'c::len word)::'c::len word))
    + (unat (ucast y::'c::len word))) mod (2::nat) ^ LENGTH('c::len)"
    using unat_word_ariths(1)[of "(push_bit LENGTH('b::len) (ucast x::'c::len word)::'c::len word)" "(ucast y::'c::len word)"]
    by presburger
  then have "unat (word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
    = ((take_bit LENGTH('c::len) (push_bit LENGTH('b::len) (unsigned (ucast x::'c::len word))))
    + (unat (ucast y::'c::len word))) mod (2::nat) ^ LENGTH('c::len)"
    using unsigned_push_bit_eq[of "LENGTH('b)" "(ucast x::'c::len word)"] by metis
  then have "unat (word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
    = ((take_bit LENGTH('c::len) (push_bit LENGTH('b::len) (unsigned (ucast x::'c::len word))))
    + (take_bit LENGTH('c::len) (unsigned y))) mod (2::nat) ^ LENGTH('c::len)"
    using unsigned_ucast_eq[of y, where 'c="'c"] by metis
  then have "unat (word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
    = ((take_bit LENGTH('c::len) (push_bit LENGTH('b::len) (take_bit LENGTH('c::len) (unsigned x))))
    + (take_bit LENGTH('c::len) (unsigned y))) mod (2::nat) ^ LENGTH('c::len)"
    using unsigned_ucast_eq[of x, where 'c="'c"] by metis
  then have "unat (word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
    = ((take_bit LENGTH('c::len) (take_bit (LENGTH('b::len) + LENGTH('c::len)) (push_bit LENGTH('b::len) (unat x))))
    + (take_bit LENGTH('c::len) (unsigned y))) mod (2::nat) ^ LENGTH('c::len)"
    using push_bit_take_bit[of "LENGTH('b)" "LENGTH('c)" "unat x"]
    by auto
 then have "unat (word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
    = ((take_bit LENGTH('c::len) (push_bit LENGTH('b::len) (unat x)))
    + (take_bit LENGTH('c::len) (unat y))) mod (2::nat) ^ LENGTH('c::len)"
    using take_bit_take_bit[of "LENGTH('c)" "LENGTH('b)" "(push_bit LENGTH('b::len) (unat x))"]
    by simp
 then have "unat (word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
    = take_bit LENGTH('c::len) ((take_bit LENGTH('c::len) (push_bit LENGTH('b::len) (unat x)))
    + (take_bit LENGTH('c::len) (unat y)))"
   using take_bit_nat_def by presburger 
 then have t0: "unat (word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
    = take_bit LENGTH('c::len) ((push_bit LENGTH('b::len) (unat x)) + (unat y))"
   using take_bit_add[of "LENGTH('c)"]
   by auto

  have "(push_bit LENGTH('b::len) (unat x)) < 2 ^ LENGTH('a) * 2 ^ LENGTH('b)"
    unfolding push_bit_eq_mult
    by simp
  moreover have "2 ^ LENGTH('a) * 2 ^ LENGTH('b) = (2::nat) ^ LENGTH('c)"
    by (simp add: a0 power_add)
  ultimately have "(push_bit LENGTH('b::len) (unat x)) < (2::nat) ^ LENGTH('c)"
    by presburger
  moreover have "unat (word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
    = push_bit LENGTH('b::len) (unat x) + unat y"
    using take_bit_nat_eq_self[of "((push_bit LENGTH('b::len) (unat x)) + (unat y))" "LENGTH('c)"]
    using a0 nat_add_offset_less push_bit_nat_def t0 by auto

   then show "unat (word_cat (x::'a::len word) (y::'b::len word)::'c::len word)
    = push_bit LENGTH('b::len) (unat x) + unat y"
   using take_bit_add[of "LENGTH('c)"]
   by auto
qed

lemma uint_word_cat: "LENGTH('c) = LENGTH('a) + LENGTH('b) \<Longrightarrow>
uint (word_cat (x::'a::len word) (y::'b::len word)::'c::len word) =
push_bit LENGTH('b::len) (uint x) + uint y"
  by (metis (mono_tags, lifting) int_plus push_bit_of_nat uint_nat unat_word_cat)


lemma word_cat_on_word_cat:
"LENGTH('a) = size (s::'f1::len word) + size (t::'f2::len word) \<Longrightarrow>
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



fun list_length_0 where
 "list_length_0 xs = (foldr (\<and>) (map (\<lambda>xs'. length xs' > 0) xs) True)"

fun list_length_0' where
 "list_length_0' (ListVar xs) = (foldr (\<and>) (map (\<lambda>xs'. length xs' > 0) xs) True)"

lemma list_length_0_monotone:
"list_length_0 (x#xss) \<Longrightarrow> list_length_0 (xss)"
  apply (induction xss)
  by simp_all

fun concat_smt :: "(bool list) list  \<Rightarrow> 'b::len  word" where
  "concat_smt xss = (THE x :: 'b::len word. length xss > 0 \<and> list_length_0 xss
 \<and> LENGTH('b) = foldr (+) (map length xss) 0 \<and> x = of_bl (foldr (append) xss []))"

lemmas[simp del] = concat_smt.simps

fun concat_smt2 :: "(bool list) cvc_ListVar  \<Rightarrow> 'b::len  word" where
  "concat_smt2 (ListVar xss) = (THE x :: 'b::len word. length xss > 0 \<and> list_length_0 xss
 \<and> LENGTH('b) = foldr (+) (map length xss) 0 \<and> x = of_bl (foldr (append) xss []))"

lemmas[simp del] = concat_smt2.simps


fun temp_sum_length where
"temp_sum_length (ListVar xss) = int (foldr (+) (map length xss) 0)"

value "concat_smt [[False]]:: 1 word"
value "concat_smt [[True],[True,False]]:: 3 word"

(*
value "concat_smt [[True],[True,False]]:: 2 word"
value "concat_smt [[]]:: 2 word"
value "concat_smt [[],[]]:: 2 word"
*)

lemma concat_smt_unique:
  \<open>LENGTH('b) = foldr (+) (map length xss) 0 \<and> a = concat_smt xss \<Longrightarrow>
  LENGTH('b::len) = foldr (+) (map length xss) 0  \<and> x = concat_smt xss \<Longrightarrow>
  x = a\<close>
  using word_eq_iff_unsigned
  by metis

lemma ex_concat_smt:
  fixes n :: \<open>'a :: len word\<close>
  assumes \<open>LENGTH('b) = foldr (+) (map length xss) 0\<close> "xss \<noteq> []" 
  shows \<open>\<exists>x::'b::len word. x = concat_smt xss\<close>
  using assms apply -
  by simp

lemma concat_smt_list:
  shows  "xss \<noteq> [] \<Longrightarrow> length(xs) = LENGTH('c)
           \<Longrightarrow> LENGTH('b) = LENGTH('c) + LENGTH('d)
           \<Longrightarrow> LENGTH('b) = foldr (+) (map length (xs # xss)) 0
           \<Longrightarrow> LENGTH('d) = foldr (+) (map length (xss)) 0 \<Longrightarrow> 
           list_length_0 (xs#xss) \<Longrightarrow> 
          (concat_smt (xs # xss)::'b::len word) = word_cat (of_bl xs::'c::len word) (concat_smt xss::'d::len word) "
proof-
  assume a0: "xss \<noteq> []"
     and a1: "length(xs) = LENGTH('c)"
     and a2: "LENGTH('b) = LENGTH('c) + LENGTH('d)"
     and a3: "LENGTH('b) = foldr (+) (map length (xs # xss)) 0"
     and a4: "LENGTH('d) = foldr (+) (map length xss) (0::nat)"
     and a5: "list_length_0 (xs#xss)"

  have a5b: "list_length_0 (xss)"
    using list_length_0_monotone a5 by simp

  obtain x where t0: "x = (concat_smt (xs # xss)::'b::len word)" by simp (*(THE x :: 'b::len word. length (xs # xss) > 0 \<and> list_length_0 (xs # xss)  \<and> LENGTH('b) = foldr (+) (map length (xs # xss)) 0 \<and> x = of_bl (foldr (append) (xs # xss) []))"*)
  obtain y where t1: "y = (concat_smt xss::'d::len word)" by simp

  have t2: "y = (of_bl (foldr (append) ( xss) [])::'d::len word)"
    using t1 apply simp
    using a0 a4 a5b
    by (simp add: concat_smt.simps)
   have t3: "x = (of_bl (foldr (append) (xs # xss) [])::'b::len word)"
     using t0 a5 a3 by (simp add: concat_smt.simps)


   have t4: "foldr (@) (xss::bool list list) [] \<in> {bl::bool list. length bl = LENGTH('d::len)}"
     apply simp
     apply (simp only: a4)
     apply (induction xss)
     by simp_all

  have "word_cat (of_bl xs::'c::len word) (concat_smt xss::'d::len word) = word_cat (of_bl xs::'c::len word) y"
    using t1 by blast
  then have "word_cat (of_bl xs::'c::len word) (concat_smt xss::'d::len word)
     = of_bl (to_bl (of_bl xs::'c::len word) @ to_bl y)"
    using word_cat_bl[of "(of_bl xs::'c::len word)" "(y::'d::len word)"]
    by metis
  then have "word_cat (of_bl xs::'c::len word) (concat_smt xss::'d::len word)
     = of_bl (xs @ to_bl y)"
    using word_bl.Abs_inverse[of xs]
    using a1 by force
  then have "word_cat (of_bl xs::'c::len word) (concat_smt xss::'d::len word)
     = of_bl (xs @ to_bl (of_bl (foldr (append) xss [])::'d::len word))"
   using t2 by simp
  then have "word_cat (of_bl xs::'c::len word) (concat_smt xss::'d::len word)
     = of_bl (xs @ (foldr (append) xss []))"
    using word_bl.Abs_inverse[of "(foldr (append) xss [])", where 'a='d]
    t4 by simp
  then have "word_cat (of_bl xs::'c::len word) (concat_smt xss::'d::len word)
     = of_bl (foldr (append) (xs#xss) [])"
    by simp
  then have "word_cat (of_bl xs::'c::len word) (concat_smt xss::'d::len word)
     = x"
    using t3 by simp
  then show "(concat_smt (xs # xss)::'b::len word) = word_cat (of_bl xs::'c::len word) (concat_smt xss::'d::len word) "
    using t0 by presburger
qed

(*named_theorems evaluate_bv_cvc5 \<open>Lemmas to resolve evaluate rewrite steps \<close>
named_theorems word_var_rbl_list \<open>Theorems to reconstruct bitblasting of a variable.\<close>

named_theorems bv_reconstruction_const \<open>Theorems to reconstruct bitblasting of a constant.\<close>
named_theorems bv_reconstruction_const_test \<open>Theorems to reconstruct bitblasting of a constant.\<close>

named_theorems word_and_rbl_bvand \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_or_rbl_bvor \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_xor_rbl_bvxor \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_notxor_rbl_bvxnor \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_not_rbl_bvnot \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>

named_theorems word_plus_rbl_bvadd \<open>Theorems to reconstruct bitblasting of a bvadd term.\<close>
named_theorems word_plus_rbl_bvadd_fun \<open>Theorems to reconstruct bitblasting of a bvadd term.\<close>
named_theorems word_plus_rbl_bvadd_fun2 \<open>Theorems to reconstruct bitblasting of a bvadd term.\<close>

named_theorems word_minus_rbl_bvneg \<open>Theorems to reconstruct bitblasting of a bvneg term.\<close>
named_theorems word_minus_rbl_bvneg_fun \<open>Theorems to reconstruct bitblasting of a bvneg term.\<close> (*temp?*)

named_theorems word_mult_rbl_bvmult \<open>Theorems to reconstruct bitblasting of a bvmult term.\<close>
named_theorems word_mult_rbl_bvmult_fun \<open>Theorems to reconstruct bitblasting of a bvmult term.\<close>

named_theorems rbl_bvult_fun \<open>Theorems to reconstruct bitblasting of a bvult term.\<close>
named_theorems word_less_rbl_bvult \<open>Theorems to reconstruct bitblasting of a bvult term.\<close>

named_theorems rbl_bvequal_fun \<open>Theorems to reconstruct bitblasting of a bvequal term.\<close>
named_theorems word_equal_rbl_bvequal \<open>Theorems to reconstruct bitblasting of a bvequal term.\<close>

named_theorems rbl_extract_fun \<open>Theorems to reconstruct bitblasting of a extract term.\<close>
named_theorems rbl_extract \<open>Theorems to reconstruct bitblasting of a extract term.\<close>

named_theorems rbl_concat \<open>Theorems to reconstruct bitblasting of a contract term.\<close>

named_theorems bv_reconstruction_length \<open>Theorems evaluate LENGTH('a) for a concrete length.\<close>
named_theorems bv_reconstruction_lists \<open>Theorems to reconstruct bitvector theorems concerning lists.\<close>
named_theorems bv_reconstruction_list_funs \<open>Theorems to reconstruct bitvector theorems concerning list function, e.g. take.\<close>
*)
named_theorems rbl_xor_temp \<open>xor_def.\<close>
(*TODO: duplicate*)
named_theorems arith_simp_cvc5 \<open>xor_def.\<close>

lemmas [arith_simp_cvc5] = Groups.monoid_mult_class.mult_1_right Nat.mult_Suc_right
                     Nat.mult_0_right Nat.add_Suc_right Groups.monoid_add_class.add.right_neutral
                     Num.numeral_2_eq_2 Nat.One_nat_def Num.numeral_2_eq_2 Nat.One_nat_def
                     Nat.Suc_less_eq Nat.zero_less_Suc minus_nat.diff_0 Nat.diff_Suc_Suc Nat.le0

named_theorems all_simplify_temp \<open>Theorems to reconstruct bitvector theorems concerning list function, e.g. take.\<close>

ML_file\<open>ML/lethe_replay_bv_methods.ML\<close>
ML\<open>

open Word_Lib
open Lethe_Replay_BV_Methods

fun mk_unary n t =
  let val T = fastype_of t
  in Const (n, T --> T) $ t end

val mk_nat = HOLogic.mk_number \<^typ>\<open>nat\<close>

fun mk_lassoc f t ts = fold (fn u1 => fn u2 => f u2 u1) ts t
fun mk_test (t1, t2) = (Const (\<^const_name>\<open>Word.word_cat\<close>, dummyT --> dummyT --> dummyT))  $ t1 $ t2

fun mk_extract i j u =
  let
    val I = HOLogic.mk_number \<^typ>\<open>nat\<close> i
    val J = HOLogic.mk_number \<^typ>\<open>nat\<close> j
val _ = @{print}("first index j",j)
val _ = @{print}("first index J",J)

val _ = @{print}("second index i",i)
val _ = @{print}("second index I",I)

    val T = fastype_of u
    val TU = i - j + 1
          |> Word_Lib.mk_wordT
  in Const (\<^const_name>\<open>SMT_Word.smt_extract\<close>, @{typ nat} --> @{typ nat} --> T --> TU) $ J $ I $ u end;

fun mk_zero_extend i u =
  let
    val T = fastype_of u
    val TU = Word_Lib.mk_wordT i
  in Const (\<^const_name>\<open>Word.cast\<close>, T --> TU) $ u end;

fun mk_scast i u =
  let
    val T = fastype_of u
    val TU = Word_Lib.mk_wordT i
  in Const (\<^const_name>\<open>Word.signed\<close>, T --> TU) $ u end;

fun bv_term_parser (SMTLIB.BVNum (i, base), []) = SOME (HOLogic.mk_number (mk_wordT(base)) i)
  | bv_term_parser (SMTLIB.Sym "bbT", xs) =
        SOME ((Const ("Reversed_Bit_Lists.of_bl", \<^typ>\<open>HOL.bool list\<close> --> mk_wordT(length xs))) 
        $ ((Const (\<^const_name>\<open>List.rev\<close>, \<^typ>\<open>HOL.bool list\<close> -->  \<^typ>\<open>HOL.bool list\<close>)) $ (HOLogic.mk_list \<^typ>\<open>bool\<close> xs)))
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "bitOf", SMTLIB.Num i], [t]) =
      SOME (Const (\<^const_name>\<open>semiring_bits_class.bit\<close>, (fastype_of t) --> HOLogic.natT --> \<^typ>\<open>HOL.bool\<close>)
      $ t $ (HOLogic.mk_nat i))
| bv_term_parser (SMTLIB.S [SMTLIB.Sym "_",SMTLIB.Sym "int2bv", SMTLIB.Num t], xs) = (*TODO*)
(* ("bad SMT term format",
             S [Sym "_", Sym "int2bv",
                Num 32]*)
let
(*val _ = @{print}("FOUND")
val _ = @{print}("bv_term_parser int2bv ",xs)*)
(*[Const ("Groups.uminus_class.uminus", "int \<Rightarrow> int") $
    (Const ("Groups.uminus_class.uminus", "int \<Rightarrow> int") $
      (Const ("Num.numeral_class.numeral", "num \<Rightarrow> int") $
        (Const ("Num.num.Bit0", "num \<Rightarrow> num") $
          (Const ("Num.num.Bit0", "num \<Rightarrow> num") $
            (Const ("Num.num.Bit0", "num \<Rightarrow> num") $
              (Const ("Num.num.Bit0", "num ... num") $ (Const ("Num.num.Bit0", "...") $ (Const ("...", ...) $ (... $ ...)))))))))]*)
in                                                  
      SOME (HOLogic.mk_number ((Type (\<^type_name>\<open>word\<close>, [dummyT]))) (snd (HOLogic.dest_number (hd xs))))
end
| bv_term_parser (SMTLIB.Sym "int2bv", xs) = (*TODO*)
(* ("bad SMT term format",
             S [Sym "_", Sym "int2bv",
                Num 32]*)
let
val _ = @{print}("FOUND2")
in
      SOME (HOLogic.mk_number \<^typ>\<open>32 word\<close> 32)
end
  | bv_term_parser (SMTLIB.Sym "bv2nat", [t1]) =
let 
  (*val _ = @{print} ("t1=", t1, (fastype_of t1))
  val _ = @{print} ("bv2nat t1=", Thm.cterm_of @{context} t1)
  val _ = @{print} ("bv2nat t1=", Thm.cterm_of @{context} (Const (\<^const_name>\<open>unsigned\<close>, (fastype_of t1) --> \<^typ>\<open>int\<close>) $ t1))*)
in
(*t1 could be in the form. In that case no further cast is needed Const ("Num.numeral_class.numeral", "num \<Rightarrow> int") $ ts*)
     SOME (Const (\<^const_name>\<open>unsigned\<close>, (fastype_of t1) --> \<^typ>\<open>int\<close>) $ t1)
end
      (*SOME ( t1)*)
 (*TODO: These are in SMTLIB3 syntax for parametric bitwidths. Put in own parser? 
         Also should variants for concrete bitwidths be added for when smtlib3 terms appear in proofs?*)
  | bv_term_parser (SMTLIB.Sym "extract", [t1,t2,t3]) =
    let 
       val T1 = fastype_of t1
       val T2 = fastype_of t2

       val t1' = if T1 = \<^typ>\<open>Int.int\<close> then Const ( \<^const_name>\<open>nat\<close>, T1 -->  \<^typ>\<open>Nat.nat\<close>) $ t1 else t1
       val t2' = if T2 = \<^typ>\<open>Int.int\<close> then Const ( \<^const_name>\<open>nat\<close>, T2 -->  \<^typ>\<open>Nat.nat\<close>) $ t2 else t2
    in SOME (Const (\<^const_name>\<open>SMT_Word.smt_extract\<close>, @{typ nat} --> @{typ nat} --> dummyT --> dummyT) $ t1' $ t2' $ t3)
    end
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_",SMTLIB.Sym "extract", SMTLIB.Num i, SMTLIB.Num j],[t]) = SOME (mk_extract i j t)
  | bv_term_parser (SMTLIB.Sym "bvnand", [t1, t2]) =
      SOME (mk_unary \<^const_name>\<open>ring_bit_operations_class.not\<close> (HOLogic.mk_binop \<^const_name>\<open>semiring_bit_operations_class.and\<close> (t1, t2)))
  | bv_term_parser (SMTLIB.Sym "bvnor", [t1, t2]) =
      SOME (mk_unary \<^const_name>\<open>ring_bit_operations_class.not\<close> (HOLogic.mk_binop \<^const_name>\<open>semiring_bit_operations_class.or\<close> (t1, t2)))
  | bv_term_parser (SMTLIB.Sym "int.log2", [t1]) =
    let
         val T1 = fastype_of t1
         val t1' = (Const (\<^const_name>\<open>nat\<close>, T1 --> \<^typ>\<open>Nat.nat\<close>) $ t1)
         val t2' = HOLogic.mk_number \<^typ>\<open>Nat.nat\<close> 2
        
     in
      SOME (Const (\<^const_name>\<open>of_nat\<close>, \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Int.int\<close> ) $ (Const (\<^const_name>\<open>Log_Nat.floorlog\<close>, \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Nat.nat\<close>)
         $ t1' $ t2'))
     end
  | bv_term_parser (SMTLIB.Sym "int.ispow2", [t1]) =
      SOME (Const (\<^const_name>\<open>SMT_Word.is_pow2\<close>,\<^typ>\<open>Int.int\<close> --> \<^typ>\<open>bool\<close>) $ t1)
  | bv_term_parser (SMTLIB.Sym "int.pow2", [t1]) =
    let
         val T1 = fastype_of t1
         val t1' = (Const (\<^const_name>\<open>nat\<close>, T1 --> \<^typ>\<open>Nat.nat\<close>) $ t1)
         val t2' = HOLogic.mk_number \<^typ>\<open>Nat.nat\<close> 2
        
     in
      SOME (Const (\<^const_name>\<open>of_nat\<close>, \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Int.int\<close> ) $ (Const (\<^const_name>\<open>power\<close>, \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Nat.nat\<close>)
         $ t1' $ t2'))
     end
  | bv_term_parser (SMTLIB.Sym "bvugt", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>Orderings.less\<close> (t2, t1))
  | bv_term_parser (SMTLIB.Sym "bvuge", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>Orderings.less_eq\<close> (t2, t1))
  | bv_term_parser (SMTLIB.Sym "bvsgt", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>word_sless\<close> (t2, t1))
  | bv_term_parser (SMTLIB.Sym "bvslt", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>word_sless\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvsge", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>word_sle\<close> (t2, t1))
  | bv_term_parser (SMTLIB.Sym "bvsle", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>word_sle\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvsmod", [t1,t2]) =
      SOME (HOLogic.mk_binop \<^const_name>\<open>smt_smod\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvurem", [t1,t2]) =
      SOME (HOLogic.mk_binop \<^const_name>\<open>smt_urem\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvsrem", [t1,t2]) =
      SOME (HOLogic.mk_binop \<^const_name>\<open>smt_srem\<close> (t1, t2))
  | bv_term_parser (SMTLIB.Sym "bvcomp", [t1,t2]) =
    let
      val T1 = fastype_of t1
    in
      SOME (Const (\<^const_name>\<open>smt_comp\<close>, T1 --> T1 --> \<^typ>\<open>1 word\<close>) $ t1 $ t2)
    end
  | bv_term_parser (SMTLIB.Sym "bvredor", [t1]) =
      SOME (Const (\<^const_name>\<open>smt_redor\<close>, fastype_of t1 --> \<^typ>\<open>1 word\<close>) $ t1)
  | bv_term_parser (SMTLIB.Sym "bvredand", [t1]) =
      SOME (Const (\<^const_name>\<open>smt_redand\<close>, fastype_of t1 --> \<^typ>\<open>1 word\<close>) $ t1)
  | bv_term_parser (SMTLIB.Sym "bvite", [t1,t2,t3]) =
      let
        val T = fastype_of t2
        val c = Const (\<^const_name>\<open>HOL.If\<close>, [\<^typ>\<open>HOL.bool\<close>, T, T] ---> T)
        val t1' = (Const (\<^const_name>\<open>semiring_bits_class.bit\<close>, fastype_of t1 --> \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>HOL.bool\<close>) $ t1 $ mk_nat 0)
      in SOME (c $ t1' $ t2 $ t3) end
(*TODO: Proofread until here*)
  | bv_term_parser (SMTLIB.Sym "repeat", [t1, t2]) =
    let
      val T2 = fastype_of t2
    in
      SOME (Const (\<^const_name>\<open>SMT_Word.smt_repeat\<close>,\<^typ>\<open>Nat.nat\<close>--> T2 --> dummyT) $ (Const (\<^const_name>\<open>nat\<close>, \<^typ>\<open>Int.int\<close> --> \<^typ>\<open>Nat.nat\<close>) $ t1) $ t2)
    end
  | bv_term_parser (SMTLIB.Sym "rotate_left", [t1, t2]) =
    let
      val T2 = fastype_of t2
    in
      SOME (Const (\<^const_name>\<open>word_rotl\<close>,\<^typ>\<open>Nat.nat\<close>--> T2 --> T2) $ (Const ( \<^const_name>\<open>nat\<close>,\<^typ>\<open>Int.int\<close> -->  \<^typ>\<open>Nat.nat\<close> ) $ t1) $ t2)
    end
  | bv_term_parser (SMTLIB.Sym "rotate_right", [t1,t2]) =
    let
      val T2 = fastype_of t2
      val _ = @{print}("rotate_right t1",t1)
      val _ = @{print}("rotate_right t2",t2)
      val _ = @{print}("rotate_right T2",T2)
(*("rotate_right t1", Free ("amount", "int")) (line 351 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("rotate_right t2", Free ("x", "_ word")) (line 352 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("rotate_right T2", "_ word") (line 353 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
("bvsize t1", Free ("x", "_ word")) (line 413 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") *)

    in
      SOME (Const (\<^const_name>\<open>word_rotr\<close>,\<^typ>\<open>Nat.nat\<close>--> T2 --> T2) $ (Const ( \<^const_name>\<open>nat\<close>, \<^typ>\<open>Int.int\<close> --> \<^typ>\<open>Nat.nat\<close>) $ t1) $ t2)
    end
  | bv_term_parser (SMTLIB.Sym "zero_extend", [t1, t2]) = (*This should push t1 0's before t2, solution above uses ucast, should I do too?*)
  let
    val T = fastype_of t2
    val TU = dummyT (*TODO: If known add concrete bitwidth*)
  in SOME (Const (\<^const_name>\<open>Word.cast\<close>, T --> TU) $ t2) end
  | bv_term_parser (SMTLIB.Sym "sign_extend", [t1, t2]) =
  let
    val _ = @{print}("sign_extend t1",t1)
    val _ = @{print}("sign_extend t2",t2)
    (*("sign_extend t1", Free ("n", "int")) (line 368 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/Library/Tools/smt_word.ML") 
    ("sign_extend t2", Free ("x", "_ word"))*)
    (*If type of t2 is known I could calculate type of t1, otherwise I would just ignore t1? Maybe better don't use signed*)
  in
   (*SOME (Const (\<^const_name>\<open>signed_take_bit\<close>,\<^typ>\<open>Nat.nat\<close>--> fastype_of t2 --> dummyT) $ (Const ( \<^const_name>\<open>nat\<close>, \<^typ>\<open>Int.int\<close> --> \<^typ>\<open>Nat.nat\<close>) $ t1) $ t2)*)
    SOME (Const (\<^const_name>\<open>Word.signed_cast\<close>, fastype_of t2 --> dummyT) $ t2)
  end
  | bv_term_parser (SMTLIB.Sym "bvuaddo", [t1, t2]) =
      SOME (Const (\<^const_name>\<open>smt_uaddo\<close>,Type("itself",[dummyT]) --> fastype_of t1--> fastype_of t2 --> dummyT) $ Free("itself",dummyT) $ t1 $ t2)
  | bv_term_parser (SMTLIB.Sym "bvsaddo", [t1, t2]) =
      SOME (Const (\<^const_name>\<open>smt_saddo\<close>,Type("itself",[dummyT]) --> fastype_of t1--> fastype_of t2 --> dummyT) $ Free("itself",dummyT) $ t1 $ t2)
  | bv_term_parser (SMTLIB.Sym "bvsdivo", [t1,t2]) = (*TODO*)
      SOME (Const (\<^const_name>\<open>smt_sdivo\<close>,Type("itself",[dummyT]) --> fastype_of t1--> fastype_of t2 --> dummyT) $ Free("itself",dummyT) $ t1 $ t2)
  | bv_term_parser (SMTLIB.Sym "bvusubo", [t1,t2]) =
      SOME (Const (\<^const_name>\<open>smt_usubo\<close>,Type("itself",[dummyT]) --> fastype_of t1--> fastype_of t2 --> dummyT) $ Free("itself",dummyT) $ t1 $ t2)
  | bv_term_parser (SMTLIB.Sym "bvssubo", [t1,t2]) =
      SOME (HOLogic.mk_binrel \<^const_name>\<open>smt_ssubo\<close> (t1, t2))
  (*| bv_term_parser (SMTLIB.Sym "xor", [t1, t2]) =
      SOME (Const ("Word.xor", \<^typ>\<open>HOL.bool\<close> --> \<^typ>\<open>HOL.bool\<close> --> \<^typ>\<open>HOL.bool\<close> ) $ t1 $ t2)*)
  | bv_term_parser (SMTLIB.Sym "concat", t::ts) = 
      SOME (mk_lassoc (curry mk_test) t ts)
  | bv_term_parser (SMTLIB.Sym "sum_length",[ts]) =
      SOME (Const (\<^const_name>\<open>temp_sum_length\<close>, dummyT -->dummyT) $ ts)
  | bv_term_parser (SMTLIB.Sym "list_length_0",[ts]) =
      SOME (Const (\<^const_name>\<open>list_length_0'\<close>, dummyT -->dummyT) $ ts)
  | bv_term_parser (SMTLIB.Sym "length",[ts]) =
      SOME (Const (\<^const_name>\<open>of_nat\<close>, dummyT -->dummyT) $ (Const (\<^const_name>\<open>size\<close>, dummyT -->dummyT) $ ts))

  | bv_term_parser (SMTLIB.Sym "smt_concat", [t]) = 
      SOME (Const (\<^const_name>\<open>concat_smt2\<close>, dummyT -->dummyT) $ t)
  | bv_term_parser (SMTLIB.Sym "bv", [int,base]) = (*TODO: Can get rid of case distinction now*)
     let
     (*There is one special case that is caught here, that is if the base is the size of another bitvector *)
    (* val _ = @{print}("int",int)
     val _ = @{print}("base",base)*)
 in
         SOME (Const  (\<^const_name>\<open>Word.Word\<close>,\<^typ>\<open>Int.int\<close>--> dummyT) $ int) (*TODO: Use ty*)
      end

(*(Sym "bv",
  [Const ("Groups.one_class.one", "int"),
   Const ("Word.size_word_inst.size_word", "_ \<Rightarrow> _") $
     Free ("x",
           "_")]*)
  | bv_term_parser (SMTLIB.Sym "bvsize", [t1]) =
let
     val _ = @{print}("bvsize t1",t1)
     val T = fastype_of t1
     val _ = @{print}("T",T)

     val _ = @{print}("bvsize t1",(Const ( \<^const_name>\<open>of_nat\<close>,  \<^typ>\<open>Nat.nat\<close> -->  \<^typ>\<open>Int.int\<close>) $
Const ( \<^const_name>\<open>size\<close>, dummyT -->  \<^typ>\<open>Nat.nat\<close>) $ t1))
in
      SOME (Const ( \<^const_name>\<open>of_nat\<close>,  \<^typ>\<open>Nat.nat\<close> -->  \<^typ>\<open>Int.int\<close>) $
(Const ( \<^const_name>\<open>size\<close>, dummyT -->  \<^typ>\<open>Nat.nat\<close>) $ t1))
(*SOME (Const ( \<^const_name>\<open>Groups.one\<close>, \<^typ>\<open>Int.int\<close>))*)

end
  | bv_term_parser (SMTLIB.Sym "bvsdiv", [t1,t2]) = (*TODO*)
      SOME (HOLogic.mk_binop \<^const_name>\<open>Rings.divide\<close> (mk_unary \<^const_name>\<open>unsigned\<close> t1, mk_unary \<^const_name>\<open>unsigned\<close> t2))
 | bv_term_parser (SMTLIB.Sym "bvudiv", [t1,t2]) =
      SOME (HOLogic.mk_binop \<^const_name>\<open>smt_udiv\<close> (t1, t2)) (*TODO: What about the case whre t2 is 0? SMTLIB semantics says it should be mask *)
  | bv_term_parser (SMTLIB.Sym "bvshl", [t1, t2]) = 
    let
      val T1 = fastype_of t1
    in
      SOME (Const (\<^const_name>\<open>semiring_bit_operations_class.push_bit\<close>, \<^typ>\<open>Nat.nat\<close> --> T1 --> T1) $ (Const ( \<^const_name>\<open>unsigned\<close>, T1 --> \<^typ>\<open>Nat.nat\<close> ) $ t2) $ t1)
   end
  | bv_term_parser (SMTLIB.Sym "bvlshr", [t1, t2]) = 
    let
      val T1 = fastype_of t1
    in
      SOME (Const (\<^const_name>\<open>semiring_bit_operations_class.drop_bit\<close>, \<^typ>\<open>Nat.nat\<close> --> T1 --> T1) $ (Const ( \<^const_name>\<open>unsigned\<close>, T1 --> \<^typ>\<open>Nat.nat\<close> ) $ t2) $ t1)
   end
  | bv_term_parser (SMTLIB.Sym "bvashr", [t1, t2]) = 
    let
      val T1 = fastype_of t1
    in
      SOME (Const (\<^const_name>\<open>signed_drop_bit\<close>, \<^typ>\<open>Nat.nat\<close> --> T1 --> T1) $ (Const ( \<^const_name>\<open>unsigned\<close>, T1 --> \<^typ>\<open>Nat.nat\<close> ) $ t2) $ t1)
   end
  | bv_term_parser (SMTLIB.Num n, _) = (ignore (@{print} ("n=", n)); NONE)
  | bv_term_parser _ = NONE




val temp = (Type (\<^type_name>\<open>word\<close>, [dummyT]))

 fun bv_type_parser (SMTLIB.Sym "?BitVec", []) = SOME (Type (\<^type_name>\<open>word\<close>, [dummyT])) (*TODO: Here it should be a 'a::len word not a word *)
  | bv_type_parser (SMTLIB.S [SMTLIB.Sym "?BitVec"], []) = SOME (Type (\<^type_name>\<open>word\<close>, [dummyT])) (*TODO*)
  | bv_type_parser (SMTLIB.Sym "?BitVec", []) = SOME (Type (\<^type_name>\<open>word\<close>, [dummyT])) (*TODO *)

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_term_parser bv_term_parser))

(*
val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_type_parser bv_type_parser))*)
\<close>


ML \<open>
let
local
  fun smt_mk_builtin_typ (Z3_Interface.Sym ("word", _)) = SOME \<^typ>\<open>_ word\<close>
    | smt_mk_builtin_typ (Z3_Interface.Sym ("Word", _)) = SOME \<^typ>\<open>_ word\<close>
        (*FIXME: delete*)
    | smt_mk_builtin_typ _ = NONE

  fun smt_mk_builtin_num _ i T =
let val _ = @{print} T in
    if Word_Lib.is_wordT T then SOME (Numeral.mk_cnumber (Thm.ctyp_of @{context} T) i)
    else NONE
end

  fun mk_nary _ cu [] = cu
    | mk_nary ct _ cts = uncurry (fold_rev (Thm.mk_binop ct)) (split_last cts)

  val mk_uminus = Thm.apply \<^cterm>\<open>uminus :: _::len word \<Rightarrow> _\<close>
  val add = \<^cterm>\<open>(+) :: _ word \<Rightarrow> _\<close>
(*  val real0 = Numeral.mk_cnumber \<^ctyp>\<open>_ word\<close> 0*)
  val mk_sub = Thm.mk_binop \<^cterm>\<open>(-) :: 'a::len word \<Rightarrow> _\<close>
  val mk_mul = Thm.mk_binop \<^cterm>\<open>(*) :: 'a::len word \<Rightarrow> _\<close>
  val mk_lt = Thm.mk_binop \<^cterm>\<open>(<) :: 'a::len word \<Rightarrow> _\<close>
  val mk_le = Thm.mk_binop \<^cterm>\<open>(\<le>) :: 'a::len word \<Rightarrow> _\<close>

  fun smt_mk_builtin_fun (Z3_Interface.Sym ("-", _)) [ct] = SOME (mk_uminus ct)
(*    | smt_mk_builtin_fun (Z3_Interface.Sym ("+", _)) cts = SOME (mk_nary add real0 cts)*)
    | smt_mk_builtin_fun (Z3_Interface.Sym ("-", _)) [ct, cu] = SOME (mk_sub ct cu)
    | smt_mk_builtin_fun (Z3_Interface.Sym ("*", _)) [ct, cu] = SOME (mk_mul ct cu)
    | smt_mk_builtin_fun (Z3_Interface.Sym ("<", _)) [ct, cu] = SOME (mk_lt ct cu)
    | smt_mk_builtin_fun (Z3_Interface.Sym ("<=", _)) [ct, cu] = SOME (mk_le ct cu)
    | smt_mk_builtin_fun (Z3_Interface.Sym (">", _)) [ct, cu] = SOME (mk_lt cu ct)
    | smt_mk_builtin_fun (Z3_Interface.Sym (">=", _)) [ct, cu] = SOME (mk_le cu ct)
    | smt_mk_builtin_fun _ _ = NONE
in
val smt_mk_builtins = {
  mk_builtin_typ = smt_mk_builtin_typ,
  mk_builtin_num = smt_mk_builtin_num,
  mk_builtin_fun = (fn _ => fn sym => fn cts =>
    (case try (Thm.typ_of_cterm o hd) cts of
      SOME a => if  Word_Lib.is_wordT a then smt_mk_builtin_fun sym cts else NONE
    | _ => NONE)) }
end
in
  Theory.setup (Context.theory_map (Z3_Interface.add_mk_builtins smt_mk_builtins))
end
\<close>

ML \<open>
let
  fun smt_mk_builtin_num T i =
   let val _ = @{print} T in
       if Word_Lib.is_wordT T then SOME (Numeral.mk_cnumber (Thm.ctyp_of @{context} T) i)
       else NONE
   end

val setup_builtins =
SMT_Builtin.add_builtin_typ SMTLIB_Interface.bvsmtlibC
  (\<^typ>\<open>'a word\<close>, K (SOME ("word", [])), K (K (NONE)))


in
()
end
\<close>


term " (0 :: 32 word)"
ML \<open>@{typ "32 word"} = \<^typ>\<open>_ word\<close>\<close>
ML \<open>@{print} (Numeral.mk_cnumber \<^ctyp>\<open>43 word\<close> 0) \<close>
lemma "- (- 1 :: int) \<le> 2"
  supply [[smt_trace,smt_debug_verit]]
  by (smt (cvc5))

lemma "x = (1 :: 32 word) \<Longrightarrow> x \<le> 2"
  supply [[smt_trace,smt_debug_verit]]
  by (smt (cvc5))

lemma " (1 :: 32 word) \<le> 2"
  supply [[smt_trace,smt_debug_verit]]
  by (smt (cvc5) )

lemma " (1 :: 32 word) \<le> 2"
  supply [[smt_trace,smt_debug_verit,z3_extensions]]
  by (smt (cvc5) )

lemma "uint (1 :: 32 word) \<le> 2"
  supply [[smt_trace,smt_debug_verit]]
by (smt (cvc5) )

lemma "unat (2048 :: 32 word) \<le> 4294967296"
  supply [[smt_trace]]
by (smt (cvc5) )


end