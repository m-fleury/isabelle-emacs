theory SMT_Word
  imports "HOL-Library.Word" "Word_Lib.Many_More"
begin
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
    (*apply simp
    apply (rule order.strict_trans2[OF unat_bit_shift_add_bound])
    using assms by simp*)
    sorry

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

definition smt_extract where
  \<open>smt_extract j i w = slice i (take_bit (Suc j) w)\<close>

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

definition smt_saddo :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> bool" where
"smt_saddo x y = 
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


end