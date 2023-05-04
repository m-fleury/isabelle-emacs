theory BV_Rewrites_Lemmas
  imports Dsl_Nary_Ops "HOL-Library.Word" Word_Lib.More_Word "HOL-Library.Log_Nat"
begin
(*imported from various places*)

(*IEEE_Float_Extend_Integer*)
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
(*
    have [simp]: 
      "is_up UCAST('l\<^sub>1 \<rightarrow> 'l\<^sub>3)" 
      "is_up UCAST('l\<^sub>2 \<rightarrow> 'l\<^sub>3)" 
      using assms 
      by (auto simp add: is_up)
*)
    have [simp]: "LENGTH('l\<^sub>2) < LENGTH('l\<^sub>3)"
      using assms 
      by (metis add_diff_cancel_right' add_leD2 diff_is_0_eq' le_neq_implies_less len_not_eq_0)
      
          
      
    have B2: "unat w\<^sub>2 + unat w\<^sub>1 * unat ((2::'l\<^sub>3 word) ^ LENGTH('l\<^sub>2)) < 2 ^ LENGTH('l\<^sub>3)"
      apply (simp)
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

 definition smt_extract where
  \<open>smt_extract j i w = slice i (take_bit (Suc j) w)\<close>


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
  \<open>i\<ge>1 \<Longrightarrow> LENGTH('b) = i * size n\<Longrightarrow> unat ((word_repeat i n) :: 'b :: len word) = replicate_nat i (size n) * (unat n)\<close>
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

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "[+1]" 60)
  where "(A [+1] B) \<equiv> (\<not>(A = B))"


(*

(define-rule bv-redor-eliminate ((x ?BitVec)) (bvredor x) (not (bvcomp x (bv 0 (bvsize x)))))
(define-rule bv-redand-eliminate ((x ?BitVec)) (bvredand x) (not (bvcomp x (not (bv 0 (bvsize x))))))
*)

definition smt_comp :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 1 word" where
  \<open>smt_comp x y = (if (x = y) then 1 else 0)\<close>

definition smt_redor :: "'a::len word \<Rightarrow> 1 word" where
  \<open>smt_redor x = not (smt_comp x 0)\<close>

definition smt_redand :: "'a::len word \<Rightarrow> 1 word" where
  \<open>smt_redand x = not (smt_comp x (not (0::'a word)))\<close>

definition smt_uaddo  :: "'a::len word \<Rightarrow> 'b::len word \<Rightarrow> bool" where
"smt_uaddo x y = (smt_extract (size x) (size x)
 ((Word.word_cat (0::1 word) x) + (Word.word_cat (0::1 word) y) :: 'c::len word) = (1:: 1 word))"

definition smt_saddo :: "'a::len word \<Rightarrow> 'b::len word \<Rightarrow> bool" where
"smt_saddo x y = (smt_extract ((size x)-1) ((size y)-1)
 ((Word.word_cat (0::1 word) x) + (Word.word_cat (0::1 word) y) :: 'c::len word) = (1:: 1 word))"

definition smt_sdivo :: "'a::len word \<Rightarrow> 'b::len word \<Rightarrow> bool" where
"smt_sdivo x y = (x = (word_cat (1::1 word) (0::'c::len word)::'a word) \<and> y = (mask (size y)::'b word))"

definition smt_usubo :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> bool" where
"smt_usubo x y = ((smt_extract ((size x)-1) ((size y)-1) (push_bit 1 x - push_bit 1 y)) = (1::1 word))"

definition smt_ssubo :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> bool" where (*TODO*)
"smt_ssubo x y = 
(let n = size x in 
(let xLt0 = ((smt_extract ((size x)-1) ((size x)-1) x) = (1::1 word)) in
(let yLt0 = ((smt_extract ((size x)-1) ((size x)-1) y) = (1::1 word)) in
(let sLt0 = ((smt_extract ((size x)-1) ((size x)-1) (x -y)) = (1::1 word)) in
((xLt0 \<and> \<not>yLt0 \<and> \<not>sLt0) \<or> (\<not>xLt0 \<and> yLt0 \<and> sLt0))))))
"

lemma "unsigned (if x then y else z) = (if x then unsigned y else unsigned z)"
  by auto
declare[[show_types]]
declare[[show_sorts]]

definition smt_urem :: "'a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
"smt_urem s t = (if (unat s = 0) then s
 else of_nat ((unat s) mod (unat t)))"

lemma "uint (smt_urem s t) = (if (s = 0) then (uint s) else int ((unat s) mod (unat t)))"
proof-
  have "uint (smt_urem s t) =
        uint (if (unat s = 0) then s else of_nat ((unat s) mod (unat t)))"
  unfolding smt_urem_def by simp
  then have "uint (smt_urem s t) =
   (if (unat s = 0) then uint s else uint (of_nat ((unat s) mod (unat t))::'a::len word))"
    by presburger
  moreover have "uint (of_nat ((unat s) mod (unat t))::'a::len word)
= int ((unat s) mod (unat t))"
    by (metis Word.of_nat_unat ucast_id unat_mod)
  ultimately show ?thesis
    by (simp add: unsigned_eq_0_iff)
qed

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
proof-
  have "uint (smt_srem s t) =
 (if ((smt_extract (size s-1) (size s-1) s = (0::1 word)) \<and> (smt_extract (size s-1) (size s-1) t = (0::1 word)))
 then uint (smt_urem s t)
 else (if ((smt_extract (size s-1) (size s-1) s = (1::1 word)) \<and> (smt_extract (size s-1) (size s-1) t = (0::1 word)))
 then uint (- (smt_urem (-s) t))
 else (if ((smt_extract (size s-1) (size s-1) s = (0::1 word)) \<and> (smt_extract (size s-1) (size s-1) t = (1::1 word)))
 then uint (smt_urem s (-t))
 else uint (- (smt_urem (-s) (-t) ))
)))"
  apply (simp add: word_uint_eq_iff[symmetric])
  using smt_srem_def[of s t]
  unfolding Let_def
  by simp
  moreover have "uint (- (smt_urem (-s) (-t))) = take_bit LENGTH('a) (- uint (smt_urem (-s) (-t)))"
    by (simp add: uint_word_arith_bintrs(4))
  moreover have "uint (- (smt_urem (-s) t)) = take_bit LENGTH('a::len) (- uint (smt_urem (-s) t))"
    by (simp add: uint_word_arith_bintrs(4))
  ultimately show 
"uint (smt_srem s t) =
 (if ((smt_extract (size s-1) (size s-1) s = (0::1 word)) \<and> (smt_extract (size s-1) (size s-1) t = (0::1 word)))
 then uint (smt_urem s t)
 else (if ((smt_extract (size s-1) (size s-1) s = (1::1 word)) \<and> (smt_extract (size s-1) (size s-1) t = (0::1 word)))
 then take_bit (size s) (- uint (smt_urem (-s) t))
 else (if ((smt_extract (size s-1) (size s-1) s = (0::1 word)) \<and> (smt_extract (size s-1) (size s-1) t = (1::1 word)))
 then uint (smt_urem s (-t))
 else take_bit (size s) (- uint (smt_urem (-s) (-t)))
)))"
    by (simp add: word_size)
qed










definition is_pow2 :: "int \<Rightarrow> bool" where
  \<open>is_pow2 i \<equiv> (i = 0) \<and> (and i (i-1) = 0)\<close>


declare[[show_types]]
declare[[show_sorts]]

value "8::4 word"


value "(smt_extract 3 0 (10::4 word))::4 word"

value "(smt_extract 3 0 (11::4 word))::4 word"
(*k = 3, j = 1, i = 0*)
value "(smt_extract 3 2 (11::4 word))::2 word"
value "(smt_extract 1 0 (11::3 word))::2 word"
value "(word_cat (2::2 word) (3::2 word))::4 word"

value "(smt_extract 2 0 (2::3 word))::3 word"
value "(smt_extract 2 2 (2::3 word))::1 word"
value "(smt_extract 1 0 (2::3 word))::2 word"
value "(word_cat (0::1 word) (2::2 word))::3 word"

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
    by (metis a1 dual_order.strict_trans2 size_word.rep_eq)
  have "unat (smt_extract j i x::'b::len word) = unat (ucast (drop_bit i (take_bit (Suc j) x))::'b::len word)"
    unfolding smt_extract_def slice_def slice1_def
    using a0 t1 by force
  also have "... = unat (drop_bit i (take_bit (Suc j) x))"
    by (metis (no_types, lifting) Suc_eq_plus1 a1 drop_bit_take_bit min.idem take_bit_take_bit unsigned_take_bit_eq unsigned_ucast_eq)
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
  apply (cases "i=0")
proof-
  assume a0: "i = (0::nat) " and a1: "i \<le> j" "j < size x" "LENGTH('b) = j + 1 - i"
  then have t0: "LENGTH('b) \<le> LENGTH('a)"
    by (simp add: size_word.rep_eq)
  have "uint (smt_extract j i x::'b::len word) = uint (ucast (take_bit (Suc j) x ::'a::len word)::'b::len word)"
   unfolding smt_extract_def slice_def slice1_def
   by (simp add: a0)
  also have "... = uint (take_bit (Suc j) x ::'a::len word)"
    by (simp add: a1 a0 unsigned_take_bit_eq unsigned_ucast_eq)
  also have "... = take_bit (Suc j) (unsigned x)" 
    using Word.semiring_bit_operations_class.unsigned_take_bit_eq
    by auto
  finally show "uint ((smt_extract j i (x::'a::len word))::'b::len word) = drop_bit i (take_bit (Suc j) (unsigned x))" 
    using a0 by force
next
  assume a0: "i \<noteq> (0::nat)" and a1: "i \<le> j" "j < size x" "LENGTH('b) = j + 1 - i"
  then have t0: "LENGTH('b) \<le> LENGTH('a)"
    by (metis Suc_eq_plus1 Suc_leI diff_le_self le_trans size_word.rep_eq)
  have t1: "i < LENGTH('a)"
    by (metis a1 dual_order.strict_trans2 size_word.rep_eq)
  have "uint (smt_extract j i x::'b::len word) = uint (ucast (drop_bit i (take_bit (Suc j) x))::'b::len word)"
    unfolding smt_extract_def slice_def slice1_def
    using a0 t1 by force
  also have "... = uint (drop_bit i (take_bit (Suc j) x))"
    by (metis (no_types, lifting) Suc_eq_plus1 a1 drop_bit_take_bit min.idem take_bit_take_bit unsigned_take_bit_eq unsigned_ucast_eq)
  also have "... = drop_bit i (take_bit LENGTH('a::len) (unsigned (take_bit (Suc j) x)))" 
    using unsigned_drop_bit_eq[of i "take_bit (Suc j) x"] by blast
  also have "... = drop_bit i (take_bit LENGTH('a::len) (take_bit (Suc j) (unsigned x)))" 
    using unsigned_take_bit_eq[of "Suc j" x] by metis
  finally have "uint (smt_extract j i x::'b::len word) = drop_bit i (take_bit LENGTH('a::len) (take_bit (Suc j) (unsigned x)))" 
    by auto
  moreover have "(min LENGTH('a::len) (Suc j)) = Suc j"
    by (metis Suc_leI a1 min_absorb2 word_size)
  ultimately show "uint (smt_extract j i x::'b::len word) = drop_bit i (take_bit (Suc j) (unsigned x))" 
    using take_bit_take_bit[of "LENGTH('a)" "Suc j" "unsigned x"]
    by auto
qed

lemma sint_smt_extract:
  fixes x::"'a::len word"
  shows  "i \<le> j \<and> j < size x \<and> LENGTH('b) = j + 1 - i
 \<Longrightarrow> sint ((smt_extract j i (x::'a::len word))::'b::len word)
= signed_take_bit (LENGTH('b::len) - Suc (0::nat)) (drop_bit i (take_bit (Suc j) (unsigned x)))"
  apply (cases "i=0")
proof-
  assume a0: "i = (0::nat) " and a1: "i \<le> j \<and> j < size x \<and> LENGTH('b) = j + 1 - i"
  then have t0: "LENGTH('b) \<le> LENGTH('a)"
    by (simp add: size_word.rep_eq)
  have "sint (smt_extract j i x::'b::len word) = sint (ucast (take_bit (Suc j) x ::'a::len word)::'b::len word)"
   unfolding smt_extract_def slice_def slice1_def
   by (simp add: a0)
  also have "... = signed_take_bit (LENGTH('b::len) - Suc (0::nat)) (unsigned (take_bit (Suc j) x))"
    using signed_ucast_eq[of "(take_bit (Suc j) x ::'a::len word)"]
    by blast
  also have "... = signed_take_bit (LENGTH('b::len) - Suc (0::nat)) (take_bit (Suc j) (unsigned x))"
    by (simp add: uint_take_bit_eq)
  finally show "sint ((smt_extract j i (x::'a::len word))::'b::len word) = signed_take_bit (LENGTH('b::len) - Suc (0::nat)) (drop_bit i (take_bit (Suc j) (unsigned x)))" 
    using a0 by force
next
  assume a0: "i \<noteq> (0::nat)" and a1: "i \<le> j \<and> j < size x \<and> LENGTH('b) = j + 1 - i"
  then have t0: "LENGTH('b) \<le> LENGTH('a)"
    by (metis Suc_eq_plus1 Suc_leI diff_le_self le_trans size_word.rep_eq)
  have t1: "i < LENGTH('a)"
    by (metis a1 dual_order.strict_trans2 size_word.rep_eq)
  have "sint (smt_extract j i x::'b::len word) = sint (ucast (drop_bit i (take_bit (Suc j) x))::'b::len word)"
    unfolding smt_extract_def slice_def slice1_def
    using a0 t1 by force
  also have "... = signed_take_bit (LENGTH('b::len) - Suc (0::nat)) (unsigned (drop_bit i (take_bit (Suc j) x)))"
    using signed_ucast_eq by blast
  also have "... = signed_take_bit (LENGTH('b::len) - Suc (0::nat)) (drop_bit i (unsigned (take_bit (Suc j) x)))"
    by (metis take_bit_length_eq unsigned_drop_bit_eq unsigned_take_bit_eq)
  also have "... = signed_take_bit (LENGTH('b::len) - Suc (0::nat)) (drop_bit i (take_bit (Suc j) (unsigned x)))"
    by (simp add: unsigned_take_bit_eq)
  finally show "sint ((smt_extract j i (x::'a::len word))::'b::len word) = signed_take_bit (LENGTH('b::len) - Suc (0::nat)) (drop_bit i (take_bit (Suc j) (unsigned x)))" 
    using unsigned_drop_bit_eq[of i "take_bit (Suc j) x"] by blast
qed

lemma uint_word_rotl_eq:
  \<open>uint (word_rotl n w) = concat_bit (n mod LENGTH('a))
    (drop_bit (LENGTH('a) - n mod LENGTH('a)) (uint w))
    (uint (take_bit (LENGTH('a) - n mod LENGTH('a)) w))\<close>
  for w :: \<open>'a::len word\<close>
  by transfer (simp add: take_bit_concat_bit_eq)

lemma smt_extract_bit: "k < size (x::'a::len word) \<longrightarrow> (smt_extract k k x::1 word) = (if bit x k then 1 else 0)" 
  apply (simp add: bang_eq)
  unfolding smt_extract_def
  apply (simp_all add: nth_slice bit_take_bit_iff)
  by (metis add_0 bot_nat_0.not_eq_extremum)

lemma bit_smt_extract: "bit (smt_extract j i x::'b::len word) n = ((n + i < Suc j \<and> bit x (n + i)) \<and> n < LENGTH('b::len))"
  unfolding smt_extract_def
  using nth_slice[of i "(take_bit (Suc j) x)" n, where 'a="'b"] bit_take_bit_iff[of "Suc j" x "n+i"]
  by simp


lemma unat_smt_extract2:
  fixes x::"'a::len word" 
  shows  "i \<le> j \<Longrightarrow> j < size x \<Longrightarrow> size (smt_extract j i (x::'a::len word)::'b::len word) = j + 1 - i
 \<Longrightarrow> unat ((smt_extract j i (x::'a::len word))::'b::len word)
   = drop_bit i (take_bit (Suc j) (unat x))"
  by (simp add: size_word.rep_eq unat_smt_extract)

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
  by (metis (mono_tags, lifting) int_plus push_bit_of_nat take_bit_of_nat uint_nat unat_word_cat zmod_int)


lemma word_cat_smt_extract: "i \<le> j \<and> j + 1 \<le> k \<and> i \<ge> 0 \<and> k < size x 
 \<and> LENGTH('a) = size x
 \<and> LENGTH('b::len) = k + (1::nat) - Suc j
 \<and> LENGTH('d::len) = k + (1::nat) - i
 \<and> LENGTH('c::len) = j + (1::nat) - i
\<longrightarrow> word_cat ((smt_extract k (j+1) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) = ((smt_extract k i x)::'d::len word)"
proof
  assume a0: "i \<le> j \<and> j + 1 \<le> k \<and> i \<ge> 0 \<and> k < size x 
            \<and> LENGTH('a) = size x
            \<and> LENGTH('b::len) = k + (1::nat) - Suc j
            \<and> LENGTH('d::len) = k + (1::nat) - i
            \<and> LENGTH('c::len) = j + (1::nat) - i"
  
  have "unat ((smt_extract k i x)::'d::len word) = drop_bit i (take_bit (Suc k) (unsigned x))"
    using unat_smt_extract[of i k x] a0 by auto
  moreover have "unat (word_cat ((smt_extract k (Suc j) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) ::'d::len word)
= (push_bit ((j + (1::nat)) - i) (drop_bit (Suc j) (take_bit (Suc k) (unat x)))
 + (drop_bit i (take_bit (Suc j) (unat x)))) mod (2::nat) ^ (k + (1::nat) - i)"
  proof-
 have "unat (word_cat ((smt_extract k (Suc j) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) ::'d::len word)
    = (take_bit LENGTH('d::len) (push_bit LENGTH('c::len) (take_bit LENGTH('d::len) (unat ((smt_extract k (Suc j) x::'b::len word)::'b::len word))))
      + unat (ucast (smt_extract j i x::'c::len word)::'d::len word)) mod (2::nat) ^ LENGTH('d::len)"
   by (simp add: unat_word_ariths(1) unsigned_push_bit_eq unsigned_ucast_eq word_cat_bin')
  moreover have " Suc (j::nat) \<le> (k::nat) \<and> k < size (x::'a::len word) \<and> LENGTH('b::len) = k + (1::nat) - Suc j "
    by (meson Suc_leI a0 discrete)
  ultimately have "unat (word_cat ((smt_extract k (Suc j) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) ::'d::len word)
= (take_bit LENGTH('d::len) (push_bit LENGTH('c::len) (take_bit LENGTH('d::len) (drop_bit (Suc j) (take_bit (Suc k) (unat x)))))
 + unat (ucast (smt_extract j i x::'c::len word)::'d::len word)) mod (2::nat) ^ LENGTH('d::len)"
    using unat_smt_extract[of "(Suc j)" k x, where ?'b='b]
    by simp
  moreover have "unat (word_cat ((smt_extract k (Suc j) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) ::'d::len word)
= (take_bit LENGTH('d::len) (push_bit LENGTH('c::len) (take_bit LENGTH('d::len) (drop_bit (Suc j) (take_bit (Suc k) (unat x)))))
 + unat ( (smt_extract j i x::'c::len word))) mod (2::nat) ^ LENGTH('d::len)"
  using unat_ucast_up_simp[of "(smt_extract j i x::'c::len word)", where ?'b='d]
  by (simp add: calculation mod_add_right_eq unat_ucast)
  ultimately have "unat (word_cat ((smt_extract k (Suc j) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) ::'d::len word)
= (take_bit LENGTH('d::len) (push_bit LENGTH('c::len) (take_bit LENGTH('d::len) (drop_bit (Suc j) (take_bit (Suc k) (unat x)))))
 + (drop_bit i (take_bit (Suc j) (unat x)))) mod (2::nat) ^ LENGTH('d::len)"
    using unat_smt_extract[of i j x, where ?'b='c]
    using a0 by auto
  then have "unat (word_cat ((smt_extract k (Suc j) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) ::'d::len word)
= (take_bit (k + (1::nat) - i) (push_bit (j + (1::nat) - i) (take_bit (k + (1::nat) - i) (drop_bit (Suc j) (take_bit (Suc k) (unat x)))))
 + (drop_bit i (take_bit (Suc j) (unat x)))) mod (2::nat) ^ (k + (1::nat) - i)"
    using a0 by simp
  moreover have "((((j::nat) + (1::nat)) - (i::nat)) + ((k::nat) - j)) = k+1 -i"
    using a0 by auto
  ultimately have "unat (word_cat ((smt_extract k (Suc j) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) ::'d::len word)
=(push_bit ((j + (1::nat)) - i) (take_bit (k - j) (take_bit (k + (1::nat) - i) (drop_bit (Suc j) (take_bit (Suc k) (unat x)))))
 + (drop_bit i (take_bit (Suc j) (unat x)))) mod (2::nat) ^ (k + (1::nat) - i)"
   using push_bit_take_bit[symmetric,of "(j + (1::nat) - i)" "k-j"]
   by metis
  moreover have "min (k - j) (k + (1::nat) - i) = (k - j)"
    by (metis \<open>(((((j::nat) + (1::nat)) - (i::nat)) + ((k::nat) - j)) = ((k + (1::nat)) - i))\<close> le_add2 min_def)
  ultimately have "unat (word_cat ((smt_extract k (Suc j) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) ::'d::len word)
=(push_bit ((j + (1::nat)) - i) (take_bit (k - j) (drop_bit (Suc j) (take_bit (Suc k) (unat x))))
 + (drop_bit i (take_bit (Suc j) (unat x)))) mod (2::nat) ^ (k + (1::nat) - i)"
    by (simp add: take_bit_take_bit)
  then have "unat (word_cat ((smt_extract k (Suc j) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) ::'d::len word)
=(push_bit ((j + (1::nat)) - i) (drop_bit (Suc j) (take_bit (k + 1) (take_bit (Suc k) (unat x))))
 + (drop_bit i (take_bit (Suc j) (unat x)))) mod (2::nat) ^ (k + (1::nat) - i)"
    using drop_bit_take_bit[symmetric, of "k+1" "Suc j"]
    by (metis Suc_eq_plus1 diff_Suc_Suc)
 then show "unat (word_cat ((smt_extract k (Suc j) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) ::'d::len word)
=(push_bit ((j + (1::nat)) - i) (drop_bit (Suc j) (take_bit (Suc k) (unat x)))
 + (drop_bit i (take_bit (Suc j) (unat x)))) mod (2::nat) ^ (k + (1::nat) - i)"
  by simp
qed
  ultimately show "word_cat ((smt_extract k (j+1) (x::'a::len word))::'b::len word) ((smt_extract j i x)::'c::len word) = ((smt_extract k i x)::'d::len word)"
    apply (simp add: word_unat_eq_iff)
    apply (simp add: push_bit_eq_mult drop_bit_eq_div take_bit_eq_mod)
    by (smt (z3) Suc_eq_plus1 a0 add.commute add.right_neutral add_Suc_right add_diff_cancel_left' add_diff_cancel_right' diff_add_inverse div_exp_eq le_add_diff_inverse min_minus' mod_add_left_eq mult.commute mult_div_mod_eq plus_1_eq_Suc power_Suc power_mod_div take_bit_eq_mod take_bit_nat_def take_bit_take_bit)
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
    by (smt (verit, del_insts) a0 diff_add_inverse2 int_eq_iff nat_1 nat_add_distrib nat_zero_as_int plus_1_eq_Suc word_size zero_less_diff)
  moreover have "LENGTH('c::len) = (((nat j) + (1::nat)) - (nat i))"
    by (smt (verit, del_insts) a0 diff_add_inverse2 int_eq_iff nat_1 nat_add_distrib nat_zero_as_int plus_1_eq_Suc word_size zero_less_diff)
  ultimately show "(word_cat t1 t2) = t3"
    using word_cat_smt_extract[of "nat i" "nat j" "nat k" x, where 'b="'b", where 'd="'d", where 'c="'c"]
    by (smt (verit, ccfv_threshold) Nat.add_0_right a0 nat_1 nat_add_distrib plus_1_eq_Suc)
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
    by (smt (verit, ccfv_SIG) a0 add_diff_cancel_right' diff_Suc_eq_diff_pred nat_diff_distrib nat_int)
  moreover have "(size x_c3) = (((nat k) + (1::nat)) - (nat i))"
    by (smt (verit, del_insts) a0 int_nat_eq int_ops(6) nat_int of_nat_1 of_nat_add)
  moreover have "(size x_c1) = (((nat j) + (1::nat)) - (nat i))"
    by (smt (verit) One_nat_def a0 nat_1 nat_add_distrib nat_diff_distrib' nat_int)
  ultimately show "x_c2 = x_c3"
    by (metis a0 word_cat_smt_extract word_size)
qed


lemma rewrite_bv_concat_to_mult:
  fixes x::"'a ::len word" and i::"int" and m::"int"
  shows "(1::int) + i + m = int (size x) \<longrightarrow> LENGTH('b) = nat i+1 \<longrightarrow> LENGTH('b) + LENGTH('c) = LENGTH('a) \<longrightarrow> int (LENGTH('c)) = m \<longrightarrow> 
   (word_cat (smt_extract (nat i) (nat (0::int)) x :: 'b:: len word) (Word.Word (0::int):: 'c::len word) ::'a::len word) =
   x * (push_bit (unat (Word.Word m :: 'a::len word)) (Word.Word (1::int)::'a::len word)::'a::len word)"
  apply (rule impI)+
proof-
  assume a0: "((((1::int) + i) + m) = (int (size x)))"
  and a1: "(LENGTH('b) = ((nat i) + (1::nat)))"
  and a2: "((LENGTH('b) + LENGTH('c)) = LENGTH('a))"
  and a3: "((int LENGTH('c)) = m)"
 
  have "m < int LENGTH('a)" 
    by (metis a2 a3 add.commute add_0 int_eq_iff len_gt_0 less_add_eq_less nat_less_iff)
  then have t0: "(m mod ((2::int) ^ LENGTH('a))) = m"
    by (metis a2 a3 n_less_equal_power_2 nat_add_left_cancel_less nat_mod_eq' real_of_nat_eq_numeral_power_cancel_iff trans_less_add2 zmod_int)
  have t1: "((min LENGTH('a::len) ((Suc (nat (i::int))) + LENGTH('c::len))) = ((Suc (nat i)) + LENGTH('c::len)))"
    using a1 a2 by presburger

  have "unat (x * (push_bit (unat (Word.Word m :: 'a::len word)) (Word.Word (1::int)::'a::len word)::'a::len word))
=  unat x * ((2::nat) ^ of_nat (nat (take_bit LENGTH('a::len) m))) mod (2::nat) ^ LENGTH('a)"
  proof-
    have "unat (x * (push_bit (unat (Word.Word m :: 'a::len word)) (Word.Word (1::int)::'a::len word)::'a::len word))
       =  unat x * unat ((2::'a word) ^ unat (word_of_int m::'a::len word)) mod (2::nat) ^ LENGTH('a)"
      using unat_word_ariths(2) by auto
    then have "unat (x * (push_bit (unat (Word.Word m :: 'a::len word)) (Word.Word (1::int)::'a::len word)::'a::len word))
            =  unat x * ((2::nat) ^ unat (word_of_int m ::'a::len word)) mod (2::nat) ^ LENGTH('a)"
      using unat_p2[of "unat (word_of_int m::'a::len word)"]
      by (smt (verit, del_insts) of_nat_inverse push_bit_eq_mult push_bit_of_nat unat_lt2p unat_of_nat word_arith_nat_mult)
    then show ?thesis
      using unsigned_of_int[of m, where 'b="'a"]
      by metis
  qed
  moreover have 
"unat (word_cat (smt_extract (nat i) (nat (0::int)) x :: 'b:: len word) (Word.Word (0::int):: 'c::len word) ::'a::len word) =
 ((take_bit ((Suc (nat i))+LENGTH('c::len)) (push_bit LENGTH('c::len) (unat x)))
 + take_bit LENGTH('a::len) 0) mod (2::nat) ^ LENGTH('a::len)"
  proof-
  have "unat (word_cat (smt_extract (nat i) (nat (0::int)) x :: 'b:: len word) (Word.Word (0::int):: 'c::len word) ::'a::len word) =
(take_bit LENGTH('a::len) (push_bit LENGTH('c::len) (unat (smt_extract (nat i) (nat (0::int)) x :: 'b:: len word)))
 + take_bit LENGTH('a::len) (unat (Word.Word (0::int)))) mod
  (2::nat) ^ LENGTH('a::len)"
    using unat_word_cat[of "(smt_extract (nat i) (nat (0::int)) x :: 'b:: len word)" "(Word.Word (0::int):: 'c::len word)"
, where 'c="'a"]
    using a2 by auto
  moreover have "nat (0::int) \<le> nat (i::int) \<and> nat i < size (x::'a::len word) \<and> LENGTH('b::len) = nat i + (1::nat) - nat (0::int) "
    by (metis a1 a2 diff_zero discrete le_add_same_cancel1 less_eq_nat.simps(1) nat_zero_as_int word_size)
  ultimately have "unat (word_cat (smt_extract (nat i) (nat (0::int)) x :: 'b:: len word) (Word.Word (0::int):: 'c::len word) ::'a::len word) =
 (take_bit LENGTH('a::len) (push_bit LENGTH('c::len) (drop_bit (nat (0::int)) (take_bit (Suc (nat i)) (unat x))))
 + take_bit LENGTH('a::len) (unat (Word.Word (0::int)))) mod
  (2::nat) ^ LENGTH('a::len)"
    using unat_smt_extract[of "nat 0" "nat i" x, where 'b="'b"] 
    by auto
  moreover have "(unat (Word.Word (0::int)::'c::len word)) = 0"
    by auto
ultimately have "unat (word_cat (smt_extract (nat i) (nat (0::int)) x :: 'b:: len word) (Word.Word (0::int):: 'c::len word) ::'a::len word) =
 (take_bit LENGTH('a::len) (push_bit LENGTH('c::len) (take_bit (Suc (nat i)) (unat x)))
 + take_bit LENGTH('a::len) 0) mod (2::nat) ^ LENGTH('a::len)"
  by auto
then have "unat (word_cat (smt_extract (nat i) (nat (0::int)) x :: 'b:: len word) (Word.Word (0::int):: 'c::len word) ::'a::len word) =
 (take_bit LENGTH('a::len) (take_bit ((Suc (nat i))+LENGTH('c::len)) (push_bit LENGTH('c::len) (unat x)))
 + take_bit LENGTH('a::len) 0) mod (2::nat) ^ LENGTH('a::len)"
  using push_bit_take_bit[of "LENGTH('c)" "Suc (nat i)"]
  by (simp add: take_bit_push_bit)
  moreover have "min (LENGTH('a::len)) ((Suc (nat i))+LENGTH('c::len)) = ((Suc (nat i))+LENGTH('c::len))"
    using a1 a2 by presburger
  ultimately show "unat (word_cat (smt_extract (nat i) (nat (0::int)) x :: 'b:: len word) (Word.Word (0::int):: 'c::len word) ::'a::len word) =
 ((take_bit ((Suc (nat i))+LENGTH('c::len)) (push_bit LENGTH('c::len) (unat x)))
 + take_bit LENGTH('a::len) 0) mod (2::nat) ^ LENGTH('a::len)"
    by (metis take_bit_take_bit)
qed

  moreover have "unat x * ((2::nat) ^ of_nat (nat (take_bit LENGTH('a::len) m))) mod (2::nat) ^ LENGTH('a)
= ((take_bit ((Suc (nat i))+LENGTH('c::len)) (push_bit LENGTH('c::len) (unat x)))
 + take_bit LENGTH('a::len) 0) mod (2::nat) ^ LENGTH('a::len)"
    apply (simp add: take_bit_eq_mod push_bit_eq_mult)
    apply (simp add: t0)
    using t1 a1 a2 a3 add.commute add_Suc mod_mod_trivial nat_int plus_1_eq_Suc power_Suc
    by metis
   

  ultimately show "(word_cat (smt_extract (nat i) (nat (0::int)) x :: 'b:: len word) (Word.Word (0::int):: 'c::len word) ::'a::len word) =
   x * (push_bit (unat (Word.Word m :: 'a::len word)) (Word.Word (1::int)::'a::len word)::'a::len word)"
    by (simp add: word_unat_eq_iff)
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
  apply (simp_all add: drop_bit_eq_div take_bit_eq_mod drop_bit_eq_div bit_or_iff mask_eq_exp_minus_1)
  using not_int_div_pow2[of "uint x" "nat j"]
  using not_int_rec[of "(uint x div (2::int) ^ nat j)"]
  by simp



lemma rewrite_bv_extract_not:
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
qed


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

  have t0: "unat (smt_extract (nat i) (nat j) (xor x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (xor (unat x) (unat y)))"
  proof-
    have "unat (smt_extract (nat i) (nat j) (xor x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (unat (xor x y)))"
      using unat_smt_extract[of "nat j" "nat i" "(xor x y)", where 'b="'b"]  
      by (metis Suc_as_int Suc_eq_plus1 a0 a1 a2 a3 int_nat_eq nat_diff_distrib' nat_int nat_mono not_less_eq_eq order_trans word_size)
    then show "unat (smt_extract (nat i) (nat j) (xor x y)::'b::len word) = drop_bit (nat j) (take_bit (Suc (nat i)) (xor (unat x) (unat y)))"
      using unsigned_xor_eq by metis
  qed
  moreover have "unat (xor ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
  = (xor (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    proof-
      have "unat (xor ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
        = (xor (unat ((smt_extract (nat i) (nat j) x)::'b::len word)) (unat ((smt_extract (nat i) (nat j) y)::'b::len word)))"
    using unsigned_xor_eq by blast
    moreover have " nat (j::int) \<le> nat (i::int) \<and> nat i < size (x::'a::len word) \<and> LENGTH('b::len) = nat i + (1::nat) - nat j "
      using a0 a1 a2 a3 by force
    moreover have "nat i < size (y::'a::len word)"
      by (metis a1 size_word.rep_eq)
    ultimately show t1: "unat (xor ((smt_extract (nat i) (nat j) x)::'b::len word) ((smt_extract (nat i) (nat j) y)::'b::len word))
    = (xor (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    using unat_smt_extract[of "nat j" "nat i" "x", where 'b="'b"]
    using unat_smt_extract[of "nat j" "nat i" "y", where 'b="'b"]
    by presburger
  qed
  moreover have  "drop_bit (nat j) (take_bit (Suc (nat i)) (xor (unat x) (unat y)))
  = (xor (drop_bit (nat j) (take_bit (Suc (nat i)) (unat x))) (drop_bit (nat j) (take_bit (Suc (nat i)) (unat y))))"
    by auto
  ultimately show "(smt_extract (nat i) (nat j) (xor x y)::'b::len word) =
   xor ((smt_extract (nat i) (nat j) x)::'b::len word) 
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