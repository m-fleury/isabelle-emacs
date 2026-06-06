theory CVC_Word
  imports "HOL-Library.Word" Word_Lib.More_Word "HOL-Library.Log_Nat" HOL.SMT_CVC
   "Word_Lib.Reversed_Bit_Lists"  "Alethe_Word_Reconstruction" 
begin



subsection \<open>Tool support\<close>

(*Additional definitions*)

definition smt_bit_word :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 1 word\<close>
  where "smt_bit_word a n = (if (bit a n) then (1::1 word) else (0::1 word))"

definition pow_2_word where "pow_2_word (TYPE('a)) y \<equiv> power (2::'a::len word) (nat y)"

(*Normalization*)

lemma [pow_2_word]:
  "power (2::'a::len word) w \<equiv> push_bit w (1::'a word)"
  unfolding pow_2_word_def by simp

named_theorems smt_word_len_evaluate \<open>\<close>

(*Speed up for commonly used bit-widths*)
lemma [smt_word_len_evaluate]:
  "len_of (a::8 itself) \<equiv> 8"
  "len_of (b::16 itself) \<equiv> 16"
  "len_of (c::32 itself) \<equiv> 32"
  "len_of (d::64 itself) \<equiv> 64"
  "len_of (e::128 itself) \<equiv> 128"
  by simp_all

lemmas [smt_word_len_evaluate] = eq_reflection[OF len_bit0] eq_reflection[OF len_bit1]
  eq_reflection[OF len_num0] eq_reflection[OF len_num1]

lemma Word_of_int:
  "Word.Word x \<equiv> of_int x"
  by simp

lemma word_odd_mult_eq_zero:
  fixes c a :: "'a::len word"
  assumes "odd c"
  shows "(c * a = 0) = (a = 0)"
proof
  assume a0: "c * a = 0"
  then have "odd (unat c)"
    by (metis unat_0 even_of_nat assms add.right_neutral word_arith_nat_add)
  then have "coprime ((2::nat) ^ LENGTH('a)) (unat c)"
    by simp
  moreover have "2 ^ LENGTH('a) dvd unat c * unat a"
  proof-
    have "(unat c * unat a) mod 2 ^ LENGTH('a) = 0"
      by (metis a0 unat_0 unat_word_ariths(2))
    then show ?thesis
      by (simp add: mod_eq_0_iff_dvd)
  qed
  ultimately have "2 ^ LENGTH('a) dvd unat a"
    by (metis coprime_dvd_mult_right_iff)
  then show "a = 0"
    using unsigned_less nat_dvd_not_less unat_eq_zero by blast
next
  assume "a = 0"
  thus "c * a = 0" by simp
qed

lemma [alethe_poly_simp_rel]:
  fixes x1::"'a::len word" and x2 y1 y2 cx cy
  shows "odd cx \<Longrightarrow> odd cy \<Longrightarrow> cx * (x1-x2) = cy * (y1-y2) \<longrightarrow> ((x1 = x2) = (y1 = y2))"
proof
  assume cx_odd: "odd cx"
  and cy_odd: "odd cy"
  and eq: "cx * (x1 - x2) = cy * (y1 - y2)"
  have "(x1 = x2) = (x1 - x2 = 0)" by simp
  also have "\<dots> = (cx * (x1 - x2) = 0)"
    using cx_odd by (simp add: word_odd_mult_eq_zero)
  also have "\<dots> = (cy * (y1 - y2) = 0)" using eq by simp
  also have "\<dots> = (y1 - y2 = 0)"
    using cy_odd by (simp add: word_odd_mult_eq_zero)
  also have "\<dots> = (y1 = y2)" by simp
  finally show "(x1 = x2) = (y1 = y2)" .
qed

(*
The following are formalizations of the resp. SMT-LIB definitions. They are mapped to the respective
operator.
*)

definition smtlib_bvshl :: \<open>'a::len word  \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word\<close> where "smtlib_bvshl s t = s * 2^(unat t)"
definition smtlib_bvlshr :: \<open>'a::len word  \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word\<close> where "smtlib_bvlshr s t = s div 2^(unat t)"
definition smtlib_bvashr :: \<open>'a::len word  \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word\<close>
  where "smtlib_bvashr s t = (if (smtlib_extract (int LENGTH('a)-1) (int LENGTH('a)-1) s = (0::1 word)) then smtlib_bvlshr s t else not (smtlib_bvlshr (not s) t))"

lemmas[cvc_evaluate_bv] = smtlib_bvshl_def smtlib_bvlshr_def
(*
The following lemmas are unfolded during normalization.
We tried a lot of different things to avoid this deep embedding but since external solvers can
generate bv terms freely in their proofs it is hard to make proof reconstruction work without this.
*)
lemma push_bit_lift:
 "push_bit k (w::'a::len word) \<equiv> (if (k \<ge> LENGTH('a::len)) then 0 else smtlib_bvshl w (word_of_int (int k)))"
  unfolding smtlib_bvshl_def atomize_eq
  apply (split if_split,rule conjI)
  subgoal by simp
  by (metis le_unat_uoi less_exp nat_le_linear of_int_of_nat_eq of_nat_inverse push_bit_eq_mult)

lemma pow2_push_bit_lift: "(2::'a::len word) ^ n \<equiv> (if n < (LENGTH('a)) then smtlib_bvshl 1 (word_of_int (int n)::'a::len word) else 0)"
  unfolding atomize_eq smtlib_bvshl_def unat_of_nat
  apply simp_all
  by (metis le_unat_uoi less_exp less_imp_le of_nat_inverse unat_of_nat)


lemma drop_bit_lift:
 "drop_bit k (w::'a::len word) \<equiv> (if (k \<ge> LENGTH('a::len)) then 0 else smtlib_bvlshr w (word_of_int (int k)))"
  unfolding smtlib_bvshl_def atomize_eq
  by (metis (no_types, lifting) drop_bit_eq_div drop_bit_word_beyond le_unat_uoi less_exp nat_le_linear of_int_of_nat_eq
      of_nat_inverse smtlib_bvlshr_def)

lemma take_bit_lift:
  "take_bit k (w::'a::len word) \<equiv> w - (if (k \<ge> LENGTH('a::len)) then 0 else smtlib_bvshl (smtlib_bvlshr w (word_of_int (int k))) (word_of_int (int k)))"
  using bits_ident drop_bit_word_beyond push_bit_word_beyond drop_bit_lift push_bit_lift
  by (smt (verit, ccfv_SIG) add.commute add_diff_cancel_right')



lemma smtlib_extract_msb_eq:
  fixes w :: "'a::len word"
  shows "(smtlib_extract (int (LENGTH('a) - 1)) (int (LENGTH('a) - 1)) w :: 1 word) = (if bit w (LENGTH('a) - 1) then 1 else 0)"
  unfolding smtlib_extract_def
  by (rule bit_word_eqI) (auto simp: bit_simps)

lemma signed_drop_bit_lift:
   "signed_drop_bit k (w::'a::len word) \<equiv>
    (if k \<ge> LENGTH('a)
     then (if bit w (LENGTH('a) - 1) then - 1 else 0)
     else smtlib_bvashr w (word_of_int (int k)))"
proof(rule eq_reflection, split if_split, rule conjI;rule impI)
  assume "LENGTH('a) \<le> k"
  then show "signed_drop_bit k w = (if bit w (LENGTH('a) - 1) then - 1 else 0)"
    by (simp add: signed_drop_bit_beyond)
next
  assume a0: "\<not> LENGTH('a) \<le> k"
  then have unat_k: "unat (word_of_int (int k) :: 'a word) = k"
    by (metis less_exp linorder_le_cases of_int_of_nat_eq of_nat_inverse order_le_less_trans)
  show "signed_drop_bit k w = smtlib_bvashr w (word_of_int (int k))"
  proof -
    have lshr: "\<And>v::'a::len word. smtlib_bvlshr v (word_of_int (int k)) = drop_bit k v"
  by (simp add: a0 drop_bit_lift)
      have msb_idx: "int LENGTH('a) - 1 = int (LENGTH('a) - 1)"
      using len_gt_0[where 'a='a] by linarith
    have msb: "(smtlib_extract (int LENGTH('a) - 1) (int LENGTH('a) - 1) w :: 1 word)
                 = (if bit w (LENGTH('a) - 1) then 1 else 0)"
      unfolding msb_idx by (rule smtlib_extract_msb_eq)
    show ?thesis
    proof (cases "bit w (LENGTH('a) - 1)")
      case True
      have "smtlib_bvashr w (word_of_int (int k)) = not (drop_bit k (not w))"
        unfolding smtlib_bvashr_def using msb True lshr by simp
      moreover have "signed_drop_bit k w = not (drop_bit k (not w))"
      proof (rule bit_word_eqI)
        fix n :: nat
        assume n: "n < LENGTH('a)"
        show "bit (signed_drop_bit k w) n = bit (not (drop_bit k (not w))) n"
        proof (cases "LENGTH('a) - k \<le> n")
          case ge: True
          hence kn: "\<not> k + n < LENGTH('a)" using a0 by linarith
          show ?thesis
            using True n ge kn
            by (auto simp: bit_signed_drop_bit_iff bit_not_iff bit_drop_bit_eq possible_bit_word
                     dest: bit_imp_possible_bit)
        next
          case lt: False
          hence kn: "k + n < LENGTH('a)" using a0 by linarith
          show ?thesis
            using n lt kn
            by (auto simp: bit_signed_drop_bit_iff bit_not_iff bit_drop_bit_eq possible_bit_word)
        qed
      qed
      ultimately show ?thesis by simp
    next
      case False
      have "smtlib_bvashr w (word_of_int (int k)) = drop_bit k w"
        unfolding smtlib_bvashr_def using msb False lshr by simp
      moreover have "signed_drop_bit k w = drop_bit k w"
      proof (rule bit_word_eqI)
        fix n :: nat
        assume n: "n < LENGTH('a)"
        show "bit (signed_drop_bit k w) n = bit (drop_bit k w) n"
        proof (cases "LENGTH('a) - k \<le> n")
          case ge: True
          hence kn: "\<not> k + n < LENGTH('a)" using a0 by linarith
          show ?thesis
            using False n ge kn
            by (auto simp: bit_signed_drop_bit_iff bit_drop_bit_eq possible_bit_word
                     dest: bit_imp_possible_bit)
        next
          case lt: False
          hence kn: "k + n < LENGTH('a)" using a0 by linarith
          show ?thesis
            using n lt kn
            by (auto simp: bit_signed_drop_bit_iff bit_drop_bit_eq possible_bit_word)
        qed
      qed
      ultimately show ?thesis by simp
    qed
  qed
qed

lemma smtlib_extract_eq_iff:
 fixes w :: "'a::len word"
 shows "(smtlib_extract (int i) (int i) w :: 1 word) = (if (bit w i) then 1 else 0)"
    unfolding smtlib_extract_def
    apply (rule bit_word_eqI)
    unfolding bit_slice_iff semiring_bit_operations_class.bit_take_bit_iff
    apply simp
    by (metis add.commute bit_imp_le_length diff_diff_cancel less_Suc_eq_le less_or_eq_imp_le nat_int
        of_nat_Suc)

lemma bit_lift:
    "bit (x::'a::len word) i \<equiv>
     (if i < LENGTH('a) then smtlib_extract (int i) (int i) x = (1::1 word) else False)"
    apply (rule eq_reflection)
    apply (subst smtlib_extract_eq_iff)
    apply (auto dest: bit_imp_le_length)
    done

lemma slice_lift:
  fixes x::"'a::len word"
  shows "slice n x \<equiv> smtlib_extract (int LENGTH('a)) (int n) x"
  unfolding smt_extract_def
  by (simp add: smtlib_extract_def take_bit_word_beyond_length_eq)

definition set_bit_lift :: \<open>int \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word\<close> where
  "set_bit_lift x = set_bit (nat x)"
lemma set_bit_lift:
  "set_bit x \<equiv> set_bit_lift (int x)"
  unfolding set_bit_lift_def by simp

definition unset_bit_lift :: \<open>int \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word\<close> where
  "unset_bit_lift x = unset_bit (nat x)"
lemma unset_bit_lift:
  "unset_bit x \<equiv> unset_bit_lift (int x)"
  unfolding unset_bit_lift_def by simp

definition flip_bit_lift :: \<open>int \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word\<close> where
  "flip_bit_lift x = flip_bit (nat x)"



(*TODO: support the non lifted case*)
(*lemma take_bit_lift:
  "take_bit n x \<equiv> (x - push_bit_lift (int n) (drop_bit_lift (int n) x))"
  sorry
*)


definition len_of_lift :: "'a::len0 itself \<Rightarrow> int" where
"len_of_lift(TYPE('a::len0)) = int(len_of(TYPE('a)))"
lemma length_lift: "(LENGTH('a)) \<equiv> nat(len_of_lift(TYPE('a::len0)))"
  unfolding len_of_lift_def by simp


definition word_rotr_lift :: "int \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
"word_rotr_lift j w = word_rotr (nat j) w"
lemma word_rotr_lift:
 "word_rotr j w \<equiv> word_rotr_lift (int j) w"
  unfolding word_rotr_lift_def by simp
lemma [nat_normalized_input]:
  "word_rotr (nat j) w \<equiv> word_rotr_lift j w"
  unfolding word_rotr_lift_def by simp


definition word_rotl_lift :: "int \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word" where
"word_rotl_lift j w = word_rotl (nat j) w"
lemma word_rotl_lift:
 "word_rotl j w \<equiv> word_rotl_lift (int j) w"
  unfolding word_rotl_lift_def by simp
lemma [nat_normalized_input]:
  "word_rotr (nat j) w \<equiv> word_rotr_lift j w"
  unfolding word_rotr_lift_def by simp


definition smt_extract_lift :: "int \<Rightarrow> int \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word" where
"smt_extract_lift j i w  = smt_extract (nat j) (nat i) w"
lemma smt_extract_lift_old:
 "smt_extract j i w \<equiv> smt_extract_lift (int j) (int i) w"
  unfolding smt_extract_lift_def by simp
lemma [nat_normalized_input]:
  "smt_extract (nat j) (nat i) w \<equiv> smt_extract_lift j i w"
  unfolding smt_extract_lift_def by simp

lemma [nat_normalized_input]:
  "ucast w \<equiv> Word.cast w"
   by simp

lemma word_numeral_lift:
"(numeral (x::num)::'a::len word) \<equiv> word_of_int (take_bit LENGTH('a::len) (numeral x))"
  using num_abs_bintr[of x]
  by auto

definition slice_lift :: \<open>int \<Rightarrow> 'a :: len word \<Rightarrow> 'b :: len word\<close> where
 \<open>slice_lift j w = slice (nat j) w\<close>

lemmas [simplify_translation] = len_bit0 len_bit1 len_num1 take_bit_numeral_numeral option.case take_bit_num_simps pred_numeral_simps option.case
of_int_numeral

ML \<open>
val nat_native_ops_tab =
[
  ("Bit_Operations.semiring_bit_operations_class.take_bit",@{thms take_bit_lift}),
  ("Bit_Operations.semiring_bit_operations_class.drop_bit",@{thms drop_bit_lift}),
  ("Bit_Operations.semiring_bit_operations_class.push_bit", @{thms push_bit_lift}),
  ("Word.signed_drop_bit", @{thms signed_drop_bit_lift}),
  ("Word.word_rotr", @{thms word_rotr_lift}),
  ("Word.word_rotl", @{thms word_rotl_lift}),
  ("Word.slice", @{thms slice_lift}),
  ("Bit_Operations.semiring_bits_class.bit", @{thms bit_lift})

]

(*TODO Hanna: That should work with NONE*)
val simplify_norm_table = [
  ("Type_Length.len0_class.len_of", (NONE, ( @{thms smt_word_len_evaluate},SOME @{thms smt_word_len_evaluate}))),
  ("Word.slice",(SOME (K true), ([],SOME @{thms slice_lift}))) ,
  ("Num.numeral_class.numeral",(SOME Word_Lib.is_overflow_bv_const, (@{thms word_numeral_lift},SOME @{thms drop_bit_int_code}))),
  ("Nat.semiring_1_class.of_nat",(SOME (K true), ([],SOME @{thms of_nat_numeral } ))), (*TODO: Add condition to only evaluate if *)
  ("Pure.type",(NONE,([],SOME []))),
  ("Power.power_class.power",(NONE,([@{thm pow2_push_bit_lift}],NONE)))
]

val _ = fold SMT_Normalize.add_nat_native_ops_tab (nat_native_ops_tab)
    |> Theory.setup o Context.theory_map

val _ = fold SMT_Normalize.add_simplify_ops_tab (simplify_norm_table)
    |> Theory.setup o Context.theory_map
\<close>


declare  [[smt_cvc_alethe = true]]

ML_file\<open>Tools/smt_word_cvc5.ML\<close>

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

lemma smt_extract_bit: "k < size (x::'a::len word) \<Longrightarrow> (smt_extract k k x::1 word) = (if bit x k then 1 else 0)" 
  apply (simp add: bang_eq)
  unfolding smt_extract_def
  apply (simp_all add: nth_slice bit_take_bit_iff)
  using bit_1_iff by fastforce

lemma bit_smt_extract2: "k < size (x::'a::len word) \<Longrightarrow> bit x k = ((smt_extract k k x) = (1::1 word))" 
  using smt_extract_bit
  by (metis zero_neq_one)

lemma bit_smt_extract2': "k < size (x::'a::len word) \<Longrightarrow> bit x k = (slice k (take_bit (Suc k) x) = (1::1 word))" 
  unfolding smt_extract_def bit_smt_extract2
  by simp

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


lemma word_repeat_word_cat2:
  fixes n :: "'a :: len word"
  assumes \<open>LENGTH('b::len) = i * LENGTH('a)\<close> \<open>i > 1\<close>
    \<open>LENGTH('c::len) = (i-1) * LENGTH('a)\<close>
  shows \<open>(word_repeat i n :: 'b word) = word_cat (n :: 'a word) (word_repeat (i-1) n :: 'c word)\<close>
  apply (cases i)
  subgoal
    using assms(2) by force
  using assms(1,2,3) word_repeat_word_cat
  by (metis diff_Suc_1 word_size zero_less_diff)




definition smt_repeat :: "int \<Rightarrow> 'a::len word \<Rightarrow> 'b::len word" where
  \<open>smt_repeat i x = (if i = 0 then (ucast x::'b::len word) else word_repeat (nat i) x)\<close>

lemma smt_repeat_zero:                                                                                           
  "smt_repeat 0 x = ucast x"                                                                                            
  unfolding smt_repeat_def by simp
                                                                                                                       
lemma smt_repeat_numeral:                                                                                               
  "smt_repeat (numeral n) x = word_repeat (numeral n) x"
  unfolding smt_repeat_def by simp                                                                                      
                  
lemma smt_repeat_Suc:                                                                                                   
  "smt_repeat (Suc i) x = word_repeat (Suc i) x"
  unfolding smt_repeat_def
  by (metis nat_int.Rep_inverse semiring_char_0_class.of_nat_neq_0)   

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
  \<open>is_pow2 i \<equiv> (i > 0) \<and> (and i (i-1) = 0)\<close>

lemmas cvc_evaluate_bv = is_pow2_def

lemma is_pow2_imp_eq_2_pow:
  fixes n :: int
  assumes "is_pow2 n"
  shows "n = 2 ^ (floorlog 2 (nat n) - 1)"
proof -
  from assms have n_pos: "0 < n" and and_zero: "and n (n - 1) = 0"
    unfolding is_pow2_def by auto
  have nn_pos: "0 < nat n" using n_pos by simp
  have base: "(1::nat) < 2" by simp

  define k where "k = floorlog 2 (nat n) - 1"

  have fl_pos: "0 < floorlog 2 (nat n)"
    using nn_pos
    by (metis base bot_nat_0.not_eq_extremum floorlog_bounds less_one power_0)
  hence fl_succ: "floorlog 2 (nat n) = Suc k" by (simp add: k_def)

  from floorlog_bounds[OF nn_pos base]
  have lo_nat: "(2::nat) ^ k \<le> nat n"
   and hi_nat: "nat n < (2::nat) ^ Suc k"
    using fl_succ by auto

  from lo_nat n_pos have lo: "(2::int) ^ k \<le> n"
    by simp
  from hi_nat n_pos have hi: "n < (2::int) ^ Suc k"
    using nat_less_numeral_power_cancel_iff by blast
  define r where "r = n - 2 ^ k"
  have r_nn: "0 \<le> r" using lo r_def by simp
  have r_lt: "r < 2 ^ k" using hi r_def by simp
  have n_eq: "n = 2 ^ k + r" using r_def by simp

  have two_k_nz: "(2::int) ^ k \<noteq> 0" by simp

  have "r = 0"
  proof (rule ccontr)
    assume "r \<noteq> 0"
    with r_nn have r_pos: "0 < r" by simp

    have bit_n: "bit n k"
    proof -
      have "n div 2 ^ k = (2 ^ k + r) div 2 ^ k" using n_eq by simp
      also have "\<dots> = r div 2 ^ k + 1"
        by (rule div_add_self1[OF two_k_nz])
      also have "r div 2 ^ k = 0" using r_nn r_lt by simp
      finally have "n div 2 ^ k = 1" by simp
      thus ?thesis by (simp add: bit_iff_odd_drop_bit drop_bit_eq_div)
    qed

    have bit_nm1: "bit (n - 1) k"
    proof -
      have "n - 1 = 2 ^ k + (r - 1)" using n_eq by simp
      moreover have "0 \<le> r - 1" using r_pos by simp
      moreover have "r - 1 < 2 ^ k" using r_lt by simp
      ultimately have "(n - 1) div 2 ^ k = 1"
        by (simp add: div_pos_geq)
      thus ?thesis by (simp add: bit_iff_odd_drop_bit drop_bit_eq_div)
    qed

    have "bit (and n (n - 1)) k"
      using bit_n bit_nm1 by (simp add: bit_and_iff)
    with and_zero show False by simp
  qed

  with n_eq show "n = 2 ^ (floorlog 2 (nat n) - 1)"
    using k_def by simp
qed


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

lemma and_word_cat_smt_extract_base:
"(and (x::'a::len word) c) = (and (smt_extract (LENGTH('a) - 1) 0 (x::'a::len word)) (smt_extract (LENGTH('a) - 1) 0 (c::'a::len word)))"
  using smt_extract_identity[of x] smt_extract_identity[of c]
  by simp

lemma xor_word_cat_smt_extract_base:
"(xor (smt_extract (LENGTH('a) - 1) 0 (x::'a::len word)) (smt_extract (LENGTH('a) - 1) 0 (c::'a::len word))) = A \<Longrightarrow> (xor (x::'a::len word) c) = A"
  using smt_extract_identity[of x] smt_extract_identity[of c]
  by simp

lemma or_word_cat_smt_extract_base:
"(or (x::'a::len word) c) = (or (smt_extract (LENGTH('a) - 1) 0 (x::'a::len word)) (smt_extract (LENGTH('a) - 1) 0 (c::'a::len word)))"
  using smt_extract_identity[of x] smt_extract_identity[of c]
  by simp

lemma and_word_cat_smt_extract_step: 
"i \<le> j \<Longrightarrow> j + 1 \<le> k \<Longrightarrow> i \<ge> 0 \<Longrightarrow> k < size x 
 \<Longrightarrow> LENGTH('b::len) = k + (1::nat) - Suc j
 \<Longrightarrow> LENGTH('d::len) = k + (1::nat) - i
 \<Longrightarrow> LENGTH('c::len) = j + (1::nat) - i
\<Longrightarrow>
 (and ((smt_extract k i (x::'a::len word))::'d::len word) ((smt_extract k i (c::'a::len word))::'d::len word))
 =
 word_cat
  (and ((smt_extract k (j+1) x)::'b::len word) ((smt_extract k (j+1) c)::'b::len word))
  (and ((smt_extract j i x)::'c::len word) ((smt_extract j i c)::'c::len word))
"
  apply (simp add: bang_eq)
  apply (rule allI)+
  subgoal for n
    apply (simp add: bit_word_cat_iff bit_and_iff)
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


lemma bitwise_slicing_smt_extract_identity:
"nat a = LENGTH('a) -1 \<Longrightarrow> smt_extract (nat a) (nat 0) (x::'a::len word) = x"
  by (simp add: smt_extract_def slice_id) 


(* lift_shiftla v0__ 1 XOR (27::8 word) =
    word_cat (smt_extract (nat (7::int)) (nat (5::int)) (27::8 word) XOR smt_extract (nat (7::int)) (nat (5::int)) (lift_shiftla v0__ 1))
     (word_cat (smt_extract (nat (4::int)) (nat (3::int)) (27::8 word) XOR smt_extract (nat (4::int)) (nat (3::int)) (lift_shiftla v0__ 1))
       (word_cat (smt_extract (nat (2::int)) (nat (2::int)) (27::8 word) XOR smt_extract (nat (2::int)) (nat (2::int)) (lift_shiftla v0__ 1))
         (smt_extract (nat 1) (nat 0) (27::8 word) XOR smt_extract (nat 1) (nat 0) (lift_shiftla v0__ 1))))*)

lemma xor_word_cat_smt_extract_step: 
"(nat i) \<le> (nat j) \<Longrightarrow> (nat j) + 1 \<le> (nat k) \<Longrightarrow> (nat i) \<ge> 0 \<Longrightarrow> (nat k) < size x 
 \<Longrightarrow> LENGTH('b::len) = (nat k) + (1::nat) - (nat j')
 \<Longrightarrow> LENGTH('d::len) = (nat k) + (1::nat) - (nat i)
 \<Longrightarrow> LENGTH('c::len) = (nat j) + (1::nat) - (nat i)
 \<Longrightarrow> j' = j + 1 \<Longrightarrow> k \<ge>0 \<Longrightarrow> j\<ge>0 \<Longrightarrow> i \<ge>0 
\<Longrightarrow>

 word_cat
  (xor ((smt_extract (nat k) (nat j') x)::'b::len word) ((smt_extract (nat k) (nat j') c)::'b::len word))
  (xor ((smt_extract (nat j) (nat i) x)::'c::len word) ((smt_extract (nat j) (nat i) c)::'c::len word))
=(xor ((smt_extract (nat k) (nat i) (x::'a::len word))::'d::len word) ((smt_extract (nat k) (nat i) (c::'a::len word))::'d::len word))
"
  apply (simp add: bang_eq)
  apply (rule allI)+
  subgoal for n
    apply (simp add: bit_word_cat_iff bit_xor_iff)
    apply (cases "n < Suc (nat j) - (nat i)")
    apply (simp_all add: bit_smt_extract bit_word_cat_iff)
     apply (cases "n < Suc (nat k) - (nat i)")
      apply simp_all
     apply (cases "n + nat i < Suc (nat j)")
    apply simp_all
     apply (cases "n + nat i < Suc (nat k) ")
      apply simp_all
    using less_diff_conv apply blast
    apply (cases "n < Suc (nat k) - nat i")
    apply simp_all
    apply (cases "n + nat i - Suc (nat j) + nat (j + 1) < Suc (nat k)")
     apply simp_all
    apply (cases "n + nat i - Suc (nat j) < Suc (nat k) - nat (j + 1)")
      apply simp_all
    apply (metis Suc_nat_eq_nat_zadd1 add.commute less_diff_conv linordered_semidom_class.add_diff_inverse)
     apply (cases "n + nat i < Suc (nat k)")
      apply simp_all
    using le_diff_conv linorder_not_less apply blast
    by (metis Suc_nat_eq_nat_zadd1 add.commute bot_nat_0.not_eq_extremum le_add_diff_inverse less_Suc_eq_le linorder_not_less nat_le_linear
      zero_less_diff)
    done


named_theorems rbl_xor_temp \<open>xor_def.\<close>
(*TODO: duplicate*)
named_theorems arith_simp_cvc5 \<open>xor_def.\<close>

lemmas [arith_simp_cvc5,arith_mult_poly_norm_cvc5] =
    Groups.monoid_mult_class.mult_1_right Nat.mult_Suc_right
    Nat.mult_0_right Nat.add_Suc_right Groups.monoid_add_class.add.right_neutral
    Num.numeral_2_eq_2 Nat.One_nat_def Num.numeral_2_eq_2 Nat.One_nat_def
    Nat.Suc_less_eq Nat.zero_less_Suc minus_nat.diff_0 Nat.diff_Suc_Suc Nat.le0

named_theorems bv_aci_simp

ML_file\<open>Tools/CVC_Word/alethe_replay_bv_methods.ML\<close>
ML\<open>

open Word_Lib


fun mk_unary n t =
  let val T = fastype_of t
  in Const (n, T --> T) $ t end

val mk_nat = HOLogic.mk_number \<^typ>\<open>nat\<close>

fun mk_lassoc f t ts = fold (fn u1 => fn u2 => f u2 u1) ts t

fun mk_extract i j u =
 let
  val I = HOLogic.mk_number \<^typ>\<open>nat\<close> i
  val J = HOLogic.mk_number \<^typ>\<open>nat\<close> j

  val T = fastype_of u
  val TU = i - j + 1 |> Word_Lib.mk_wordT
 in
   Const (\<^const_name>\<open>Word.smt_extract\<close>, @{typ nat} --> @{typ nat} --> T --> TU) $ I $ J $ u
 end

fun mk_extract_from_terms i j u =
 let
  val I = HOLogic.dest_number i |> snd
  val J = HOLogic.dest_number j |> snd

  val T = fastype_of u
  val TU = I - J + 1 |> Word_Lib.mk_wordT
 in
   Const (\<^const_name>\<open>Word.smt_extract\<close>, @{typ nat} --> @{typ nat} --> T --> TU) $ i $ j $ u
 end

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

fun
  (*All operators from the FixedSizeBitVectors theory are in smt_word_cvc5*)
  (*| bv_term_parser (SMTLIB.S [SMTLIB.Sym "_",SMTLIB.Sym "extract", SMTLIB.Num i, SMTLIB.Num j],[t])
       = SOME (mk_extract i j t)*)

  (*SMT-LIB3 Syntax. First, we wanted to automatically map SMT-LIB2 syntax to this in preprocessing
    but decided against it in case that there are changes other than syntax*)
  (*TODO: Move into its own parser*)
  bv_term_parser (SMTLIB.Sym "@bbT", xs) = (*old name, now bbterm eventually remove*)
        SOME ((Const ("Reversed_Bit_Lists.of_bl", \<^typ>\<open>HOL.bool list\<close> --> mk_wordT(length xs))) 
        $ ((Const (\<^const_name>\<open>List.rev\<close>, \<^typ>\<open>HOL.bool list\<close> -->  \<^typ>\<open>HOL.bool list\<close>)) $ (HOLogic.mk_list \<^typ>\<open>bool\<close> xs)))
  | bv_term_parser (SMTLIB.Sym "@bbterm", xs) =
        SOME ((Const ("Reversed_Bit_Lists.of_bl", \<^typ>\<open>HOL.bool list\<close> --> mk_wordT(length xs))) 
        $ ((Const (\<^const_name>\<open>List.rev\<close>, \<^typ>\<open>HOL.bool list\<close> -->  \<^typ>\<open>HOL.bool list\<close>)) $ (HOLogic.mk_list \<^typ>\<open>bool\<close> xs)))
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "@bitOf", SMTLIB.Num i], [t]) =
      SOME (Const (\<^const_name>\<open>semiring_bits_class.bit\<close>, (fastype_of t) --> HOLogic.natT --> \<^typ>\<open>HOL.bool\<close>)
      $ t $ (HOLogic.mk_nat i))
 | bv_term_parser (SMTLIB.Sym "@bvsize", [t1]) =
      SOME (Const ( \<^const_name>\<open>of_nat\<close>,  \<^typ>\<open>Nat.nat\<close> -->  \<^typ>\<open>Int.int\<close>) $ (Const (\<^const_name>\<open>size\<close>, dummyT --> \<^typ>\<open>Nat.nat\<close>) $ t1))
 | bv_term_parser (SMTLIB.Sym "@bv", [int,base]) = (*TODO: Can get rid of case distinction now*)
     let
     (*There is one special case that is caught here, that is if the base is the size of another bitvector *)
    (* val _ = @{print}("int",int)
     val _ = @{print}("base",base)*)
     val ty = Word_Lib.mk_wordT (snd (HOLogic.dest_number base))
        val num = snd (HOLogic.dest_number int)
     (* in
        SOME (HOLogic.mk_number ty num)
      end*)
 in
        SOME (SMT_Word_cvc5.mk_bv_from_int_base int base) (* SOME (Const  (\<^const_name>\<open>Word.Word\<close>,\<^typ>\<open>Int.int\<close>--> dummyT) $ int)*) (*TODO: Use ty*)
      end
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
      SOME (HOLogic.mk_number \<^typ>\<open>32 word\<close> 32)
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
      SOME (Const (\<^const_name>\<open>of_nat\<close>, \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Int.int\<close> ) $ (@{term "(-)::nat \<Rightarrow> nat \<Rightarrow> nat"} $ (Const (\<^const_name>\<open>Log_Nat.floorlog\<close>, \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Nat.nat\<close>)
         $ t2' $ t1') $ @{term "1::nat"}))
     end
  | bv_term_parser (SMTLIB.Sym "int.ispow2", [t1]) =
      SOME (Const (\<^const_name>\<open>CVC_Word.is_pow2\<close>,\<^typ>\<open>Int.int\<close> --> \<^typ>\<open>bool\<close>) $ t1)
  | bv_term_parser (SMTLIB.Sym "int.pow2", [t1]) =
    let
         val T1 = fastype_of t1
         val t1' = (Const (\<^const_name>\<open>nat\<close>, T1 --> \<^typ>\<open>Nat.nat\<close>) $ t1)
         val t2' = HOLogic.mk_number \<^typ>\<open>Nat.nat\<close> 2
        
     in
      SOME (Const (\<^const_name>\<open>of_nat\<close>, \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Int.int\<close> ) $ (Const (\<^const_name>\<open>power\<close>, \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Nat.nat\<close> --> \<^typ>\<open>Nat.nat\<close>)
         $ t2' $ t1'))
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
      SOME (Const (\<^const_name>\<open>CVC_Word.smt_repeat\<close>,\<^typ>\<open>Int.int\<close>--> T2 --> dummyT) $ t1 $ t2)
    end
  | bv_term_parser (SMTLIB.S [SMTLIB.Sym "_", SMTLIB.Sym "repeat", SMTLIB.Num i], [t2]) =

    let
      val T2 = fastype_of t2
      val bw = Word_Lib.dest_wordT T2
      val i' = HOLogic.mk_number @{typ "int"} i
      val T = Word_Lib.mk_wordT(i * bw)
    in
      SOME (Const (\<^const_name>\<open>CVC_Word.smt_repeat\<close>,\<^typ>\<open>Int.int\<close>--> T2 --> T) $ i' $ t2)
    end
  | bv_term_parser (SMTLIB.Sym "rotate_left", [t1, t2]) =
    let
      val T2 = fastype_of t2
    in
      SOME (Const (\<^const_name>\<open>word_rotl_lift\<close>, \<^typ>\<open>Int.int\<close> --> T2 --> T2) $ t1 $ t2)
    end
  | bv_term_parser (SMTLIB.Sym "rotate_right", [t1,t2]) =
    let
      val T2 = fastype_of t2
    in
      SOME (Const (\<^const_name>\<open>word_rotr_lift\<close>, \<^typ>\<open>Int.int\<close> --> T2 --> T2) $ t1 $ t2)
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
  
  | bv_term_parser (SMTLIB.Sym "sum_length",[ts]) =
      SOME (Const (\<^const_name>\<open>temp_sum_length\<close>, dummyT -->dummyT) $ ts)
  | bv_term_parser (SMTLIB.Sym "list_length_0",[ts]) =
      SOME (Const (\<^const_name>\<open>list_length_0'\<close>, dummyT -->dummyT) $ ts)
  | bv_term_parser (SMTLIB.Sym "length",[ts]) =
      SOME (Const (\<^const_name>\<open>of_nat\<close>, dummyT -->dummyT) $ (Const (\<^const_name>\<open>size\<close>, dummyT -->dummyT) $ ts))

  | bv_term_parser (SMTLIB.Sym "smt_concat", [t]) = 
      SOME (Const (\<^const_name>\<open>concat_smt2\<close>, dummyT -->dummyT) $ t)
  | bv_term_parser (SMTLIB.Sym "bvsdiv", [t1,t2]) = (*TODO*)
      SOME (HOLogic.mk_binop \<^const_name>\<open>Rings.divide\<close> (mk_unary \<^const_name>\<open>unsigned\<close> t1, mk_unary \<^const_name>\<open>unsigned\<close> t2))
 | bv_term_parser (SMTLIB.Sym "bvudiv", [t1,t2]) =
      SOME (HOLogic.mk_binop \<^const_name>\<open>smt_udiv\<close> (t1, t2)) (*TODO: What about the case whre t2 is 0? SMTLIB semantics says it should be mask *)

  | bv_term_parser (SMTLIB.S[SMTLIB.Sym "_", SMTLIB.Sym "@bit_of",SMTLIB.Num num], [t1]) = 
    let
      val T1 = fastype_of t1
      val t2 = HOLogic.mk_number @{typ nat} num

    in
      SOME (Const (\<^const_name>\<open>bit\<close>, T1 --> @{typ nat} --> @{typ bool}) $ t1 $ t2)
   end
 

  | bv_term_parser (SMTLIB.Num n, _) = NONE (*(ignore (@{print} ("n=", n)); NONE)*)
  | bv_term_parser xs = (NONE)

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Proof.add_term_parser bv_term_parser))
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
 fun smtlib_logic "z3" ts _ =
    (*if exists (Term.exists_type (Term.exists_subtype is_wordT)) ts then SOME [""] else NONE*)
    if exists (Term.exists_type (Term.exists_subtype is_wordT)) ts then SOME (SMT_Translate.NO_LOGIC) else NONE

  | smtlib_logic "verit" _ _ = NONE
  | smtlib_logic _ ts _ =
    if exists (Term.exists_type (Term.exists_subtype is_wordT)) ts 
    then SOME (SMT_Translate.SL { fixedSizeBitVectors=true, real=true, set=true }) else NONE
    (*if exists (Term.exists_type (Term.exists_subtype is_wordT)) ts then SOME ["AUFBVLIRA"] else NONE*)

 val smtlibC = SMTLIB_Interface.bvsmtlibC

 fun index2 s i j = "(_ " ^ s ^ " " ^ string_of_int i ^ " " ^ string_of_int j ^ ")"

 fun remove_cast (Const ("Int.nat", _) $ x) = x |
     remove_cast x = x

 fun add_word_fun f (t, n) =
  let val (m, _) = Term.dest_Const t
  in SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const t, K (f m n)) end
  
 fun mk_extract c i j ts = Term.list_comb (Const c, HOLogic.mk_number @{typ nat} i :: mk_nat j :: ts)
                                                      
 fun extract m n (U as (Type(_,[_,Type(_,[_,Type(_,[Tx,T])])]))) [i,j,x] =
(
  (case (try (snd o HOLogic.dest_number o remove_cast) i, (*Interesting HOLogic.dest_nat instead of this does not work*)
         try (snd o HOLogic.dest_number o remove_cast) j,
         try dest_wordT Tx,
         try dest_wordT T) of
   (SOME i', SOME j', SOME Tx', SOME T') =>
    let
      val k = i' - j' + 1
      val U' = @{typ "nat"} --> @{typ "nat"} --> Tx --> T
    in
     if j' <= i' andalso k = T' andalso i' < Tx'
     then SOME (index2 n i' j', 1, [x], mk_extract (m, U') i' j')
     else NONE
    end |
   _ => NONE)) |
 extract _ _ _ _ = ( NONE)

val setup_builtins =
  add_word_fun extract
    (\<^term>\<open>smt_extract :: _ \<Rightarrow> _ \<Rightarrow> 'a::len word \<Rightarrow> _\<close>, "extract") 

val _ = Theory.setup (Context.theory_map (
  SMTLIB_Interface.add_logic (1, smtlib_logic) #>
  setup_builtins))
\<close>


lemma [cvc_ListOp_neutral]:
 "cvc_isListOp (ListOp (semiring_bit_operations_class.and) (-1::'a::len word))"
 "cvc_isListOp (ListOp (semiring_bit_operations_class.xor) (0::'a::len word))"
  by auto

lemma [cvc_list_right_transfer_op]:
"cvc_list_right xor (y::'a::len word) (ListVar (xs::'a::len word list)) = xor y (foldr xor xs 0)"
  using cvc_list_right_transfer_neutral1[of xor 0 y _] cvc_ListOp_neutral
  by simp


lemma [cvc_list_both_transfer_op]:
"cvc_list_both xor (Word.Word 0)  (ListVar (xs::'a::len word list)) (ListVar (ys::'a::len word list))
 = foldr xor xs (foldr xor ys (Word.Word 0) )"
  using cvc_list_both_transfer[of xor 0 xs ys] cvc_ListOp_neutral
  by simp

definition word_cat_rbl_right :: "'a::len word \<Rightarrow> bool list list \<Rightarrow> 'c::len itself \<Rightarrow> 'b::len word" where
"word_cat_rbl_right x ys _ = (word_cat x (of_bl (concat ys) :: 'c word) :: 'b word)"

definition word_cat_rbl_left :: "bool list list \<Rightarrow> 'a::len word \<Rightarrow> 'c::len itself \<Rightarrow> 'b::len word" where
"word_cat_rbl_left xs y _ = (word_cat (of_bl (concat xs) :: 'c word) y :: 'b word)"

fun word_cat_length :: "bool list list \<Rightarrow> int" where
  "word_cat_length [] = 0"
| "word_cat_length (x#xs) = length x + word_cat_length xs"

lemma word_cat_rbl_right_eq:
"word_cat_rbl_right x ys TYPE('c::len) = (word_cat x (of_bl (concat ys) :: 'c::len word) :: 'b::len word)"
  by (simp add: word_cat_rbl_right_def)


lemma word_cat_rbl_right_comm:
    fixes x :: "'a::len word" and y :: "'b::len word" and zs :: "bool list list"
    assumes d: "LENGTH('b) + LENGTH('c) = LENGTH('d)"
        and e: "LENGTH('a) + LENGTH('d) = LENGTH('e)"
        and f: "LENGTH('a) + LENGTH('b) = LENGTH('f)"
      shows
      "(word_cat x (word_cat_rbl_right y zs TYPE('c::len) :: 'd::len word) :: 'e::len word) =
       (word_cat_rbl_right (word_cat x y :: 'f::len word) zs TYPE('c) :: 'e::len word)"
  proof (rule bit_word_eqI)
    fix n :: nat
    assume n_lt: "n < LENGTH('e::len)"
    show "bit (word_cat x (word_cat_rbl_right y zs TYPE('c) :: 'd::len word) :: 'e::len word) n =
          bit (word_cat_rbl_right (word_cat x y :: 'f::len word) zs TYPE('c) :: 'e::len word) n"
    proof (cases "n < LENGTH('c::len)")
      case True
      then show ?thesis
        using n_lt d
        by (simp add: word_cat_rbl_right_def bit_word_cat_iff)
    next
      case c_le: False
      show ?thesis
      proof (cases "n < LENGTH('d::len)")
        case True
        with c_le n_lt d
        show ?thesis
          apply (simp add: word_cat_rbl_right_def bit_word_cat_iff)
          apply (cases "n - LENGTH('c) < LENGTH('b)")
           apply simp_all
          using f by auto
      next
        case False
        with c_le n_lt d e f
        show ?thesis
          apply (simp add: word_cat_rbl_right_def bit_word_cat_iff)
          apply (cases "n - LENGTH('c) < LENGTH('b)")
           apply simp_all
          by (metis add.commute add.left_commute diff_is_0_eq len_gt_0 less_diff_conv2 linorder_linear)
      qed
    qed
  qed


lemma foldr_word_and_pullout:
  fixes a b :: "'a::len word"
  shows "foldr (and::'a word \<Rightarrow> _ \<Rightarrow> _) xs (and a b) = and a (foldr and xs b)"
  by (induction xs) (simp_all add: word_bw_lcs)

lemma cvc_nary_op_fold_butlast:
  "xs \<noteq> [] \<Longrightarrow> cvc_nary_op_fold op xs = foldr op (butlast xs) (last xs)"
proof (induction xs)
  case Nil then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (cases xs) (simp_all add: Cons.IH)
qed
lemma rewrite_bv_xor_ones_lemma: "foldr xor xs (not a) = not (foldr xor xs a)"
  apply (induction xs)
  by simp_all

end