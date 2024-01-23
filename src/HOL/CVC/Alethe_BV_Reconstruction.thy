theory Alethe_BV_Reconstruction
  imports "Word_Lib.Reversed_Bit_Lists" SMT_CVC_Util
begin

declare[[show_sorts]]
declare[[show_types]]

(* Note: These lemmas will partly or completely disappear once SMT.thy is able to import List.thy *)
(* Therefore, these are not separated or organized well for now *)
named_theorems bv_reconstruction_lists 
named_theorems bv_reconstruction_list_funs
named_theorems bv_reconstruction_length 
named_theorems word_var_rbl_list
named_theorems bv_reconstruction_const
named_theorems bv_reconstruction_const_test
named_theorems word_plus_rbl_bvadd_fun
named_theorems word_plus_rbl_bvadd
named_theorems word_minus_rbl_bvneg_fun
named_theorems word_minus_rbl_bvneg 
named_theorems word_mult_rbl_bvmult_fun
named_theorems rbl_bvult_fun
named_theorems evaluate_bv_cvc5 \<open>Lemmas to resolve evaluate rewrite steps \<close>

named_theorems word_and_rbl_bvand \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_or_rbl_bvor \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_xor_rbl_bvxor \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_notxor_rbl_bvxnor \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_not_rbl_bvnot \<open>Theorems to reconstruct bitblasting of a bvand term.\<close>
named_theorems word_plus_rbl_bvadd_fun2 \<open>Theorems to reconstruct bitblasting of a bvadd term.\<close>

named_theorems word_mult_rbl_bvmult \<open>Theorems to reconstruct bitblasting of a bvmult term.\<close>

named_theorems word_less_rbl_bvult \<open>Theorems to reconstruct bitblasting of a bvult term.\<close>

named_theorems rbl_bvequal_fun \<open>Theorems to reconstruct bitblasting of a bvequal term.\<close>
named_theorems word_equal_rbl_bvequal \<open>Theorems to reconstruct bitblasting of a bvequal term.\<close>

named_theorems rbl_extract_fun \<open>Theorems to reconstruct bitblasting of a extract term.\<close>
named_theorems rbl_extract \<open>Theorems to reconstruct bitblasting of a extract term.\<close>

named_theorems rbl_concat \<open>Theorems to reconstruct bitblasting of a contract term.\<close>


lemma [bv_reconstruction_lists]:
  "[0..<Suc j] = [0..<j] @ [j]"
  "[x] @ xs = x # xs"
  "[] @ [x] = [x]"
  "hd (x # xs) = x"
  by auto

lemmas [bv_reconstruction_lists] = List.upt.simps(1) List.append.simps append_Cons append_Nil
                                   List.list.map List.rev.simps List.list.size(3-4)
                                   list.sel

lemmas [bv_reconstruction_list_funs] = drop.drop_Nil drop_Suc_Cons drop_0 List.rev.simps
takefill_Suc_Cons[of False] takefill.Z[of False] takefill_Suc_Nil[of False] take_Suc_Cons take_0 of_bl_False
nth_Cons_0 nth_Cons_Suc

lemma [bv_reconstruction_list_funs]:
"map2 f [] [] = []"
"map2 f (x#xs) (y#ys) = (f x y) # map2 f xs ys"
  by auto

lemmas [bv_reconstruction_length] = len_num0 len_num1 len_bit0 len_bit1


(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast variable ------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

lemma of_bl_rev_map_bits[word_var_rbl_list]:
  shows "(a :: 'a :: len word) = of_bl (rev (map (bit a) [0..<LENGTH('a)]))"
  using to_bl_unfold
  by (metis word_bl.Rep_inverse')


(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast constant ------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

lemma rbl_const[bv_reconstruction_const]:
  shows "to_bl a = rev xs \<Longrightarrow> LENGTH('a) = length xs \<Longrightarrow> (a :: 'a :: len word) = of_bl (rev xs)"
  by (simp add: to_bl_use_of_bl)

lemmas [bv_reconstruction_const_test] = to_bl_numeral bin_to_bl_def Reversed_Bit_Lists.bin_to_bl_aux.Suc
Num.Suc_eq_numeral bin_to_bl_aux.Z not_is_unit_0 bin_last_numeral_simps
Reversed_Bit_Lists.to_bl_0 List.replicate.replicate_Suc List.replicate.replicate_0

(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast bvadd ---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

fun bvadd_carry :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" where
[word_plus_rbl_bvadd_fun]: "bvadd_carry [] [] = False" |
[word_plus_rbl_bvadd_fun]: "bvadd_carry (x#xs) (y#ys) = ((x \<and> y) \<or> ((x [+] y) \<and> bvadd_carry xs ys))"

fun bvadd :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list" where
[word_plus_rbl_bvadd_fun]: "bvadd [] [] _ _ = []" |
[word_plus_rbl_bvadd_fun]: "bvadd (x#xs) (y#ys) xs' ys' = (((x [+] y) [+] bvadd_carry xs' ys')) # bvadd xs ys (x#xs') (y#ys')"

fun bvadd3 :: "bool list \<Rightarrow> bool list \<Rightarrow> bool \<Rightarrow> bool list" where
"bvadd3 [] [] _ = []" |
"bvadd3 (x#xs) (y#ys) carry = (((x [+] y) [+] carry)) # bvadd3 xs ys ((x \<and> y) \<or> ((x [+] y) \<and> carry))"

lemma bvadd_bvadd3: "length xs = length ys \<Longrightarrow> bvadd xs ys [] [] = bvadd3 xs ys False"
proof-
  assume "length xs = length ys"
  moreover have  "length xs = length ys \<Longrightarrow> length xs' = length ys' \<Longrightarrow>
        bvadd xs ys xs' ys' = bvadd3 xs ys (bvadd_carry xs' ys')" for xs' ys'
  apply (induction xs arbitrary:  ys xs' ys')
   apply simp
  subgoal for x xs ys xs' ys'
  apply (cases ys)
    by simp_all
  done
  ultimately show ?thesis
    by simp
qed

lemma h1:
  "\<And>bina binb. bvadd3 (rev (bin_to_bl n bina)) (rev (bin_to_bl n binb)) carry =
    rev (bin_to_bl n (bina + binb + of_bool carry))"
  apply (unfold bin_to_bl_def)
  apply (induct n arbitrary: carry)
   apply simp
  apply clarsimp
  apply (case_tac bina rule: bin_exhaust)
  apply (case_tac binb rule: bin_exhaust)
  apply (case_tac b)
   apply (case_tac [!] "ba")
  unfolding bin_to_bl_aux_alt
     apply (auto simp: rbl_succ xor_simps)
      apply (simp_all add: ac_simps div_add1_eq)
done

lemma word_add_bvadd3:
  "to_bl v = vbl \<Longrightarrow> to_bl w = wbl \<Longrightarrow>
    to_bl (v + w) = rev (bvadd3 (rev vbl) (rev wbl) False)"
  apply transfer
  apply (drule sym)
  apply (drule sym)
  subgoal for v vbl w wbl
    using h1[of "LENGTH('a)" v w False]
    apply simp
    done
  done

lemma word_add_bvadd[word_plus_rbl_bvadd]:
"length xs = LENGTH('a) \<Longrightarrow> length xs = length ys \<Longrightarrow> 
  (of_bl (rev xs)::'a::len word) + (of_bl (rev ys))
 = (of_bl (rev (bvadd xs ys [] [])) :: 'a::len word)" for i j xs
  by (metis bvadd_bvadd3 rev_rev_ident takefill_same word_add_bvadd3 word_bl.Rep_inverse' word_rev_tf)

(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast bvneg ---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

(*TODO: This could also be solved with this equivalence: (bvneg a) \<equiv> (bvadd (bvnot a) 1):*)

fun bvneg_carry :: "bool list \<Rightarrow> bool" where
[word_minus_rbl_bvneg_fun]: "bvneg_carry [] = True" |
[word_minus_rbl_bvneg_fun]: "bvneg_carry (x#xs) = ((\<not>x \<and> False) \<or> ((\<not>x [+] False) \<and> bvneg_carry xs))"

fun bvneg :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" where
[word_minus_rbl_bvneg_fun]: "bvneg [] _ = []" |
[word_minus_rbl_bvneg_fun]: "bvneg (x#xs) xs' = ((\<not>x [+] False) [+] bvneg_carry xs') # bvneg xs (x#xs')"

fun bvneg3 :: "bool list \<Rightarrow> bool \<Rightarrow> bool list" where
"bvneg3 [] _ = []" |
"bvneg3 (x#xs) carry = (((\<not>x [+] False) [+] carry)) # bvneg3 xs ((\<not>x \<and> False) \<or> ((\<not>x [+] False) \<and> carry))"


lemma bvneg_bvneg3: "bvneg xs [] = bvneg3 xs True"
proof-
  have  "bvneg xs xs' = bvneg3 xs (bvneg_carry xs')" for xs'
   apply (induction xs arbitrary: xs')
    by (simp_all add: xor_simps)
  then show ?thesis
    by simp
qed

lemma h2:
  "\<And>bina. bvneg3 (rev (bin_to_bl n bina)) carry =
    rev (bin_to_bl n (-bina - 1 + of_bool carry))"
  apply (unfold bin_to_bl_def)
  apply (induct n arbitrary: carry)
   apply simp
  apply clarsimp
  apply (case_tac bina rule: bin_exhaust)
  apply (case_tac b)
  unfolding bin_to_bl_aux_alt
     apply (auto simp: rbl_succ xor_simps)
     apply (simp_all add: ac_simps div_add1_eq)
  apply (metis add.left_commute bin_rest_NOT mult_2 mult_2_right nonzero_mult_div_cancel_left not_int_def uminus_add_conv_diff verit_sum_simplify zero_neq_numeral)
  apply (simp add: minus_diff_commute)
  apply (metis is_num_normalize(8) mult_2 mult_2_right nonzero_mult_div_cancel_left zero_neq_numeral)
  using bin_rest_NOT not_int_def by auto

lemma word_neg_bvneg3:
  "to_bl v = vbl \<Longrightarrow> to_bl (-v) = rev (bvneg3 (rev vbl) True)"
  apply transfer
  apply (drule sym)
  apply (drule sym)
  subgoal for v vbl
    using h2[of "LENGTH('a)" v True]
    unfolding zero_neq_one_class.of_bool_eq(2)
    by simp
  done

lemma word_neg_bvneg[word_minus_rbl_bvneg]:
"length xs = LENGTH('a) \<Longrightarrow>
-(of_bl (rev xs)::'a::len word) = (of_bl (rev (bvneg xs [])) :: 'a::len word)" for i j xs
  by (metis bvneg_bvneg3 rev_rev_ident takefill_same to_bl_use_of_bl word_neg_bvneg3 word_rev_tf)



(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast bvmult---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)


(*TODO: This will change after the summer on the cvc5 side, so it is not worth putting more work in*)
definition sh :: "bool list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"sh xs ys i j = (if j\<le>i then xs ! (i-j) \<and> ys ! j else False)"

(*
function res_mult :: "bool list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" and
carry_mult :: "bool list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
[word_mult_rbl_bvmult_fun]: "res_mult xs ys i 0 = sh xs ys i 0" |
[word_mult_rbl_bvmult_fun]: "res_mult xs ys 0 j = sh xs ys 0 0" |
[word_mult_rbl_bvmult_fun]: "res_mult xs ys i (Suc j) = (res_mult xs ys i j) [+] (sh xs ys i (Suc j)) [+] carry_mult xs ys i (Suc j)" |
[word_mult_rbl_bvmult_fun]: "carry_mult xs ys i 0 = False" |
[word_mult_rbl_bvmult_fun]: "carry_mult xs ys (Suc i) (Suc j) = 
(if j < i then (res_mult xs ys i j \<and> sh xs ys i (Suc j)
 \<or> ((res_mult xs ys i j [+] sh xs ys i (Suc j)) \<and> carry_mult xs ys i (Suc j))) else False)"
  sorry  

lemma[word_mult_rbl_bvmult]:
"length xs = LENGTH('a) \<Longrightarrow> length xs = length ys \<Longrightarrow> 
  (of_bl (rev xs)::'a::len word) * of_bl (rev ys) =
   of_bl (map (\<lambda>i. res_mult xs ys (length xs-1) i) (rev [0..<length xs]))"
  sorry*)

lemma
"length xs = LENGTH('a) \<Longrightarrow> length xs = length ys \<Longrightarrow> 
  (of_bl (rev xs)::'a::len word) * of_bl (rev ys) =
   of_bl (rev (rbl_mult xs ys))"
proof-
  assume a0: "length xs = LENGTH('a)" and a1: "length xs = length ys"
  have "to_bl (of_bl (rev (xs::bool list))::'a::len word) = rev xs"
    by (simp add: a0 to_bl_use_of_bl)
  moreover have "to_bl (of_bl (rev (ys::bool list))::'a::len word) = rev ys"
    using a0 a1 to_bl_use_of_bl by fastforce
  ultimately have "to_bl (of_bl (rev xs) * of_bl (rev ys)::'a::len word) = rev (rbl_mult xs ys)"
    using word_mult_rbl[of "of_bl (rev xs)::'a word" "rev xs" "of_bl (rev ys)" "rev ys"]
    by simp
  then have "(of_bl (to_bl (of_bl (rev xs) * of_bl (rev ys)::'a::len word))::'a::len word)
 = of_bl (rev (rbl_mult xs ys))"
    by presburger
  then show ?thesis
    by simp
qed

(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast bvult ---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

fun bvult :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" where
 [rbl_bvult_fun]: "bvult [] [] = False" |
 [rbl_bvult_fun]: "bvult [] x = undefined" |
 [rbl_bvult_fun]: "bvult y [] = undefined" |
 [rbl_bvult_fun]: "bvult (x#xs) (y#ys) = (((x \<longleftrightarrow> y) \<and> bvult xs ys) \<or> (\<not> x \<and> y))"

lemma word_less_rbl_bvult_aux:
  assumes "a < 2^k" "Suc k \<le> LENGTH('a)" 
  shows "((2::'a word)^(k::nat) \<le> (2::'a word)^k + (a::'a::len word))"
proof-
  have "unat ((2::'a::len word) ^ k) \<le> 2^k"
    by (simp add: Suc_le_lessD assms(2))
  moreover have "unat a < 2^k"
    by (meson assms(1) less_2p_is_upper_bits_unset unat_less_power)
  moreover have "(2::nat)^k + 2^k = 2^(Suc k)"
    by simp
  moreover have "2^(Suc k) \<le> (2::nat) ^ LENGTH('a::len)"
    using assms(2) linordered_semidom_class.power_increasing_iff[of "2::nat" "Suc k" "LENGTH('a)"]
    by simp
  ultimately have "(unat ((2::'a::len word) ^ k) + unat a) < (2::nat) ^ LENGTH('a::len)"
    by linarith
  then have "unat ((2::'a word) ^ (k::nat)) \<le> (unat ((2::'a::len word) ^ k) + unat a) mod (2::nat) ^ LENGTH('a::len)"
    by simp
  then have "unat ((2::'a word) ^ (k::nat)) \<le> unat ((2::'a word) ^ k + (a::'a::len word))"
    using unat_word_ariths(1)[of "(2::'a word)^k" a]
    by simp
  then show ?thesis
    unfolding word_le_nat_alt
    by simp
qed

lemma word_less_rbl_bvult2[word_less_rbl_bvult]:
 "length xs = length ys \<Longrightarrow>
 length xs \<le> LENGTH('a) \<Longrightarrow>
 (of_bl xs::'a::len word) < (of_bl ys) = bvult xs (ys::bool list)"
  sorry

(*proof (induction xs arbitrary: ys)
  fix ys
  show "length [] = length ys \<Longrightarrow> length [] \<le> LENGTH('a) \<Longrightarrow> (of_bl [] < of_bl ys) = bvult [] ys"
    by simp
next
  fix x::bool and xss ys::"bool list"
  assume IH: "(\<And>yss::bool list. length xss = length yss \<Longrightarrow>
                                 length xss \<le> LENGTH('a) \<Longrightarrow>
                                 ((of_bl xss::'a::len word) < of_bl yss) = bvult xss yss)"
     and a0: "length (x # xss) = length (ys::bool list)"
     and a1: "length (x # xss) \<le> LENGTH('a)"
  then obtain y yss where t0: "ys = y # yss" 
    by (metis Suc_length_conv a0)

  have t1: "of_bl xss < (2::'a word) ^ length yss + of_bl yss"
  proof-
    have "Suc (length xss) = length ys"
      using a0 by fastforce
    moreover have "length ys \<le> LENGTH('a)"
      using a0 a1 by force
    moreover have "length yss = length xss"
      using t0 a0 by force
    ultimately have "(2::'a::len word) ^ length xss \<le> (2::'a::len word) ^ length yss + of_bl yss"
      by (simp add: word_less_rbl_bvult_aux less_eq_Suc_le of_bl_length_less)
    then show ?thesis
      using a1 dual_order.strict_trans1 of_bl_length_less by fastforce
  qed

  have IH': "bvult xss yss = ((of_bl xss::'a::len word) < of_bl yss)"
    using IH[of yss] a0 a1 t0
    by (metis Suc_inject length_Cons less_eq_Suc_le linorder_linear linorder_not_less)
  have "((of_bl (x # xss)::'a::len word) < of_bl (y#yss)) = bvult (x # xss) (y#yss)"
    apply (cases x)
     apply (case_tac [!] y)
       apply (simp_all add: IH')
      subgoal
        using word_plus_strict_mono_right[of "of_bl xss" "of_bl yss" "(2::'a word) ^ length xss"]
        by (metis Suc_inject Suc_le_lessD a0 a1 word_less_rbl_bvult_aux length_Cons of_bl_length plus_le_left_cancel_nowrap t0)
      subgoal
        sorry
      subgoal
        using t1 by blast
      done
  then show "((of_bl (x # xss)::'a::len word) < of_bl ys) = bvult (x # xss) ys"
    using t0 by auto
qed *)


(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast bvule ---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

(*TODO: HOW IS THIS DEFINED, I ASSUME LIKE THIS? *)
fun bvule :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" where
 [rbl_bvult_fun]: "bvule [] [] = True" |
 [rbl_bvult_fun]: "bvule [] x = undefined" |
 [rbl_bvult_fun]: "bvule y [] = undefined" |
 [rbl_bvult_fun]: "bvule (x#xs) (y#ys) = (((x \<longleftrightarrow> y) \<and> bvule xs ys) \<or> (\<not> x \<and> y))"



(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast Extract--------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

definition rbl_extract :: "nat \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> bool list" where
 [rbl_extract_fun]: "rbl_extract j i xs
   = rev (drop i (takefill False (length xs) (take (Suc j) (rev xs))))"

lemma slice_take_bit_rbl:
"LENGTH('a) = length xs \<Longrightarrow> Suc i < length xs  \<Longrightarrow> j \<le> i
\<Longrightarrow> (slice j (take_bit (Suc i) (of_bl xs::'a::len word)) ::'b::len word)
= of_bl (take (length xs - j) (rev (takefill False LENGTH('a::len) (rev (drop (length xs - Suc i) xs)))))"
  using of_bl_drop_eq_take_bit slice_take word_rev_tf
  by (metis diff_diff_cancel nless_le)
(*TODO:
lemma smt_extract_rbl_extract[rbl_extract]:
"j \<le> i \<Longrightarrow> Suc i < length xs \<Longrightarrow> length xs = LENGTH('a)
\<Longrightarrow> Word.smt_extract j i (of_bl xs::'a::len word)
= (of_bl (rbl_extract i j xs) :: 'b::len word)" for i j xs
  unfolding Word.smt_extract_def rbl_extract_def
  using slice_take_bit_rbl
  by (metis length_takefill rev_drop take_rev)*)

(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast concat---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

lemma [rbl_concat]: "LENGTH('a) = length xs
\<Longrightarrow> LENGTH('b) = length ys
\<Longrightarrow> LENGTH('a) + LENGTH('b) = LENGTH('c)
\<Longrightarrow> word_cat (of_bl (rev xs)::'a::len word) (of_bl (rev ys)::'b::len word)
 = (of_bl (rev (ys @ xs))::'c::len word)"
  unfolding word_cat_bl
  using word_bl.Abs_inverse[of "rev xs", where 'a="'a"]
        word_bl.Abs_inverse[of "rev ys", where 'a="'b"]
  by simp




(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast equal ---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

fun bvequal :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" where
 [rbl_bvequal_fun]: "bvequal [] [] = True" |
 [rbl_bvequal_fun]: "bvequal [] x = undefined" |
 [rbl_bvequal_fun]: "bvequal y [] = undefined" |
 [rbl_bvequal_fun]: "bvequal (x#xs) (y#ys) = (x = y \<and> bvequal xs ys)"


lemma t2: "length (x # xs) \<le> LENGTH('a) \<Longrightarrow> LENGTH('a) > Suc (0::nat) \<Longrightarrow>
(unat (of_bl (rev (xs::bool list))::'a::len word) * unat (2::'a::len word) < (2::nat) ^ LENGTH('a::len))"
proof-
  assume a0: "length (x # xs) \<le> LENGTH('a)"  "LENGTH('a) > Suc (0::nat)"
    have "(unat (of_bl (rev (xs::bool list))::'a::len word)) < 2^length xs"
      using unat_of_bl_length[of "rev xs"] by simp
    moreover have "unat (2::'a::len word) = 2"
      using a0 by simp
    moreover have "2^length xs * 2 \<le> (2::nat) ^ LENGTH('a::len)"
      by (metis a0(1) a0(2) list.size(4) numeral_2_eq_2 one_le_numeral power_Suc0_right power_add power_increasing)
    ultimately show ?thesis 
      by (metis dual_order.strict_trans1 len_gt_0 len_of_finite_2_def mult_less_mono1)
  qed

lemma [word_equal_rbl_bvequal]:
"length xs \<le> LENGTH('a)  \<Longrightarrow> length xs = length ys \<Longrightarrow> LENGTH('a) > Suc (0::nat)
 \<Longrightarrow> ((of_bl (rev xs)::'a::len word) = of_bl (rev ys)) = bvequal xs ys"
  apply (induction xs arbitrary: ys)
   apply simp
proof-
  fix x::bool and xs ys :: "bool list"
  assume IH: "(\<And>ys::bool list.
           length xs \<le> LENGTH('a) \<Longrightarrow>
           length xs = length ys \<Longrightarrow>  LENGTH('a) > Suc (0::nat) \<Longrightarrow>
          ((of_bl (rev xs)::'a::len word) = of_bl (rev ys)) = bvequal xs ys)"
  assume a0: "length (x # xs) \<le> LENGTH('a)" "length (x # xs) = length ys" "LENGTH('a) > Suc (0::nat)"
  obtain y yss where t0: "ys = y#yss"
    by (metis a0(2) length_0_conv neq_Nil_conv)

  have [simp]: "unat (2::'a word) \<noteq> 0"
    using a0 by simp

  have t1: "((of_bl (rev xs)::'a::len word) = of_bl (rev yss)) = bvequal xs yss"
    by (metis IH Suc_leD a0 length_Cons length_tl list.sel(3) t0)

  have t2: "(unat (of_bl (rev (xs::bool list))::'a::len word) * unat (2::'a::len word) < (2::nat) ^ LENGTH('a::len))"
  proof-
    have "(unat (of_bl (rev (xs::bool list))::'a::len word)) < 2^length xs"
      using unat_of_bl_length[of "rev xs"] by simp
    moreover have "unat (2::'a::len word) = 2"
      using a0(3) by simp
    moreover have "2^length xs * 2 \<le> (2::nat) ^ LENGTH('a::len)"
      by (metis a0(1) a0(2) list.size(4) numeral_2_eq_2 one_le_numeral power_Suc0_right power_add power_increasing)
    ultimately show ?thesis 
      by (metis dual_order.strict_trans1 len_gt_0 len_of_finite_2_def mult_less_mono1)
  qed
  then have t3: "(unat ((of_bl (rev (xs::bool list))::'a::len word) * (2::'a::len word)))
               = (unat (of_bl (rev (xs::bool list))::'a::len word) * unat (2::'a::len word))"
    by (metis unat_mult_lem)


  have t2_2: "(unat (of_bl (rev (yss::bool list))::'a::len word) * unat (2::'a::len word) < (2::nat) ^ LENGTH('a::len))"
  proof-
    have "(unat (of_bl (rev (yss::bool list))::'a::len word)) < 2^length yss"
      using unat_of_bl_length[of "rev yss"] by simp
    moreover have "unat (2::'a::len word) = 2"
      using a0 by simp
    moreover have "2^length yss * 2 \<le> (2::nat) ^ LENGTH('a::len)"
      by (metis Suc_1 Suc_eq_plus1 a0(1) a0(2) leI length_Cons mult.commute not_add_less1 power_Suc power_increasing t0)
    ultimately show ?thesis 
      by (metis dual_order.strict_trans1 len_gt_0 len_of_finite_2_def mult_less_mono1)
  qed
  then have t3_2: "(unat ((of_bl (rev (yss::bool list))::'a::len word) * (2::'a::len word)))
               = (unat (of_bl (rev (yss::bool list))::'a::len word) * unat (2::'a::len word))"
    by (metis unat_mult_lem)


  have t4: "of_bl (rev xs) * (2::'a::len word) + (1::'a::len word) \<noteq> (0::'a::len word)"
    using word_plus_one_nonzero[of "of_bl (rev xs) * (2::'a::len word)" 1]
    by (metis even_mult_iff even_numeral even_plus_one_iff even_zero)
  then have t5: "unat (of_bl (rev xs) * (2::'a word) + (1::'a word)) = unat (of_bl (rev xs) * (2::'a word)) + 1"
    using word_overflow_unat[of "(of_bl (rev xs)::'a::len word) * (2::'a word)"]
    by simp

  have "((of_bl (rev (x # xs))::'a::len word) = of_bl (rev (y#yss)))
       = bvequal (x # xs) (y#yss)"
    apply (cases x)
     apply simp_all
     apply (cases y)
      apply simp_all
      unfolding of_bl_append
        apply simp_all
      unfolding word_unat_eq_iff
      unfolding t3 t3_2 t5
        subgoal
          using mult_cancel2[of "unat (of_bl (rev (xs::bool list))::'a::len word)" "unat (2::'a word)"
                            "unat (of_bl (rev (yss::bool list))::'a::len word)"] t1 a0
          by simp
        subgoal
          by (metis even_mult_iff even_numeral even_plus_one_iff t3 t3_2 t5 word_unat.Rep_eqD)
        subgoal
          apply (cases y)
          using a0
      unfolding word_unat_eq_iff
      unfolding t3 t3_2 t5
       apply simp_all
      subgoal
        by (metis (no_types, opaque_lifting) mult_2_right odd_add odd_one power_Suc0_right t3 unat_power_lower word_eq_iff_unsigned)
      subgoal
        using t1 t3_2 by force
      done
    done
  then show "((of_bl (rev (x # xs))::'a::len word) = of_bl (rev ys)) = bvequal (x # xs) ys"
    using t0 by blast
qed


(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast and ------------------------------------------ *)
(* ---------------------------------------------------------------------------------------------- *)

lemma [word_and_rbl_bvand]:
"length xs = LENGTH('a)  \<Longrightarrow> length xs = length ys 
 \<Longrightarrow> (and (of_bl xs::'a::len word) ((of_bl ys)::'a::len word))
   = of_bl (map2 (\<and>) xs ys)"
proof-
  assume a0: "length xs = LENGTH('a)" "length xs = length ys"
  have "rev (to_bl (and (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
      = map2 (\<and>) (rev (to_bl (of_bl xs::'a::len word))) (rev (to_bl ((of_bl ys)::'a::len word)))"
    using rbl_word_and[of "(of_bl xs::'a::len word)" "((of_bl ys)::'a::len word)"]
    by simp
  moreover have "(to_bl (of_bl xs::'a::len word)) = xs"
    using word_bl.Abs_inverse a0(1) by blast
  moreover have "(to_bl (of_bl ys::'a::len word)) = ys"
    using word_bl.Abs_inverse a0
    by (simp add: to_bl_use_of_bl)
  ultimately have "rev (to_bl (and (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
      = map2 (\<and>) (rev xs) (rev ys)"
    by presburger
  then have "(to_bl (and (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
      = rev (map2 (\<and>) (rev xs) (rev ys))"
    using rev_swap by blast
  then have "(to_bl (and (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
      = (map2 (\<and>) xs ys)"
    by (simp add: a0(2) rev_map zip_rev)
  then have "(of_bl (to_bl (and (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))::'a::len word)
      = (of_bl (map2 (\<and>) xs ys))"
    by presburger
  then show "(and (of_bl xs::'a::len word) ((of_bl ys)::'a::len word))
      = (of_bl (map2 (\<and>) xs ys))"
    using word_bl.Abs_inverse by auto
qed


(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast bvor ----------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

lemma word_or_rbl_bvor2 [word_or_rbl_bvor]:
"length xs = LENGTH('a)  \<Longrightarrow> length xs = length ys 
 \<Longrightarrow> (or (of_bl xs::'a::len word) ((of_bl ys)::'a::len word))
   = of_bl (map2 (\<or>) xs ys)"
proof-
  assume a0: "length xs = LENGTH('a)" "length xs = length ys"
  have "rev (to_bl (or (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
      = map2 (\<or>) (rev (to_bl (of_bl xs::'a::len word))) (rev (to_bl ((of_bl ys)::'a::len word)))"
    using rbl_word_or[of "(of_bl xs::'a::len word)" "((of_bl ys)::'a::len word)"]
    by simp
  moreover have "(to_bl (of_bl xs::'a::len word)) = xs"
    using word_bl.Abs_inverse a0(1) by blast
  moreover have "(to_bl (of_bl ys::'a::len word)) = ys"
    using word_bl.Abs_inverse a0
    by (simp add: to_bl_use_of_bl)
  ultimately have "rev (to_bl (or (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
      = map2 (\<or>) (rev xs) (rev ys)"
    by presburger
  then have "(to_bl (or (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
      = rev (map2 (\<or>) (rev xs) (rev ys))"
    using rev_swap by blast
  then have "(to_bl (or (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
      = (map2 (\<or>) xs ys)"
    by (simp add: a0(2) rev_map zip_rev)
  then have "(of_bl (to_bl (or (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))::'a::len word)
      = (of_bl (map2 (\<or>) xs ys))"
    by presburger
  then show "(or (of_bl xs::'a::len word) ((of_bl ys)::'a::len word))
      = (of_bl (map2 (\<or>) xs ys))"
    using word_bl.Abs_inverse by auto
qed


(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast bvxor ---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

(*lemma word_xor_rbl_bvxor2 [word_xor_rbl_bvxor]:
"length xs = LENGTH('a)  \<Longrightarrow> length xs = length ys 
 \<Longrightarrow> (xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word))
   = of_bl (map2 (SMT.xor) xs ys)"
proof-
  assume a0: "length xs = LENGTH('a)" "length xs = length ys"
  have "rev (to_bl (xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
      = map2 (\<noteq>) (rev (to_bl (of_bl xs::'a::len word))) (rev (to_bl ((of_bl ys)::'a::len word)))"
    using rbl_word_xor[of "(of_bl xs::'a::len word)" "((of_bl ys)::'a::len word)"]
    by simp
  moreover have "(to_bl (of_bl xs::'a::len word)) = xs"
    using word_bl.Abs_inverse a0(1) by blast
  moreover have "(to_bl (of_bl ys::'a::len word)) = ys"
    using word_bl.Abs_inverse a0
    by (simp add: to_bl_use_of_bl)
  ultimately have "rev (to_bl (xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
      = map2 (\<noteq>) (rev xs) (rev ys)"
    by presburger
  then have "(to_bl (xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
      = rev (map2 (\<noteq>) (rev xs) (rev ys))"
    using rev_swap by blast
  then have "(to_bl (xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
      = (map2 (\<noteq>) xs ys)"
    by (simp add: a0(2) rev_map zip_rev)
  then have "(of_bl (to_bl (xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))::'a::len word)
      = (of_bl (map2 (\<noteq>) xs ys))"
    by presburger
  then show "(xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word))
      = (of_bl (map2 (SMT.xor) xs ys))"
    using word_bl.Abs_inverse xor_def
    by simp
qed*)


(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast bvnot ---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

lemma word_not_rbl_bvnot2 [word_not_rbl_bvnot]:
"length xs = LENGTH('a)  \<Longrightarrow> (not (of_bl xs::'a::len word)) = of_bl (map Not xs)"
proof-
  assume a0: "length xs = LENGTH('a)" 
  have "rev (to_bl (not (of_bl (xs::bool list)::'a::len word))) = map Not (rev (to_bl (of_bl xs ::'a::len word)))"
    using rbl_word_not[of "(of_bl xs::'a::len word)"]
    by simp
  moreover have "(to_bl (of_bl xs::'a::len word)) = xs"
    using word_bl.Abs_inverse a0(1) by blast
  ultimately have "rev (to_bl (not (of_bl (xs::bool list)::'a::len word))) = map Not (rev xs)"
    by presburger
  then have "(to_bl (not (of_bl (xs::bool list)::'a::len word))) = rev (map Not (rev xs))"
    using rev_swap by blast
  then have "(to_bl (not (of_bl (xs::bool list)::'a::len word))) = (map Not xs)"
    by (simp add: rev_map)
  then have "(of_bl (to_bl (not (of_bl (xs::bool list)::'a::len word)))::'a::len word) = of_bl (map Not xs)"
    by simp
  then show "(not (of_bl (xs::bool list)::'a::len word)) = of_bl (map Not xs)"
    by simp
qed


(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast bvxnor ---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

lemma map_Not_map2_diseq: "length xs = length ys \<Longrightarrow> (map Not (map2 (\<noteq>) xs ys)) = map2 (=) xs ys"
  apply (induction xs arbitrary: ys)
  by auto

(*lemma word_notxor_rbl_bvxnor [word_notxor_rbl_bvxnor]:
"length xs = LENGTH('a) \<Longrightarrow> length xs = length ys 
 \<Longrightarrow> (not (xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)))
   = of_bl (map2 (=) xs ys)"
proof-
  assume a0: "length xs = LENGTH('a)" "length xs = length ys"
  have "(xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)) = (of_bl (map2 (\<noteq>) xs ys)::'a::len word)"
    using word_xor_rbl_bvxor[of xs ys, where 'a="'a"] a0 xor_def by simp
  then have "not (xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)) = not (of_bl (map2 (\<noteq>) xs ys)::'a::len word)"
    by simp
  then have "not (xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)) = (of_bl (map Not (map2 (\<noteq>) xs ys))::'a::len word)"
    using word_not_rbl_bvnot[of "(map2 (\<noteq>) xs ys)"]
    using a0(1) a0(2) by auto
  then show "not (xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word)) = (of_bl (map2 (=) xs ys)::'a::len word)"
    using map_Not_map2_diseq[of xs ys] a0
    by presburger
qed*)

end