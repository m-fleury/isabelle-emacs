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
lemmas[bv_reconstruction_lists] = upt_Suc upt_0 (*upt_zero_numeral_unfold pred_numeral_simps BitM.simps*)

lemmas [bv_reconstruction_const_test] = to_bl_numeral bin_to_bl_def Reversed_Bit_Lists.bin_to_bl_aux.Suc
Num.Suc_eq_numeral bin_to_bl_aux.Z not_is_unit_0 bin_last_numeral_simps
Reversed_Bit_Lists.to_bl_0 List.replicate.replicate_Suc List.replicate.replicate_0

lemmas [bv_reconstruction_list_funs] = drop.drop_Nil drop_Suc_Cons drop_0
takefill_Suc_Cons[of False] takefill.Z[of False] takefill_Suc_Nil[of False] take_Suc_Cons take_0 of_bl_False
nth_Cons_0 nth_Cons_Suc

lemma [bv_reconstruction_list_funs]:
"map2 f [] [] = []"
"map2 f (x#xs) (y#ys) = (f x y) # map2 f xs ys"
  by auto


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


(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast bvadd ---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

fun bvadd_carry :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" where
[word_plus_rbl_bvadd_fun]: "bvadd_carry [] [] = False" |
                           "bvadd_carry _ [] = undefined" |
                           "bvadd_carry [] _ = undefined" |
[word_plus_rbl_bvadd_fun]: "bvadd_carry (x#xs) (y#ys) = ((x \<and> y) \<or> ((x \<noteq> y) \<and> bvadd_carry xs ys))"

fun bvadd :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list" where
[word_plus_rbl_bvadd_fun]: "bvadd [] [] _ _ = []" |
                           "bvadd _ [] _ _ = undefined" |
                           "bvadd [] _ _ _ = undefined" |
[word_plus_rbl_bvadd_fun]: "bvadd (x#xs) (y#ys) xs' ys' = (((x \<noteq> y) \<noteq> bvadd_carry xs' ys')) # bvadd xs ys (x#xs') (y#ys')"

lemma length_bvadd:
"length xs = length ys \<Longrightarrow> length (bvadd xs ys xs' ys') = length xs"
  by (induction xs ys arbitrary: xs' ys' rule: list_induct2) simp_all

lemma bvadd_bin:
"length xs' = length ys' \<Longrightarrow>
bvadd (rev (bin_to_bl n bina)) (rev (bin_to_bl n binb)) xs' ys' =
rev (bin_to_bl n (bina + binb + (if bvadd_carry xs' ys' then 1 else 0)))"
proof (induction n arbitrary: bina binb xs' ys')
  case 0 thus ?case by simp
next
  case (Suc n)
  then show ?case
    unfolding bin_to_bl_def
    apply (simp only: bin_to_bl_aux.simps)
    apply (case_tac bina rule: bin_exhaust)
    apply (case_tac binb rule: bin_exhaust)
    subgoal for _ ba _ bb
      unfolding bin_to_bl_aux_alt
      apply (case_tac [!] bb)
       apply (cases "bvadd_carry xs' ys'")
      subgoal
        apply (cases ba)
        apply (simp only: bin_to_bl_def zero_neq_one_class.of_bool_eq semiring_parity_class.odd_add bin_last_numeral_simps dvd_triv_left if_True simp_thms bvadd.simps append.right_neutral div_mult_self2 divmod_trivial)
          apply (simp add: add.commute)
         apply (metis arith_mult_dist_lemma(1) bin_rest_numeral_simps(6) one_eq_numeral_iff zdiv_mult_self zero_neq_numeral)
         apply (simp add: add.commute rbl_succ)
      done
    subgoal
      by (simp_all add: add.commute rbl_succ)
    subgoal
    apply (cases "bvadd_carry xs' ys'")
     by (simp_all add: add.commute rbl_succ)
    done
  done
qed

lemma word_add_bvadd_bin:
  "to_bl v = vbl \<Longrightarrow> to_bl w = wbl \<Longrightarrow>
    to_bl (v + w) = rev (bvadd (rev vbl) (rev wbl) [] [])"
  apply transfer
  using bvadd_bin[of "[]" "[]"]
  by auto


lemma word_add_bvadd[word_plus_rbl_bvadd]:
"length xs = LENGTH('a) \<Longrightarrow> length xs = length ys \<Longrightarrow>
  (of_bl (rev xs)::'a::len word) + (of_bl (rev ys))
 = (of_bl (rev (bvadd xs ys [] [])) :: 'a::len word)" for i j xs
  by (metis word_add_bvadd_bin rev_rev_ident takefill_same word_bl.Rep_inverse' word_rev_tf)

(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast bvneg ---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)

fun bvneg_carry :: "bool list \<Rightarrow> bool" where
[word_minus_rbl_bvneg_fun]: "bvneg_carry [] = True" |
[word_minus_rbl_bvneg_fun]: "bvneg_carry (x#xs) = ((\<not>x \<and> False) \<or> ((\<not>x \<noteq> False) \<and> bvneg_carry xs))"

fun bvneg :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list" where
[word_minus_rbl_bvneg_fun]: "bvneg [] _ = []" |
[word_minus_rbl_bvneg_fun]: "bvneg (x#xs) xs' = ((\<not>x \<noteq> False) \<noteq> bvneg_carry xs') # bvneg xs (x#xs')"

lemma bvneg_bin:
    "bvneg (rev (bin_to_bl n bina)) xs' =
     rev (bin_to_bl n (-bina - 1 + (if bvneg_carry xs' then 1 else 0)))"
    apply (induct n arbitrary: bina xs')
  subgoal by simp
  apply clarsimp
    apply (case_tac bina rule: bin_exhaust)
     unfolding bin_to_bl_aux_alt
     apply (auto simp: rbl_succ)
        apply (simp_all add: ac_simps div_add1_eq)
        apply (metis is_num_normalize(8) mult_2 mult_2_right nonzero_mult_div_cancel_left zero_neq_numeral)
  apply (metis bin_rest_NOT mult_2 mult_2_right nonzero_mult_div_cancel_left not_int_def zero_neq_numeral)
  using bin_rest_NOT not_int_def
  apply (metis ab_group_add_class.ab_diff_conv_add_uminus add.commute axxdiv2 comm_monoid_add_class.add_0 mult_2_right)
  by (simp add: minus_diff_commute)

lemma word_neg_bvneg_bin:
    "to_bl v = vbl \<Longrightarrow> to_bl (-v) = rev (bvneg (rev vbl) [])"
  apply transfer
  using bvneg_bin by auto

lemma word_neg_bvneg[word_minus_rbl_bvneg]:
"length xs = LENGTH('a) \<Longrightarrow>
-(of_bl (rev xs)::'a::len word) = (of_bl (rev (bvneg xs [])) :: 'a::len word)" for i j xs
      by (metis rev_rev_ident takefill_same to_bl_use_of_bl word_neg_bvneg_bin word_rev_tf)




(* ---------------------------------------------------------------------------------------------- *)
(* -------------------------------------- Bitblast bvmult---------------------------------------- *)
(* ---------------------------------------------------------------------------------------------- *)


definition sh :: "bool list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"sh xs ys i j = (if j\<le>i then xs ! (i-j) \<and> ys ! j else False)"

fun res_mult :: "bool list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" and
carry_mult :: "bool list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"res_mult xs ys i 0 = sh xs ys i 0" |
"res_mult xs ys 0 (Suc j) = sh xs ys 0 0" |
"res_mult xs ys (Suc i) (Suc j)
   = (((res_mult xs ys (Suc i) j) \<noteq> (sh xs ys (Suc i) (Suc j))) \<noteq> carry_mult xs ys (Suc i) (Suc j))" |
"carry_mult xs ys i 0 = False" |
"carry_mult xs ys 0 j = False" |
"carry_mult xs ys (Suc i) (Suc j) =
(if j < i then (res_mult xs ys i j \<and> sh xs ys i (Suc j)
 \<or> ((res_mult xs ys i j \<noteq> sh xs ys i (Suc j)) \<and> carry_mult xs ys i (Suc j))) else False)"


(*
Helpful function:
Get the carry bit at a specific position instead of on-the-fly calculation as in bvadd
or calculating it based on the length of the input lists as in bvadd_carry.

It's like a halfway point between res_mult and bvadd.
*)

fun bvadd_carry_idx :: "bool list \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> bool" where
    "bvadd_carry_idx _ _ 0 = False"
  | "bvadd_carry_idx xs ys (Suc i) =
       ((xs!i \<and> ys!i) \<or> ((xs!i \<noteq> ys!i) \<and> bvadd_carry_idx xs ys i))"

lemma bvadd_carry_bvadd_carry_idx:
  assumes "i \<le> length xs" "length xs = length ys"
  shows "bvadd_carry (rev (take i xs)) (rev (take i ys)) = bvadd_carry_idx xs ys i"
  using assms
  apply (induction i)
   apply simp
  by (simp add: take_Suc_conv_app_nth)


lemma bvadd_in_progress_nth:
  assumes "length xs = length ys" "length xs' = length ys'" " i < length xs"
  shows "bvadd xs ys xs' ys' ! i = ((xs!i \<noteq> ys!i) \<noteq> bvadd_carry (rev (take i xs) @ xs') (rev (take i ys) @ ys'))"
  using assms
proof (induction i arbitrary: xs ys xs' ys')
  fix xs ys xs' ys'::"bool list"
  assume IB: "length xs = length ys" "length xs' = length ys'" "0 < length xs"
  obtain a as where xs_def: "xs = a # as" using IB by (cases xs) auto
  obtain b bs where ys_def: "ys = b # bs" using IB by (cases ys) auto
  show "bvadd xs ys xs' ys' ! 0 = ((xs ! 0 \<noteq> ys ! 0) \<noteq> bvadd_carry (rev (take 0 xs) @ xs') (rev (take 0 ys) @ ys'))"
    by (simp add: xs_def ys_def)
next
    case (Suc i)
    obtain a as where xeq: "xs = a # as" using Suc by (cases xs) auto
    obtain b bs where yeq: "ys = b # bs" using Suc xeq by (cases ys) auto
    have lens: "length as = length bs" "length (a#xs') = length (b#ys')" "i < length as"
      using Suc.prems xeq yeq by auto
    have ih: "bvadd as bs (a#xs') (b#ys') ! i =
              ((as!i \<noteq> bs!i) \<noteq>
               bvadd_carry (rev (take i as) @ a#xs') (rev (take i bs) @ b#ys'))"
      using Suc.IH[OF lens] by simp
    have ta: "rev (take (Suc i) xs) @ xs' = rev (take i as) @ a # xs'"
      using xeq lens(3) by (simp add: take_Suc_conv_app_nth)
    have tb: "rev (take (Suc i) ys) @ ys' = rev (take i bs) @ b # ys'"
      using yeq lens(3) lens(1) by (simp add: take_Suc_conv_app_nth)
    show ?case using ih ta tb xeq yeq by simp
  qed

lemma bvadd_nth:
  assumes "length xs = length ys" "i < length xs"
  shows "bvadd xs ys [] [] ! i = ((xs!i \<noteq> ys!i) \<noteq> bvadd_carry_idx xs ys i)"
  using bvadd_in_progress_nth bvadd_carry_bvadd_carry_idx assms
  by simp


(*These helper functions make inductive reasoning about res_mult easier*)
fun sh_j where "sh_j xs ys j = (map (\<lambda>i. sh xs ys i j) [0..<length xs])"
fun res_j where "res_j xs ys j = (map (\<lambda>i. res_mult xs ys i j) [0..<length xs])"

lemma sh_j_nth:
  assumes "j < length ys" "length xs = length ys" "ys ! j"
  shows "sh_j xs ys j = replicate j False @ take (length xs - j) xs"
  unfolding sh_j.simps
  apply (rule nth_equalityI)
  subgoal using assms by simp
  by (auto simp: assms sh_def nth_append)

lemma sh_j_false: 
  assumes "j \<ge> i" "i < length xs"
  shows  "\<forall>k < Suc i. sh_j xs ys (Suc j) ! k = False"
  apply (rule allI,rule impI)
  unfolding sh_j.simps sh_def
  using assms
  by simp

lemma of_bl_sh_j_helper:
  assumes  "length xs = LENGTH('a)" "j < length ys" "length xs = length ys" "ys ! j"
  shows "(of_bl (rev (take (length xs - j) xs)) * 2^j::'a::len word) = of_bl (rev xs) * 2^j"
proof -
  let ?m = "length xs - j"
  have "rev xs = (rev (drop ?m xs)) @ (rev (take ?m xs))"
    by (metis append_take_drop_id rev_append)
  then have "(of_bl (rev xs) :: 'a::len word) = of_bl ((rev (drop ?m xs)) @ (rev (take ?m xs)))"
    by simp
  moreover have "length (rev (take ?m xs)) = ?m"
    using assms by simp
  ultimately have "(of_bl (rev xs) :: 'a::len word) = of_bl (rev (drop ?m xs)) * 2^?m + of_bl (rev (take ?m xs))"
    by (simp add: of_bl_append)
  then have "(of_bl (rev xs) :: 'a::len word) * 2 ^j = of_bl (rev (drop ?m xs)) * 2^?m * 2 ^j  + of_bl (rev (take ?m xs)) * 2 ^j "
    by (simp add: distrib_left mult.commute)
  moreover have "(2::'a::len word)^?m * 2^j = 2 ^ (length xs)"
    using assms
    by (metis le_add_diff_inverse less_or_eq_imp_le mult.commute power_add)
  moreover have "(2::'a::len word)^(length xs) = 0" using assms by simp
  ultimately have "(of_bl (rev xs) :: 'a::len word) * 2 ^j = of_bl (rev (drop ?m xs)) * 0 + of_bl (rev (take ?m xs)) * 2 ^j "
    by (simp add: ab_semigroup_mult_class.mult_ac(1))
  then show ?thesis
    by simp
qed

lemma of_bl_sh_j:
  assumes "length xs = LENGTH('a)" "length xs = length ys" "j < length ys"
  shows "(of_bl (rev (sh_j xs ys j))::'a::len word) = of_bl (rev xs) * 2^j * of_bool (ys!j)"
proof (cases "ys!j")
  assume a0: "\<not> ys ! j"
  then have "sh_j xs ys j = replicate (length xs) False"
    unfolding sh_j.simps sh_def
    by (simp add: map_replicate_const assms)
  then show ?thesis using a0 by simp
next
  assume a0: "ys ! j"
  have "sh_j xs ys j = replicate j False @ take (length xs - j) xs"
    using sh_j_nth assms a0 by blast
  then have "(of_bl (rev (sh_j xs ys j))::'a::len word) = of_bl (rev (take (length xs - j) xs) @ replicate j False)"
    by auto
  also have "\<dots> = of_bl (rev (take (length xs - j) xs)) * 2^j"
    by (simp add: of_bl_append)
  also have "\<dots> = of_bl (rev xs) * 2^j"
    using of_bl_sh_j_helper assms a0 by blast
  finally show ?thesis using a0 by simp
qed


lemma sh_false_all_carry_false:
  shows  "\<not>(Suc j \<le> i) \<Longrightarrow> (\<forall>k < i. (sh_j xs ys (Suc j)) ! k = False) \<Longrightarrow> bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) i= False"
  apply (induction i)
  by simp_all
  
lemma carry_mult_eq:
  assumes "Suc j < length xs" "length xs = length ys" "i \<le> length xs"
  shows "carry_mult xs ys i (Suc j) =
    bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) i"
  using assms(3)
proof (induction i)
  assume IB: "0 \<le> length xs"
  then show "carry_mult xs ys 0 (Suc j) = bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) 0"
    by simp
next
  fix i::nat
  assume IH: "(i \<le> length xs \<Longrightarrow> carry_mult xs ys i (Suc j) = bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) i)"
  and a0: "Suc i \<le> length xs"
  then have IH': "carry_mult xs ys i (Suc j) = bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) i"
    using IH by simp
  have t0: "carry_mult xs ys (Suc i) (Suc j) = (if j < i then (res_mult xs ys i j \<and> sh xs ys i (Suc j)) \<or> (res_mult xs ys i j \<noteq> sh xs ys i (Suc j) \<and> carry_mult xs ys i (Suc j))
     else False)"
    by simp
  have t1: "((res_j xs ys j ! i \<and> sh_j xs ys (Suc j) ! i) \<or> (res_j xs ys j ! i \<noteq> sh_j xs ys (Suc j) ! i \<and> bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) i))
      = bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) (Suc i)"
    by force
     
  have "j < i \<Longrightarrow> carry_mult xs ys (Suc i) (Suc j) = bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) (Suc i)"
  proof-
    assume a1: "j < i"
    then have "carry_mult xs ys (Suc i) (Suc j) = ((res_mult xs ys i j \<and> sh xs ys i (Suc j)) \<or> (res_mult xs ys i j \<noteq> sh xs ys i (Suc j) \<and> carry_mult xs ys i (Suc j)))"
      using t0 by force
    moreover have "res_mult xs ys i j = res_j xs ys j ! i" using a0 by simp
    moreover have "sh xs ys i (Suc j) = sh_j xs ys (Suc j) ! i" using a0 by simp
    moreover have "carry_mult xs ys i (Suc j) = bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) i" using IH a0 by auto
    ultimately have "carry_mult xs ys (Suc i) (Suc j) = 
        ((res_j xs ys j ! i \<and> sh_j xs ys (Suc j) ! i) \<or> (res_j xs ys j ! i \<noteq> sh_j xs ys (Suc j) ! i) \<and> bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) i)" by simp
    then show ?thesis using t1 by simp
  qed

  moreover have "j \<ge> i \<Longrightarrow> carry_mult xs ys (Suc i) (Suc j) = bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) (Suc i)"
  proof-
    assume a1: "j \<ge> i"
    have t2: "\<forall>k < Suc i. sh_j xs ys (Suc j) ! k = False"
      using sh_j_false a0 a1 IH carry_mult.elims(2) by fastforce

    have "carry_mult xs ys (Suc i) (Suc j) = False"
      using t0 a1 by force
    moreover have "bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) i = False"
      using sh_false_all_carry_false a1 t2 by auto
    ultimately show ?thesis
      using t1 t2 by blast
  qed

  ultimately show "carry_mult xs ys (Suc i) (Suc j) = bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) (Suc i)" by fastforce
qed

  lemma res_j_Suc:
    assumes "length xs = length ys" "Suc j < length xs"
    shows "res_j xs ys (Suc j) = bvadd (res_j xs ys j) (sh_j xs ys (Suc j)) [] []"
  proof (rule nth_equalityI)
    show "length (res_j xs ys (Suc j)) =
          length (bvadd (res_j xs ys j) (sh_j xs ys (Suc j)) [] [])"
      using assms by (simp add: length_bvadd)
  next
    fix i assume "i < length (res_j xs ys (Suc j))"
    hence ilen: "i < length xs" by simp
    have len_eq: "length (res_j xs ys j) = length (sh_j xs ys (Suc j))" by simp
    have lhs: "res_j xs ys (Suc j) ! i = res_mult xs ys i (Suc j)"
      using ilen by simp
    have rhs: "bvadd (res_j xs ys j) (sh_j xs ys (Suc j)) [] [] ! i =
               ((res_mult xs ys i j \<noteq> sh xs ys i (Suc j)) \<noteq>
                bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) i)"
      using bvadd_nth[OF len_eq, of i] ilen by simp
    show "res_j xs ys (Suc j) ! i =
          bvadd (res_j xs ys j) (sh_j xs ys (Suc j)) [] [] ! i"
    proof (cases i)
      case 0
      show ?thesis apply (subst rhs lhs) using 0 sh_def apply (simp add: sh_def)
        by (metis res_mult.elims(3) lhs res_mult.elims(2) res_j.elims nat.distinct(1))
    next
      case (Suc i')
      have c: "carry_mult xs ys (Suc i') (Suc j) =
               bvadd_carry_idx (res_j xs ys j) (sh_j xs ys (Suc j)) (Suc i')"
        using carry_mult_eq[] ilen Suc
        using assms(1,2) order.strict_implies_order by blast
      show ?thesis using lhs rhs c Suc by simp
    qed
  qed




  lemma of_bl_res_j:
    assumes "length xs = LENGTH('a)" "length xs = length ys"
    shows "j < length xs \<Longrightarrow>
           (of_bl (rev (res_j xs ys j))::'a::len word) =
           (\<Sum>k\<le>j. of_bl (rev xs) * 2^k * of_bool (ys!k))"
    proof (induction j)
      case 0
      have rj0: "res_j xs ys 0 = sh_j xs ys 0"
        by (rule nth_equalityI) (auto simp: res_mult.simps(1))
      have len_ys: "0 < length ys" using "0.prems" assms by simp
      have "(of_bl (rev (res_j xs ys 0))::'a::len word)
          = of_bl (rev xs) * 2^0 * of_bool (ys!0)"
        using rj0 of_bl_sh_j[OF assms(1) assms(2) len_ys] by simp
      thus ?case by simp
  next
    case (Suc j)
    have step: "res_j xs ys (Suc j) = bvadd (res_j xs ys j) (sh_j xs ys (Suc j)) [] []"
      using res_j_Suc[OF assms(2)] Suc.prems by simp
    have len_rj: "length (res_j xs ys j) = LENGTH('a)" using assms by simp
    have len_sh: "length (sh_j xs ys (Suc j)) = LENGTH('a)" using assms by simp
    have "(of_bl (rev (res_j xs ys (Suc j)))::'a::len word) =
          of_bl (rev (res_j xs ys j)) + of_bl (rev (sh_j xs ys (Suc j)))"
      using step word_add_bvadd[OF len_rj] len_sh
      using len_rj by presburger
    also have "\<dots> = (\<Sum>k\<le>j. of_bl (rev xs) * 2^k * of_bool (ys!k))
                  + of_bl (rev xs) * 2^Suc j * of_bool (ys!Suc j)"
      using Suc.IH Suc.prems of_bl_sh_j[OF assms(1,2), of "Suc j"] assms by simp
    also have "\<dots> = (\<Sum>k\<le>Suc j. of_bl (rev xs) * 2^k * of_bool (ys!k))"
      by simp
    finally show ?case .
  qed

   lemma sum_shifts_eq_mult:
      fixes a :: "'a::len word"
      assumes "length ys = LENGTH('a)"
      shows "(\<Sum>k<LENGTH('a). a * 2^k * of_bool (ys!k)) = a * of_bl (rev ys)"
    proof -
      have "(of_bl (rev ys)::'a::len word) = horner_sum of_bool 2 ys"
        by (rule of_bl_rev_eq)
      also have "\<dots> = (\<Sum>k = 0..<length ys. of_bool (ys!k) * 2^k)"
        by (rule horner_sum_eq_sum)
      also have "\<dots> = (\<Sum>k<LENGTH('a). of_bool (ys!k) * 2^k)"
        using assms by (simp add: atLeast0LessThan)
      finally have horner:
        "(of_bl (rev ys)::'a::len word) = (\<Sum>k<LENGTH('a). of_bool (ys!k) * 2^k)" .
      have "a * of_bl (rev ys) = (\<Sum>k<LENGTH('a). a * (of_bool (ys!k) * 2^k))"
        apply (simp add: horner sum_distrib_left)
        by (metis (no_types) finite_lessThan sum_distrib_left sum_of_bool_mult_eq)
      also have "\<dots> = (\<Sum>k<LENGTH('a). a * 2^k * of_bool (ys!k))"
        apply (simp add: mult.assoc mult.commute)
        by (metis (no_types) finite_lessThan sum_distrib_left sum_of_bool_mult_eq)
      finally show ?thesis by simp
    qed

lemma word_mult_bvmult [word_mult_rbl_bvmult]:
    assumes "length xs = LENGTH('a)" "length xs = length ys" "0 < length xs"
    shows "(of_bl (rev xs)::'a::len word) * of_bl (rev ys)
         = of_bl (rev (map (\<lambda>i. res_mult xs ys i (length xs - 1)) [0..<length xs]))"
  proof -
    have nm1: "length xs - 1 < length xs" using assms by simp
    have unfold_resj: "map (\<lambda>i. res_mult xs ys i (length xs - 1)) [0..<length xs]
                     = res_j xs ys (length xs - 1)"
      by simp
    have idx: "{..length xs - 1} = {..<length xs}"
      using assms by auto
    have "(of_bl (rev (map (\<lambda>i. res_mult xs ys i (length xs - 1)) [0..<length xs]))::'a::len word)
          = (\<Sum>k\<le>length xs - 1. of_bl (rev xs) * 2^k * of_bool (ys!k))"
      using of_bl_res_j[OF assms(1,2) nm1] unfold_resj by simp
    also have "\<dots> = (\<Sum>k<LENGTH('a). of_bl (rev xs) * 2^k * of_bool (ys!k))"
      using idx assms by simp
    also have "\<dots> = of_bl (rev xs) * of_bl (rev ys)"
      using sum_shifts_eq_mult[of ys "of_bl (rev xs)"] assms by auto
    finally show ?thesis by simp
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

lemma rev_takefill:
  "rev (takefill c l xs) = replicate (l - length xs) c @ drop (length xs - l) (rev xs)"
  unfolding takefill_alt rev_append rev_take rev_replicate by simp

lemma of_bl_rbl_extract:
"Suc j \<le> length xs \<Longrightarrow> i \<le> j \<Longrightarrow> of_bl (rbl_extract j i xs) = of_bl (take (Suc j - i) (drop (length xs - Suc j) xs))  "
  unfolding rbl_extract_def
  by (simp add: rev_drop rev_takefill rev_take of_bl_rep_False)

(*"smtlib_extract (31::int) (24::int)
          (of_bl
            (rev [bit (vptr::32 word) 0, bit vptr 1, bit vptr (2::nat), bit vptr (3::nat), bit vptr (4::nat), bit vptr (5::nat), bit vptr (6::nat),
                  bit vptr (7::nat), bit vptr (8::nat), bit vptr (9::nat), bit vptr (10::nat), bit vptr (11::nat), bit vptr (12::nat),
                  bit vptr (13::nat), bit vptr (14::nat), bit vptr (15::nat), bit vptr (16::nat), bit vptr (17::nat), bit vptr (18::nat),
                  bit vptr (19::nat), bit vptr (20::nat), bit vptr (21::nat), bit vptr (22::nat), bit vptr (23::nat), bit vptr (24::nat),
                  bit vptr (25::nat), bit vptr (26::nat), bit vptr (27::nat), bit vptr (28::nat), bit vptr (29::nat), bit vptr (30::nat),
                  bit vptr (31::nat)])) =
         of_bl
          (rev [bit vptr (24::nat), bit vptr (25::nat), bit vptr (26::nat), bit vptr (27::nat), bit vptr (28::nat), bit vptr (29::nat),
                bit vptr (30::nat), bit vptr (31::nat)])"*)

lemma smt_extract_of_bl:
  fixes i::int
  shows "- i + j + 1 = int LENGTH('b) \<Longrightarrow>
    length xs = LENGTH('a) \<Longrightarrow>
    LENGTH('b) < LENGTH('a) \<Longrightarrow>
    i \<le> j \<Longrightarrow>
    j + 1 \<le> int LENGTH('a) \<Longrightarrow>
    0 \<le> i \<Longrightarrow> 0 \<le> j \<Longrightarrow> (smtlib_extract j i (of_bl xs::'a::len word)::'b::len word) = of_bl (take (Suc (nat j) - nat i) (drop (length xs - Suc (nat j)) xs))"
proof-
  assume a0: "- i + j + 1 = int LENGTH('b)"
    "length xs = LENGTH('a)"
    "LENGTH('b) < LENGTH('a)"
    "i \<le> j"
    "j + 1 \<le> int LENGTH('a)"
    "0 \<le> i" "0 \<le> j"
  obtain k where k_def: "k = LENGTH('a) - LENGTH('b) - i" by blast
  have t0: "LENGTH('a::len) - nat (i::int) \<le> LENGTH('a::len)" by simp
  have t1: "length (xs::bool list) - nat (k::int) = nat ((j::int) + 1)"
    using a0(1,2,3,5) k_def by fastforce
  have t2: " (min (LENGTH('a::len) - nat i) (nat k)) = nat k"
    using a0(6) k_def by auto
  have t3: "(LENGTH('a) - nat i - nat (int (LENGTH('a) - LENGTH('b)) - i)) = LENGTH('b)"
    using a0(1,5,6) by force
  have "(to_bl (of_bl (drop (nat k) (rev xs))::'a::len word)) = rev (takefill False LENGTH('a) (rev (drop (nat k) (rev xs))))"
    by (simp add: word_rev_tf)



  have "(smtlib_extract j i (of_bl xs::'a::len word)::'b::len word) = of_bl (take (LENGTH('a) - nat i) (to_bl (take_bit (nat (j + 1)) (of_bl xs ::'a::len word))))"
    by (simp add: slice_take smtlib_extract_def)
  moreover have "(length (xs::bool list) - nat (k::int)) = (nat (j + 1))" using a0 unfolding k_def a0(2) by simp
  ultimately have "(smtlib_extract j i (of_bl xs::'a::len word)::'b::len word) = of_bl (take (LENGTH('a) - nat i) (to_bl (of_bl (drop (nat k) xs)::'a::len word)))"
    using of_bl_drop_eq_take_bit[symmetric, of "xs" "nat k",where 'a='a] by simp
  also have "... = of_bl (take (LENGTH('a) - nat i) (rev (takefill False LENGTH('a) (rev (drop (nat k) xs)))))"
    unfolding word_rev_tf by simp
  also have "... =  of_bl
     (take (LENGTH('a) - nat i)
       (replicate (LENGTH('a) - length (rev (drop (nat k) xs))) False @
        drop (length (rev (drop (nat k) xs)) - LENGTH('a)) (drop (nat k) xs)))"
    unfolding rev_takefill by simp
  also have "... =  of_bl
     (take (LENGTH('a) - nat i)
       (replicate (LENGTH('a) - length (rev (drop (nat k) xs))) False @ (drop (nat k) xs)))"
    by (simp add: a0(2) drop_0)
  also have "... =  of_bl (take (LENGTH('a) - nat i) (replicate (nat k) False @ (drop (nat k) xs)))"
    by (metis t1 a0(2,7) add.commute diff_diff_cancel diff_is_0_eq' int_eq_iff
        length_drop length_rev nat.simps(3) nat_le_linear of_nat_Suc)
  also have "... =  of_bl ((take (LENGTH('a) - nat i) (replicate (nat k) False) @ (take (LENGTH('a) - nat i - nat k) (drop (nat k) xs))))"
    by simp
  also have "... =  of_bl ((take (LENGTH('a) - nat i) (replicate (nat k) False) @ (take (LENGTH('b)) (drop (nat k) xs))))"
    unfolding k_def
    using t3 by presburger
  also have "... =  of_bl ((take (LENGTH('b)) (drop (nat k) xs)))"
    by (metis of_bl_rep_False take_replicate)
  finally show "(smtlib_extract j i (of_bl xs::'a::len word)::'b::len word) = of_bl (take (Suc (nat j) - nat i) (drop (length xs - Suc (nat j)) xs))"
    by (metis (no_types, opaque_lifting) Suc_as_int a0(2,7) add.commute drop_drop int_eq_iff k_def length_drop rev_drop rev_rev_ident t1 t3
        take_rev)
qed

lemma [rbl_extract]:
  fixes i::int
  shows "- i + j + 1 = int LENGTH('b) \<Longrightarrow>
    length xs = LENGTH('a) \<Longrightarrow>
    LENGTH('b) < LENGTH('a) \<Longrightarrow>
    i \<le> j \<Longrightarrow>
    j + 1 \<le> int LENGTH('a) \<Longrightarrow>
    0 \<le> i \<Longrightarrow> 0 \<le> j \<Longrightarrow>
(smtlib_extract j i (of_bl xs::'a::len word)::'b::len word) = of_bl (rbl_extract (nat j) (nat i) xs)"
  unfolding rbl_extract_def
  apply (simp add: smt_extract_of_bl)
  by (smt (z3) of_bl_rbl_extract rbl_extract_def)

lemmas [bv_reconstruction_const_test] = int_ops

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

lemma word_xor_rbl_bvxor2 [word_xor_rbl_bvxor]:
"length xs = LENGTH('a)  \<Longrightarrow> length xs = length ys
 \<Longrightarrow> (xor (of_bl xs::'a::len word) ((of_bl ys)::'a::len word))
   = of_bl (map2 (\<lambda> x. \<lambda> y. x \<noteq> y) xs ys)"
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
      = (of_bl (map2 (\<lambda> x. \<lambda> y. x \<noteq> y) xs ys))"
    using word_bl.Abs_inverse
    by simp
qed


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