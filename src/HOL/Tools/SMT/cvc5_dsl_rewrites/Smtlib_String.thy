theory Smtlib_String
imports "HOL-Library.Sublist"
begin

type_synonym RegLan = "string set"

(*------------------------------------------------------------------------------------------------*)
(*-------------------------------------------- str.++ --------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(*Defines the SMTLIB string operators*)
(* (str.++ String String String) \<lbrakk>str.++\<rbrakk> is the word concatenation function.*)

definition smtlib_str_concat :: "string \<Rightarrow> string \<Rightarrow> string" where 
  "smtlib_str_concat \<equiv> List.append"


(*------------------------------------------------------------------------------------------------*)
(*-------------------------------------------- str.len -------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.len String Int)
   \<lbrakk>str.len\<rbrakk>(w) is the number of characters (elements of UC) in w, denoted below as |w|. *)

definition smtlib_str_len :: "string \<Rightarrow> int" where
  "smtlib_str_len str \<equiv> int (List.length str)"

lemma smtlib_str_concat_length: 
  "smtlib_str_len (smtlib_str_concat w1 w2) = smtlib_str_len w1 + smtlib_str_len w2"
  by (simp add: smtlib_str_len_def smtlib_str_concat_def)


(*------------------------------------------------------------------------------------------------*)
(*---------------------------------------------- str.< -------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.< String String Bool)

   \<lbrakk>str.<\<rbrakk>(w1, w2) is true iff w1 is smaller than w2 in the lexicographic 
   extension to UC* of the standard numerical < ordering over UC.

   Note: The order induced by str.< corresponds to alphabetical order
   for strings composed of characters from the alphabet of a western language 
   such as English:
   \<lbrakk>(str.< ""a"" ""aardvark"" ""aardwolf"" ... ""zygomorphic"" ""zygotic"")\<rbrakk> = true
*)

fun string_comp :: "char list \<Rightarrow> char list \<Rightarrow> bool" where
"string_comp _ [] = False" |
"string_comp [] _ = True" |
"string_comp (w1#w1s) (w2#w2s)
  = (if w1 = w2 then string_comp w1s w2s else (of_char w1::int) < of_char w2)"

definition smtlib_str_less :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "smtlib_str_less \<equiv> string_comp"


(*------------------------------------------------------------------------------------------------*)
(*------------------------------------------ str.to_re -------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.to_re String RegLan)
   \<lbrakk>str.to_re\<rbrakk>(w) = { w } *)

definition smtlib_str_to_re :: "string \<Rightarrow> RegLan" where
  "smtlib_str_to_re w \<equiv> {w}"

lemma smtlib_str_to_re_length [simp]:
  "card (smtlib_str_to_re w) = 1"
  by (simp add: smtlib_str_to_re_def)

lemma smtlib_str_to_re_empty [simp]:
 "(smtlib_str_to_re []) = {[]}"
  by (simp add: smtlib_str_to_re_def)

(*------------------------------------------------------------------------------------------------*)
(*------------------------------------------ str.to_re -------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.in_re String RegLan Bool) 
   \<lbrakk>str.in_re\<rbrakk>(w, L) = true iff w \<in> L *)

definition smtlib_str_in_re :: "string \<Rightarrow> RegLan \<Rightarrow> bool" where
  "smtlib_str_in_re str regLan \<equiv> str \<in> regLan"


(*------------------------------------------------------------------------------------------------*)
(*------------------------------------------- re.none --------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (re.none RegLan)
   \<lbrakk>re.none\<rbrakk>  = \<emptyset> *)
definition smtlib_re_none :: "RegLan" where
  "smtlib_re_none \<equiv> {}"

lemma smtlib_re_none_length [simp]:
  "card smtlib_re_none = 0"
  by (simp add: smtlib_re_none_def)


(*------------------------------------------------------------------------------------------------*)
(*-------------------------------------------- re.all --------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (re.all RegLan)
   \<lbrakk>re.all\<rbrakk>  = \<lbrakk>String\<rbrakk> = UC *)
definition smtlib_re_all :: "RegLan" where
  "smtlib_re_all \<equiv> UNIV"


(*------------------------------------------------------------------------------------------------*)
(*------------------------------------------ re.allchar ------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (re.allchar RegLan)
   \<lbrakk>re.allchar\<rbrakk>  = { w \<in> UC* | |w| = 1 } *)
definition smtlib_re_allchar :: "RegLan" where
  "smtlib_re_allchar \<equiv> { w. w \<in> UNIV \<and> List.length w = 1 } "


(*------------------------------------------------------------------------------------------------*)
(*--------------------------------------------- re.++ --------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (re.++ RegLan RegLan RegLan :left-assoc)
   \<lbrakk>re.++\<rbrakk>(L1, L2) = { w1₁w2 | w1 \<in> L1 and w2 \<in> L2} *)
definition smtlib_re_concat :: "RegLan \<Rightarrow> RegLan \<Rightarrow> RegLan" where
  "smtlib_re_concat L1 L2 \<equiv> { w . \<exists> w1 w2. w = w1 @ w2 \<and> w1 \<in> L1 \<and> w2 \<in> L2 }"

inductive_set smtlib_re_concat_ind :: "RegLan \<Rightarrow> RegLan \<Rightarrow> RegLan"
  for L1 :: "RegLan" and L2::"RegLan"
  where smtlib_re_concat_ind: "x \<in> L1 \<Longrightarrow> y \<in> L2 \<Longrightarrow> x @ y \<in> smtlib_re_concat_ind L1 L2"

lemma smtlib_re_concat_smtlib_re_concat_induct:
 "smtlib_re_concat L1 L2 = smtlib_re_concat_ind L1 L2"
  unfolding smtlib_re_concat_def
  using smtlib_re_concat_ind_def smtlib_re_concat_indp.simps by presburger

lemma smtlib_re_concat_foldr:
 "(foldr smtlib_re_concat xs (smtlib_re_concat s x))
 = (smtlib_re_concat (foldr smtlib_re_concat xs s) x)"
  unfolding smtlib_re_concat_def
  apply (induction xs)
   apply simp_all
  by (metis (no_types, lifting) append.assoc)


(*------------------------------------------------------------------------------------------------*)
(*------------------------------------------- re.union -------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (re.union RegLan RegLan RegLan :left-assoc)
   \<lbrakk>re.union\<rbrakk>(L1, L2) = { w | w \<in> L1 or w \<in> L2 } *)
definition smtlib_re_union :: "RegLan \<Rightarrow> RegLan \<Rightarrow> RegLan" where
  "smtlib_re_union L1 L2 \<equiv> { w . w \<in> L1 \<or> w \<in> L2} "

lemma smtlib_re_union_card [simp]: "card (smtlib_re_union L1 L2) = card (L1 \<union> L2)"
  by (simp add: Un_def smtlib_re_union_def)


(*------------------------------------------------------------------------------------------------*)
(*------------------------------------------- re.inter -------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (re.inter RegLan RegLan RegLan :left-assoc)
   \<lbrakk>re.inter\<rbrakk>(L1, L2) = { w | w \<in> L1 and w \<in> L2 } *)
definition smtlib_re_inter :: "RegLan \<Rightarrow> RegLan \<Rightarrow> RegLan" where
  "smtlib_re_inter L1 L2 \<equiv> { w . w \<in> L1 \<and> w \<in> L2} "

lemma smtlib_re_inter_card [simp]: "card (smtlib_re_inter L1 L2) = card (L1 \<inter> L2)"
  unfolding smtlib_re_inter_def
  by (simp add: Int_def)


(*------------------------------------------------------------------------------------------------*)
(*------------------------------------------- re.star --------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(*(re.* RegLan RegLan) 
    \<lbrakk>re.*\<rbrakk>(L) is the smallest subset K of UC* such that
    1. \<epsilon> \<in> K
    2. \<lbrakk>re.++\<rbrakk>(L,K) \<subseteq> K *)

(*definition smtlib_re_star :: "RegLan \<Rightarrow> RegLan" where
  "smtlib_re_star L \<equiv> LEAST K . ('''' \<in> (K::char list set) \<and> smtlib_re_concat L K \<subseteq> K)"*)

inductive_set smtlib_re_star_ind :: "string set \<Rightarrow> string set"
  for L :: "string set"
  where
    smtlib_re_star_ind_empty: "'''' \<in> smtlib_re_star_ind L"
  | smtlib_re_star_ind_single: "x \<in> L \<Longrightarrow> x \<in> smtlib_re_star_ind L"
  | smtlib_re_star_ind_Cons: "b \<in> smtlib_re_star_ind L \<Longrightarrow> a \<in> smtlib_re_star_ind L
   \<Longrightarrow> a \<noteq> '''' \<Longrightarrow> b \<noteq> ''''
   \<Longrightarrow> a @ b \<in> smtlib_re_star_ind L"

definition smtlib_re_star :: "RegLan \<Rightarrow> RegLan" where
  "smtlib_re_star L \<equiv> smtlib_re_star_ind L "

definition smtlib_re_star2 :: "RegLan \<Rightarrow> RegLan" where
  "smtlib_re_star2 L \<equiv> LEAST K . ('''' \<in> (K::char list set) \<and> smtlib_re_concat L K \<subseteq> K)"

lemma smtlib_re_star_ind_1:
  assumes "x \<in> smtlib_re_star_ind r"
  shows "x = [] \<or> x \<in> r \<or> (\<exists> a b. x = a @ b \<and> a \<in> smtlib_re_star_ind r \<and> b \<in> r)"
  using assms
  apply (induction rule: smtlib_re_star_ind.induct)
    apply simp_all
  by (metis (mono_tags, lifting) append_assoc self_append_conv2 smtlib_re_star_ind.smtlib_re_star_ind_Cons)

lemma smtlib_re_star_ind_2:
  assumes "x \<in> smtlib_re_star_ind r"
  shows "x = [] \<or> x \<in> r \<or> (\<exists> a b. x = a @ b \<and> a \<in> r \<and> b \<in> smtlib_re_star_ind r)"
  using assms
  apply (induction rule: smtlib_re_star_ind.induct)
    apply simp_all
  by (metis (mono_tags, lifting) append_assoc self_append_conv2 smtlib_re_star_ind.smtlib_re_star_ind_Cons)

lemma re_concat_star_swap:
  "smtlib_re_concat (smtlib_re_star_ind r) r = smtlib_re_concat r (smtlib_re_star_ind r)"
  apply (rule set_eqI)
  unfolding smtlib_re_concat_def
  apply (rule iffI)
   apply simp_all
    apply (metis append_Nil append_Nil2 append_is_Nil_conv smtlib_re_star_ind.smtlib_re_star_ind_Cons smtlib_re_star_ind.smtlib_re_star_ind_empty smtlib_re_star_ind.smtlib_re_star_ind_single smtlib_re_star_ind_2)
    by (metis Nil_is_append_conv append_Nil append_Nil2 smtlib_re_star_ind.smtlib_re_star_ind_Cons smtlib_re_star_ind.smtlib_re_star_ind_empty smtlib_re_star_ind.smtlib_re_star_ind_single smtlib_re_star_ind_1)

lemma smtlib_re_star_ind_elem1: "x \<in> L \<Longrightarrow> (x \<in> smtlib_re_star_ind L)"
  by (simp add: smtlib_re_star_ind.smtlib_re_star_ind_single)

lemma smtlib_re_star_ind_elem2: "(x \<in> smtlib_re_star_ind L) = (x = [] \<or> (\<exists>b a. x = a @ b \<and> b \<in> smtlib_re_star_ind L \<and> a \<in> L))"
  using smtlib_re_star_ind.simps[of x L]
  by (metis append.right_neutral append_Nil smtlib_re_star_ind.smtlib_re_star_ind_empty smtlib_re_star_ind_2 smtlib_re_star_ind_elem1)

lemma smtlib_re_star_smtlib_re_allchar [simp]:
  "(smtlib_re_star smtlib_re_allchar) = UNIV"
  apply (simp add: smtlib_re_allchar_def smtlib_re_star_def)
  apply (rule set_eqI)
  apply simp
  subgoal for x
    apply (induction x)
     apply (simp add: smtlib_re_star_ind.smtlib_re_star_ind_empty)
    subgoal for a as
      using smtlib_re_star_ind.simps[of "a#as" "{w. length w = Suc 0}"]
      apply simp
      by (metis (mono_tags, lifting) CollectI append.left_neutral append_Cons length_Cons list.size(3) smtlib_re_star_ind.smtlib_re_star_ind_single)
    done
  done

lemma smtlib_re_star_smtlib_re_all [simp]:
  "(smtlib_re_star smtlib_re_all) = UNIV"
  unfolding smtlib_re_all_def
  apply (rule set_eqI)
  subgoal for x
    apply (induction x)
     apply (simp add: smtlib_re_star_def smtlib_re_star_ind.smtlib_re_star_ind_empty)
    by (simp add: smtlib_re_star_def smtlib_re_star_ind.smtlib_re_star_ind_single)
  done

lemma smtlib_re_star_smtlib_re_none [simp]:
  "(smtlib_re_star smtlib_re_none) = {''''}"
  unfolding smtlib_re_none_def
  apply (rule set_eqI)
  subgoal for x
    apply (induction x)
    unfolding smtlib_re_star_def
     apply (simp add: smtlib_re_star_def smtlib_re_star_ind.smtlib_re_star_ind_empty)
    using smtlib_re_star_ind_1 by auto
  done

(*------------------------------------------------------------------------------------------------*)
(*-------------------------------------------- re.\<le> ----------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.<= String String Bool)
   \<lbrakk>str.<=\<rbrakk>(w1, w2) is true iff either \<lbrakk>str.<\<rbrakk>(w1, w2) or w1 = w2. *)

definition smtlib_str_leq :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "smtlib_str_leq w1 w2 \<equiv> smtlib_str_less w1 w2 \<or> w1 = w2 "


(*------------------------------------------------------------------------------------------------*)
(*----------------------------------------- re.substr --------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.substr String Int Int String)

   - \<lbrakk>str.substr\<rbrakk>(w, m, n) is the unique word w2 such that
     for some words w1 and w3
      - w = w1₁w2₂w3
      - |w1| = m
      - |w2| = min(n, |w| - m) 
                                    if 0 <= m < |w| and 0 < n
    - \<lbrakk>str.substr\<rbrakk>(w, m, n) = \<epsilon>      otherwise

    Note: The second part of the definition makes \<lbrakk>str.substr\<rbrakk> a total function. *)

definition smtlib_str_substr :: "string \<Rightarrow> int \<Rightarrow> int \<Rightarrow> string" where
  "smtlib_str_substr w m n \<equiv>
 (if 0 \<le> m \<and> m < int (length w) \<and> 0 < n
  then List.take (min (nat n) (List.length w - (nat m))) (List.drop (nat m) w)
  else '''' )"

lemma smtlib_str_substr_length [simp]:
  shows "smtlib_str_len (smtlib_str_substr w m n)
       = (if 0 \<le> m \<and>  m < int (length w) \<and> 0 < n then int (min (nat n) (length w - nat m)) else 0)"
  unfolding smtlib_str_substr_def smtlib_str_len_def  by simp


(*------------------------------------------------------------------------------------------------*)
(*-------------------------------------------- re.at ---------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.at String Int String)
   \<lbrakk>str.at\<rbrakk>(w, n) = \<lbrakk>str.substr\<rbrakk>(w, n, 1) *)

definition smtlib_str_at :: "string \<Rightarrow> int \<Rightarrow> string" where
  "smtlib_str_at w n \<equiv> smtlib_str_substr w n 1"

lemma smtlib_str_at_length [simp]:
  shows "smtlib_str_len (smtlib_str_at w n)
 = (if 0 \<le> n \<and> n < int (length w) then int (min (nat 1) (length w - nat n))
   else 0)"
  by (simp add: smtlib_str_at_def)


(*------------------------------------------------------------------------------------------------*)
(*----------------------------------------- str.prefixof -----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.prefixof String String Bool)
   \<lbrakk>str.prefixof\<rbrakk>(w1, w) = true  iff  w = w1 w2 for some word w2₂*)

definition smtlib_str_prefixof :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "smtlib_str_prefixof w1 w \<equiv> prefix w1 w"


(*------------------------------------------------------------------------------------------------*)
(*----------------------------------------- str.suffixof -----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.suffixof String String Bool)
   \<lbrakk>str.suffixof\<rbrakk>(w2, w) = true  iff  w = w1 w2 for some word w1 *)
definition smtlib_str_suffixof :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "smtlib_str_suffixof w1 w \<equiv> suffix w1 w"


(*------------------------------------------------------------------------------------------------*)
(*----------------------------------------- str.contains -----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.contains String String Bool)
   \<lbrakk>str.contains\<rbrakk>(w, w2) = true  iff  w = w1 w2 w3 for some words w1, w3 *)

definition smtlib_str_contains2 :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "smtlib_str_contains2 w w2 \<equiv> (\<exists> w1 w3. w = w1 @ w2 @ w3)"

fun smtlib_str_contains_ind  :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "smtlib_str_contains_ind [] w2 = (w2 = [])" |
  "smtlib_str_contains_ind (w#ws) w2 =
   (if length (w#ws) < length w2 then False else
   (if take (length w2) (w#ws) = w2 then True else smtlib_str_contains_ind ws w2))"

definition smtlib_str_contains :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "smtlib_str_contains w w2 \<equiv> smtlib_str_contains_ind w w2"

lemma smtlib_str_contains_equal: "smtlib_str_contains w w2 = smtlib_str_contains2 w w2"
  unfolding smtlib_str_contains_def smtlib_str_contains2_def
  apply (induction w)
   apply (cases w2)
    apply simp_all
  subgoal for w' ws
    apply (cases "Suc (length ws) < length w2")
     apply simp_all
     apply (cases "w' # ws = w2")
      apply simp_all
      apply force
    apply (metis add.left_commute le_add1 length_Cons length_append linorder_not_less)
  by (metis Cons_eq_appendI Cons_eq_append_conv append_eq_append_conv2 append_eq_conv_conj append_self_conv2 append_take_drop_id)
  done

lemma smtlib_str_contains_append: 
  "(smtlib_str_contains x w \<or> smtlib_str_contains y w) \<Longrightarrow> smtlib_str_contains (x @ y) w "
  by (metis append.assoc smtlib_str_contains2_def smtlib_str_contains_equal)

lemma smtlib_str_contains_add:
  "smtlib_str_contains x w \<Longrightarrow> smtlib_str_contains (a@x@b) w"
  by (metis smtlib_str_contains_append)
  
lemma smtlib_str_contains_singleton:
  shows "smtlib_str_len w = 1 \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> smtlib_str_contains xs w = (smtlib_str_contains [hd xs] w \<or> smtlib_str_contains (tl xs) w)"
  apply (induction xs)
  apply (simp_all add: smtlib_str_contains_def smtlib_str_len_def)
  by force

lemma smtlib_str_contains_append_Singleton:
  assumes "smtlib_str_len w = 1"
  shows "smtlib_str_contains (x @ y) w = (smtlib_str_contains x w \<or> smtlib_str_contains y w)"
  apply (induction "length (x@y)" arbitrary: x y)
   apply simp_all
  subgoal for n x' y'
  proof-
    assume IH: "(\<And>x y. n = length x + length y \<Longrightarrow> smtlib_str_contains (x @ y) w = (smtlib_str_contains x w \<or> smtlib_str_contains y w))"
    and a0: "Suc n = length x' + length y'" 
    obtain a as where t0: "a # as = x' @ y'" 
      by (metis Suc_length_conv a0 length_append)
    have t1: "smtlib_str_contains (x' @ y') w = (smtlib_str_contains [hd (x' @ y')] w \<or> smtlib_str_contains (tl (x' @ y')) w)"
      by (metis assms list.distinct(1) t0 smtlib_str_contains_singleton)
    show "smtlib_str_contains (x' @ y') w = (smtlib_str_contains x' w \<or> smtlib_str_contains y' w)"
      apply (cases "a = hd w")
      apply (metis IH a0 add_diff_cancel_left' append_self_conv2 assms hd_append2 length_Cons length_append list.sel(3) plus_1_eq_Suc smtlib_str_contains_singleton t0 t1 tl_append2)
      by (metis IH a0 add_diff_cancel_left' append_self_conv2 assms hd_append2 length_Cons length_append list.sel(3) plus_1_eq_Suc smtlib_str_contains_append smtlib_str_contains_singleton t0 tl_append2)
  qed
  done

(*------------------------------------------------------------------------------------------------*)
(*----------------------------------------- str.indexof -----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.indexof String String Int Int)
    - \<lbrakk>str.indexof\<rbrakk>(w, w2, i) is the smallest n such that for some words w1, w3
        - w = w1w2w3
        - i <= n = |w1|
      if \<lbrakk>str.contains\<rbrakk>(w, w2) = true and i >= 0
    - \<lbrakk>str.indexof\<rbrakk>(w,w2,i) = -1  otherwise *)

definition smtlib_str_indexof :: "string \<Rightarrow> string \<Rightarrow> int \<Rightarrow> int" where
  "smtlib_str_indexof w w2 i \<equiv> 
  if smtlib_str_contains w w2 \<and> i \<ge> 0
  then (LEAST n. (\<exists> w1 w3. w = w1 @ w2 @ w3 \<and> nat i \<le> List.length w1))
  else -1"


(*------------------------------------------------------------------------------------------------*)
(*----------------------------------------- str.replace -----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(*(str.replace String String String String)
    - \<lbrakk>str.replace\<rbrakk>(w, w1, w2) = w          if \<lbrakk>str.contains\<rbrakk>(w, w1) = false
    - \<lbrakk>str.replace\<rbrakk>(w, w1, w2) = u1w2u2
      where u1 is the shortest word such that 
            w = u1w1u2
                                            if \<lbrakk>str.contains\<rbrakk>(w, w1) = true*)

fun smtlib_str_replace2 :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string" where
  "smtlib_str_replace2 [] [] w2 = w2"|
  "smtlib_str_replace2 [] w1 w2 = []"|
  "smtlib_str_replace2 (w#ws) w1 w2 =
    (if prefix w1 (w#ws) then w2 @ drop (length w1) (w#ws) else w # smtlib_str_replace2 ws w1 w2)"

definition smtlib_str_replace :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string" where
  "smtlib_str_replace w w1 w2 \<equiv> 
     if smtlib_str_contains w w1 then smtlib_str_replace2 w w1 w2 else w"

lemma smtlib_str_replace_empty [simp]:
 "(smtlib_str_replace [] w1 w2) = (if w1 = [] then w2 else [])"
  unfolding smtlib_str_len_def smtlib_str_replace_def
  using smtlib_str_contains_def smtlib_str_contains_ind.simps smtlib_str_replace2.simps(1) by presburger

lemma smtlib_str_replace_empty_length [simp]:
 "smtlib_str_len (smtlib_str_replace [] w1 w2) = (if w1 = [] then smtlib_str_len w2 else 0)"
  by (simp add: smtlib_str_len_def smtlib_str_replace_empty)

lemma h2: "smtlib_str_contains (s' # ss) s \<Longrightarrow> \<not> prefix s (s' # ss) \<Longrightarrow> smtlib_str_contains ss s"
  by (metis smtlib_str_contains_def smtlib_str_contains_ind.simps take_is_prefix)

lemma smtlib_str_replace_length_h1:
 "smtlib_str_len s = smtlib_str_len r \<Longrightarrow>
 smtlib_str_contains t s \<Longrightarrow>
 smtlib_str_len (smtlib_str_replace2 t s r) = smtlib_str_len t"
  unfolding smtlib_str_len_def smtlib_str_contains_def
  apply (induction t)
  apply force
  subgoal for s' ss
    apply (cases "prefix s (s' # ss)")
    using prefix_length_le apply fastforce
    by (metis h2 smtlib_str_contains_def length_Cons of_nat_eq_iff smtlib_str_replace2.simps(3))
  done

lemma smtlib_str_replace_length_h2:
 " smtlib_str_contains t s \<Longrightarrow>
 smtlib_str_len (smtlib_str_replace2 t s r) = smtlib_str_len t - smtlib_str_len s + smtlib_str_len r "
  unfolding smtlib_str_len_def 
  apply (induction t)
  apply (simp add: smtlib_str_contains_def)
  subgoal for s' ss
    apply (cases "prefix s (s' # ss)")
    using prefix_length_le apply fastforce
    by (simp add: h2)
  done

lemma smtlib_str_replace_length:
  assumes "smtlib_str_contains w w1" 
  shows "smtlib_str_len (smtlib_str_replace w w1 w2)
 = smtlib_str_len w - smtlib_str_len w1 + smtlib_str_len w2"
  unfolding smtlib_str_replace_def
  using smtlib_str_replace_length_h2[of w w1 w2] assms
  by simp

(*definition smtlib_str_replace :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string" where
  "smtlib_str_replace w w1 w2 \<equiv> 
  if smtlib_str_contains w w1
  then (THE w'. \<exists> u1 u2 :: string. w' = u1 @ w2 @ u2 \<and> w = u1 @ w1 @ u2
       \<and> (\<forall> u1'::string. w = u1' @ w1 @ u2 \<longrightarrow> length u1 \<le> length u1'))
  else w"*)


(*------------------------------------------------------------------------------------------------*)
(*--------------------------------------- str.replace_all ----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.replace_all String String String String)
    - \<lbrakk>str.replace_all\<rbrakk>(w, w1, w2) = w      if \<lbrakk>str.contains\<rbrakk>(w, w1) = false 
                                             or 
                                             w1 = \<epsilon>

    - \<lbrakk>str.replace_all\<rbrakk>(w, w1, w2) = u1w2 \<lbrakk>str.replace_all\<rbrakk>(u2, w1, w2)
      where u1 is the shortest word such that 
            w = u1w1u2
                                          if \<lbrakk>str.contains\<rbrakk>(w, w1) = true
                                            and 
                                            w1 \<noteq> \<epsilon> *)


function smtlib_str_replace_all_fun :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string" where
  "smtlib_str_replace_all_fun [] w1 w2 = (if w1 = [] then w2 else [])"|
  "smtlib_str_replace_all_fun (w#ws) w1 w2 =
 (if prefix w1 (w#ws)
 then w2 @ smtlib_str_replace_all_fun (drop (length w1) (w#ws)) w1 w2
 else w # smtlib_str_replace_all_fun ws w1 w2)"
     apply simp_all
  by (metis smtlib_str_replace2.cases)


definition smtlib_str_replace_all :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string" where
  "smtlib_str_replace_all w w1 w2 \<equiv> 
  if smtlib_str_contains w w1 \<and> w1 \<noteq> ''''
  then smtlib_str_replace_all_fun w w1 w2 
  else w"



(*function smtlib_str_replace_all_fun :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string" where
  "smtlib_str_replace_all_fun w w1 w2 = 
  (if smtlib_str_contains w w1 \<and> w1 \<noteq> ''''
  then (THE w'. \<exists> u1 u2. w' = u1 @ w2 @ smtlib_str_replace_all_fun u2 w1 w2
        \<and> w = u1 @ w1 @ u2 \<and> (\<forall> u1'::string. w = u1' @ w1 @ u2 \<longrightarrow> length u1 \<le> length u1'))
  else w)"
  apply simp_all
  sorry

definition smtlib_str_replace_all  :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string" where
 "smtlib_str_replace_all = smtlib_str_replace_all_fun" *)


(*------------------------------------------------------------------------------------------------*)
(*---------------------------------------- str.replace_re ----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(*(str.replace_re String String String String)
    - \<lbrakk>str.replace_re\<rbrakk>(w, L, w2) = w        if no substring of w is in L
    - \<lbrakk>str.replace_re\<rbrakk>(w, L, w2) = u1₁w2₂u2₂ 
      where u1, w1 are the shortest words such that 
            - w = u1 w1 u2₂
            - w1 \<in> L
                                            if some substring of w is in L *)
(*TODO*)
definition smtlib_str_replace_re  :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string" where
 "smtlib_str_replace_re w L w2 = ''''" 


(*------------------------------------------------------------------------------------------------*)
(*-------------------------------------- str.replace_re_all --------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(*(str.replace_re_all String String String String)

    - \<lbrakk>str.replace_re\<rbrakk>(w, L, w₂) = w        if no substring of w is in L

    - \<lbrakk>str.replace_re\<rbrakk>(w, L, w₂) = u₁w₂\<lbrakk>str.replace_re\<rbrakk>(u₂, L, w₂)
      where u₁, w₁ are the shortest words such that 
            - w = u₁w₁u₂
            - w₁ \<in> L
            - w₁ \<noteq> \<epsilon>
                                          if some substring of w is in L *)
(*TODO*)
definition smtlib_str_replace_re_all  :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string" where
 "smtlib_str_replace_re_all w L w2 = ''''" 


(*------------------------------------------------------------------------------------------------*)
(*-------------------------------------------- re.comp -------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (re.comp RegLan RegLan)
    \<lbrakk>str.comp\<rbrakk>(L) = UC* \ L *) 
definition smtlib_re_comp  :: "RegLan \<Rightarrow> RegLan" where
 "smtlib_re_comp L = UNIV - L" 


(*------------------------------------------------------------------------------------------------*)
(*-------------------------------------------- re.diff -------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (re.diff RegLan RegLan RegLan :left-assoc)
   \<lbrakk>re.diff\<rbrakk>(L1, L2) = L1 \ L2 *)
definition smtlib_re_diff  :: "RegLan \<Rightarrow> RegLan \<Rightarrow> RegLan" where
 "smtlib_re_diff L1 L2 = L1 - L2" 


(*------------------------------------------------------------------------------------------------*)
(*---------------------------------------------- re.+ --------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (re.+ RegLan RegLan)
   \<lbrakk>re.+\<rbrakk>(L) = \<lbrakk>re.++\<rbrakk>(L, \<lbrakk>re.*\<rbrakk>(L)) *)
definition smtlib_re_plus  :: "RegLan \<Rightarrow> RegLan" where
 "smtlib_re_plus L = smtlib_re_concat L (smtlib_re_star L)" 


(*------------------------------------------------------------------------------------------------*)
(*--------------------------------------------- re.opt -------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (re.opt RegLan RegLan)
    \<lbrakk>re.opt\<rbrakk>(L) = L \<union> { \<epsilon> } *)
definition smtlib_re_opt  :: "RegLan \<Rightarrow> RegLan" where
 "smtlib_re_opt rl = rl \<union> {''''}" 


(*------------------------------------------------------------------------------------------------*)
(*-------------------------------------------- re.range ------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (re.range String String RegLan)

    - \<lbrakk>re.range\<rbrakk>(w1, w2) = { w \<in> UC | w1 <= w <= w2 }  
      where <= is \<lbrakk>str.<=\<rbrakk>                             if |w1| = |w2| = 1
    - \<lbrakk>re.range\<rbrakk>(w1, w2) = \<emptyset>                           otherwise                     

    Note: \<lbrakk>re.range\<rbrakk>(\<lbrakk>""ab""\<rbrakk>, \<lbrakk>""c""\<rbrakk>) = \<lbrakk>re.range\<rbrakk>(\<lbrakk>""a""\<rbrakk>, \<lbrakk>""bc""\<rbrakk>) =
          \<lbrakk>re.range\<rbrakk>(\<lbrakk>""c""\<rbrakk>, \<lbrakk>""a""\<rbrakk>) =  \<emptyset> *)

definition smtlib_re_range  :: "string \<Rightarrow> string \<Rightarrow> RegLan" where
 "smtlib_re_range w1 w2 = (if length w1 = 1 \<and> length w2 = 1 then {w . smtlib_str_leq w1 w \<and> smtlib_str_leq w w2} else {})" 


(*------------------------------------------------------------------------------------------------*)
(*--------------------------------------------- re.^n --------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* ((_ re.^ n) RegLan RegLan)

    \<lbrakk>(_ re.^ n)\<rbrakk>(L) = Lⁿ  where Lⁿ is defined inductively on n as follows:
    - L⁰ = { \<epsilon> } 
    - Lⁿ⁺¹ = \<lbrakk>re.++\<rbrakk>(L, Lⁿ) *)
(*TODO*)
definition smtlib_re_pow  :: "RegLan \<Rightarrow> RegLan" where
 "smtlib_re_pow rl = rl" 


(*------------------------------------------------------------------------------------------------*)
(*-------------------------------------------- re.loop -------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* ((_ re.loop i n) RegLan RegLan)

    \<lbrakk>(_ re.loop i n)\<rbrakk>(L) = Lⁱ \<union> ... \<union> Lⁿ   if i <= n       
    \<lbrakk>(_ re.loop i n)\<rbrakk>(L) = \<emptyset>               otherwise *)
(*TODO*)
definition smtlib_re_loop :: "RegLan \<Rightarrow> RegLan" where
 "smtlib_re_loop rl = rl" 


(*------------------------------------------------------------------------------------------------*)
(*----------------------------------------- str.is_digit -----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(*(str.is_digit String Bool)
    \<lbrakk>str.is_digit\<rbrakk>(w) = true  iff |w| = 1 and 0x00030 <= w <= 0x00039 *)

definition smtlib_str_is_digit :: "string \<Rightarrow> bool" where
 "smtlib_str_is_digit w = (length w = 1 \<and> 0x00030 <= (of_char (hd w)::int) \<and> (of_char (hd w)::int) <= 0x00039)"


(*------------------------------------------------------------------------------------------------*)
(*------------------------------------------ str.to_code -----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.to_code String Int)

    - \<lbrakk>str.to_code\<rbrakk>(w) = -1         if |w| \<noteq> 1
    - \<lbrakk>str.to_code\<rbrakk>(w) = w          otherwise  (as w consists of a single code point) *)

definition smtlib_str_to_code :: "string \<Rightarrow> int" where
 "smtlib_str_to_code w = (if length w \<noteq> 1 then -1 else of_char (nth w 0))"


(*------------------------------------------------------------------------------------------------*)
(*----------------------------------------- str.from_code ----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(*(str.from_code Int String) 
                                     
    - \<lbrakk>str.from_code\<rbrakk>(n) = n        if 0x00000 <= n <= 0x2FFFF 
    - \<lbrakk>str.from_code\<rbrakk>(n) = \<epsilon>        otherwise
*)

definition smtlib_str_from_code :: "int \<Rightarrow> string" where (*TODO*)
 "smtlib_str_from_code n = (if 0x00000 \<le> n \<and> n \<le> 0x2FFFF then '''' else '''')"


(*------------------------------------------------------------------------------------------------*)
(*------------------------------------------ str.to_int ------------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(* (str.to_int String Int)

    - \<lbrakk>str.to_int\<rbrakk>(w) = -1 if w = \<lbrakk>l\<rbrakk>  
      where l is the empty string literal or one containing anything other than
      digits, i.e., characters with code point in the range 0x00030–0x00039

    - \<lbrakk>str.to_int\<rbrakk>(w) = n if w = \<lbrakk>l\<rbrakk>  
      where l is a string literal consisting of a single digit denoting number n

    - \<lbrakk>str.to_int\<rbrakk>(w) = 10*\<lbrakk>str.to_int\<rbrakk>(w1) + \<lbrakk>str.to_int\<rbrakk>(w2) if 
      - w = w1w2
      - |w1| > 0
      - |w2| = 1
      - \<lbrakk>str.to_int\<rbrakk>(w1) >= 0
      - \<lbrakk>str.to_int\<rbrakk>(w2) >= 0
 
    Note: This function is made total by mapping the empty word and words with
          non-digits to -1.

    Note: The function returns a non-negative number also for words that start
          with (characters corresponding to) superfluous zeros, such as 
          \<lbrakk>""0023""\<rbrakk>. *)

(*TODO*)
definition smtlib_str_to_int :: "string \<Rightarrow> int" where
 "smtlib_str_to_int w = -1"


(*------------------------------------------------------------------------------------------------*)
(*----------------------------------------- str.from_int -----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(*(str.from_int Int String)

    - \<lbrakk>str.from_int\<rbrakk>(n) = w  where w is the shortest word such that \<lbrakk>str.to_int\<rbrakk>(w) = n      if n >= 0
    - \<lbrakk>str.from_int\<rbrakk>(n) = \<epsilon>    otherwise

    Note: This function is made total by mapping negative integers
          to the empty word.

    Note: \<lbrakk>str.to_int\<rbrakk>(\<lbrakk>str.from_int\<rbrakk>(n)) = n iff n is a non-negative integer.

    Note: \<lbrakk>str.from_int\<rbrakk>(\<lbrakk>str.to_int\<rbrakk>(w)) = w iff w consists only of digits *and*
          has no leading zeros.*)

definition smtlib_str_from_int :: "int \<Rightarrow> string" where
 "smtlib_str_from_int n = (if n \<ge> 0 then (THE w. smtlib_str_to_int w = n \<and> (\<forall>w'::string . smtlib_str_to_int w = n --> length w' >= length w )) else '''')"

end

