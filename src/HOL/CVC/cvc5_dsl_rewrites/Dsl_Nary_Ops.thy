theory Dsl_Nary_Ops
  imports Smtlib_String
begin

datatype 'a cvc_ListVar = ListVar "'a list"
datatype 'a cvc_ListOp = ListOp "'a \<Rightarrow> 'a \<Rightarrow> 'a" "'a"

fun cvc_isListOp where
 "cvc_isListOp (ListOp op neutralElement) =
 ((\<forall>x. op x neutralElement = x) \<and> (\<forall>x. op neutralElement x = x))"

(*

Standard operators. If operator is not part of those the user has to add a custom lemma here by 
explicitly stating the neutral element of their operation
There are some operators which have no neutral element, e.g, and on bitvectors. In that case an
additional assumption should be added to the lemma making sure that not all operands can be empty
at the same time and a lemma should be proven below with the same assumption.

*)

lemma cvc_ListOp_neutral:
  shows cvc_ListOp_neutral_and: "cvc_isListOp (ListOp (\<and>) True)"
  and cvc_ListOp_neutral_or: "cvc_isListOp (ListOp (\<or>) False)"
  and cvc_ListOp_neutral_plus: "cvc_isListOp (ListOp (+) (0::'a::monoid_add))"
  and cvc_ListOp_neutral_plus_int: "cvc_isListOp (ListOp (+) (0::int))"
  and cvc_ListOp_neutral_mult: "cvc_isListOp (ListOp (*) (1::int))"
  and cvc_ListOp_neutral_append: "cvc_isListOp (ListOp (@) [])"
  and cvc_ListOp_neutral_re_concat: "cvc_isListOp (ListOp (smtlib_re_concat) {''''})"
  and cvc_ListOp_neutral_str_concat: "cvc_isListOp (ListOp (smtlib_str_concat) [])"
  and cvc_ListOp_neutral_re_union: "cvc_isListOp (ListOp (smtlib_re_union) {})"
  and cvc_ListOp_neutral_re_inter: "cvc_isListOp (ListOp (smtlib_re_inter) (UNIV))"
  and cvc_ListOp_neutral_bv_xor: "cvc_isListOp (ListOp (semiring_bit_operations_class.xor) 0)"
  and cvc_ListOp_neutral_bv_or: "cvc_isListOp (ListOp (semiring_bit_operations_class.or) 0)"
  by (simp_all add: smtlib_re_concat_def smtlib_str_concat_def smtlib_re_union_def
                    smtlib_re_inter_def)

(*Since the SMT-LIB term parser in Isabelle parses all operators as right-associative we assume
that this is the case. Further testing is needed to see if this is enough. *)

fun cvc_nary_op_fold :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a" where
 cvc_nary_op_fold_Nil: "cvc_nary_op_fold op [x] = x" |
 cvc_nary_op_fold_Cons: "cvc_nary_op_fold op (x#xs) = (op x (cvc_nary_op_fold op xs))"

fun cvc_bin_op_fold :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
 cvc_bin_op_fold_Nil: "cvc_bin_op_fold op [] y = y" |
 cvc_bin_op_fold_Cons: "cvc_bin_op_fold op (x#xs) y = (op x (cvc_bin_op_fold op xs y))"

fun cvc_bin_op where
 "cvc_bin_op op (ListVar xs) y = cvc_bin_op_fold op xs y"
fun cvc_bin_op2 where
 "cvc_bin_op2 op y (ListVar xs) = (if xs = [] then y else op y (cvc_nary_op_fold op xs))"
fun cvc_bin_op3 where
  "cvc_bin_op3 op (ListVar []) (ListVar []) neutral = neutral" | 
  "cvc_bin_op3 op (ListVar xs) (ListVar []) neutral = cvc_nary_op_fold op xs" | 
  "cvc_bin_op3 op (ListVar xs) (ListVar ys) neutral = cvc_bin_op_fold op xs (cvc_nary_op_fold op ys)"

definition cvc_list_left where "cvc_list_left op lv y = cvc_bin_op op lv y"
definition cvc_list_right where "cvc_list_right op y lv = cvc_bin_op2 op y lv"
definition cvc_list_both where "cvc_list_both op neutral lv1 lv2 = cvc_bin_op3 op lv1 lv2 neutral"

lemma cvc_nary_op_fold_transfer_h1:
  assumes "1 \<le> n" "cvc_isListOp (ListOp op neutral)"
  shows "\<forall>xs. n = length xs \<longrightarrow> cvc_nary_op_fold op xs = foldr op xs neutral"
  apply (induct_tac rule: nat_induct_at_least[of 1])
  subgoal
    using assms(1) by simp
  subgoal
    proof(rule allI,rule impI)
    fix xs::"'a list"
    assume a0: "1 = length xs"
    obtain x where t0: "[x] = xs"
      by (metis One_nat_def Suc_length_conv a0 length_0_conv)
    have "cvc_nary_op_fold op xs = x"
      using t0 cvc_nary_op_fold_Nil by force
    moreover have "foldr op xs neutral = (op x neutral)"
      using t0 by force
    ultimately show "cvc_nary_op_fold op xs = foldr op xs neutral"
      using assms(2) by auto
  qed      
  subgoal for n
  proof(rule allI, rule impI)
    fix xs::"'a list"
    assume a0: "1 \<le> n"
    assume a1: "\<forall>xs. n = length xs \<longrightarrow> cvc_nary_op_fold op xs = foldr op xs neutral"
    assume a2: "Suc n = length xs"
    then obtain x xss where t0: "xs = x#xss"
      by (meson Suc_length_conv)
    show "cvc_nary_op_fold op xs = foldr op xs neutral"
    proof(cases "xss = []")
      assume a00: "xss = []"
      then show "cvc_nary_op_fold op xs = foldr op xs neutral"
        using a0 a00 a2 t0 by auto
    next
      assume a01: "xss \<noteq> []"
      then have "cvc_nary_op_fold op xs = op x (cvc_nary_op_fold op xss)" 
        using cvc_nary_op_fold.elims(1) t0
        by (metis list.inject list.simps(3))
      then have "cvc_nary_op_fold op xs = op x (foldr op xss neutral)" 
        using a1 a2 t0 by fastforce
      then show "cvc_nary_op_fold op xs = (foldr op xs neutral)" 
        by (simp add: t0)
    qed
  qed
done
  
lemma cvc_nary_op_fold_transfer:
  assumes "1 \<le> length xs " "cvc_isListOp (ListOp op neutral)"
  shows "cvc_nary_op_fold op xs = foldr op xs neutral"
  by (meson assms(1) assms(2) cvc_nary_op_fold_transfer_h1)

lemma cvc_bin_op_fold_transfer: "cvc_bin_op_fold op xs y = foldr op xs y"
  apply (induction xs)
  by auto

(*Left Transfer*)

lemma cvc_list_left_transfer:
  shows "cvc_list_left op (ListVar xs) y = foldr op xs y"
  by (simp add: cvc_list_left_def cvc_bin_op_fold_transfer)

(*Right Transfer*)

lemma cvc_list_right_transfer_neutral1: 
  assumes "cvc_isListOp (ListOp op neutral)"
  shows "cvc_list_right op y (ListVar xs) = op y (foldr op xs neutral)"
  using assms
  unfolding cvc_list_right_def
  apply (cases xs)
  by (simp_all add: cvc_nary_op_fold_transfer)

lemma cvc_list_right_transfer_neutral2: 
  assumes "cvc_isListOp (ListOp op neutral)"
  shows "cvc_list_right op y (ListVar xs) = (foldr op (y#xs) neutral)"
  using assms
  unfolding cvc_list_right_def
  apply (cases xs)
  by (simp_all add: cvc_nary_op_fold_transfer)

lemma cvc_list_right_transfer:
  "cvc_list_right op y (ListVar (xs @ [xn])) = op y (foldr op xs xn)"
  apply (induction xs arbitrary: y)
  unfolding cvc_list_right_def
  apply simp
  subgoal for x1 xss yshows
    apply (cases xss)
    by simp_all
  done

lemma cvc_list_right_transfer_2: 
  assumes "xs \<noteq> []"
  shows "cvc_list_right op y (ListVar xs) = (foldr op (y # butlast xs) (last xs))"
  apply (cases "rev xs")
  using assms apply force
  by (simp add: cvc_list_right_transfer)

(*TODO: Hopefully these can be safely deleted after testing is complete*)
named_theorems cvc_list_right_transfer_op \<open>cvc_list_right_transfer instantiated with operator\<close>

lemma [cvc_list_right_transfer_op]: 
  "cvc_list_right (\<and>) y (ListVar xs) = (\<and>) y (foldr (\<and>) xs True)"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (\<or>) y (ListVar xs) = (\<or>) y (foldr (\<or>) xs False)"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (+) y (ListVar xs) = (+) y (foldr (+) xs (0::int))"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (+) y (ListVar xs) = (+) y (foldr (+) xs (0::'a::monoid_add))"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (*) y (ListVar xs) = (*) y (foldr (*) xs (1::int))"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (*) y (ListVar xs) = (*) y (foldr (*) xs (1::'a::monoid_mult))"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (@) y (ListVar xs) = (@) y (foldr (@) xs [])"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (smtlib_re_concat) y (ListVar xs)
   = (smtlib_re_concat) y (foldr (smtlib_re_concat) xs {''''})"
  by (meson cvc_ListOp_neutral_re_concat cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (smtlib_str_concat) y (ListVar xs)
   = (smtlib_str_concat) y (foldr (smtlib_str_concat) xs [])"
  by (simp add: cvc_list_right_transfer_neutral1 smtlib_str_concat_def)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (smtlib_re_union) y (ListVar xs)
   = (smtlib_re_union) y (foldr (smtlib_re_union) xs {})"
  by (meson cvc_ListOp_neutral_re_union cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (smtlib_re_inter) y (ListVar xs)
   = (smtlib_re_inter) y (foldr (smtlib_re_inter) xs (UNIV))"
  by (meson cvc_ListOp_neutral_re_inter cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (semiring_bit_operations_class.xor) y (ListVar xs)
   = (semiring_bit_operations_class.xor) y (foldr (semiring_bit_operations_class.xor) xs 0)"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (semiring_bit_operations_class.or) y (ListVar xs)
   = (semiring_bit_operations_class.or) y (foldr (semiring_bit_operations_class.or) xs 0)"
  by (simp add: cvc_list_right_transfer_neutral1)

lemma [cvc_list_right_transfer_op]:
  "xs \<noteq> [] \<longrightarrow> cvc_list_right (semiring_bit_operations_class.and) y (ListVar xs)
   = (semiring_bit_operations_class.and) y (foldr (semiring_bit_operations_class.and) (butlast xs)
   (last xs))"
  by (simp add: cvc_list_right_transfer_2)


(*Both Transfer*)

lemma cvc_list_both_transfer: 
  assumes "cvc_isListOp (ListOp op neutral)"
  shows "cvc_list_both op neutral (ListVar ys) (ListVar xs) = foldr op ys (foldr op xs neutral)"
  using assms
  unfolding cvc_list_both_def
  apply(cases \<open>(op,(ListVar ys),(ListVar xs),neutral)\<close>  rule: cvc_bin_op3.cases)
  by (simp_all add: cvc_bin_op_fold_transfer cvc_nary_op_fold_transfer)

named_theorems cvc_list_both_transfer_op \<open>cvc_list_both_transfer instantiated with operator\<close>

lemma [cvc_list_both_transfer_op]: 
  "cvc_list_both (\<and>) True (ListVar ys) (ListVar xs) = foldr (\<and>) ys (foldr (\<and>) xs True)"
  by (simp add: cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (\<or>) False (ListVar ys) (ListVar xs) = foldr (\<or>) ys (foldr (\<or>) xs False)"
  by (simp add: cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (+) (0::int) (ListVar ys) (ListVar xs) = foldr (+) ys (foldr (+) xs 0)"
  by (simp add: cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (*) (1::int) (ListVar ys) (ListVar xs) = foldr (*) ys (foldr (*) xs 1)"
  by (simp add: cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (@) [] (ListVar ys) (ListVar xs) = foldr (@) ys (foldr (@) xs [])"
  by (simp add: cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (smtlib_re_concat) {''''} (ListVar ys) (ListVar xs) = foldr (smtlib_re_concat) ys (foldr (smtlib_re_concat) xs {''''})"
  by (meson cvc_ListOp_neutral_re_concat cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (smtlib_str_concat) [] (ListVar ys) (ListVar xs) = foldr (smtlib_str_concat) ys (foldr (smtlib_str_concat) xs [])"
  by (meson cvc_ListOp_neutral_str_concat cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (smtlib_re_union) {} (ListVar ys) (ListVar xs) = foldr (smtlib_re_union) ys (foldr (smtlib_re_union) xs {})"
  by (meson cvc_ListOp_neutral_re_union cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (smtlib_re_inter) (UNIV) (ListVar ys) (ListVar xs) = foldr (smtlib_re_inter) ys (foldr (smtlib_re_inter) xs (UNIV))"
  by (meson cvc_ListOp_neutral_re_inter cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (semiring_bit_operations_class.xor) 0 (ListVar ys) (ListVar xs) = foldr (semiring_bit_operations_class.xor) ys (foldr (semiring_bit_operations_class.xor) xs 0)"
  by (meson cvc_ListOp_neutral_bv_xor cvc_list_both_transfer)

lemma [cvc_list_both_transfer_op]:
  "cvc_list_both (semiring_bit_operations_class.or) 0 (ListVar ys) (ListVar xs) = foldr (semiring_bit_operations_class.or) ys (foldr (semiring_bit_operations_class.or) xs 0)"
  by (meson cvc_ListOp_neutral_bv_or cvc_list_both_transfer)

lemma cvc_list_left_Nil: "cvc_list_left op (ListVar []) y = y"
  unfolding cvc_list_left_def
  by simp

lemma cvc_list_right_Nil: "cvc_list_right op y (ListVar []) = y"
  unfolding cvc_list_right_def 
  by simp

(*Note that: "cvc_list_both (\<and>) (ListVar []) (ListVar []) = y" is forbidden and should be ruled out
by parsing*)
lemma cvc_list_both_Singleton: "cvc_list_both op neutral (ListVar [x]) (ListVar []) = x"
                     "cvc_list_both op neutral (ListVar []) (ListVar [x]) = x"
                     "cvc_list_both op neutral (ListVar []) (ListVar [x]) = x"
  unfolding cvc_list_both_def
  by auto

lemma cvc_list_left_Cons: "cvc_list_left op (ListVar (x#xs)) y
    = op x (cvc_list_left op (ListVar xs) y)"
  unfolding cvc_list_left_def
  apply (induction xs)
  by auto

lemma cvc_list_right_Cons: "cvc_list_right op y (ListVar (x#xs))
       = op y (cvc_list_right op x (ListVar xs))"
  unfolding cvc_list_right_def
  apply (induction xs)
  by auto

lemma cvc_list_both_Cons: "cvc_list_both op neutral (ListVar (x#xs)) (ListVar (y#ys))
       = op x (cvc_list_both op neutral (ListVar xs) (ListVar (y#ys)))"
  unfolding cvc_list_both_def
  apply (induction xs)
  by auto


lemma bool_and_flatten_test_help:
  shows  "foldr (\<and>) c (b \<and> foldr (\<and>) d True \<and> foldr (\<and>) e True) = foldr (\<and>) c (foldr (\<and>) e (b \<and> foldr (\<and>) d True))"
  apply (induction c)
   apply simp
   apply (induction d)
    apply simp
    apply (induction e)
     apply simp
    apply simp
    apply blast
   apply (induction e)
    apply simp
  apply auto[1]
   apply (induction d)
   apply simp
  by simp

lemma bool_and_flatten_test:
  fixes xs ys zs :: "bool cvc_ListVar"
  shows "(cvc_list_left (\<and>) xs (cvc_list_right (\<and>) (cvc_list_right (\<and>) b ys) zs))
 = (cvc_list_left (\<and>) xs (cvc_list_left (\<and>) zs (cvc_list_right (\<and>) b ys)))"
  apply (cases xs)
  apply (cases ys)
  apply (cases zs)
  apply simp_all
  subgoal for xss yss zss
  unfolding cvc_list_left_transfer
  unfolding cvc_list_right_transfer_op
  using bool_and_flatten_test_help by auto
  done

lemma test: "a \<and> (c \<and> (b \<and> d)) \<longrightarrow> (a \<and> (c \<and> (b \<and> d)))"
  using bool_and_flatten_test[of "ListVar [a,c]" b "ListVar [d]" "ListVar []"]
  apply (unfold cvc_list_right_Nil)
  unfolding cvc_list_right_Nil cvc_list_left_Nil
  unfolding cvc_list_right_Cons cvc_list_left_Cons
  unfolding cvc_list_right_Nil cvc_list_left_Nil
  by simp

end
