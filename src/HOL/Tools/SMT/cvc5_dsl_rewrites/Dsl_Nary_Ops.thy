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
(*TODO: QUESTION: Now that we don't always have neutral operators should this be replaced by SMTLIB
neutrals that are just defined?*)
named_theorems cvc_ListOp_neutral \<open>Neutral elements for cvc_ListOps\<close>
lemma cvc_ListOp_neutral_and [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (\<and>) True)" by simp
lemma cvc_ListOp_neutral_or [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (\<or>) False)" by simp
lemma cvc_ListOp_neutral_plus [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (+) (0::'a::monoid_add))" by simp
lemma cvc_ListOp_neutral_plus_int [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (+) (0::int))" by simp
lemma cvc_ListOp_neutral_mult [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (*) (1::int))" by simp
lemma cvc_ListOp_neutral_append [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (@) [])" by simp
lemma cvc_ListOp_neutral_re_concat [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (smtlib_re_concat) {''''})" 
  by (simp add: smtlib_re_concat_def)
lemma cvc_ListOp_neutral_str_concat [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (smtlib_str_concat) [])"
  by (simp add: smtlib_str_concat_def)
lemma cvc_ListOp_neutral_re_union [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (smtlib_re_union) {})"
  by (simp add: smtlib_re_union_def)
lemma cvc_ListOp_neutral_re_inter [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (smtlib_re_inter) (UNIV))"
  unfolding smtlib_re_inter_def by simp
lemma cvc_ListOp_neutral_bv_xor [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (semiring_bit_operations_class.xor) 0)"
  by simp
lemma cvc_ListOp_neutral_bv_or [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (semiring_bit_operations_class.or) 0)"
  by simp  



fun cvc_nary_op_fold :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a" where
 cvc_nary_op_fold_Nil: "cvc_nary_op_fold op [x] = x" |
 cvc_nary_op_fold_Cons: "cvc_nary_op_fold op (x#xs) = (op x (cvc_nary_op_fold op xs))"

fun cvc_bin_op_fold :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
 cvc_bin_op_fold_Nil: "cvc_bin_op_fold op [] y = y" |
 cvc_bin_op_fold_Cons: "cvc_bin_op_fold op (x#xs) y = (op x (cvc_bin_op_fold op xs y))"

(*op xs a    (op x1 (op ... (op xn a)))*)
(*and [] a = a *)
(*and [x] a = and x a*)

(*xs = [x1,xs], ys = [y1], zs = [(and z1 z2)]

  "((cvc_list_left (\<and>) xs
 (cvc_list_right (\<and>) (cvc_list_right (\<and>) b ys) zs)) = (cvc_list_left (\<and>) xs
 (cvc_list_left (\<and>) zs (cvc_list_right (\<and>) b ys))))"

xs = [x1, x2], ys = [y1], zs = [(and z1 z2)]

(and x1 (and x2 (and (and b y1) (and z2 z3)))) = (and x1 (and x2 (and (and z1 z2) (and b y1)))



(and x1 x2 (and b y1) (and z1 z2))

*)
fun cvc_bin_op where "cvc_bin_op op (ListVar xs) y = cvc_bin_op_fold op xs y"
fun cvc_bin_op2 where "cvc_bin_op2 op y (ListVar xs) = (if xs = [] then y else op y (cvc_nary_op_fold op xs))"
fun cvc_bin_op3 where "cvc_bin_op3 op (ListVar xs) (ListVar ys) neutral
   = (if ys = [] \<and> xs = [] then neutral
      else if ys = [] then (cvc_nary_op_fold op xs)
      else cvc_bin_op_fold op xs (cvc_nary_op_fold op ys))"

(* (\<and> b (\<or> xs ys))  = (\<and> b False) *)
(* (\<or> b (\<or> xs ys))  =  b *)
definition cvc_list_left where "cvc_list_left op lv y = cvc_bin_op op lv y"
definition cvc_list_right where "cvc_list_right op y lv = cvc_bin_op2 op y lv"
definition cvc_list_both where "cvc_list_both op neutral lv1 lv2 = cvc_bin_op3 op lv1 lv2 neutral"

value "((cvc_list_left (\<and>) (ListVar [x1, x2])
 (cvc_list_right (\<and>) (cvc_list_right (\<and>) b (ListVar [y1])) (ListVar [(z1 \<and> z2)]))) = (cvc_list_left (\<and>) (ListVar [x1, x2])
 (cvc_list_left (\<and>) (ListVar [(z1 \<and> z2)]) (cvc_list_right (\<and>) b (ListVar [y1])))))"


lemma transfer_h1:
  assumes "1 \<le> n" "cvc_isListOp (ListOp op neutral)"
  shows "n = length xs \<longrightarrow> cvc_nary_op_fold op xs = foldr op xs neutral"
proof-
  have
  "\<forall>xs. n = length xs \<longrightarrow> cvc_nary_op_fold op xs = foldr op xs neutral"
    apply (rule nat_induct_at_least[of 1 n "\<lambda>n. \<forall>xs. n = length xs \<longrightarrow> cvc_nary_op_fold op xs = foldr op xs neutral"])
    subgoal
      using assms by simp
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
          then have "cvc_nary_op_fold op xs = x" using t0 by auto
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
  then show ?thesis
    by auto
qed

lemma cvc_nary_op_fold_transfer:
  assumes "1 \<le> length xs " "cvc_isListOp (ListOp op neutral)"
  shows "cvc_nary_op_fold op xs = foldr op xs neutral"
  using transfer_h1 assms by metis

lemma cvc_bin_op_fold_transfer:
  shows "cvc_bin_op_fold op xs y = foldr op xs y"
  apply (induction xs)
  by auto

lemma cvc_list_left_transfer:
  shows "cvc_list_left op (ListVar xs) y = foldr op xs y"
  by (simp add: cvc_list_left_def cvc_bin_op_fold_transfer)

lemma cvc_list_right_transfer2': 
  assumes "cvc_isListOp (ListOp op neutral)"
  shows "cvc_list_right op y (ListVar xs) = (foldr op (y#xs) neutral)"
  apply (cases xs)
  unfolding cvc_list_right_def
  using assms apply auto[1]
  by (metis Dsl_Nary_Ops.cvc_nary_op_fold_Cons One_nat_def assms cvc_bin_op2.simps le_numeral_extra(4) list.distinct(1) list.size(4) trans_le_add2 transfer_h1)


lemma cvc_list_right_transfer: 
  assumes "cvc_isListOp (ListOp op neutral)"
  shows "cvc_list_right op y (ListVar xs) = op y (foldr op xs neutral)"
  apply (cases xs)
   apply simp
  using assms cvc_list_right_def
  apply (metis cvc_bin_op2.simps cvc_isListOp.simps)
  using assms cvc_list_right_def cvc_nary_op_fold_transfer
  by (metis One_nat_def cvc_bin_op2.simps le_numeral_extra(4) list.simps(3) list.size(4) trans_le_add2)

(*TODO: clean-up*)
lemma cvc_list_right_transfer_h1:
"cvc_list_right op y (ListVar (xs @ [xn])) = op y (foldr op xs xn)"
  apply (induction xs arbitrary: y)
   apply simp_all
   apply (simp add: cvc_list_right_def)
  unfolding cvc_list_right_def
  apply simp
  subgoal for x1 xss y
    apply (cases xss)
    by simp_all
  done


lemma cvc_list_right_transfer3: 
  assumes "xs \<noteq> []"
  shows "cvc_list_right op y (ListVar xs) = (foldr op (y # butlast xs) (last xs))"
  apply (cases "rev xs")
  using assms apply force
  using cvc_list_right_transfer_h1
  by (metis Dsl_Nary_Ops.cvc_bin_op_fold_Cons butlast_snoc cvc_bin_op_fold_transfer last_snoc rev_eq_Cons_iff)


lemma cvc_list_right_transfer2: 
  assumes "xs \<noteq> []"
  shows "cvc_list_right op y (ListVar xs) = op y (foldr op (butlast xs) (last xs))"
  apply (cases "rev xs")
  using assms apply force
  using cvc_list_right_transfer_h1
  by (metis Nil_is_rev_conv append_butlast_last_id list.distinct(1))


named_theorems cvc_list_right_transfer_op \<open>cvc_list_right_transfer instantiated with operator\<close>

lemma [cvc_list_right_transfer_op]: 
  "cvc_list_right (\<and>) y (ListVar xs) = (\<and>) y (foldr (\<and>) xs True)"
  by (simp add: cvc_list_right_transfer)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (\<or>) y (ListVar xs) = (\<or>) y (foldr (\<or>) xs False)"
  by (simp add: cvc_list_right_transfer)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (+) y (ListVar xs) = (+) y (foldr (+) xs (0::int))"
  by (simp add: cvc_list_right_transfer)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (+) y (ListVar xs) = (+) y (foldr (+) xs (0::'a::monoid_add))"
  by (simp add: cvc_list_right_transfer)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (*) y (ListVar xs) = (*) y (foldr (*) xs (1::int))"
  by (simp add: cvc_list_right_transfer)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (*) y (ListVar xs) = (*) y (foldr (*) xs (1::'a::monoid_mult))"
  by (simp add: cvc_list_right_transfer)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (@) y (ListVar xs) = (@) y (foldr (@) xs [])"
  by (simp add: cvc_list_right_transfer)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (smtlib_re_concat) y (ListVar xs) = (smtlib_re_concat) y (foldr (smtlib_re_concat) xs {''''})"
  by (meson cvc_ListOp_neutral_re_concat cvc_list_right_transfer)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (smtlib_str_concat) y (ListVar xs) = (smtlib_str_concat) y (foldr (smtlib_str_concat) xs [])"
  by (simp add: cvc_list_right_transfer smtlib_str_concat_def)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (smtlib_re_union) y (ListVar xs) = (smtlib_re_union) y (foldr (smtlib_re_union) xs {})"
  by (meson cvc_ListOp_neutral_re_union cvc_list_right_transfer)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (smtlib_re_inter) y (ListVar xs) = (smtlib_re_inter) y (foldr (smtlib_re_inter) xs (UNIV))"
  by (meson cvc_ListOp_neutral_re_inter cvc_list_right_transfer)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (semiring_bit_operations_class.xor) y (ListVar xs) = (semiring_bit_operations_class.xor) y (foldr (semiring_bit_operations_class.xor) xs 0)"
  by (simp add: cvc_list_right_transfer smtlib_str_concat_def)

lemma [cvc_list_right_transfer_op]:
  "cvc_list_right (semiring_bit_operations_class.or) y (ListVar xs) = (semiring_bit_operations_class.or) y (foldr (semiring_bit_operations_class.or) xs 0)"
  by (simp add: cvc_list_right_transfer smtlib_str_concat_def)

lemma [cvc_list_right_transfer_op]:
  "xs \<noteq> [] \<longrightarrow> cvc_list_right (semiring_bit_operations_class.and) y (ListVar xs) = (semiring_bit_operations_class.and) y (foldr (semiring_bit_operations_class.and) (butlast xs) (last xs))"
  using cvc_list_right_transfer2[of xs "(semiring_bit_operations_class.and)" y]
  by blast




lemma cvc_list_both_transfer: 
  assumes "cvc_isListOp (ListOp op neutral)"
  shows "cvc_list_both op neutral (ListVar ys) (ListVar xs) = foldr op ys (foldr op xs neutral)"
  using assms
  apply (cases "xs = [] \<and> ys = []")
   apply simp
  unfolding cvc_list_both_def
  apply simp
  apply (cases ys)
  unfolding cvc_list_both_def
    apply simp
  apply (metis assms(1) cvc_bin_op2.simps cvc_list_right_def cvc_list_right_transfer)
  by (metis One_nat_def cvc_bin_op.simps cvc_bin_op3.simps cvc_bin_op_fold_transfer cvc_nary_op_fold_transfer foldr.simps(1) id_apply length_0_conv less_Suc0 linorder_not_less)

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
