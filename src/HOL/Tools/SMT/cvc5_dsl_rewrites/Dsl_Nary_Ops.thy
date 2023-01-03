theory Dsl_Nary_Ops
  imports Main
begin

datatype 'a cvc_ListVar = ListVar "'a list"
datatype 'a cvc_ListOp = ListOp "'a \<Rightarrow> 'a \<Rightarrow> 'a" "'a" (*TODO: Could be generalized*)

fun cvc_isListOp where
 "cvc_isListOp (ListOp op neutralElement) =
 ((\<forall>x. op x neutralElement = x) \<and> (\<forall>x. op neutralElement x = x))"

(*Standard operators. If operator is not part of those the user has to add a custom lemma here by 
explicitly stating the neutral element of their operation*)
named_theorems cvc_ListOp_neutral \<open>Neutral elements for cvc_ListOps\<close>
lemma cvc_ListOp_neutral_and [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (\<and>) True)" by simp
lemma cvc_ListOp_neutral_or [cvc_ListOp_neutral]: "cvc_isListOp (ListOp (\<or>) False)" by simp

fun cvc_nary_op_fold :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a" where
 cvc_nary_op_fold_Nil: "cvc_nary_op_fold op [x] = x" |
 cvc_nary_op_fold_Cons: "cvc_nary_op_fold op (x#xs) = (op x (cvc_nary_op_fold op xs))"

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

lemma transfer1:
  assumes "1 \<le> length xs " "cvc_isListOp (ListOp op neutral)"
  shows "cvc_nary_op_fold op xs = foldr op xs neutral"
  using transfer_h1 assms by metis


fun cvc_bin_op_fold :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
 cvc_bin_op_fold_Nil: "cvc_bin_op_fold op [] y = y" |
 cvc_bin_op_fold_Cons: "cvc_bin_op_fold op (x#xs) y = (op x (cvc_bin_op_fold op xs y))"

lemma transfer2:
  shows "cvc_bin_op_fold op xs y = foldr op xs y"
  apply (induction xs)
  by auto

fun cvc_bin_op where "cvc_bin_op op (ListVar xs) y = cvc_bin_op_fold op xs y"
fun cvc_bin_op2 where "cvc_bin_op2 op y (ListVar xs) = (if xs = [] then y else op y (cvc_nary_op_fold op xs))"
fun cvc_bin_op3 where "cvc_bin_op3 op (ListVar xs) (ListVar ys)
   = (if ys = [] then (cvc_nary_op_fold op xs) else cvc_bin_op op (ListVar xs) (cvc_nary_op_fold op ys))"

definition cvc_list_left where "cvc_list_left op lv y = cvc_bin_op op lv y"
definition cvc_list_right where "cvc_list_right op y lv = cvc_bin_op2 op y lv"
definition cvc_list_both where "cvc_list_both op lv1 lv2 = cvc_bin_op3 op lv1 lv2"

lemma cvc_list_left_transfer: "cvc_list_left op (ListVar xs) y = foldr op xs y"
  by (simp add: cvc_list_left_def transfer2)

lemma cvc_list_right_transfer: 
  assumes "cvc_isListOp (ListOp op neutral)"
  shows "cvc_list_right op y (ListVar xs) = op y (foldr op xs neutral)"
  apply (cases xs)
   apply simp
  using assms cvc_list_right_def
  apply (metis cvc_bin_op2.simps cvc_isListOp.simps)
  using assms cvc_list_right_def transfer1
  by (metis One_nat_def cvc_bin_op2.simps le_numeral_extra(4) list.simps(3) list.size(4) trans_le_add2)

lemma cvc_list_left_Nil: "cvc_list_left op (ListVar []) y = y"
  unfolding cvc_list_left_def
  by simp

lemma cvc_list_right_Nil: "cvc_list_right op y (ListVar []) = y"
  unfolding cvc_list_right_def 
  by simp

(*Note that: "cvc_list_both (\<and>) (ListVar []) (ListVar []) = y" is forbidden and should be ruled out
by parsing*)
lemma cvc_list_both_Singleton: "cvc_list_both op (ListVar [x]) (ListVar []) = x"
                     "cvc_list_both op (ListVar []) (ListVar [x]) = x"
                     "cvc_list_both op (ListVar []) (ListVar [x]) = x"
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

lemma cvc_list_both_Cons: "cvc_list_both op (ListVar (x#xs)) (ListVar (y#ys))
       = op x (cvc_list_both op (ListVar xs) (ListVar (y#ys)))"
  unfolding cvc_list_both_def
  apply (induction xs)
  by auto

lemma test: "foldr (\<and>) c (b \<and> foldr (\<and>) d True \<and> foldr (\<and>) e True) = foldr (\<and>) c (foldr (\<and>) e (b \<and> foldr (\<and>) d True))"
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
  unfolding cvc_list_left_transfer
  unfolding cvc_list_right_transfer
  using cvc_list_right_transfer[of "(\<and>)" True b ] 
  apply simp
  subgoal for c d e
    using cvc_list_right_transfer[of "(\<and>)" True "(b \<and> foldr (\<and>) d True)" e]
    apply simp
    using test
    by auto
  done

lemma "a \<and> (c \<and> (b \<and> d)) \<longrightarrow> (a \<and> (c \<and> (b \<and> d)))"
  using bool_and_flatten_test[of "ListVar [a,c]" b "ListVar [d]" "ListVar []"]
  apply (unfold cvc_list_right_Nil)
  unfolding cvc_list_right_Nil cvc_list_left_Nil
  unfolding cvc_list_right_Cons cvc_list_left_Cons
  unfolding cvc_list_right_Nil cvc_list_left_Nil
  by simp



end
