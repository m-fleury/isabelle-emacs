theory Boolean_Rewrites
  imports Boolean_Rewrites_Lemmas
begin

(* This is a theory automatically created from a rare file! All that remains to do is to prove
any lemma whose auto proof fails and to to import this file in SMT.thy. 
If your rare statements use nary operators over lists that would be binarised by Isabelle 
you have to add it in Dsl_Nary_Ops.thy. Currently supported are the operators:
and,or*)

named_theorems bool_or_taut \<open>automatically_generated\<close>

lemma [bool_or_taut]:
  fixes zs::"bool cvc_ListVar" and ys::"bool cvc_ListVar" and w::"bool" and xs::"bool cvc_ListVar"
  shows "((cvc_list_left (\<or>) xs
 (w \<or> cvc_list_left (\<or>) ys (cvc_list_right (\<or>) (\<not> w) zs))) = (True))"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op)
    by (simp add: bool_or_taut_lemma)
  done

named_theorems bool_and_conf \<open>automatically_generated\<close>

lemma [bool_and_conf]:
  fixes zs::"bool cvc_ListVar" and ys::"bool cvc_ListVar" and w::"bool" and xs::"bool cvc_ListVar"
  shows "((cvc_list_left (\<and>) xs
 (w \<and>
  cvc_list_left (\<and>) ys (cvc_list_right (\<and>) (\<not> w) zs))) = (False))"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op)
    apply (simp add: bool_and_conf_lemma)
    done
  done

named_theorems bool_ite_not_cond \<open>automatically_generated\<close>

lemma [bool_ite_not_cond]:
  fixes y::"bool" and x::"bool" and c::"bool"
  shows "((if \<not> c then x else y) = (if c then y else x))"
  by auto

named_theorems bool_ite_false_cond \<open>automatically_generated\<close>

lemma [bool_ite_false_cond]:
  fixes y::"bool" and x::"bool"
  shows "((if False then x else y) = (y))"
  by auto

named_theorems bool_ite_true_cond \<open>automatically_generated\<close>

lemma [bool_ite_true_cond]:
  fixes y::"bool" and x::"bool"
  shows "((if True then x else y) = (x))"
  by auto

named_theorems bool_and_dup \<open>automatically_generated\<close>

(*xs = [] \<and> ys = []*)
(*b \<or> cvc_list_both (\<and>) True ys zs = b \<or> True     You would have this*)
(*b \<and> cvc_list_both (\<and>) True ys zs = b \<and> Neutral_And = b           You would have this*)
(*b \<and> cvc_list_both (\<and>) True ys zs = b \<and> True     Not this*)

lemma [bool_and_dup]:
  fixes zs::"bool cvc_ListVar" and ys::"bool cvc_ListVar" and b::"bool" and xs::"bool cvc_ListVar"
  shows "((cvc_list_left (\<and>) xs
 (b \<and> cvc_list_left (\<and>) ys (cvc_list_right (\<and>) b zs))) = (cvc_list_left (\<and>) xs (b \<and> cvc_list_both (\<and>) True ys zs)))"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: bool_and_dup_lemma)
  done

named_theorems bool_and_flatten \<open>automatically_generated\<close>

lemma [bool_and_flatten]:
  fixes zs::"bool cvc_ListVar" and ys::"bool cvc_ListVar" and b::"bool" and xs::"bool cvc_ListVar"
  shows "((cvc_list_left (\<and>) xs
 (cvc_list_right (\<and>) (cvc_list_right (\<and>) b ys) zs)) = (cvc_list_left (\<and>) xs
 (cvc_list_left (\<and>) zs (cvc_list_right (\<and>) b ys))))"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss
    apply (simp add: cvc_list_right_transfer_op)
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: bool_and_flatten_lemma)
  done

lemma "(x1 \<and> x2 \<and> (b \<and> y1) \<and> (z1 \<and> z2)) = (x1 \<and> x2 \<and> (z1 \<and> z2) \<and> b \<and> y1)"
  using bool_and_flatten[of "ListVar [x1,x2]" b "ListVar [y1]" "ListVar [(z1 \<and> z2)]"]
  unfolding cvc_list_right_def cvc_list_left_def cvc_list_both_def
  by simp

named_theorems bool_and_false \<open>automatically_generated\<close>

lemma [bool_and_false]:
  fixes ys::"bool cvc_ListVar" and xs::"bool cvc_ListVar"
  shows "((cvc_list_left (\<and>) xs (cvc_list_right (\<and>) False ys)) = (False))"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    done
  done


named_theorems bool_and_true \<open>automatically_generated\<close>

lemma [bool_and_true]:
  fixes ys::"bool cvc_ListVar" and xs::"bool cvc_ListVar"
  shows "((cvc_list_left (\<and>) xs (cvc_list_right (\<and>) True ys)) = (cvc_list_both (\<and>) True xs ys))"
  apply (cases ys)
  apply (cases xs)
  subgoal for yss xss
    by (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
  done

named_theorems bool_or_dup \<open>automatically_generated\<close>

lemma [bool_or_dup]:
  fixes zs::"bool cvc_ListVar" and ys::"bool cvc_ListVar" and b::"bool" and xs::"bool cvc_ListVar"
  shows "((cvc_list_left (\<or>) xs
 (b \<or>
  cvc_list_left (\<or>) ys
   (cvc_list_right (\<or>) b zs))) = (cvc_list_left (\<or>) xs
 (b \<or> cvc_list_both (\<or>) False ys zs)))"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: bool_or_dup_lemma)
  done

named_theorems bool_or_flatten \<open>automatically_generated\<close>

lemma [bool_or_flatten]:
  fixes zs::"bool cvc_ListVar" and ys::"bool cvc_ListVar" and b::"bool" and xs::"bool cvc_ListVar"
  shows "((cvc_list_left (\<or>) xs
 (cvc_list_right (\<or>) (cvc_list_right (\<or>) b ys) zs)) = (cvc_list_left (\<or>) xs
 (cvc_list_left (\<or>) zs (cvc_list_right (\<or>) b ys))))"
  apply (cases zs)
  apply (cases ys)
  apply (cases xs)
  subgoal for zss yss xss
    apply (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)
    by (simp add: bool_or_flatten_lemma)
  done


named_theorems bool_or_false \<open>automatically_generated\<close>

lemma [bool_or_false]:
  fixes ys::"bool cvc_ListVar" and xs::"bool cvc_ListVar"
  shows "((cvc_list_left (\<or>) xs (cvc_list_right (\<or>) False ys)) = (cvc_list_both (\<or>) False xs ys))"
  apply (cases ys)
  apply (cases xs)
  by (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)

named_theorems bool_or_true \<open>automatically_generated\<close>

lemma [bool_or_true]:
  fixes ys::"bool cvc_ListVar" and xs::"bool cvc_ListVar"
  shows "((cvc_list_left (\<or>) xs (cvc_list_right (\<or>) True ys)) = (True))"
  apply (cases ys)
  apply (cases xs)
  by (simp add: cvc_list_left_transfer cvc_list_right_transfer_op cvc_list_both_transfer)

named_theorems bool_impl_true2 \<open>automatically_generated\<close>

lemma [bool_impl_true2]:
  fixes t::"bool"
  shows "((True \<longrightarrow> t) = (t))"
  by auto

named_theorems bool_impl_true1 \<open>automatically_generated\<close>

lemma [bool_impl_true1]:
  fixes t::"bool"
  shows "((t \<longrightarrow> True) = (True))"
  by auto

named_theorems bool_impl_false2 \<open>automatically_generated\<close>

lemma [bool_impl_false2]:
  fixes t::"bool"
  shows "((False \<longrightarrow> t) = (True))"
  by auto

named_theorems bool_impl_false1 \<open>automatically_generated\<close>

lemma [bool_impl_false1]:
  fixes t::"bool"
  shows "((t \<longrightarrow> False) = (\<not> t))"
  by auto

named_theorems bool_eq_false \<open>automatically_generated\<close>

lemma [bool_eq_false]:
  fixes t::"bool"
  shows "((t = False) = (\<not> t))"
  by auto

named_theorems bool_eq_true \<open>automatically_generated\<close>

lemma [bool_eq_true]:
  fixes t::"bool"
  shows "((t = True) = (t))"
  by auto

named_theorems bool_double_neg_elim \<open>automatically_generated\<close>

lemma [bool_double_neg_elim]:
  fixes t::"bool"
  shows "((\<not> \<not> t) = (t))"
  by auto

named_theorems bool_eq_symm \<open>automatically_generated\<close>

lemma [bool_eq_symm]:
  fixes s::"bool" and t::"bool"
  shows "((t = s) = (s = t))"
  by auto

named_theorems bool_eq_refl \<open>automatically_generated\<close>

lemma [bool_eq_refl]:
  fixes t::"bool"
  shows "((t = t) = (True))"
  by auto

end