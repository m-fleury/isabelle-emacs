theory Dsl_Nary_Ops_String
  imports Smtlib_String "HOL.Dsl_Nary_Ops"
begin

lemma 
      cvc_ListOp_neutral_re_concat[cvc_ListOp_neutral]: "cvc_isListOp (ListOp (smtlib_re_concat) {''''})"
  and cvc_ListOp_neutral_str_concat[cvc_ListOp_neutral]: "cvc_isListOp (ListOp (smtlib_str_concat) [])"
  and cvc_ListOp_neutral_re_union[cvc_ListOp_neutral]: "cvc_isListOp (ListOp (smtlib_re_union) {})"
  and cvc_ListOp_neutral_re_inter[cvc_ListOp_neutral]: "cvc_isListOp (ListOp (smtlib_re_inter) (UNIV))"
  and cvc_ListOp_neutral_bv_xor[cvc_ListOp_neutral]: "cvc_isListOp (ListOp (semiring_bit_operations_class.xor) 0)"
  and cvc_ListOp_neutral_bv_or[cvc_ListOp_neutral]: "cvc_isListOp (ListOp (semiring_bit_operations_class.or) 0)"
  by (simp_all add: smtlib_re_concat_def smtlib_str_concat_def smtlib_re_union_def
                    smtlib_re_inter_def)

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

end