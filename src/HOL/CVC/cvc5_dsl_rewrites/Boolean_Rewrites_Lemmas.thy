theory Boolean_Rewrites_Lemmas
  imports Dsl_Nary_Ops
begin

lemma foldr_or_neutral [simp]: "foldr (\<or>) xs True = True"
  apply (induction xs)
  by auto

lemma foldr_and_neutral [simp]: "foldr (\<and>) xs False = False"
  apply (induction xs)
  by auto

lemma bool_or_taut_lemma: 
  "foldr (\<or>) xss (w \<or> foldr (\<or>) yss (w \<longrightarrow> foldr (\<or>) zss False))"
    apply (induction zss)
     apply (induction yss)
     apply (induction xss)
     apply simp_all
  apply (metis (mono_tags, lifting) foldr_or_neutral)
  by metis


lemma bool_and_conf_lemma:
  "\<not> foldr (\<and>) xss (w \<and> foldr (\<and>) yss (\<not> w \<and> foldr (\<and>) zss True))"
  apply (induction zss)
   apply (induction yss)
    apply (induction xss)
     apply simp_all
   apply (metis (mono_tags, lifting) foldr_and_neutral)
  by (metis (mono_tags, lifting))


lemma bool_and_dup_lemma:
  "foldr (\<and>) xss (b \<and> foldr (\<and>) yss (b \<and> foldr (\<and>) zss True))
 = foldr (\<and>) xss (b \<and> foldr (\<and>) yss (foldr (\<and>) zss True))"
  apply (induction zss)
   apply (induction yss)
    apply (induction xss)
     apply simp_all
  apply metis
  by metis

lemma bool_and_flatten_lemma:
  "foldr (\<and>) xss (b \<and> foldr (\<and>) yss True \<and> foldr (\<and>) zss True)
  = foldr (\<and>) xss (foldr (\<and>) zss (b \<and> foldr (\<and>) yss True))"
    apply (induction zss)
     apply simp_all
     apply (induction yss)
      apply simp_all
     apply (induction xss)
      apply simp_all
    apply (metis foldr_and_neutral)
     apply (metis foldr_and_neutral)
    by (metis foldr_and_neutral)

lemma bool_or_dup_lemma:
  "foldr (\<or>) xss (b \<or> foldr (\<or>) yss (b \<or> foldr (\<or>) zss False))
 = foldr (\<or>) xss (b \<or> foldr (\<or>) yss (foldr (\<or>) zss False))"
  apply (induction zss)
   apply simp_all
     apply (induction yss)
      apply simp_all
     apply (induction xss)
      apply simp_all
    apply blast
  apply blast
  by (metis foldr_or_neutral)

lemma bool_or_flatten_lemma:
  "foldr (\<or>) xss (b \<or> foldr (\<or>) yss False \<or> foldr (\<or>) zss False)
 = foldr (\<or>) xss (foldr (\<or>) zss (b \<or> foldr (\<or>) yss False))"
  apply (induction zss)
   apply simp_all
     apply (induction yss)
      apply simp_all
     apply (induction xss)
      apply simp_all
    apply blast
  apply blast
  by (metis foldr_or_neutral)

end