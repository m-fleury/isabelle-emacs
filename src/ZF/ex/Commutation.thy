(*  Title:      ZF/ex/Commutation.thy
    Author:     Tobias Nipkow & Sidi Ould Ehmety
    Copyright   1995  TU Muenchen

Commutation theory for proving the Church Rosser theorem.
*)

theory Commutation imports ZF begin

definition
  square  :: "[i, i, i, i] \<Rightarrow> o" where
  "square(r,s,t,u) \<equiv>
    (\<forall>a b. \<langle>a,b\<rangle> \<in> r \<longrightarrow> (\<forall>c. \<langle>a, c\<rangle> \<in> s \<longrightarrow> (\<exists>x. \<langle>b,x\<rangle> \<in> t \<and> \<langle>c,x\<rangle> \<in> u)))"

definition
  commute :: "[i, i] \<Rightarrow> o" where
  "commute(r,s) \<equiv> square(r,s,s,r)"

definition
  diamond :: "i\<Rightarrow>o" where
  "diamond(r)   \<equiv> commute(r, r)"

definition
  strip :: "i\<Rightarrow>o" where
  "strip(r) \<equiv> commute(r^*, r)"

definition
  Church_Rosser :: "i \<Rightarrow> o" where
  "Church_Rosser(r) \<equiv> (\<forall>x y. \<langle>x,y\<rangle> \<in>  (r \<union> converse(r))^* \<longrightarrow>
                        (\<exists>z. \<langle>x,z\<rangle> \<in> r^* \<and> \<langle>y,z\<rangle> \<in> r^*))"

definition
  confluent :: "i\<Rightarrow>o" where
  "confluent(r) \<equiv> diamond(r^*)"


lemma square_sym: "square(r,s,t,u) \<Longrightarrow> square(s,r,u,t)"
  unfolding square_def by blast

lemma square_subset: "\<lbrakk>square(r,s,t,u); t \<subseteq> t'\<rbrakk> \<Longrightarrow> square(r,s,t',u)"
  unfolding square_def by blast


lemma square_rtrancl:
  "square(r,s,s,t) \<Longrightarrow> field(s)<=field(t) \<Longrightarrow> square(r^*,s,s,t^*)"
apply (unfold square_def, clarify)
apply (erule rtrancl_induct)
apply (blast intro: rtrancl_refl)
apply (blast intro: rtrancl_into_rtrancl)
done

(* A special case of square_rtrancl_on *)
lemma diamond_strip:
  "diamond(r) \<Longrightarrow> strip(r)"
  unfolding diamond_def commute_def strip_def
apply (rule square_rtrancl, simp_all)
done

(*** commute ***)

lemma commute_sym: "commute(r,s) \<Longrightarrow> commute(s,r)"
  unfolding commute_def by (blast intro: square_sym)

lemma commute_rtrancl:
  "commute(r,s) \<Longrightarrow> field(r)=field(s) \<Longrightarrow> commute(r^*,s^*)"
  unfolding commute_def
apply (rule square_rtrancl)
apply (rule square_sym [THEN square_rtrancl, THEN square_sym])
apply (simp_all add: rtrancl_field)
done


lemma confluentD: "confluent(r) \<Longrightarrow> diamond(r^*)"
by (simp add: confluent_def)

lemma strip_confluent: "strip(r) \<Longrightarrow> confluent(r)"
  unfolding strip_def confluent_def diamond_def
apply (drule commute_rtrancl)
apply (simp_all add: rtrancl_field)
done

lemma commute_Un: "\<lbrakk>commute(r,t); commute(s,t)\<rbrakk> \<Longrightarrow> commute(r \<union> s, t)"
  unfolding commute_def square_def by blast

lemma diamond_Un:
     "\<lbrakk>diamond(r); diamond(s); commute(r, s)\<rbrakk> \<Longrightarrow> diamond(r \<union> s)"
  unfolding diamond_def by (blast intro: commute_Un commute_sym)

lemma diamond_confluent:
    "diamond(r) \<Longrightarrow> confluent(r)"
  unfolding diamond_def confluent_def
apply (erule commute_rtrancl, simp)
done

lemma confluent_Un:
 "\<lbrakk>confluent(r); confluent(s); commute(r^*, s^*);
     relation(r); relation(s)\<rbrakk> \<Longrightarrow> confluent(r \<union> s)"
  unfolding confluent_def
apply (rule rtrancl_Un_rtrancl [THEN subst], auto)
apply (blast dest: diamond_Un intro: diamond_confluent [THEN confluentD])
done


lemma diamond_to_confluence:
     "\<lbrakk>diamond(r); s \<subseteq> r; r<= s^*\<rbrakk> \<Longrightarrow> confluent(s)"
apply (drule rtrancl_subset [symmetric], assumption)
apply (simp_all add: confluent_def)
apply (blast intro: diamond_confluent [THEN confluentD])
done


(*** Church_Rosser ***)

lemma Church_Rosser1:
     "Church_Rosser(r) \<Longrightarrow> confluent(r)"
apply (unfold confluent_def Church_Rosser_def square_def
              commute_def diamond_def, auto)
apply (drule converseI)
apply (simp (no_asm_use) add: rtrancl_converse [symmetric])
apply (drule_tac x = b in spec)
apply (drule_tac x1 = c in spec [THEN mp])
apply (rule_tac b = a in rtrancl_trans)
apply (blast intro: rtrancl_mono [THEN subsetD])+
done


lemma Church_Rosser2:
     "confluent(r) \<Longrightarrow> Church_Rosser(r)"
apply (unfold confluent_def Church_Rosser_def square_def
              commute_def diamond_def, auto)
apply (frule fieldI1)
apply (simp add: rtrancl_field)
apply (erule rtrancl_induct, auto)
apply (blast intro: rtrancl_refl)
apply (blast del: rtrancl_refl intro: r_into_rtrancl rtrancl_trans)+
done


lemma Church_Rosser: "Church_Rosser(r) \<longleftrightarrow> confluent(r)"
  by (blast intro: Church_Rosser1 Church_Rosser2)

end
