(*  Title:      ZF/ex/Primes.thy
    Author:     Christophe Tabacznyj and Lawrence C Paulson
    Copyright   1996  University of Cambridge
*)

section\<open>The Divides Relation and Euclid's algorithm for the GCD\<close>

theory Primes imports ZF begin

definition
  divides :: "[i,i]\<Rightarrow>o"              (infixl \<open>dvd\<close> 50)  where
    "m dvd n \<equiv> m \<in> nat \<and> n \<in> nat \<and> (\<exists>k \<in> nat. n = m#*k)"

definition
  is_gcd  :: "[i,i,i]\<Rightarrow>o"     \<comment> \<open>definition of great common divisor\<close>  where
    "is_gcd(p,m,n) \<equiv> ((p dvd m) \<and> (p dvd n))   \<and>
                       (\<forall>d\<in>nat. (d dvd m) \<and> (d dvd n) \<longrightarrow> d dvd p)"

definition
  gcd     :: "[i,i]\<Rightarrow>i"       \<comment> \<open>Euclid's algorithm for the gcd\<close>  where
    "gcd(m,n) \<equiv> transrec(natify(n),
                        \<lambda>n f. \<lambda>m \<in> nat.
                                if n=0 then m else f`(m mod n)`n) ` natify(m)"

definition
  coprime :: "[i,i]\<Rightarrow>o"       \<comment> \<open>the coprime relation\<close>  where
    "coprime(m,n) \<equiv> gcd(m,n) = 1"
  
definition
  prime   :: i                \<comment> \<open>the set of prime numbers\<close>  where
   "prime \<equiv> {p \<in> nat. 1<p \<and> (\<forall>m \<in> nat. m dvd p \<longrightarrow> m=1 | m=p)}"


subsection\<open>The Divides Relation\<close>

lemma dvdD: "m dvd n \<Longrightarrow> m \<in> nat \<and> n \<in> nat \<and> (\<exists>k \<in> nat. n = m#*k)"
by (unfold divides_def, assumption)

lemma dvdE:
     "\<lbrakk>m dvd n;  \<And>k. \<lbrakk>m \<in> nat; n \<in> nat; k \<in> nat; n = m#*k\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (blast dest!: dvdD)

lemmas dvd_imp_nat1 = dvdD [THEN conjunct1]
lemmas dvd_imp_nat2 = dvdD [THEN conjunct2, THEN conjunct1]


lemma dvd_0_right [simp]: "m \<in> nat \<Longrightarrow> m dvd 0"
apply (simp add: divides_def)
apply (fast intro: nat_0I mult_0_right [symmetric])
done

lemma dvd_0_left: "0 dvd m \<Longrightarrow> m = 0"
by (simp add: divides_def)

lemma dvd_refl [simp]: "m \<in> nat \<Longrightarrow> m dvd m"
apply (simp add: divides_def)
apply (fast intro: nat_1I mult_1_right [symmetric])
done

lemma dvd_trans: "\<lbrakk>m dvd n; n dvd p\<rbrakk> \<Longrightarrow> m dvd p"
by (auto simp add: divides_def intro: mult_assoc mult_type)

lemma dvd_anti_sym: "\<lbrakk>m dvd n; n dvd m\<rbrakk> \<Longrightarrow> m=n"
apply (simp add: divides_def)
apply (force dest: mult_eq_self_implies_10
             simp add: mult_assoc mult_eq_1_iff)
done

lemma dvd_mult_left: "\<lbrakk>(i#*j) dvd k; i \<in> nat\<rbrakk> \<Longrightarrow> i dvd k"
by (auto simp add: divides_def mult_assoc)

lemma dvd_mult_right: "\<lbrakk>(i#*j) dvd k; j \<in> nat\<rbrakk> \<Longrightarrow> j dvd k"
apply (simp add: divides_def, clarify)
apply (rule_tac x = "i#*ka" in bexI)
apply (simp add: mult_ac)
apply (rule mult_type)
done


subsection\<open>Euclid's Algorithm for the GCD\<close>

lemma gcd_0 [simp]: "gcd(m,0) = natify(m)"
apply (simp add: gcd_def)
apply (subst transrec, simp)
done

lemma gcd_natify1 [simp]: "gcd(natify(m),n) = gcd(m,n)"
by (simp add: gcd_def)

lemma gcd_natify2 [simp]: "gcd(m, natify(n)) = gcd(m,n)"
by (simp add: gcd_def)

lemma gcd_non_0_raw: 
    "\<lbrakk>0<n;  n \<in> nat\<rbrakk> \<Longrightarrow> gcd(m,n) = gcd(n, m mod n)"
apply (simp add: gcd_def)
apply (rule_tac P = "\<lambda>z. left (z) = right" for left right in transrec [THEN ssubst])
apply (simp add: ltD [THEN mem_imp_not_eq, THEN not_sym] 
                 mod_less_divisor [THEN ltD])
done

lemma gcd_non_0: "0 < natify(n) \<Longrightarrow> gcd(m,n) = gcd(n, m mod n)"
apply (cut_tac m = m and n = "natify (n) " in gcd_non_0_raw)
apply auto
done

lemma gcd_1 [simp]: "gcd(m,1) = 1"
by (simp (no_asm_simp) add: gcd_non_0)

lemma dvd_add: "\<lbrakk>k dvd a; k dvd b\<rbrakk> \<Longrightarrow> k dvd (a #+ b)"
apply (simp add: divides_def)
apply (fast intro: add_mult_distrib_left [symmetric] add_type)
done

lemma dvd_mult: "k dvd n \<Longrightarrow> k dvd (m #* n)"
apply (simp add: divides_def)
apply (fast intro: mult_left_commute mult_type)
done

lemma dvd_mult2: "k dvd m \<Longrightarrow> k dvd (m #* n)"
apply (subst mult_commute)
apply (blast intro: dvd_mult)
done

(* k dvd (m*k) *)
lemmas dvdI1 [simp] = dvd_refl [THEN dvd_mult]
lemmas dvdI2 [simp] = dvd_refl [THEN dvd_mult2]

lemma dvd_mod_imp_dvd_raw:
     "\<lbrakk>a \<in> nat; b \<in> nat; k dvd b; k dvd (a mod b)\<rbrakk> \<Longrightarrow> k dvd a"
apply (case_tac "b=0") 
 apply (simp add: DIVISION_BY_ZERO_MOD)
apply (blast intro: mod_div_equality [THEN subst]
             elim: dvdE 
             intro!: dvd_add dvd_mult mult_type mod_type div_type)
done

lemma dvd_mod_imp_dvd: "\<lbrakk>k dvd (a mod b); k dvd b; a \<in> nat\<rbrakk> \<Longrightarrow> k dvd a"
apply (cut_tac b = "natify (b)" in dvd_mod_imp_dvd_raw)
apply auto
apply (simp add: divides_def)
done

(*Imitating TFL*)
lemma gcd_induct_lemma [rule_format (no_asm)]: "\<lbrakk>n \<in> nat;  
         \<forall>m \<in> nat. P(m,0);  
         \<forall>m \<in> nat. \<forall>n \<in> nat. 0<n \<longrightarrow> P(n, m mod n) \<longrightarrow> P(m,n)\<rbrakk>  
      \<Longrightarrow> \<forall>m \<in> nat. P (m,n)"
apply (erule_tac i = n in complete_induct)
apply (case_tac "x=0")
apply (simp (no_asm_simp))
apply clarify
apply (drule_tac x1 = m and x = x in bspec [THEN bspec])
apply (simp_all add: Ord_0_lt_iff)
apply (blast intro: mod_less_divisor [THEN ltD])
done

lemma gcd_induct: "\<And>P. \<lbrakk>m \<in> nat; n \<in> nat;  
         \<And>m. m \<in> nat \<Longrightarrow> P(m,0);  
         \<And>m n. \<lbrakk>m \<in> nat; n \<in> nat; 0<n; P(n, m mod n)\<rbrakk> \<Longrightarrow> P(m,n)\<rbrakk>  
      \<Longrightarrow> P (m,n)"
by (blast intro: gcd_induct_lemma)


subsection\<open>Basic Properties of \<^term>\<open>gcd\<close>\<close>

text\<open>type of gcd\<close>
lemma gcd_type [simp,TC]: "gcd(m, n) \<in> nat"
apply (subgoal_tac "gcd (natify (m), natify (n)) \<in> nat")
apply simp
apply (rule_tac m = "natify (m)" and n = "natify (n)" in gcd_induct)
apply auto
apply (simp add: gcd_non_0)
done


text\<open>Property 1: gcd(a,b) divides a and b\<close>

lemma gcd_dvd_both:
     "\<lbrakk>m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> gcd (m, n) dvd m \<and> gcd (m, n) dvd n"
apply (rule_tac m = m and n = n in gcd_induct)
apply (simp_all add: gcd_non_0)
apply (blast intro: dvd_mod_imp_dvd_raw nat_into_Ord [THEN Ord_0_lt])
done

lemma gcd_dvd1 [simp]: "m \<in> nat \<Longrightarrow> gcd(m,n) dvd m"
apply (cut_tac m = "natify (m)" and n = "natify (n)" in gcd_dvd_both)
apply auto
done

lemma gcd_dvd2 [simp]: "n \<in> nat \<Longrightarrow> gcd(m,n) dvd n"
apply (cut_tac m = "natify (m)" and n = "natify (n)" in gcd_dvd_both)
apply auto
done

text\<open>if f divides a and b then f divides gcd(a,b)\<close>

lemma dvd_mod: "\<lbrakk>f dvd a; f dvd b\<rbrakk> \<Longrightarrow> f dvd (a mod b)"
apply (simp add: divides_def)
apply (case_tac "b=0")
 apply (simp add: DIVISION_BY_ZERO_MOD, auto)
apply (blast intro: mod_mult_distrib2 [symmetric])
done

text\<open>Property 2: for all a,b,f naturals, 
               if f divides a and f divides b then f divides gcd(a,b)\<close>

lemma gcd_greatest_raw [rule_format]:
     "\<lbrakk>m \<in> nat; n \<in> nat; f \<in> nat\<rbrakk>    
      \<Longrightarrow> (f dvd m) \<longrightarrow> (f dvd n) \<longrightarrow> f dvd gcd(m,n)"
apply (rule_tac m = m and n = n in gcd_induct)
apply (simp_all add: gcd_non_0 dvd_mod)
done

lemma gcd_greatest: "\<lbrakk>f dvd m;  f dvd n;  f \<in> nat\<rbrakk> \<Longrightarrow> f dvd gcd(m,n)"
apply (rule gcd_greatest_raw)
apply (auto simp add: divides_def)
done

lemma gcd_greatest_iff [simp]: "\<lbrakk>k \<in> nat; m \<in> nat; n \<in> nat\<rbrakk>  
      \<Longrightarrow> (k dvd gcd (m, n)) \<longleftrightarrow> (k dvd m \<and> k dvd n)"
by (blast intro!: gcd_greatest gcd_dvd1 gcd_dvd2 intro: dvd_trans)


subsection\<open>The Greatest Common Divisor\<close>

text\<open>The GCD exists and function gcd computes it.\<close>

lemma is_gcd: "\<lbrakk>m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> is_gcd(gcd(m,n), m, n)"
by (simp add: is_gcd_def)

text\<open>The GCD is unique\<close>

lemma is_gcd_unique: "\<lbrakk>is_gcd(m,a,b); is_gcd(n,a,b); m\<in>nat; n\<in>nat\<rbrakk> \<Longrightarrow> m=n"
apply (simp add: is_gcd_def)
apply (blast intro: dvd_anti_sym)
done

lemma is_gcd_commute: "is_gcd(k,m,n) \<longleftrightarrow> is_gcd(k,n,m)"
by (simp add: is_gcd_def, blast)

lemma gcd_commute_raw: "\<lbrakk>m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> gcd(m,n) = gcd(n,m)"
apply (rule is_gcd_unique)
apply (rule is_gcd)
apply (rule_tac [3] is_gcd_commute [THEN iffD1])
apply (rule_tac [3] is_gcd, auto)
done

lemma gcd_commute: "gcd(m,n) = gcd(n,m)"
apply (cut_tac m = "natify (m)" and n = "natify (n)" in gcd_commute_raw)
apply auto
done

lemma gcd_assoc_raw: "\<lbrakk>k \<in> nat; m \<in> nat; n \<in> nat\<rbrakk>  
      \<Longrightarrow> gcd (gcd (k, m), n) = gcd (k, gcd (m, n))"
apply (rule is_gcd_unique)
apply (rule is_gcd)
apply (simp_all add: is_gcd_def)
apply (blast intro: gcd_dvd1 gcd_dvd2 gcd_type intro: dvd_trans)
done

lemma gcd_assoc: "gcd (gcd (k, m), n) = gcd (k, gcd (m, n))"
apply (cut_tac k = "natify (k)" and m = "natify (m)" and n = "natify (n) " 
       in gcd_assoc_raw)
apply auto
done

lemma gcd_0_left [simp]: "gcd (0, m) = natify(m)"
by (simp add: gcd_commute [of 0])

lemma gcd_1_left [simp]: "gcd (1, m) = 1"
by (simp add: gcd_commute [of 1])


subsection\<open>Addition laws\<close>

lemma gcd_add1 [simp]: "gcd (m #+ n, n) = gcd (m, n)"
apply (subgoal_tac "gcd (m #+ natify (n), natify (n)) = gcd (m, natify (n))")
apply simp
apply (case_tac "natify (n) = 0")
apply (auto simp add: Ord_0_lt_iff gcd_non_0)
done

lemma gcd_add2 [simp]: "gcd (m, m #+ n) = gcd (m, n)"
apply (rule gcd_commute [THEN trans])
apply (subst add_commute, simp)
apply (rule gcd_commute)
done

lemma gcd_add2' [simp]: "gcd (m, n #+ m) = gcd (m, n)"
by (subst add_commute, rule gcd_add2)

lemma gcd_add_mult_raw: "k \<in> nat \<Longrightarrow> gcd (m, k #* m #+ n) = gcd (m, n)"
apply (erule nat_induct)
apply (auto simp add: gcd_add2 add_assoc)
done

lemma gcd_add_mult: "gcd (m, k #* m #+ n) = gcd (m, n)"
apply (cut_tac k = "natify (k)" in gcd_add_mult_raw)
apply auto
done


subsection\<open>Multiplication Laws\<close>

lemma gcd_mult_distrib2_raw:
     "\<lbrakk>k \<in> nat; m \<in> nat; n \<in> nat\<rbrakk>  
      \<Longrightarrow> k #* gcd (m, n) = gcd (k #* m, k #* n)"
apply (erule_tac m = m and n = n in gcd_induct, assumption)
apply simp
apply (case_tac "k = 0", simp)
apply (simp add: mod_geq gcd_non_0 mod_mult_distrib2 Ord_0_lt_iff)
done

lemma gcd_mult_distrib2: "k #* gcd (m, n) = gcd (k #* m, k #* n)"
apply (cut_tac k = "natify (k)" and m = "natify (m)" and n = "natify (n) " 
       in gcd_mult_distrib2_raw)
apply auto
done

lemma gcd_mult [simp]: "gcd (k, k #* n) = natify(k)"
by (cut_tac k = k and m = 1 and n = n in gcd_mult_distrib2, auto)

lemma gcd_self [simp]: "gcd (k, k) = natify(k)"
by (cut_tac k = k and n = 1 in gcd_mult, auto)

lemma relprime_dvd_mult:
     "\<lbrakk>gcd (k,n) = 1;  k dvd (m #* n);  m \<in> nat\<rbrakk> \<Longrightarrow> k dvd m"
apply (cut_tac k = m and m = k and n = n in gcd_mult_distrib2, auto)
apply (erule_tac b = m in ssubst)
apply (simp add: dvd_imp_nat1)
done

lemma relprime_dvd_mult_iff:
     "\<lbrakk>gcd (k,n) = 1;  m \<in> nat\<rbrakk> \<Longrightarrow> k dvd (m #* n) \<longleftrightarrow> k dvd m"
by (blast intro: dvdI2 relprime_dvd_mult dvd_trans)

lemma prime_imp_relprime: 
     "\<lbrakk>p \<in> prime;  \<not> (p dvd n);  n \<in> nat\<rbrakk> \<Longrightarrow> gcd (p, n) = 1"
apply (simp add: prime_def, clarify)
apply (drule_tac x = "gcd (p,n)" in bspec)
apply auto
apply (cut_tac m = p and n = n in gcd_dvd2, auto)
done

lemma prime_into_nat: "p \<in> prime \<Longrightarrow> p \<in> nat"
by (simp add: prime_def)

lemma prime_nonzero: "p \<in> prime \<Longrightarrow> p\<noteq>0"
by (auto simp add: prime_def)


text\<open>This theorem leads immediately to a proof of the uniqueness of
  factorization.  If \<^term>\<open>p\<close> divides a product of primes then it is
  one of those primes.\<close>

lemma prime_dvd_mult:
     "\<lbrakk>p dvd m #* n; p \<in> prime; m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> p dvd m \<or> p dvd n"
by (blast intro: relprime_dvd_mult prime_imp_relprime prime_into_nat)


lemma gcd_mult_cancel_raw:
     "\<lbrakk>gcd (k,n) = 1; m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> gcd (k #* m, n) = gcd (m, n)"
apply (rule dvd_anti_sym)
 apply (rule gcd_greatest)
  apply (rule relprime_dvd_mult [of _ k])
apply (simp add: gcd_assoc)
apply (simp add: gcd_commute)
apply (simp_all add: mult_commute)
apply (blast intro: dvdI1 gcd_dvd1 dvd_trans)
done

lemma gcd_mult_cancel: "gcd (k,n) = 1 \<Longrightarrow> gcd (k #* m, n) = gcd (m, n)"
apply (cut_tac m = "natify (m)" and n = "natify (n)" in gcd_mult_cancel_raw)
apply auto
done


subsection\<open>The Square Root of a Prime is Irrational: Key Lemma\<close>

lemma prime_dvd_other_side:
     "\<lbrakk>n#*n = p#*(k#*k); p \<in> prime; n \<in> nat\<rbrakk> \<Longrightarrow> p dvd n"
apply (subgoal_tac "p dvd n#*n")
 apply (blast dest: prime_dvd_mult)
apply (rule_tac j = "k#*k" in dvd_mult_left)
 apply (auto simp add: prime_def)
done

lemma reduction:
     "\<lbrakk>k#*k = p#*(j#*j); p \<in> prime; 0 < k; j \<in> nat; k \<in> nat\<rbrakk>  
      \<Longrightarrow> k < p#*j \<and> 0 < j"
apply (rule ccontr)
apply (simp add: not_lt_iff_le prime_into_nat)
apply (erule disjE)
 apply (frule mult_le_mono, assumption+)
apply (simp add: mult_ac)
apply (auto dest!: natify_eqE 
            simp add: not_lt_iff_le prime_into_nat mult_le_cancel_le1)
apply (simp add: prime_def)
apply (blast dest: lt_trans1)
done

lemma rearrange: "j #* (p#*j) = k#*k \<Longrightarrow> k#*k = p#*(j#*j)"
by (simp add: mult_ac)

lemma prime_not_square:
     "\<lbrakk>m \<in> nat; p \<in> prime\<rbrakk> \<Longrightarrow> \<forall>k \<in> nat. 0<k \<longrightarrow> m#*m \<noteq> p#*(k#*k)"
apply (erule complete_induct, clarify)
apply (frule prime_dvd_other_side, assumption)
apply assumption
apply (erule dvdE)
apply (simp add: mult_assoc mult_cancel1 prime_nonzero prime_into_nat)
apply (blast dest: rearrange reduction ltD)
done

end
