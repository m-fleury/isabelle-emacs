(*  Title:      ZF/Constructible/Internalize.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

theory Internalize imports L_axioms Datatype_absolute begin

subsection\<open>Internalized Forms of Data Structuring Operators\<close>

subsubsection\<open>The Formula \<^term>\<open>is_Inl\<close>, Internalized\<close>

(*  is_Inl(M,a,z) \<equiv> \<exists>zero[M]. empty(M,zero) \<and> pair(M,zero,a,z) *)
definition
  Inl_fm :: "[i,i]\<Rightarrow>i" where
    "Inl_fm(a,z) \<equiv> Exists(And(empty_fm(0), pair_fm(0,succ(a),succ(z))))"

lemma Inl_type [TC]:
     "\<lbrakk>x \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> Inl_fm(x,z) \<in> formula"
by (simp add: Inl_fm_def)

lemma sats_Inl_fm [simp]:
   "\<lbrakk>x \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, Inl_fm(x,z), env) \<longleftrightarrow> is_Inl(##A, nth(x,env), nth(z,env))"
by (simp add: Inl_fm_def is_Inl_def)

lemma Inl_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(k,env) = z;
          i \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_Inl(##A, x, z) \<longleftrightarrow> sats(A, Inl_fm(i,k), env)"
by simp

theorem Inl_reflection:
     "REFLECTS[\<lambda>x. is_Inl(L,f(x),h(x)),
               \<lambda>i x. is_Inl(##Lset(i),f(x),h(x))]"
apply (simp only: is_Inl_def)
apply (intro FOL_reflections function_reflections)
done


subsubsection\<open>The Formula \<^term>\<open>is_Inr\<close>, Internalized\<close>

(*  is_Inr(M,a,z) \<equiv> \<exists>n1[M]. number1(M,n1) \<and> pair(M,n1,a,z) *)
definition
  Inr_fm :: "[i,i]\<Rightarrow>i" where
    "Inr_fm(a,z) \<equiv> Exists(And(number1_fm(0), pair_fm(0,succ(a),succ(z))))"

lemma Inr_type [TC]:
     "\<lbrakk>x \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> Inr_fm(x,z) \<in> formula"
by (simp add: Inr_fm_def)

lemma sats_Inr_fm [simp]:
   "\<lbrakk>x \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, Inr_fm(x,z), env) \<longleftrightarrow> is_Inr(##A, nth(x,env), nth(z,env))"
by (simp add: Inr_fm_def is_Inr_def)

lemma Inr_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(k,env) = z;
          i \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_Inr(##A, x, z) \<longleftrightarrow> sats(A, Inr_fm(i,k), env)"
by simp

theorem Inr_reflection:
     "REFLECTS[\<lambda>x. is_Inr(L,f(x),h(x)),
               \<lambda>i x. is_Inr(##Lset(i),f(x),h(x))]"
apply (simp only: is_Inr_def)
apply (intro FOL_reflections function_reflections)
done


subsubsection\<open>The Formula \<^term>\<open>is_Nil\<close>, Internalized\<close>

(* is_Nil(M,xs) \<equiv> \<exists>zero[M]. empty(M,zero) \<and> is_Inl(M,zero,xs) *)

definition
  Nil_fm :: "i\<Rightarrow>i" where
    "Nil_fm(x) \<equiv> Exists(And(empty_fm(0), Inl_fm(0,succ(x))))"

lemma Nil_type [TC]: "x \<in> nat \<Longrightarrow> Nil_fm(x) \<in> formula"
by (simp add: Nil_fm_def)

lemma sats_Nil_fm [simp]:
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, Nil_fm(x), env) \<longleftrightarrow> is_Nil(##A, nth(x,env))"
by (simp add: Nil_fm_def is_Nil_def)

lemma Nil_iff_sats:
      "\<lbrakk>nth(i,env) = x; i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_Nil(##A, x) \<longleftrightarrow> sats(A, Nil_fm(i), env)"
by simp

theorem Nil_reflection:
     "REFLECTS[\<lambda>x. is_Nil(L,f(x)),
               \<lambda>i x. is_Nil(##Lset(i),f(x))]"
apply (simp only: is_Nil_def)
apply (intro FOL_reflections function_reflections Inl_reflection)
done


subsubsection\<open>The Formula \<^term>\<open>is_Cons\<close>, Internalized\<close>


(*  "is_Cons(M,a,l,Z) \<equiv> \<exists>p[M]. pair(M,a,l,p) \<and> is_Inr(M,p,Z)" *)
definition
  Cons_fm :: "[i,i,i]\<Rightarrow>i" where
    "Cons_fm(a,l,Z) \<equiv>
       Exists(And(pair_fm(succ(a),succ(l),0), Inr_fm(0,succ(Z))))"

lemma Cons_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> Cons_fm(x,y,z) \<in> formula"
by (simp add: Cons_fm_def)

lemma sats_Cons_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, Cons_fm(x,y,z), env) \<longleftrightarrow>
       is_Cons(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Cons_fm_def is_Cons_def)

lemma Cons_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow>is_Cons(##A, x, y, z) \<longleftrightarrow> sats(A, Cons_fm(i,j,k), env)"
by simp

theorem Cons_reflection:
     "REFLECTS[\<lambda>x. is_Cons(L,f(x),g(x),h(x)),
               \<lambda>i x. is_Cons(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_Cons_def)
apply (intro FOL_reflections pair_reflection Inr_reflection)
done

subsubsection\<open>The Formula \<^term>\<open>is_quasilist\<close>, Internalized\<close>

(* is_quasilist(M,xs) \<equiv> is_Nil(M,z) | (\<exists>x[M]. \<exists>l[M]. is_Cons(M,x,l,z))" *)

definition
  quasilist_fm :: "i\<Rightarrow>i" where
    "quasilist_fm(x) \<equiv>
       Or(Nil_fm(x), Exists(Exists(Cons_fm(1,0,succ(succ(x))))))"

lemma quasilist_type [TC]: "x \<in> nat \<Longrightarrow> quasilist_fm(x) \<in> formula"
by (simp add: quasilist_fm_def)

lemma sats_quasilist_fm [simp]:
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, quasilist_fm(x), env) \<longleftrightarrow> is_quasilist(##A, nth(x,env))"
by (simp add: quasilist_fm_def is_quasilist_def)

lemma quasilist_iff_sats:
      "\<lbrakk>nth(i,env) = x; i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_quasilist(##A, x) \<longleftrightarrow> sats(A, quasilist_fm(i), env)"
by simp

theorem quasilist_reflection:
     "REFLECTS[\<lambda>x. is_quasilist(L,f(x)),
               \<lambda>i x. is_quasilist(##Lset(i),f(x))]"
apply (simp only: is_quasilist_def)
apply (intro FOL_reflections Nil_reflection Cons_reflection)
done


subsection\<open>Absoluteness for the Function \<^term>\<open>nth\<close>\<close>


subsubsection\<open>The Formula \<^term>\<open>is_hd\<close>, Internalized\<close>

(*   "is_hd(M,xs,H) \<equiv> 
       (is_Nil(M,xs) \<longrightarrow> empty(M,H)) \<and>
       (\<forall>x[M]. \<forall>l[M]. \<not> is_Cons(M,x,l,xs) | H=x) \<and>
       (is_quasilist(M,xs) | empty(M,H))" *)
definition
  hd_fm :: "[i,i]\<Rightarrow>i" where
    "hd_fm(xs,H) \<equiv> 
       And(Implies(Nil_fm(xs), empty_fm(H)),
           And(Forall(Forall(Or(Neg(Cons_fm(1,0,xs#+2)), Equal(H#+2,1)))),
               Or(quasilist_fm(xs), empty_fm(H))))"

lemma hd_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> hd_fm(x,y) \<in> formula"
by (simp add: hd_fm_def) 

lemma sats_hd_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, hd_fm(x,y), env) \<longleftrightarrow> is_hd(##A, nth(x,env), nth(y,env))"
by (simp add: hd_fm_def is_hd_def)

lemma hd_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_hd(##A, x, y) \<longleftrightarrow> sats(A, hd_fm(i,j), env)"
by simp

theorem hd_reflection:
     "REFLECTS[\<lambda>x. is_hd(L,f(x),g(x)), 
               \<lambda>i x. is_hd(##Lset(i),f(x),g(x))]"
apply (simp only: is_hd_def)
apply (intro FOL_reflections Nil_reflection Cons_reflection
             quasilist_reflection empty_reflection)  
done


subsubsection\<open>The Formula \<^term>\<open>is_tl\<close>, Internalized\<close>

(*     "is_tl(M,xs,T) \<equiv>
       (is_Nil(M,xs) \<longrightarrow> T=xs) \<and>
       (\<forall>x[M]. \<forall>l[M]. \<not> is_Cons(M,x,l,xs) | T=l) \<and>
       (is_quasilist(M,xs) | empty(M,T))" *)
definition
  tl_fm :: "[i,i]\<Rightarrow>i" where
    "tl_fm(xs,T) \<equiv>
       And(Implies(Nil_fm(xs), Equal(T,xs)),
           And(Forall(Forall(Or(Neg(Cons_fm(1,0,xs#+2)), Equal(T#+2,0)))),
               Or(quasilist_fm(xs), empty_fm(T))))"

lemma tl_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> tl_fm(x,y) \<in> formula"
by (simp add: tl_fm_def)

lemma sats_tl_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, tl_fm(x,y), env) \<longleftrightarrow> is_tl(##A, nth(x,env), nth(y,env))"
by (simp add: tl_fm_def is_tl_def)

lemma tl_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_tl(##A, x, y) \<longleftrightarrow> sats(A, tl_fm(i,j), env)"
by simp

theorem tl_reflection:
     "REFLECTS[\<lambda>x. is_tl(L,f(x),g(x)),
               \<lambda>i x. is_tl(##Lset(i),f(x),g(x))]"
apply (simp only: is_tl_def)
apply (intro FOL_reflections Nil_reflection Cons_reflection
             quasilist_reflection empty_reflection)
done


subsubsection\<open>The Operator \<^term>\<open>is_bool_of_o\<close>\<close>

(*   is_bool_of_o :: "[i\<Rightarrow>o, o, i] \<Rightarrow> o"
   "is_bool_of_o(M,P,z) \<equiv> (P \<and> number1(M,z)) | (\<not>P \<and> empty(M,z))" *)

text\<open>The formula \<^term>\<open>p\<close> has no free variables.\<close>
definition
  bool_of_o_fm :: "[i, i]\<Rightarrow>i" where
  "bool_of_o_fm(p,z) \<equiv> 
    Or(And(p,number1_fm(z)),
       And(Neg(p),empty_fm(z)))"

lemma is_bool_of_o_type [TC]:
     "\<lbrakk>p \<in> formula; z \<in> nat\<rbrakk> \<Longrightarrow> bool_of_o_fm(p,z) \<in> formula"
by (simp add: bool_of_o_fm_def)

lemma sats_bool_of_o_fm:
  assumes p_iff_sats: "P \<longleftrightarrow> sats(A, p, env)"
  shows 
      "\<lbrakk>z \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> sats(A, bool_of_o_fm(p,z), env) \<longleftrightarrow>
           is_bool_of_o(##A, P, nth(z,env))"
by (simp add: bool_of_o_fm_def is_bool_of_o_def p_iff_sats [THEN iff_sym])

lemma is_bool_of_o_iff_sats:
  "\<lbrakk>P \<longleftrightarrow> sats(A, p, env); nth(k,env) = z; k \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> is_bool_of_o(##A, P, z) \<longleftrightarrow> sats(A, bool_of_o_fm(p,k), env)"
by (simp add: sats_bool_of_o_fm)

theorem bool_of_o_reflection:
     "REFLECTS [P(L), \<lambda>i. P(##Lset(i))] \<Longrightarrow>
      REFLECTS[\<lambda>x. is_bool_of_o(L, P(L,x), f(x)),  
               \<lambda>i x. is_bool_of_o(##Lset(i), P(##Lset(i),x), f(x))]"
apply (simp (no_asm) only: is_bool_of_o_def)
apply (intro FOL_reflections function_reflections, assumption+)
done


subsection\<open>More Internalizations\<close>

subsubsection\<open>The Operator \<^term>\<open>is_lambda\<close>\<close>

text\<open>The two arguments of \<^term>\<open>p\<close> are always 1, 0. Remember that
 \<^term>\<open>p\<close> will be enclosed by three quantifiers.\<close>

(* is_lambda :: "[i\<Rightarrow>o, i, [i,i]\<Rightarrow>o, i] \<Rightarrow> o"
    "is_lambda(M, A, is_b, z) \<equiv> 
       \<forall>p[M]. p \<in> z \<longleftrightarrow>
        (\<exists>u[M]. \<exists>v[M]. u\<in>A \<and> pair(M,u,v,p) \<and> is_b(u,v))" *)
definition
  lambda_fm :: "[i, i, i]\<Rightarrow>i" where
  "lambda_fm(p,A,z) \<equiv> 
    Forall(Iff(Member(0,succ(z)),
            Exists(Exists(And(Member(1,A#+3),
                           And(pair_fm(1,0,2), p))))))"

text\<open>We call \<^term>\<open>p\<close> with arguments x, y by equating them with 
  the corresponding quantified variables with de Bruijn indices 1, 0.\<close>

lemma is_lambda_type [TC]:
     "\<lbrakk>p \<in> formula; x \<in> nat; y \<in> nat\<rbrakk> 
      \<Longrightarrow> lambda_fm(p,x,y) \<in> formula"
by (simp add: lambda_fm_def) 

lemma sats_lambda_fm:
  assumes is_b_iff_sats: 
      "\<And>a0 a1 a2. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A\<rbrakk> 
        \<Longrightarrow> is_b(a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,env))))"
  shows 
      "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> sats(A, lambda_fm(p,x,y), env) \<longleftrightarrow> 
           is_lambda(##A, nth(x,env), is_b, nth(y,env))"
by (simp add: lambda_fm_def is_lambda_def is_b_iff_sats [THEN iff_sym]) 

theorem is_lambda_reflection:
  assumes is_b_reflection:
    "\<And>f g h. REFLECTS[\<lambda>x. is_b(L, f(x), g(x), h(x)), 
                     \<lambda>i x. is_b(##Lset(i), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. is_lambda(L, A(x), is_b(L,x), f(x)), 
               \<lambda>i x. is_lambda(##Lset(i), A(x), is_b(##Lset(i),x), f(x))]"
apply (simp (no_asm_use) only: is_lambda_def)
apply (intro FOL_reflections is_b_reflection pair_reflection)
done

subsubsection\<open>The Operator \<^term>\<open>is_Member\<close>, Internalized\<close>

(*    "is_Member(M,x,y,Z) \<equiv>
        \<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) \<and> is_Inl(M,p,u) \<and> is_Inl(M,u,Z)" *)
definition
  Member_fm :: "[i,i,i]\<Rightarrow>i" where
    "Member_fm(x,y,Z) \<equiv>
       Exists(Exists(And(pair_fm(x#+2,y#+2,1), 
                      And(Inl_fm(1,0), Inl_fm(0,Z#+2)))))"

lemma is_Member_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> Member_fm(x,y,z) \<in> formula"
by (simp add: Member_fm_def)

lemma sats_Member_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, Member_fm(x,y,z), env) \<longleftrightarrow>
        is_Member(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Member_fm_def is_Member_def)

lemma Member_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_Member(##A, x, y, z) \<longleftrightarrow> sats(A, Member_fm(i,j,k), env)"
by (simp)

theorem Member_reflection:
     "REFLECTS[\<lambda>x. is_Member(L,f(x),g(x),h(x)),
               \<lambda>i x. is_Member(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_Member_def)
apply (intro FOL_reflections pair_reflection Inl_reflection)
done

subsubsection\<open>The Operator \<^term>\<open>is_Equal\<close>, Internalized\<close>

(*    "is_Equal(M,x,y,Z) \<equiv>
        \<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) \<and> is_Inr(M,p,u) \<and> is_Inl(M,u,Z)" *)
definition
  Equal_fm :: "[i,i,i]\<Rightarrow>i" where
    "Equal_fm(x,y,Z) \<equiv>
       Exists(Exists(And(pair_fm(x#+2,y#+2,1), 
                      And(Inr_fm(1,0), Inl_fm(0,Z#+2)))))"

lemma is_Equal_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> Equal_fm(x,y,z) \<in> formula"
by (simp add: Equal_fm_def)

lemma sats_Equal_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, Equal_fm(x,y,z), env) \<longleftrightarrow>
        is_Equal(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Equal_fm_def is_Equal_def)

lemma Equal_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_Equal(##A, x, y, z) \<longleftrightarrow> sats(A, Equal_fm(i,j,k), env)"
by (simp)

theorem Equal_reflection:
     "REFLECTS[\<lambda>x. is_Equal(L,f(x),g(x),h(x)),
               \<lambda>i x. is_Equal(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_Equal_def)
apply (intro FOL_reflections pair_reflection Inl_reflection Inr_reflection)
done

subsubsection\<open>The Operator \<^term>\<open>is_Nand\<close>, Internalized\<close>

(*    "is_Nand(M,x,y,Z) \<equiv>
        \<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) \<and> is_Inl(M,p,u) \<and> is_Inr(M,u,Z)" *)
definition
  Nand_fm :: "[i,i,i]\<Rightarrow>i" where
    "Nand_fm(x,y,Z) \<equiv>
       Exists(Exists(And(pair_fm(x#+2,y#+2,1), 
                      And(Inl_fm(1,0), Inr_fm(0,Z#+2)))))"

lemma is_Nand_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> Nand_fm(x,y,z) \<in> formula"
by (simp add: Nand_fm_def)

lemma sats_Nand_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, Nand_fm(x,y,z), env) \<longleftrightarrow>
        is_Nand(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: Nand_fm_def is_Nand_def)

lemma Nand_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_Nand(##A, x, y, z) \<longleftrightarrow> sats(A, Nand_fm(i,j,k), env)"
by (simp)

theorem Nand_reflection:
     "REFLECTS[\<lambda>x. is_Nand(L,f(x),g(x),h(x)),
               \<lambda>i x. is_Nand(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_Nand_def)
apply (intro FOL_reflections pair_reflection Inl_reflection Inr_reflection)
done

subsubsection\<open>The Operator \<^term>\<open>is_Forall\<close>, Internalized\<close>

(* "is_Forall(M,p,Z) \<equiv> \<exists>u[M]. is_Inr(M,p,u) \<and> is_Inr(M,u,Z)" *)
definition
  Forall_fm :: "[i,i]\<Rightarrow>i" where
    "Forall_fm(x,Z) \<equiv>
       Exists(And(Inr_fm(succ(x),0), Inr_fm(0,succ(Z))))"

lemma is_Forall_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> Forall_fm(x,y) \<in> formula"
by (simp add: Forall_fm_def)

lemma sats_Forall_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, Forall_fm(x,y), env) \<longleftrightarrow>
        is_Forall(##A, nth(x,env), nth(y,env))"
by (simp add: Forall_fm_def is_Forall_def)

lemma Forall_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_Forall(##A, x, y) \<longleftrightarrow> sats(A, Forall_fm(i,j), env)"
by (simp)

theorem Forall_reflection:
     "REFLECTS[\<lambda>x. is_Forall(L,f(x),g(x)),
               \<lambda>i x. is_Forall(##Lset(i),f(x),g(x))]"
apply (simp only: is_Forall_def)
apply (intro FOL_reflections pair_reflection Inr_reflection)
done


subsubsection\<open>The Operator \<^term>\<open>is_and\<close>, Internalized\<close>

(* is_and(M,a,b,z) \<equiv> (number1(M,a)  \<and> z=b) | 
                       (\<not>number1(M,a) \<and> empty(M,z)) *)
definition
  and_fm :: "[i,i,i]\<Rightarrow>i" where
    "and_fm(a,b,z) \<equiv>
       Or(And(number1_fm(a), Equal(z,b)),
          And(Neg(number1_fm(a)),empty_fm(z)))"

lemma is_and_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> and_fm(x,y,z) \<in> formula"
by (simp add: and_fm_def)

lemma sats_and_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, and_fm(x,y,z), env) \<longleftrightarrow>
        is_and(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: and_fm_def is_and_def)

lemma is_and_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_and(##A, x, y, z) \<longleftrightarrow> sats(A, and_fm(i,j,k), env)"
by simp

theorem is_and_reflection:
     "REFLECTS[\<lambda>x. is_and(L,f(x),g(x),h(x)),
               \<lambda>i x. is_and(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_and_def)
apply (intro FOL_reflections function_reflections)
done


subsubsection\<open>The Operator \<^term>\<open>is_or\<close>, Internalized\<close>

(* is_or(M,a,b,z) \<equiv> (number1(M,a)  \<and> number1(M,z)) | 
                     (\<not>number1(M,a) \<and> z=b) *)

definition
  or_fm :: "[i,i,i]\<Rightarrow>i" where
    "or_fm(a,b,z) \<equiv>
       Or(And(number1_fm(a), number1_fm(z)),
          And(Neg(number1_fm(a)), Equal(z,b)))"

lemma is_or_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> or_fm(x,y,z) \<in> formula"
by (simp add: or_fm_def)

lemma sats_or_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, or_fm(x,y,z), env) \<longleftrightarrow>
        is_or(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: or_fm_def is_or_def)

lemma is_or_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_or(##A, x, y, z) \<longleftrightarrow> sats(A, or_fm(i,j,k), env)"
by simp

theorem is_or_reflection:
     "REFLECTS[\<lambda>x. is_or(L,f(x),g(x),h(x)),
               \<lambda>i x. is_or(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_or_def)
apply (intro FOL_reflections function_reflections)
done



subsubsection\<open>The Operator \<^term>\<open>is_not\<close>, Internalized\<close>

(* is_not(M,a,z) \<equiv> (number1(M,a)  \<and> empty(M,z)) | 
                     (\<not>number1(M,a) \<and> number1(M,z)) *)
definition
  not_fm :: "[i,i]\<Rightarrow>i" where
    "not_fm(a,z) \<equiv>
       Or(And(number1_fm(a), empty_fm(z)),
          And(Neg(number1_fm(a)), number1_fm(z)))"

lemma is_not_type [TC]:
     "\<lbrakk>x \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> not_fm(x,z) \<in> formula"
by (simp add: not_fm_def)

lemma sats_is_not_fm [simp]:
   "\<lbrakk>x \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, not_fm(x,z), env) \<longleftrightarrow> is_not(##A, nth(x,env), nth(z,env))"
by (simp add: not_fm_def is_not_def)

lemma is_not_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(k,env) = z;
          i \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_not(##A, x, z) \<longleftrightarrow> sats(A, not_fm(i,k), env)"
by simp

theorem is_not_reflection:
     "REFLECTS[\<lambda>x. is_not(L,f(x),g(x)),
               \<lambda>i x. is_not(##Lset(i),f(x),g(x))]"
apply (simp only: is_not_def)
apply (intro FOL_reflections function_reflections)
done


lemmas extra_reflections = 
    Inl_reflection Inr_reflection Nil_reflection Cons_reflection
    quasilist_reflection hd_reflection tl_reflection bool_of_o_reflection
    is_lambda_reflection Member_reflection Equal_reflection Nand_reflection
    Forall_reflection is_and_reflection is_or_reflection is_not_reflection

subsection\<open>Well-Founded Recursion!\<close>

subsubsection\<open>The Operator \<^term>\<open>M_is_recfun\<close>\<close>

text\<open>Alternative definition, minimizing nesting of quantifiers around MH\<close>
lemma M_is_recfun_iff:
   "M_is_recfun(M,MH,r,a,f) \<longleftrightarrow>
    (\<forall>z[M]. z \<in> f \<longleftrightarrow> 
     (\<exists>x[M]. \<exists>f_r_sx[M]. \<exists>y[M]. 
             MH(x, f_r_sx, y) \<and> pair(M,x,y,z) \<and>
             (\<exists>xa[M]. \<exists>sx[M]. \<exists>r_sx[M]. 
                pair(M,x,a,xa) \<and> upair(M,x,x,sx) \<and>
               pre_image(M,r,sx,r_sx) \<and> restriction(M,f,r_sx,f_r_sx) \<and>
               xa \<in> r)))"
apply (simp add: M_is_recfun_def)
apply (rule rall_cong, blast) 
done


(* M_is_recfun :: "[i\<Rightarrow>o, [i,i,i]\<Rightarrow>o, i, i, i] \<Rightarrow> o"
   "M_is_recfun(M,MH,r,a,f) \<equiv>
     \<forall>z[M]. z \<in> f \<longleftrightarrow>
               2      1           0
new def     (\<exists>x[M]. \<exists>f_r_sx[M]. \<exists>y[M]. 
             MH(x, f_r_sx, y) \<and> pair(M,x,y,z) \<and>
             (\<exists>xa[M]. \<exists>sx[M]. \<exists>r_sx[M]. 
                pair(M,x,a,xa) \<and> upair(M,x,x,sx) \<and>
               pre_image(M,r,sx,r_sx) \<and> restriction(M,f,r_sx,f_r_sx) \<and>
               xa \<in> r)"
*)

text\<open>The three arguments of \<^term>\<open>p\<close> are always 2, 1, 0 and z\<close>
definition
  is_recfun_fm :: "[i, i, i, i]\<Rightarrow>i" where
  "is_recfun_fm(p,r,a,f) \<equiv> 
   Forall(Iff(Member(0,succ(f)),
    Exists(Exists(Exists(
     And(p, 
      And(pair_fm(2,0,3),
       Exists(Exists(Exists(
        And(pair_fm(5,a#+7,2),
         And(upair_fm(5,5,1),
          And(pre_image_fm(r#+7,1,0),
           And(restriction_fm(f#+7,0,4), Member(2,r#+7)))))))))))))))"

lemma is_recfun_type [TC]:
     "\<lbrakk>p \<in> formula; x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> 
      \<Longrightarrow> is_recfun_fm(p,x,y,z) \<in> formula"
by (simp add: is_recfun_fm_def)


lemma sats_is_recfun_fm:
  assumes MH_iff_sats: 
      "\<And>a0 a1 a2 a3. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A\<rbrakk> 
        \<Longrightarrow> MH(a2, a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,env)))))"
  shows 
      "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> sats(A, is_recfun_fm(p,x,y,z), env) \<longleftrightarrow>
           M_is_recfun(##A, MH, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: is_recfun_fm_def M_is_recfun_iff MH_iff_sats [THEN iff_sym])

lemma is_recfun_iff_sats:
  assumes MH_iff_sats: 
      "\<And>a0 a1 a2 a3. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A\<rbrakk> 
        \<Longrightarrow> MH(a2, a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,env)))))"
  shows
  "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> M_is_recfun(##A, MH, x, y, z) \<longleftrightarrow> sats(A, is_recfun_fm(p,i,j,k), env)"
by (simp add: sats_is_recfun_fm [OF MH_iff_sats]) 

text\<open>The additional variable in the premise, namely \<^term>\<open>f'\<close>, is essential.
It lets \<^term>\<open>MH\<close> depend upon \<^term>\<open>x\<close>, which seems often necessary.
The same thing occurs in \<open>is_wfrec_reflection\<close>.\<close>
theorem is_recfun_reflection:
  assumes MH_reflection:
    "\<And>f' f g h. REFLECTS[\<lambda>x. MH(L, f'(x), f(x), g(x), h(x)), 
                     \<lambda>i x. MH(##Lset(i), f'(x), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. M_is_recfun(L, MH(L,x), f(x), g(x), h(x)), 
             \<lambda>i x. M_is_recfun(##Lset(i), MH(##Lset(i),x), f(x), g(x), h(x))]"
apply (simp (no_asm_use) only: M_is_recfun_def)
apply (intro FOL_reflections function_reflections
             restriction_reflection MH_reflection)
done

subsubsection\<open>The Operator \<^term>\<open>is_wfrec\<close>\<close>

text\<open>The three arguments of \<^term>\<open>p\<close> are always 2, 1, 0;
      \<^term>\<open>p\<close> is enclosed by 5 quantifiers.\<close>

(* is_wfrec :: "[i\<Rightarrow>o, i, [i,i,i]\<Rightarrow>o, i, i] \<Rightarrow> o"
    "is_wfrec(M,MH,r,a,z) \<equiv> 
      \<exists>f[M]. M_is_recfun(M,MH,r,a,f) \<and> MH(a,f,z)" *)
definition
  is_wfrec_fm :: "[i, i, i, i]\<Rightarrow>i" where
  "is_wfrec_fm(p,r,a,z) \<equiv> 
    Exists(And(is_recfun_fm(p, succ(r), succ(a), 0),
           Exists(Exists(Exists(Exists(
             And(Equal(2,a#+5), And(Equal(1,4), And(Equal(0,z#+5), p)))))))))"

text\<open>We call \<^term>\<open>p\<close> with arguments a, f, z by equating them with 
  the corresponding quantified variables with de Bruijn indices 2, 1, 0.\<close>

text\<open>There's an additional existential quantifier to ensure that the
      environments in both calls to MH have the same length.\<close>

lemma is_wfrec_type [TC]:
     "\<lbrakk>p \<in> formula; x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> 
      \<Longrightarrow> is_wfrec_fm(p,x,y,z) \<in> formula"
by (simp add: is_wfrec_fm_def) 

lemma sats_is_wfrec_fm:
  assumes MH_iff_sats: 
      "\<And>a0 a1 a2 a3 a4. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A\<rbrakk> 
        \<Longrightarrow> MH(a2, a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env))))))"
  shows 
      "\<lbrakk>x \<in> nat; y < length(env); z < length(env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> sats(A, is_wfrec_fm(p,x,y,z), env) \<longleftrightarrow> 
           is_wfrec(##A, MH, nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule lt_length_in_nat, assumption)  
apply (simp add: is_wfrec_fm_def sats_is_recfun_fm is_wfrec_def MH_iff_sats [THEN iff_sym], blast) 
done


lemma is_wfrec_iff_sats:
  assumes MH_iff_sats: 
      "\<And>a0 a1 a2 a3 a4. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A\<rbrakk> 
        \<Longrightarrow> MH(a2, a1, a0) \<longleftrightarrow> sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,Cons(a4,env))))))"
  shows
  "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j < length(env); k < length(env); env \<in> list(A)\<rbrakk>
   \<Longrightarrow> is_wfrec(##A, MH, x, y, z) \<longleftrightarrow> sats(A, is_wfrec_fm(p,i,j,k), env)" 
by (simp add: sats_is_wfrec_fm [OF MH_iff_sats])

theorem is_wfrec_reflection:
  assumes MH_reflection:
    "\<And>f' f g h. REFLECTS[\<lambda>x. MH(L, f'(x), f(x), g(x), h(x)), 
                     \<lambda>i x. MH(##Lset(i), f'(x), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. is_wfrec(L, MH(L,x), f(x), g(x), h(x)), 
               \<lambda>i x. is_wfrec(##Lset(i), MH(##Lset(i),x), f(x), g(x), h(x))]"
apply (simp (no_asm_use) only: is_wfrec_def)
apply (intro FOL_reflections MH_reflection is_recfun_reflection)
done


subsection\<open>For Datatypes\<close>

subsubsection\<open>Binary Products, Internalized\<close>

definition
  cartprod_fm :: "[i,i,i]\<Rightarrow>i" where
(* "cartprod(M,A,B,z) \<equiv>
        \<forall>u[M]. u \<in> z \<longleftrightarrow> (\<exists>x[M]. x\<in>A \<and> (\<exists>y[M]. y\<in>B \<and> pair(M,x,y,u)))" *)
    "cartprod_fm(A,B,z) \<equiv>
       Forall(Iff(Member(0,succ(z)),
                  Exists(And(Member(0,succ(succ(A))),
                         Exists(And(Member(0,succ(succ(succ(B)))),
                                    pair_fm(1,0,2)))))))"

lemma cartprod_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> cartprod_fm(x,y,z) \<in> formula"
by (simp add: cartprod_fm_def)

lemma sats_cartprod_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, cartprod_fm(x,y,z), env) \<longleftrightarrow>
        cartprod(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: cartprod_fm_def cartprod_def)

lemma cartprod_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> cartprod(##A, x, y, z) \<longleftrightarrow> sats(A, cartprod_fm(i,j,k), env)"
by (simp)

theorem cartprod_reflection:
     "REFLECTS[\<lambda>x. cartprod(L,f(x),g(x),h(x)),
               \<lambda>i x. cartprod(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: cartprod_def)
apply (intro FOL_reflections pair_reflection)
done


subsubsection\<open>Binary Sums, Internalized\<close>

(* "is_sum(M,A,B,Z) \<equiv>
       \<exists>A0[M]. \<exists>n1[M]. \<exists>s1[M]. \<exists>B1[M].
         3      2       1        0
       number1(M,n1) \<and> cartprod(M,n1,A,A0) \<and> upair(M,n1,n1,s1) \<and>
       cartprod(M,s1,B,B1) \<and> union(M,A0,B1,Z)"  *)
definition
  sum_fm :: "[i,i,i]\<Rightarrow>i" where
    "sum_fm(A,B,Z) \<equiv>
       Exists(Exists(Exists(Exists(
        And(number1_fm(2),
            And(cartprod_fm(2,A#+4,3),
                And(upair_fm(2,2,1),
                    And(cartprod_fm(1,B#+4,0), union_fm(3,0,Z#+4)))))))))"

lemma sum_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> sum_fm(x,y,z) \<in> formula"
by (simp add: sum_fm_def)

lemma sats_sum_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, sum_fm(x,y,z), env) \<longleftrightarrow>
        is_sum(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: sum_fm_def is_sum_def)

lemma sum_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_sum(##A, x, y, z) \<longleftrightarrow> sats(A, sum_fm(i,j,k), env)"
by simp

theorem sum_reflection:
     "REFLECTS[\<lambda>x. is_sum(L,f(x),g(x),h(x)),
               \<lambda>i x. is_sum(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_sum_def)
apply (intro FOL_reflections function_reflections cartprod_reflection)
done


subsubsection\<open>The Operator \<^term>\<open>quasinat\<close>\<close>

(* "is_quasinat(M,z) \<equiv> empty(M,z) | (\<exists>m[M]. successor(M,m,z))" *)
definition
  quasinat_fm :: "i\<Rightarrow>i" where
    "quasinat_fm(z) \<equiv> Or(empty_fm(z), Exists(succ_fm(0,succ(z))))"

lemma quasinat_type [TC]:
     "x \<in> nat \<Longrightarrow> quasinat_fm(x) \<in> formula"
by (simp add: quasinat_fm_def)

lemma sats_quasinat_fm [simp]:
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, quasinat_fm(x), env) \<longleftrightarrow> is_quasinat(##A, nth(x,env))"
by (simp add: quasinat_fm_def is_quasinat_def)

lemma quasinat_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_quasinat(##A, x) \<longleftrightarrow> sats(A, quasinat_fm(i), env)"
by simp

theorem quasinat_reflection:
     "REFLECTS[\<lambda>x. is_quasinat(L,f(x)),
               \<lambda>i x. is_quasinat(##Lset(i),f(x))]"
apply (simp only: is_quasinat_def)
apply (intro FOL_reflections function_reflections)
done


subsubsection\<open>The Operator \<^term>\<open>is_nat_case\<close>\<close>
text\<open>I could not get it to work with the more natural assumption that 
 \<^term>\<open>is_b\<close> takes two arguments.  Instead it must be a formula where 1 and 0
 stand for \<^term>\<open>m\<close> and \<^term>\<open>b\<close>, respectively.\<close>

(* is_nat_case :: "[i\<Rightarrow>o, i, [i,i]\<Rightarrow>o, i, i] \<Rightarrow> o"
    "is_nat_case(M, a, is_b, k, z) \<equiv>
       (empty(M,k) \<longrightarrow> z=a) \<and>
       (\<forall>m[M]. successor(M,m,k) \<longrightarrow> is_b(m,z)) \<and>
       (is_quasinat(M,k) | empty(M,z))" *)
text\<open>The formula \<^term>\<open>is_b\<close> has free variables 1 and 0.\<close>
definition
  is_nat_case_fm :: "[i, i, i, i]\<Rightarrow>i" where
 "is_nat_case_fm(a,is_b,k,z) \<equiv> 
    And(Implies(empty_fm(k), Equal(z,a)),
        And(Forall(Implies(succ_fm(0,succ(k)), 
                   Forall(Implies(Equal(0,succ(succ(z))), is_b)))),
            Or(quasinat_fm(k), empty_fm(z))))"

lemma is_nat_case_type [TC]:
     "\<lbrakk>is_b \<in> formula;  
         x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> 
      \<Longrightarrow> is_nat_case_fm(x,is_b,y,z) \<in> formula"
by (simp add: is_nat_case_fm_def)

lemma sats_is_nat_case_fm:
  assumes is_b_iff_sats: 
      "\<And>a. a \<in> A \<Longrightarrow> is_b(a,nth(z, env)) \<longleftrightarrow> 
                      sats(A, p, Cons(nth(z,env), Cons(a, env)))"
  shows 
      "\<lbrakk>x \<in> nat; y \<in> nat; z < length(env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> sats(A, is_nat_case_fm(x,p,y,z), env) \<longleftrightarrow>
           is_nat_case(##A, nth(x,env), is_b, nth(y,env), nth(z,env))"
apply (frule lt_length_in_nat, assumption)
apply (simp add: is_nat_case_fm_def is_nat_case_def is_b_iff_sats [THEN iff_sym])
done

lemma is_nat_case_iff_sats:
  "\<lbrakk>(\<And>a. a \<in> A \<Longrightarrow> is_b(a,z) \<longleftrightarrow>
                      sats(A, p, Cons(z, Cons(a,env))));
      nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j \<in> nat; k < length(env); env \<in> list(A)\<rbrakk>
   \<Longrightarrow> is_nat_case(##A, x, is_b, y, z) \<longleftrightarrow> sats(A, is_nat_case_fm(i,p,j,k), env)"
by (simp add: sats_is_nat_case_fm [of A is_b])


text\<open>The second argument of \<^term>\<open>is_b\<close> gives it direct access to \<^term>\<open>x\<close>,
  which is essential for handling free variable references.  Without this
  argument, we cannot prove reflection for \<^term>\<open>iterates_MH\<close>.\<close>
theorem is_nat_case_reflection:
  assumes is_b_reflection:
    "\<And>h f g. REFLECTS[\<lambda>x. is_b(L, h(x), f(x), g(x)),
                     \<lambda>i x. is_b(##Lset(i), h(x), f(x), g(x))]"
  shows "REFLECTS[\<lambda>x. is_nat_case(L, f(x), is_b(L,x), g(x), h(x)),
               \<lambda>i x. is_nat_case(##Lset(i), f(x), is_b(##Lset(i), x), g(x), h(x))]"
apply (simp (no_asm_use) only: is_nat_case_def)
apply (intro FOL_reflections function_reflections
             restriction_reflection is_b_reflection quasinat_reflection)
done


subsection\<open>The Operator \<^term>\<open>iterates_MH\<close>, Needed for Iteration\<close>

(*  iterates_MH :: "[i\<Rightarrow>o, [i,i]\<Rightarrow>o, i, i, i, i] \<Rightarrow> o"
   "iterates_MH(M,isF,v,n,g,z) \<equiv>
        is_nat_case(M, v, \<lambda>m u. \<exists>gm[M]. fun_apply(M,g,m,gm) \<and> isF(gm,u),
                    n, z)" *)
definition
  iterates_MH_fm :: "[i, i, i, i, i]\<Rightarrow>i" where
 "iterates_MH_fm(isF,v,n,g,z) \<equiv> 
    is_nat_case_fm(v, 
      Exists(And(fun_apply_fm(succ(succ(succ(g))),2,0), 
                     Forall(Implies(Equal(0,2), isF)))), 
      n, z)"

lemma iterates_MH_type [TC]:
     "\<lbrakk>p \<in> formula;  
         v \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> 
      \<Longrightarrow> iterates_MH_fm(p,v,x,y,z) \<in> formula"
by (simp add: iterates_MH_fm_def)

lemma sats_iterates_MH_fm:
  assumes is_F_iff_sats:
      "\<And>a b c d. \<lbrakk>a \<in> A; b \<in> A; c \<in> A; d \<in> A\<rbrakk>
              \<Longrightarrow> is_F(a,b) \<longleftrightarrow>
                  sats(A, p, Cons(b, Cons(a, Cons(c, Cons(d,env)))))"
  shows 
      "\<lbrakk>v \<in> nat; x \<in> nat; y \<in> nat; z < length(env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> sats(A, iterates_MH_fm(p,v,x,y,z), env) \<longleftrightarrow>
           iterates_MH(##A, is_F, nth(v,env), nth(x,env), nth(y,env), nth(z,env))"
apply (frule lt_length_in_nat, assumption)  
apply (simp add: iterates_MH_fm_def iterates_MH_def sats_is_nat_case_fm 
              is_F_iff_sats [symmetric])
apply (rule is_nat_case_cong) 
apply (simp_all add: setclass_def)
done

lemma iterates_MH_iff_sats:
  assumes is_F_iff_sats:
      "\<And>a b c d. \<lbrakk>a \<in> A; b \<in> A; c \<in> A; d \<in> A\<rbrakk>
              \<Longrightarrow> is_F(a,b) \<longleftrightarrow>
                  sats(A, p, Cons(b, Cons(a, Cons(c, Cons(d,env)))))"
  shows 
  "\<lbrakk>nth(i',env) = v; nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i' \<in> nat; i \<in> nat; j \<in> nat; k < length(env); env \<in> list(A)\<rbrakk>
   \<Longrightarrow> iterates_MH(##A, is_F, v, x, y, z) \<longleftrightarrow>
       sats(A, iterates_MH_fm(p,i',i,j,k), env)"
by (simp add: sats_iterates_MH_fm [OF is_F_iff_sats]) 

text\<open>The second argument of \<^term>\<open>p\<close> gives it direct access to \<^term>\<open>x\<close>,
  which is essential for handling free variable references.  Without this
  argument, we cannot prove reflection for \<^term>\<open>list_N\<close>.\<close>
theorem iterates_MH_reflection:
  assumes p_reflection:
    "\<And>f g h. REFLECTS[\<lambda>x. p(L, h(x), f(x), g(x)),
                     \<lambda>i x. p(##Lset(i), h(x), f(x), g(x))]"
 shows "REFLECTS[\<lambda>x. iterates_MH(L, p(L,x), e(x), f(x), g(x), h(x)),
               \<lambda>i x. iterates_MH(##Lset(i), p(##Lset(i),x), e(x), f(x), g(x), h(x))]"
apply (simp (no_asm_use) only: iterates_MH_def)
apply (intro FOL_reflections function_reflections is_nat_case_reflection
             restriction_reflection p_reflection)
done


subsubsection\<open>The Operator \<^term>\<open>is_iterates\<close>\<close>

text\<open>The three arguments of \<^term>\<open>p\<close> are always 2, 1, 0;
      \<^term>\<open>p\<close> is enclosed by 9 (??) quantifiers.\<close>

(*    "is_iterates(M,isF,v,n,Z) \<equiv> 
      \<exists>sn[M]. \<exists>msn[M]. successor(M,n,sn) \<and> membership(M,sn,msn) \<and>
       1       0       is_wfrec(M, iterates_MH(M,isF,v), msn, n, Z)"*)

definition
  is_iterates_fm :: "[i, i, i, i]\<Rightarrow>i" where
  "is_iterates_fm(p,v,n,Z) \<equiv> 
     Exists(Exists(
      And(succ_fm(n#+2,1),
       And(Memrel_fm(1,0),
              is_wfrec_fm(iterates_MH_fm(p, v#+7, 2, 1, 0), 
                          0, n#+2, Z#+2)))))"

text\<open>We call \<^term>\<open>p\<close> with arguments a, f, z by equating them with 
  the corresponding quantified variables with de Bruijn indices 2, 1, 0.\<close>


lemma is_iterates_type [TC]:
     "\<lbrakk>p \<in> formula; x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> 
      \<Longrightarrow> is_iterates_fm(p,x,y,z) \<in> formula"
by (simp add: is_iterates_fm_def) 

lemma sats_is_iterates_fm:
  assumes is_F_iff_sats:
      "\<And>a b c d e f g h i j k. 
              \<lbrakk>a \<in> A; b \<in> A; c \<in> A; d \<in> A; e \<in> A; f \<in> A; 
                 g \<in> A; h \<in> A; i \<in> A; j \<in> A; k \<in> A\<rbrakk>
              \<Longrightarrow> is_F(a,b) \<longleftrightarrow>
                  sats(A, p, Cons(b, Cons(a, Cons(c, Cons(d, Cons(e, Cons(f, 
                      Cons(g, Cons(h, Cons(i, Cons(j, Cons(k, env))))))))))))"
  shows 
      "\<lbrakk>x \<in> nat; y < length(env); z < length(env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> sats(A, is_iterates_fm(p,x,y,z), env) \<longleftrightarrow>
           is_iterates(##A, is_F, nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule lt_length_in_nat, assumption)  
apply (simp add: is_iterates_fm_def is_iterates_def sats_is_nat_case_fm 
              is_F_iff_sats [symmetric] sats_is_wfrec_fm sats_iterates_MH_fm)
done


lemma is_iterates_iff_sats:
  assumes is_F_iff_sats:
      "\<And>a b c d e f g h i j k. 
              \<lbrakk>a \<in> A; b \<in> A; c \<in> A; d \<in> A; e \<in> A; f \<in> A; 
                 g \<in> A; h \<in> A; i \<in> A; j \<in> A; k \<in> A\<rbrakk>
              \<Longrightarrow> is_F(a,b) \<longleftrightarrow>
                  sats(A, p, Cons(b, Cons(a, Cons(c, Cons(d, Cons(e, Cons(f, 
                      Cons(g, Cons(h, Cons(i, Cons(j, Cons(k, env))))))))))))"
  shows 
  "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z; 
      i \<in> nat; j < length(env); k < length(env); env \<in> list(A)\<rbrakk>
   \<Longrightarrow> is_iterates(##A, is_F, x, y, z) \<longleftrightarrow>
       sats(A, is_iterates_fm(p,i,j,k), env)"
by (simp add: sats_is_iterates_fm [OF is_F_iff_sats]) 

text\<open>The second argument of \<^term>\<open>p\<close> gives it direct access to \<^term>\<open>x\<close>,
  which is essential for handling free variable references.  Without this
  argument, we cannot prove reflection for \<^term>\<open>list_N\<close>.\<close>
theorem is_iterates_reflection:
  assumes p_reflection:
    "\<And>f g h. REFLECTS[\<lambda>x. p(L, h(x), f(x), g(x)),
                     \<lambda>i x. p(##Lset(i), h(x), f(x), g(x))]"
 shows "REFLECTS[\<lambda>x. is_iterates(L, p(L,x), f(x), g(x), h(x)),
               \<lambda>i x. is_iterates(##Lset(i), p(##Lset(i),x), f(x), g(x), h(x))]"
apply (simp (no_asm_use) only: is_iterates_def)
apply (intro FOL_reflections function_reflections p_reflection
             is_wfrec_reflection iterates_MH_reflection)
done


subsubsection\<open>The Formula \<^term>\<open>is_eclose_n\<close>, Internalized\<close>

(* is_eclose_n(M,A,n,Z) \<equiv> is_iterates(M, big_union(M), A, n, Z) *)

definition
  eclose_n_fm :: "[i,i,i]\<Rightarrow>i" where
  "eclose_n_fm(A,n,Z) \<equiv> is_iterates_fm(big_union_fm(1,0), A, n, Z)"

lemma eclose_n_fm_type [TC]:
 "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> eclose_n_fm(x,y,z) \<in> formula"
by (simp add: eclose_n_fm_def)

lemma sats_eclose_n_fm [simp]:
   "\<lbrakk>x \<in> nat; y < length(env); z < length(env); env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, eclose_n_fm(x,y,z), env) \<longleftrightarrow>
        is_eclose_n(##A, nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: eclose_n_fm_def is_eclose_n_def 
                 sats_is_iterates_fm) 
done

lemma eclose_n_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j < length(env); k < length(env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_eclose_n(##A, x, y, z) \<longleftrightarrow> sats(A, eclose_n_fm(i,j,k), env)"
by (simp)

theorem eclose_n_reflection:
     "REFLECTS[\<lambda>x. is_eclose_n(L, f(x), g(x), h(x)),  
               \<lambda>i x. is_eclose_n(##Lset(i), f(x), g(x), h(x))]"
apply (simp only: is_eclose_n_def)
apply (intro FOL_reflections function_reflections is_iterates_reflection) 
done


subsubsection\<open>Membership in \<^term>\<open>eclose(A)\<close>\<close>

(* mem_eclose(M,A,l) \<equiv> 
      \<exists>n[M]. \<exists>eclosen[M]. 
       finite_ordinal(M,n) \<and> is_eclose_n(M,A,n,eclosen) \<and> l \<in> eclosen *)
definition
  mem_eclose_fm :: "[i,i]\<Rightarrow>i" where
    "mem_eclose_fm(x,y) \<equiv>
       Exists(Exists(
         And(finite_ordinal_fm(1),
           And(eclose_n_fm(x#+2,1,0), Member(y#+2,0)))))"

lemma mem_eclose_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> mem_eclose_fm(x,y) \<in> formula"
by (simp add: mem_eclose_fm_def)

lemma sats_mem_eclose_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, mem_eclose_fm(x,y), env) \<longleftrightarrow> mem_eclose(##A, nth(x,env), nth(y,env))"
by (simp add: mem_eclose_fm_def mem_eclose_def)

lemma mem_eclose_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> mem_eclose(##A, x, y) \<longleftrightarrow> sats(A, mem_eclose_fm(i,j), env)"
by simp

theorem mem_eclose_reflection:
     "REFLECTS[\<lambda>x. mem_eclose(L,f(x),g(x)),
               \<lambda>i x. mem_eclose(##Lset(i),f(x),g(x))]"
apply (simp only: mem_eclose_def)
apply (intro FOL_reflections finite_ordinal_reflection eclose_n_reflection)
done


subsubsection\<open>The Predicate ``Is \<^term>\<open>eclose(A)\<close>''\<close>

(* is_eclose(M,A,Z) \<equiv> \<forall>l[M]. l \<in> Z \<longleftrightarrow> mem_eclose(M,A,l) *)
definition
  is_eclose_fm :: "[i,i]\<Rightarrow>i" where
    "is_eclose_fm(A,Z) \<equiv>
       Forall(Iff(Member(0,succ(Z)), mem_eclose_fm(succ(A),0)))"

lemma is_eclose_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> is_eclose_fm(x,y) \<in> formula"
by (simp add: is_eclose_fm_def)

lemma sats_is_eclose_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, is_eclose_fm(x,y), env) \<longleftrightarrow> is_eclose(##A, nth(x,env), nth(y,env))"
by (simp add: is_eclose_fm_def is_eclose_def)

lemma is_eclose_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_eclose(##A, x, y) \<longleftrightarrow> sats(A, is_eclose_fm(i,j), env)"
by simp

theorem is_eclose_reflection:
     "REFLECTS[\<lambda>x. is_eclose(L,f(x),g(x)),
               \<lambda>i x. is_eclose(##Lset(i),f(x),g(x))]"
apply (simp only: is_eclose_def)
apply (intro FOL_reflections mem_eclose_reflection)
done


subsubsection\<open>The List Functor, Internalized\<close>

definition
  list_functor_fm :: "[i,i,i]\<Rightarrow>i" where
(* "is_list_functor(M,A,X,Z) \<equiv>
        \<exists>n1[M]. \<exists>AX[M].
         number1(M,n1) \<and> cartprod(M,A,X,AX) \<and> is_sum(M,n1,AX,Z)" *)
    "list_functor_fm(A,X,Z) \<equiv>
       Exists(Exists(
        And(number1_fm(1),
            And(cartprod_fm(A#+2,X#+2,0), sum_fm(1,0,Z#+2)))))"

lemma list_functor_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> list_functor_fm(x,y,z) \<in> formula"
by (simp add: list_functor_fm_def)

lemma sats_list_functor_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, list_functor_fm(x,y,z), env) \<longleftrightarrow>
        is_list_functor(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: list_functor_fm_def is_list_functor_def)

lemma list_functor_iff_sats:
  "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
      i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> is_list_functor(##A, x, y, z) \<longleftrightarrow> sats(A, list_functor_fm(i,j,k), env)"
by simp

theorem list_functor_reflection:
     "REFLECTS[\<lambda>x. is_list_functor(L,f(x),g(x),h(x)),
               \<lambda>i x. is_list_functor(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_list_functor_def)
apply (intro FOL_reflections number1_reflection
             cartprod_reflection sum_reflection)
done


subsubsection\<open>The Formula \<^term>\<open>is_list_N\<close>, Internalized\<close>

(* "is_list_N(M,A,n,Z) \<equiv> 
      \<exists>zero[M]. empty(M,zero) \<and> 
                is_iterates(M, is_list_functor(M,A), zero, n, Z)" *)

definition
  list_N_fm :: "[i,i,i]\<Rightarrow>i" where
  "list_N_fm(A,n,Z) \<equiv> 
     Exists(
       And(empty_fm(0),
           is_iterates_fm(list_functor_fm(A#+9#+3,1,0), 0, n#+1, Z#+1)))"

lemma list_N_fm_type [TC]:
 "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> list_N_fm(x,y,z) \<in> formula"
by (simp add: list_N_fm_def)

lemma sats_list_N_fm [simp]:
   "\<lbrakk>x \<in> nat; y < length(env); z < length(env); env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, list_N_fm(x,y,z), env) \<longleftrightarrow>
        is_list_N(##A, nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: list_N_fm_def is_list_N_def sats_is_iterates_fm) 
done

lemma list_N_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j < length(env); k < length(env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_list_N(##A, x, y, z) \<longleftrightarrow> sats(A, list_N_fm(i,j,k), env)"
by (simp)

theorem list_N_reflection:
     "REFLECTS[\<lambda>x. is_list_N(L, f(x), g(x), h(x)),  
               \<lambda>i x. is_list_N(##Lset(i), f(x), g(x), h(x))]"
apply (simp only: is_list_N_def)
apply (intro FOL_reflections function_reflections 
             is_iterates_reflection list_functor_reflection) 
done



subsubsection\<open>The Predicate ``Is A List''\<close>

(* mem_list(M,A,l) \<equiv> 
      \<exists>n[M]. \<exists>listn[M]. 
       finite_ordinal(M,n) \<and> is_list_N(M,A,n,listn) \<and> l \<in> listn *)
definition
  mem_list_fm :: "[i,i]\<Rightarrow>i" where
    "mem_list_fm(x,y) \<equiv>
       Exists(Exists(
         And(finite_ordinal_fm(1),
           And(list_N_fm(x#+2,1,0), Member(y#+2,0)))))"

lemma mem_list_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> mem_list_fm(x,y) \<in> formula"
by (simp add: mem_list_fm_def)

lemma sats_mem_list_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, mem_list_fm(x,y), env) \<longleftrightarrow> mem_list(##A, nth(x,env), nth(y,env))"
by (simp add: mem_list_fm_def mem_list_def)

lemma mem_list_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> mem_list(##A, x, y) \<longleftrightarrow> sats(A, mem_list_fm(i,j), env)"
by simp

theorem mem_list_reflection:
     "REFLECTS[\<lambda>x. mem_list(L,f(x),g(x)),
               \<lambda>i x. mem_list(##Lset(i),f(x),g(x))]"
apply (simp only: mem_list_def)
apply (intro FOL_reflections finite_ordinal_reflection list_N_reflection)
done


subsubsection\<open>The Predicate ``Is \<^term>\<open>list(A)\<close>''\<close>

(* is_list(M,A,Z) \<equiv> \<forall>l[M]. l \<in> Z \<longleftrightarrow> mem_list(M,A,l) *)
definition
  is_list_fm :: "[i,i]\<Rightarrow>i" where
    "is_list_fm(A,Z) \<equiv>
       Forall(Iff(Member(0,succ(Z)), mem_list_fm(succ(A),0)))"

lemma is_list_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> is_list_fm(x,y) \<in> formula"
by (simp add: is_list_fm_def)

lemma sats_is_list_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, is_list_fm(x,y), env) \<longleftrightarrow> is_list(##A, nth(x,env), nth(y,env))"
by (simp add: is_list_fm_def is_list_def)

lemma is_list_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_list(##A, x, y) \<longleftrightarrow> sats(A, is_list_fm(i,j), env)"
by simp

theorem is_list_reflection:
     "REFLECTS[\<lambda>x. is_list(L,f(x),g(x)),
               \<lambda>i x. is_list(##Lset(i),f(x),g(x))]"
apply (simp only: is_list_def)
apply (intro FOL_reflections mem_list_reflection)
done


subsubsection\<open>The Formula Functor, Internalized\<close>

definition formula_functor_fm :: "[i,i]\<Rightarrow>i" where
(*     "is_formula_functor(M,X,Z) \<equiv>
        \<exists>nat'[M]. \<exists>natnat[M]. \<exists>natnatsum[M]. \<exists>XX[M]. \<exists>X3[M].
           4           3               2       1       0
          omega(M,nat') \<and> cartprod(M,nat',nat',natnat) \<and>
          is_sum(M,natnat,natnat,natnatsum) \<and>
          cartprod(M,X,X,XX) \<and> is_sum(M,XX,X,X3) \<and>
          is_sum(M,natnatsum,X3,Z)" *)
    "formula_functor_fm(X,Z) \<equiv>
       Exists(Exists(Exists(Exists(Exists(
        And(omega_fm(4),
         And(cartprod_fm(4,4,3),
          And(sum_fm(3,3,2),
           And(cartprod_fm(X#+5,X#+5,1),
            And(sum_fm(1,X#+5,0), sum_fm(2,0,Z#+5)))))))))))"

lemma formula_functor_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> formula_functor_fm(x,y) \<in> formula"
by (simp add: formula_functor_fm_def)

lemma sats_formula_functor_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, formula_functor_fm(x,y), env) \<longleftrightarrow>
        is_formula_functor(##A, nth(x,env), nth(y,env))"
by (simp add: formula_functor_fm_def is_formula_functor_def)

lemma formula_functor_iff_sats:
  "\<lbrakk>nth(i,env) = x; nth(j,env) = y;
      i \<in> nat; j \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> is_formula_functor(##A, x, y) \<longleftrightarrow> sats(A, formula_functor_fm(i,j), env)"
by simp

theorem formula_functor_reflection:
     "REFLECTS[\<lambda>x. is_formula_functor(L,f(x),g(x)),
               \<lambda>i x. is_formula_functor(##Lset(i),f(x),g(x))]"
apply (simp only: is_formula_functor_def)
apply (intro FOL_reflections omega_reflection
             cartprod_reflection sum_reflection)
done


subsubsection\<open>The Formula \<^term>\<open>is_formula_N\<close>, Internalized\<close>

(*  "is_formula_N(M,n,Z) \<equiv> 
      \<exists>zero[M]. empty(M,zero) \<and> 
                is_iterates(M, is_formula_functor(M), zero, n, Z)" *) 
definition
  formula_N_fm :: "[i,i]\<Rightarrow>i" where
  "formula_N_fm(n,Z) \<equiv> 
     Exists(
       And(empty_fm(0),
           is_iterates_fm(formula_functor_fm(1,0), 0, n#+1, Z#+1)))"

lemma formula_N_fm_type [TC]:
 "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> formula_N_fm(x,y) \<in> formula"
by (simp add: formula_N_fm_def)

lemma sats_formula_N_fm [simp]:
   "\<lbrakk>x < length(env); y < length(env); env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, formula_N_fm(x,y), env) \<longleftrightarrow>
        is_formula_N(##A, nth(x,env), nth(y,env))"
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (frule lt_length_in_nat, assumption)  
apply (simp add: formula_N_fm_def is_formula_N_def sats_is_iterates_fm) 
done

lemma formula_N_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; 
          i < length(env); j < length(env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_formula_N(##A, x, y) \<longleftrightarrow> sats(A, formula_N_fm(i,j), env)"
by (simp)

theorem formula_N_reflection:
     "REFLECTS[\<lambda>x. is_formula_N(L, f(x), g(x)),  
               \<lambda>i x. is_formula_N(##Lset(i), f(x), g(x))]"
apply (simp only: is_formula_N_def)
apply (intro FOL_reflections function_reflections 
             is_iterates_reflection formula_functor_reflection) 
done



subsubsection\<open>The Predicate ``Is A Formula''\<close>

(*  mem_formula(M,p) \<equiv> 
      \<exists>n[M]. \<exists>formn[M]. 
       finite_ordinal(M,n) \<and> is_formula_N(M,n,formn) \<and> p \<in> formn *)
definition
  mem_formula_fm :: "i\<Rightarrow>i" where
    "mem_formula_fm(x) \<equiv>
       Exists(Exists(
         And(finite_ordinal_fm(1),
           And(formula_N_fm(1,0), Member(x#+2,0)))))"

lemma mem_formula_type [TC]:
     "x \<in> nat \<Longrightarrow> mem_formula_fm(x) \<in> formula"
by (simp add: mem_formula_fm_def)

lemma sats_mem_formula_fm [simp]:
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, mem_formula_fm(x), env) \<longleftrightarrow> mem_formula(##A, nth(x,env))"
by (simp add: mem_formula_fm_def mem_formula_def)

lemma mem_formula_iff_sats:
      "\<lbrakk>nth(i,env) = x; i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> mem_formula(##A, x) \<longleftrightarrow> sats(A, mem_formula_fm(i), env)"
by simp

theorem mem_formula_reflection:
     "REFLECTS[\<lambda>x. mem_formula(L,f(x)),
               \<lambda>i x. mem_formula(##Lset(i),f(x))]"
apply (simp only: mem_formula_def)
apply (intro FOL_reflections finite_ordinal_reflection formula_N_reflection)
done



subsubsection\<open>The Predicate ``Is \<^term>\<open>formula\<close>''\<close>

(* is_formula(M,Z) \<equiv> \<forall>p[M]. p \<in> Z \<longleftrightarrow> mem_formula(M,p) *)
definition
  is_formula_fm :: "i\<Rightarrow>i" where
    "is_formula_fm(Z) \<equiv> Forall(Iff(Member(0,succ(Z)), mem_formula_fm(0)))"

lemma is_formula_type [TC]:
     "x \<in> nat \<Longrightarrow> is_formula_fm(x) \<in> formula"
by (simp add: is_formula_fm_def)

lemma sats_is_formula_fm [simp]:
   "\<lbrakk>x \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, is_formula_fm(x), env) \<longleftrightarrow> is_formula(##A, nth(x,env))"
by (simp add: is_formula_fm_def is_formula_def)

lemma is_formula_iff_sats:
      "\<lbrakk>nth(i,env) = x; i \<in> nat; env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_formula(##A, x) \<longleftrightarrow> sats(A, is_formula_fm(i), env)"
by simp

theorem is_formula_reflection:
     "REFLECTS[\<lambda>x. is_formula(L,f(x)),
               \<lambda>i x. is_formula(##Lset(i),f(x))]"
apply (simp only: is_formula_def)
apply (intro FOL_reflections mem_formula_reflection)
done


subsubsection\<open>The Operator \<^term>\<open>is_transrec\<close>\<close>

text\<open>The three arguments of \<^term>\<open>p\<close> are always 2, 1, 0.  It is buried
   within eight quantifiers!
   We call \<^term>\<open>p\<close> with arguments a, f, z by equating them with 
  the corresponding quantified variables with de Bruijn indices 2, 1, 0.\<close>

(* is_transrec :: "[i\<Rightarrow>o, [i,i,i]\<Rightarrow>o, i, i] \<Rightarrow> o"
   "is_transrec(M,MH,a,z) \<equiv> 
      \<exists>sa[M]. \<exists>esa[M]. \<exists>mesa[M]. 
       2       1         0
       upair(M,a,a,sa) \<and> is_eclose(M,sa,esa) \<and> membership(M,esa,mesa) \<and>
       is_wfrec(M,MH,mesa,a,z)" *)
definition
  is_transrec_fm :: "[i, i, i]\<Rightarrow>i" where
 "is_transrec_fm(p,a,z) \<equiv> 
    Exists(Exists(Exists(
      And(upair_fm(a#+3,a#+3,2),
       And(is_eclose_fm(2,1),
        And(Memrel_fm(1,0), is_wfrec_fm(p,0,a#+3,z#+3)))))))"


lemma is_transrec_type [TC]:
     "\<lbrakk>p \<in> formula; x \<in> nat; z \<in> nat\<rbrakk> 
      \<Longrightarrow> is_transrec_fm(p,x,z) \<in> formula"
by (simp add: is_transrec_fm_def) 

lemma sats_is_transrec_fm:
  assumes MH_iff_sats: 
      "\<And>a0 a1 a2 a3 a4 a5 a6 a7. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A; a5\<in>A; a6\<in>A; a7\<in>A\<rbrakk> 
        \<Longrightarrow> MH(a2, a1, a0) \<longleftrightarrow> 
            sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,
                          Cons(a4,Cons(a5,Cons(a6,Cons(a7,env)))))))))"
  shows 
      "\<lbrakk>x < length(env); z < length(env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> sats(A, is_transrec_fm(p,x,z), env) \<longleftrightarrow> 
           is_transrec(##A, MH, nth(x,env), nth(z,env))"
apply (frule_tac x=z in lt_length_in_nat, assumption)  
apply (frule_tac x=x in lt_length_in_nat, assumption)  
apply (simp add: is_transrec_fm_def sats_is_wfrec_fm is_transrec_def MH_iff_sats [THEN iff_sym]) 
done


lemma is_transrec_iff_sats:
  assumes MH_iff_sats: 
      "\<And>a0 a1 a2 a3 a4 a5 a6 a7. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A; a3\<in>A; a4\<in>A; a5\<in>A; a6\<in>A; a7\<in>A\<rbrakk> 
        \<Longrightarrow> MH(a2, a1, a0) \<longleftrightarrow> 
            sats(A, p, Cons(a0,Cons(a1,Cons(a2,Cons(a3,
                          Cons(a4,Cons(a5,Cons(a6,Cons(a7,env)))))))))"
  shows
  "\<lbrakk>nth(i,env) = x; nth(k,env) = z; 
      i < length(env); k < length(env); env \<in> list(A)\<rbrakk>
   \<Longrightarrow> is_transrec(##A, MH, x, z) \<longleftrightarrow> sats(A, is_transrec_fm(p,i,k), env)" 
by (simp add: sats_is_transrec_fm [OF MH_iff_sats])

theorem is_transrec_reflection:
  assumes MH_reflection:
    "\<And>f' f g h. REFLECTS[\<lambda>x. MH(L, f'(x), f(x), g(x), h(x)), 
                     \<lambda>i x. MH(##Lset(i), f'(x), f(x), g(x), h(x))]"
  shows "REFLECTS[\<lambda>x. is_transrec(L, MH(L,x), f(x), h(x)), 
               \<lambda>i x. is_transrec(##Lset(i), MH(##Lset(i),x), f(x), h(x))]"
apply (simp (no_asm_use) only: is_transrec_def)
apply (intro FOL_reflections function_reflections MH_reflection 
             is_wfrec_reflection is_eclose_reflection)
done

end
