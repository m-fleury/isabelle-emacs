(*  Title:      ZF/Constructible/Satisfies_absolute.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>Absoluteness for the Satisfies Relation on Formulas\<close>

theory Satisfies_absolute imports Datatype_absolute Rec_Separation begin 


subsection \<open>More Internalization\<close>

subsubsection\<open>The Formula \<^term>\<open>is_depth\<close>, Internalized\<close>

(*    "is_depth(M,p,n) \<equiv> 
       \<exists>sn[M]. \<exists>formula_n[M]. \<exists>formula_sn[M]. 
         2          1                0
        is_formula_N(M,n,formula_n) \<and> p \<notin> formula_n \<and>
        successor(M,n,sn) \<and> is_formula_N(M,sn,formula_sn) \<and> p \<in> formula_sn" *)
definition
  depth_fm :: "[i,i]\<Rightarrow>i" where
  "depth_fm(p,n) \<equiv> 
     Exists(Exists(Exists(
       And(formula_N_fm(n#+3,1),
         And(Neg(Member(p#+3,1)),
          And(succ_fm(n#+3,2),
           And(formula_N_fm(2,0), Member(p#+3,0))))))))"

lemma depth_fm_type [TC]:
 "\<lbrakk>x \<in> nat; y \<in> nat\<rbrakk> \<Longrightarrow> depth_fm(x,y) \<in> formula"
by (simp add: depth_fm_def)

lemma sats_depth_fm [simp]:
   "\<lbrakk>x \<in> nat; y < length(env); env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, depth_fm(x,y), env) \<longleftrightarrow>
        is_depth(##A, nth(x,env), nth(y,env))"
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: depth_fm_def is_depth_def) 
done

lemma depth_iff_sats:
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; 
          i \<in> nat; j < length(env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_depth(##A, x, y) \<longleftrightarrow> sats(A, depth_fm(i,j), env)"
by (simp)

theorem depth_reflection:
     "REFLECTS[\<lambda>x. is_depth(L, f(x), g(x)),  
               \<lambda>i x. is_depth(##Lset(i), f(x), g(x))]"
apply (simp only: is_depth_def)
apply (intro FOL_reflections function_reflections formula_N_reflection) 
done



subsubsection\<open>The Operator \<^term>\<open>is_formula_case\<close>\<close>

text\<open>The arguments of \<^term>\<open>is_a\<close> are always 2, 1, 0, and the formula
      will be enclosed by three quantifiers.\<close>

(* is_formula_case :: 
    "[i\<Rightarrow>o, [i,i,i]\<Rightarrow>o, [i,i,i]\<Rightarrow>o, [i,i,i]\<Rightarrow>o, [i,i]\<Rightarrow>o, i, i] \<Rightarrow> o"
  "is_formula_case(M, is_a, is_b, is_c, is_d, v, z) \<equiv> 
      (\<forall>x[M]. \<forall>y[M]. x\<in>nat \<longrightarrow> y\<in>nat \<longrightarrow> is_Member(M,x,y,v) \<longrightarrow> is_a(x,y,z)) \<and>
      (\<forall>x[M]. \<forall>y[M]. x\<in>nat \<longrightarrow> y\<in>nat \<longrightarrow> is_Equal(M,x,y,v) \<longrightarrow> is_b(x,y,z)) \<and>
      (\<forall>x[M]. \<forall>y[M]. x\<in>formula \<longrightarrow> y\<in>formula \<longrightarrow> 
                     is_Nand(M,x,y,v) \<longrightarrow> is_c(x,y,z)) \<and>
      (\<forall>x[M]. x\<in>formula \<longrightarrow> is_Forall(M,x,v) \<longrightarrow> is_d(x,z))" *)

definition
  formula_case_fm :: "[i, i, i, i, i, i]\<Rightarrow>i" where
  "formula_case_fm(is_a, is_b, is_c, is_d, v, z) \<equiv> 
        And(Forall(Forall(Implies(finite_ordinal_fm(1), 
                           Implies(finite_ordinal_fm(0), 
                            Implies(Member_fm(1,0,v#+2), 
                             Forall(Implies(Equal(0,z#+3), is_a))))))),
        And(Forall(Forall(Implies(finite_ordinal_fm(1), 
                           Implies(finite_ordinal_fm(0), 
                            Implies(Equal_fm(1,0,v#+2), 
                             Forall(Implies(Equal(0,z#+3), is_b))))))),
        And(Forall(Forall(Implies(mem_formula_fm(1), 
                           Implies(mem_formula_fm(0), 
                            Implies(Nand_fm(1,0,v#+2), 
                             Forall(Implies(Equal(0,z#+3), is_c))))))),
        Forall(Implies(mem_formula_fm(0), 
                       Implies(Forall_fm(0,succ(v)), 
                             Forall(Implies(Equal(0,z#+2), is_d))))))))"


lemma is_formula_case_type [TC]:
     "\<lbrakk>is_a \<in> formula;  is_b \<in> formula;  is_c \<in> formula;  is_d \<in> formula;  
         x \<in> nat; y \<in> nat\<rbrakk> 
      \<Longrightarrow> formula_case_fm(is_a, is_b, is_c, is_d, x, y) \<in> formula"
by (simp add: formula_case_fm_def)

lemma sats_formula_case_fm:
  assumes is_a_iff_sats: 
      "\<And>a0 a1 a2. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A\<rbrakk>  
        \<Longrightarrow> ISA(a2, a1, a0) \<longleftrightarrow> sats(A, is_a, Cons(a0,Cons(a1,Cons(a2,env))))"
  and is_b_iff_sats: 
      "\<And>a0 a1 a2. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A\<rbrakk>  
        \<Longrightarrow> ISB(a2, a1, a0) \<longleftrightarrow> sats(A, is_b, Cons(a0,Cons(a1,Cons(a2,env))))"
  and is_c_iff_sats: 
      "\<And>a0 a1 a2. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A\<rbrakk>  
        \<Longrightarrow> ISC(a2, a1, a0) \<longleftrightarrow> sats(A, is_c, Cons(a0,Cons(a1,Cons(a2,env))))"
  and is_d_iff_sats: 
      "\<And>a0 a1. 
        \<lbrakk>a0\<in>A; a1\<in>A\<rbrakk>  
        \<Longrightarrow> ISD(a1, a0) \<longleftrightarrow> sats(A, is_d, Cons(a0,Cons(a1,env)))"
  shows 
      "\<lbrakk>x \<in> nat; y < length(env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> sats(A, formula_case_fm(is_a,is_b,is_c,is_d,x,y), env) \<longleftrightarrow>
           is_formula_case(##A, ISA, ISB, ISC, ISD, nth(x,env), nth(y,env))"
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: formula_case_fm_def is_formula_case_def 
                 is_a_iff_sats [THEN iff_sym] is_b_iff_sats [THEN iff_sym]
                 is_c_iff_sats [THEN iff_sym] is_d_iff_sats [THEN iff_sym])
done

lemma formula_case_iff_sats:
  assumes is_a_iff_sats: 
      "\<And>a0 a1 a2. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A\<rbrakk>  
        \<Longrightarrow> ISA(a2, a1, a0) \<longleftrightarrow> sats(A, is_a, Cons(a0,Cons(a1,Cons(a2,env))))"
  and is_b_iff_sats: 
      "\<And>a0 a1 a2. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A\<rbrakk>  
        \<Longrightarrow> ISB(a2, a1, a0) \<longleftrightarrow> sats(A, is_b, Cons(a0,Cons(a1,Cons(a2,env))))"
  and is_c_iff_sats: 
      "\<And>a0 a1 a2. 
        \<lbrakk>a0\<in>A; a1\<in>A; a2\<in>A\<rbrakk>  
        \<Longrightarrow> ISC(a2, a1, a0) \<longleftrightarrow> sats(A, is_c, Cons(a0,Cons(a1,Cons(a2,env))))"
  and is_d_iff_sats: 
      "\<And>a0 a1. 
        \<lbrakk>a0\<in>A; a1\<in>A\<rbrakk>  
        \<Longrightarrow> ISD(a1, a0) \<longleftrightarrow> sats(A, is_d, Cons(a0,Cons(a1,env)))"
  shows 
      "\<lbrakk>nth(i,env) = x; nth(j,env) = y; 
      i \<in> nat; j < length(env); env \<in> list(A)\<rbrakk>
       \<Longrightarrow> is_formula_case(##A, ISA, ISB, ISC, ISD, x, y) \<longleftrightarrow>
           sats(A, formula_case_fm(is_a,is_b,is_c,is_d,i,j), env)"
by (simp add: sats_formula_case_fm [OF is_a_iff_sats is_b_iff_sats 
                                       is_c_iff_sats is_d_iff_sats])


text\<open>The second argument of \<^term>\<open>is_a\<close> gives it direct access to \<^term>\<open>x\<close>,
  which is essential for handling free variable references.  Treatment is
  based on that of \<open>is_nat_case_reflection\<close>.\<close>
theorem is_formula_case_reflection:
  assumes is_a_reflection:
    "\<And>h f g g'. REFLECTS[\<lambda>x. is_a(L, h(x), f(x), g(x), g'(x)),
                     \<lambda>i x. is_a(##Lset(i), h(x), f(x), g(x), g'(x))]"
  and is_b_reflection:
    "\<And>h f g g'. REFLECTS[\<lambda>x. is_b(L, h(x), f(x), g(x), g'(x)),
                     \<lambda>i x. is_b(##Lset(i), h(x), f(x), g(x), g'(x))]"
  and is_c_reflection:
    "\<And>h f g g'. REFLECTS[\<lambda>x. is_c(L, h(x), f(x), g(x), g'(x)),
                     \<lambda>i x. is_c(##Lset(i), h(x), f(x), g(x), g'(x))]"
  and is_d_reflection:
    "\<And>h f g g'. REFLECTS[\<lambda>x. is_d(L, h(x), f(x), g(x)),
                     \<lambda>i x. is_d(##Lset(i), h(x), f(x), g(x))]"
  shows "REFLECTS[\<lambda>x. is_formula_case(L, is_a(L,x), is_b(L,x), is_c(L,x), is_d(L,x), g(x), h(x)),
               \<lambda>i x. is_formula_case(##Lset(i), is_a(##Lset(i), x), is_b(##Lset(i), x), is_c(##Lset(i), x), is_d(##Lset(i), x), g(x), h(x))]"
apply (simp (no_asm_use) only: is_formula_case_def)
apply (intro FOL_reflections function_reflections finite_ordinal_reflection
         mem_formula_reflection
         Member_reflection Equal_reflection Nand_reflection Forall_reflection
         is_a_reflection is_b_reflection is_c_reflection is_d_reflection)
done



subsection \<open>Absoluteness for the Function \<^term>\<open>satisfies\<close>\<close>

definition
  is_depth_apply :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
   \<comment> \<open>Merely a useful abbreviation for the sequel.\<close>
  "is_depth_apply(M,h,p,z) \<equiv>
    \<exists>dp[M]. \<exists>sdp[M]. \<exists>hsdp[M]. 
        finite_ordinal(M,dp) \<and> is_depth(M,p,dp) \<and> successor(M,dp,sdp) \<and>
        fun_apply(M,h,sdp,hsdp) \<and> fun_apply(M,hsdp,p,z)"

lemma (in M_datatypes) is_depth_apply_abs [simp]:
     "\<lbrakk>M(h); p \<in> formula; M(z)\<rbrakk> 
      \<Longrightarrow> is_depth_apply(M,h,p,z) \<longleftrightarrow> z = h ` succ(depth(p)) ` p"
by (simp add: is_depth_apply_def formula_into_M depth_type eq_commute)



text\<open>There is at present some redundancy between the relativizations in
 e.g. \<open>satisfies_is_a\<close> and those in e.g. \<open>Member_replacement\<close>.\<close>

text\<open>These constants let us instantiate the parameters \<^term>\<open>a\<close>, \<^term>\<open>b\<close>,
      \<^term>\<open>c\<close>, \<^term>\<open>d\<close>, etc., of the locale \<open>Formula_Rec\<close>.\<close>
definition
  satisfies_a :: "[i,i,i]\<Rightarrow>i" where
   "satisfies_a(A) \<equiv> 
    \<lambda>x y. \<lambda>env \<in> list(A). bool_of_o (nth(x,env) \<in> nth(y,env))"

definition
  satisfies_is_a :: "[i\<Rightarrow>o,i,i,i,i]\<Rightarrow>o" where
   "satisfies_is_a(M,A) \<equiv> 
    \<lambda>x y zz. \<forall>lA[M]. is_list(M,A,lA) \<longrightarrow>
             is_lambda(M, lA, 
                \<lambda>env z. is_bool_of_o(M, 
                      \<exists>nx[M]. \<exists>ny[M]. 
                       is_nth(M,x,env,nx) \<and> is_nth(M,y,env,ny) \<and> nx \<in> ny, z),
                zz)"

definition
  satisfies_b :: "[i,i,i]\<Rightarrow>i" where
   "satisfies_b(A) \<equiv>
    \<lambda>x y. \<lambda>env \<in> list(A). bool_of_o (nth(x,env) = nth(y,env))"

definition
  satisfies_is_b :: "[i\<Rightarrow>o,i,i,i,i]\<Rightarrow>o" where
   \<comment> \<open>We simplify the formula to have just \<^term>\<open>nx\<close> rather than 
       introducing \<^term>\<open>ny\<close> with  \<^term>\<open>nx=ny\<close>\<close>
  "satisfies_is_b(M,A) \<equiv> 
    \<lambda>x y zz. \<forall>lA[M]. is_list(M,A,lA) \<longrightarrow>
             is_lambda(M, lA, 
                \<lambda>env z. is_bool_of_o(M, 
                      \<exists>nx[M]. is_nth(M,x,env,nx) \<and> is_nth(M,y,env,nx), z),
                zz)"

definition 
  satisfies_c :: "[i,i,i,i,i]\<Rightarrow>i" where
   "satisfies_c(A) \<equiv> \<lambda>p q rp rq. \<lambda>env \<in> list(A). not(rp ` env and rq ` env)"

definition
  satisfies_is_c :: "[i\<Rightarrow>o,i,i,i,i,i]\<Rightarrow>o" where
   "satisfies_is_c(M,A,h) \<equiv> 
    \<lambda>p q zz. \<forall>lA[M]. is_list(M,A,lA) \<longrightarrow>
             is_lambda(M, lA, \<lambda>env z. \<exists>hp[M]. \<exists>hq[M]. 
                 (\<exists>rp[M]. is_depth_apply(M,h,p,rp) \<and> fun_apply(M,rp,env,hp)) \<and> 
                 (\<exists>rq[M]. is_depth_apply(M,h,q,rq) \<and> fun_apply(M,rq,env,hq)) \<and> 
                 (\<exists>pq[M]. is_and(M,hp,hq,pq) \<and> is_not(M,pq,z)),
                zz)"

definition
  satisfies_d :: "[i,i,i]\<Rightarrow>i" where
   "satisfies_d(A) 
    \<equiv> \<lambda>p rp. \<lambda>env \<in> list(A). bool_of_o (\<forall>x\<in>A. rp ` (Cons(x,env)) = 1)"

definition
  satisfies_is_d :: "[i\<Rightarrow>o,i,i,i,i]\<Rightarrow>o" where
   "satisfies_is_d(M,A,h) \<equiv> 
    \<lambda>p zz. \<forall>lA[M]. is_list(M,A,lA) \<longrightarrow>
             is_lambda(M, lA, 
                \<lambda>env z. \<exists>rp[M]. is_depth_apply(M,h,p,rp) \<and> 
                    is_bool_of_o(M, 
                           \<forall>x[M]. \<forall>xenv[M]. \<forall>hp[M]. 
                              x\<in>A \<longrightarrow> is_Cons(M,x,env,xenv) \<longrightarrow> 
                              fun_apply(M,rp,xenv,hp) \<longrightarrow> number1(M,hp),
                  z),
               zz)"

definition
  satisfies_MH :: "[i\<Rightarrow>o,i,i,i,i]\<Rightarrow>o" where
    \<comment> \<open>The variable \<^term>\<open>u\<close> is unused, but gives \<^term>\<open>satisfies_MH\<close> 
        the correct arity.\<close>
  "satisfies_MH \<equiv> 
    \<lambda>M A u f z. 
         \<forall>fml[M]. is_formula(M,fml) \<longrightarrow>
             is_lambda (M, fml, 
               is_formula_case (M, satisfies_is_a(M,A), 
                                satisfies_is_b(M,A), 
                                satisfies_is_c(M,A,f), satisfies_is_d(M,A,f)),
               z)"

definition
  is_satisfies :: "[i\<Rightarrow>o,i,i,i]\<Rightarrow>o" where
  "is_satisfies(M,A) \<equiv> is_formula_rec (M, satisfies_MH(M,A))"


text\<open>This lemma relates the fragments defined above to the original primitive
      recursion in \<^term>\<open>satisfies\<close>.
      Induction is not required: the definitions are directly equal!\<close>
lemma satisfies_eq:
  "satisfies(A,p) = 
   formula_rec (satisfies_a(A), satisfies_b(A), 
                satisfies_c(A), satisfies_d(A), p)"
by (simp add: satisfies_formula_def satisfies_a_def satisfies_b_def 
              satisfies_c_def satisfies_d_def) 

text\<open>Further constraints on the class \<^term>\<open>M\<close> in order to prove
      absoluteness for the constants defined above.  The ultimate goal
      is the absoluteness of the function \<^term>\<open>satisfies\<close>.\<close>
locale M_satisfies = M_eclose +
 assumes 
   Member_replacement:
    "\<lbrakk>M(A); x \<in> nat; y \<in> nat\<rbrakk>
     \<Longrightarrow> strong_replacement
         (M, \<lambda>env z. \<exists>bo[M]. \<exists>nx[M]. \<exists>ny[M]. 
              env \<in> list(A) \<and> is_nth(M,x,env,nx) \<and> is_nth(M,y,env,ny) \<and> 
              is_bool_of_o(M, nx \<in> ny, bo) \<and>
              pair(M, env, bo, z))"
 and
   Equal_replacement:
    "\<lbrakk>M(A); x \<in> nat; y \<in> nat\<rbrakk>
     \<Longrightarrow> strong_replacement
         (M, \<lambda>env z. \<exists>bo[M]. \<exists>nx[M]. \<exists>ny[M]. 
              env \<in> list(A) \<and> is_nth(M,x,env,nx) \<and> is_nth(M,y,env,ny) \<and> 
              is_bool_of_o(M, nx = ny, bo) \<and>
              pair(M, env, bo, z))"
 and
   Nand_replacement:
    "\<lbrakk>M(A); M(rp); M(rq)\<rbrakk>
     \<Longrightarrow> strong_replacement
         (M, \<lambda>env z. \<exists>rpe[M]. \<exists>rqe[M]. \<exists>andpq[M]. \<exists>notpq[M]. 
               fun_apply(M,rp,env,rpe) \<and> fun_apply(M,rq,env,rqe) \<and> 
               is_and(M,rpe,rqe,andpq) \<and> is_not(M,andpq,notpq) \<and> 
               env \<in> list(A) \<and> pair(M, env, notpq, z))"
 and
  Forall_replacement:
   "\<lbrakk>M(A); M(rp)\<rbrakk>
    \<Longrightarrow> strong_replacement
        (M, \<lambda>env z. \<exists>bo[M]. 
              env \<in> list(A) \<and> 
              is_bool_of_o (M, 
                            \<forall>a[M]. \<forall>co[M]. \<forall>rpco[M]. 
                               a\<in>A \<longrightarrow> is_Cons(M,a,env,co) \<longrightarrow>
                               fun_apply(M,rp,co,rpco) \<longrightarrow> number1(M, rpco), 
                            bo) \<and>
              pair(M,env,bo,z))"
 and
  formula_rec_replacement: 
      \<comment> \<open>For the \<^term>\<open>transrec\<close>\<close>
   "\<lbrakk>n \<in> nat; M(A)\<rbrakk> \<Longrightarrow> transrec_replacement(M, satisfies_MH(M,A), n)"
 and
  formula_rec_lambda_replacement:  
      \<comment> \<open>For the \<open>\<lambda>-abstraction\<close> in the \<^term>\<open>transrec\<close> body\<close>
   "\<lbrakk>M(g); M(A)\<rbrakk> \<Longrightarrow>
    strong_replacement (M, 
       \<lambda>x y. mem_formula(M,x) \<and>
             (\<exists>c[M]. is_formula_case(M, satisfies_is_a(M,A),
                                  satisfies_is_b(M,A),
                                  satisfies_is_c(M,A,g),
                                  satisfies_is_d(M,A,g), x, c) \<and>
             pair(M, x, c, y)))"


lemma (in M_satisfies) Member_replacement':
    "\<lbrakk>M(A); x \<in> nat; y \<in> nat\<rbrakk>
     \<Longrightarrow> strong_replacement
         (M, \<lambda>env z. env \<in> list(A) \<and>
                     z = \<langle>env, bool_of_o(nth(x, env) \<in> nth(y, env))\<rangle>)"
by (insert Member_replacement, simp) 

lemma (in M_satisfies) Equal_replacement':
    "\<lbrakk>M(A); x \<in> nat; y \<in> nat\<rbrakk>
     \<Longrightarrow> strong_replacement
         (M, \<lambda>env z. env \<in> list(A) \<and>
                     z = \<langle>env, bool_of_o(nth(x, env) = nth(y, env))\<rangle>)"
by (insert Equal_replacement, simp) 

lemma (in M_satisfies) Nand_replacement':
    "\<lbrakk>M(A); M(rp); M(rq)\<rbrakk>
     \<Longrightarrow> strong_replacement
         (M, \<lambda>env z. env \<in> list(A) \<and> z = \<langle>env, not(rp`env and rq`env)\<rangle>)"
by (insert Nand_replacement, simp) 

lemma (in M_satisfies) Forall_replacement':
   "\<lbrakk>M(A); M(rp)\<rbrakk>
    \<Longrightarrow> strong_replacement
        (M, \<lambda>env z.
               env \<in> list(A) \<and>
               z = \<langle>env, bool_of_o (\<forall>a\<in>A. rp ` Cons(a,env) = 1)\<rangle>)"
by (insert Forall_replacement, simp) 

lemma (in M_satisfies) a_closed:
     "\<lbrakk>M(A); x\<in>nat; y\<in>nat\<rbrakk> \<Longrightarrow> M(satisfies_a(A,x,y))"
apply (simp add: satisfies_a_def) 
apply (blast intro: lam_closed2 Member_replacement') 
done

lemma (in M_satisfies) a_rel:
     "M(A) \<Longrightarrow> Relation2(M, nat, nat, satisfies_is_a(M,A), satisfies_a(A))"
apply (simp add: Relation2_def satisfies_is_a_def satisfies_a_def)
apply (auto del: iffI intro!: lambda_abs2 simp add: Relation1_def) 
done

lemma (in M_satisfies) b_closed:
     "\<lbrakk>M(A); x\<in>nat; y\<in>nat\<rbrakk> \<Longrightarrow> M(satisfies_b(A,x,y))"
apply (simp add: satisfies_b_def) 
apply (blast intro: lam_closed2 Equal_replacement') 
done

lemma (in M_satisfies) b_rel:
     "M(A) \<Longrightarrow> Relation2(M, nat, nat, satisfies_is_b(M,A), satisfies_b(A))"
apply (simp add: Relation2_def satisfies_is_b_def satisfies_b_def)
apply (auto del: iffI intro!: lambda_abs2 simp add: Relation1_def) 
done

lemma (in M_satisfies) c_closed:
     "\<lbrakk>M(A); x \<in> formula; y \<in> formula; M(rx); M(ry)\<rbrakk> 
      \<Longrightarrow> M(satisfies_c(A,x,y,rx,ry))"
apply (simp add: satisfies_c_def) 
apply (rule lam_closed2) 
apply (rule Nand_replacement') 
apply (simp_all add: formula_into_M list_into_M [of _ A])
done

lemma (in M_satisfies) c_rel:
 "\<lbrakk>M(A); M(f)\<rbrakk> \<Longrightarrow> 
  Relation2 (M, formula, formula, 
               satisfies_is_c(M,A,f),
               \<lambda>u v. satisfies_c(A, u, v, f ` succ(depth(u)) ` u, 
                                          f ` succ(depth(v)) ` v))"
apply (simp add: Relation2_def satisfies_is_c_def satisfies_c_def)
apply (auto del: iffI intro!: lambda_abs2 
            simp add: Relation1_def formula_into_M) 
done

lemma (in M_satisfies) d_closed:
     "\<lbrakk>M(A); x \<in> formula; M(rx)\<rbrakk> \<Longrightarrow> M(satisfies_d(A,x,rx))"
apply (simp add: satisfies_d_def) 
apply (rule lam_closed2) 
apply (rule Forall_replacement') 
apply (simp_all add: formula_into_M list_into_M [of _ A])
done

lemma (in M_satisfies) d_rel:
 "\<lbrakk>M(A); M(f)\<rbrakk> \<Longrightarrow> 
  Relation1(M, formula, satisfies_is_d(M,A,f), 
     \<lambda>u. satisfies_d(A, u, f ` succ(depth(u)) ` u))"
apply (simp del: rall_abs 
            add: Relation1_def satisfies_is_d_def satisfies_d_def)
apply (auto del: iffI intro!: lambda_abs2 simp add: Relation1_def) 
done


lemma (in M_satisfies) fr_replace:
      "\<lbrakk>n \<in> nat; M(A)\<rbrakk> \<Longrightarrow> transrec_replacement(M,satisfies_MH(M,A),n)" 
by (blast intro: formula_rec_replacement) 

lemma (in M_satisfies) formula_case_satisfies_closed:
 "\<lbrakk>M(g); M(A); x \<in> formula\<rbrakk> \<Longrightarrow>
  M(formula_case (satisfies_a(A), satisfies_b(A),
       \<lambda>u v. satisfies_c(A, u, v, 
                         g ` succ(depth(u)) ` u, g ` succ(depth(v)) ` v),
       \<lambda>u. satisfies_d (A, u, g ` succ(depth(u)) ` u),
       x))"
by (blast intro: a_closed b_closed c_closed d_closed) 

lemma (in M_satisfies) fr_lam_replace:
   "\<lbrakk>M(g); M(A)\<rbrakk> \<Longrightarrow>
    strong_replacement (M, \<lambda>x y. x \<in> formula \<and>
            y = \<langle>x, 
                 formula_rec_case(satisfies_a(A),
                                  satisfies_b(A),
                                  satisfies_c(A),
                                  satisfies_d(A), g, x)\<rangle>)"
apply (insert formula_rec_lambda_replacement) 
apply (simp add: formula_rec_case_def formula_case_satisfies_closed
                 formula_case_abs [OF a_rel b_rel c_rel d_rel]) 
done



text\<open>Instantiate locale \<open>Formula_Rec\<close> for the 
      Function \<^term>\<open>satisfies\<close>\<close>

lemma (in M_satisfies) Formula_Rec_axioms_M:
   "M(A) \<Longrightarrow>
    Formula_Rec_axioms(M, satisfies_a(A), satisfies_is_a(M,A), 
                          satisfies_b(A), satisfies_is_b(M,A), 
                          satisfies_c(A), satisfies_is_c(M,A), 
                          satisfies_d(A), satisfies_is_d(M,A))"
apply (rule Formula_Rec_axioms.intro)
apply (assumption | 
       rule a_closed a_rel b_closed b_rel c_closed c_rel d_closed d_rel
       fr_replace [unfolded satisfies_MH_def]
       fr_lam_replace) +
done


theorem (in M_satisfies) Formula_Rec_M: 
    "M(A) \<Longrightarrow>
     Formula_Rec(M, satisfies_a(A), satisfies_is_a(M,A), 
                         satisfies_b(A), satisfies_is_b(M,A), 
                         satisfies_c(A), satisfies_is_c(M,A), 
                         satisfies_d(A), satisfies_is_d(M,A))"
  apply (rule Formula_Rec.intro)
   apply (rule M_satisfies.axioms, rule M_satisfies_axioms)
  apply (erule Formula_Rec_axioms_M) 
  done

lemmas (in M_satisfies) 
    satisfies_closed' = Formula_Rec.formula_rec_closed [OF Formula_Rec_M]
and satisfies_abs'    = Formula_Rec.formula_rec_abs [OF Formula_Rec_M]


lemma (in M_satisfies) satisfies_closed:
  "\<lbrakk>M(A); p \<in> formula\<rbrakk> \<Longrightarrow> M(satisfies(A,p))"
by (simp add: Formula_Rec.formula_rec_closed [OF Formula_Rec_M]  
              satisfies_eq) 

lemma (in M_satisfies) satisfies_abs:
  "\<lbrakk>M(A); M(z); p \<in> formula\<rbrakk> 
   \<Longrightarrow> is_satisfies(M,A,p,z) \<longleftrightarrow> z = satisfies(A,p)"
by (simp only: Formula_Rec.formula_rec_abs [OF Formula_Rec_M]  
               satisfies_eq is_satisfies_def satisfies_MH_def)


subsection\<open>Internalizations Needed to Instantiate \<open>M_satisfies\<close>\<close>

subsubsection\<open>The Operator \<^term>\<open>is_depth_apply\<close>, Internalized\<close>

(* is_depth_apply(M,h,p,z) \<equiv>
    \<exists>dp[M]. \<exists>sdp[M]. \<exists>hsdp[M]. 
      2        1         0
        finite_ordinal(M,dp) \<and> is_depth(M,p,dp) \<and> successor(M,dp,sdp) \<and>
        fun_apply(M,h,sdp,hsdp) \<and> fun_apply(M,hsdp,p,z) *)
definition
  depth_apply_fm :: "[i,i,i]\<Rightarrow>i" where
    "depth_apply_fm(h,p,z) \<equiv>
       Exists(Exists(Exists(
        And(finite_ordinal_fm(2),
         And(depth_fm(p#+3,2),
          And(succ_fm(2,1),
           And(fun_apply_fm(h#+3,1,0), fun_apply_fm(0,p#+3,z#+3))))))))"

lemma depth_apply_type [TC]:
     "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk> \<Longrightarrow> depth_apply_fm(x,y,z) \<in> formula"
by (simp add: depth_apply_fm_def)

lemma sats_depth_apply_fm [simp]:
   "\<lbrakk>x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, depth_apply_fm(x,y,z), env) \<longleftrightarrow>
        is_depth_apply(##A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: depth_apply_fm_def is_depth_apply_def)

lemma depth_apply_iff_sats:
    "\<lbrakk>nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
        i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)\<rbrakk>
     \<Longrightarrow> is_depth_apply(##A, x, y, z) \<longleftrightarrow> sats(A, depth_apply_fm(i,j,k), env)"
by simp

lemma depth_apply_reflection:
     "REFLECTS[\<lambda>x. is_depth_apply(L,f(x),g(x),h(x)),
               \<lambda>i x. is_depth_apply(##Lset(i),f(x),g(x),h(x))]"
apply (simp only: is_depth_apply_def)
apply (intro FOL_reflections function_reflections depth_reflection 
             finite_ordinal_reflection)
done


subsubsection\<open>The Operator \<^term>\<open>satisfies_is_a\<close>, Internalized\<close>

(* satisfies_is_a(M,A) \<equiv> 
    \<lambda>x y zz. \<forall>lA[M]. is_list(M,A,lA) \<longrightarrow>
             is_lambda(M, lA, 
                \<lambda>env z. is_bool_of_o(M, 
                      \<exists>nx[M]. \<exists>ny[M]. 
                       is_nth(M,x,env,nx) \<and> is_nth(M,y,env,ny) \<and> nx \<in> ny, z),
                zz)  *)

definition
  satisfies_is_a_fm :: "[i,i,i,i]\<Rightarrow>i" where
  "satisfies_is_a_fm(A,x,y,z) \<equiv>
   Forall(
     Implies(is_list_fm(succ(A),0),
       lambda_fm(
         bool_of_o_fm(Exists(
                       Exists(And(nth_fm(x#+6,3,1), 
                               And(nth_fm(y#+6,3,0), 
                                   Member(1,0))))), 0), 
         0, succ(z))))"

lemma satisfies_is_a_type [TC]:
     "\<lbrakk>A \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk>
      \<Longrightarrow> satisfies_is_a_fm(A,x,y,z) \<in> formula"
by (simp add: satisfies_is_a_fm_def)

lemma sats_satisfies_is_a_fm [simp]:
   "\<lbrakk>u \<in> nat; x < length(env); y < length(env); z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, satisfies_is_a_fm(u,x,y,z), env) \<longleftrightarrow>
        satisfies_is_a(##A, nth(u,env), nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=x in lt_length_in_nat, assumption)  
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: satisfies_is_a_fm_def satisfies_is_a_def sats_lambda_fm 
                 sats_bool_of_o_fm)
done

lemma satisfies_is_a_iff_sats:
  "\<lbrakk>nth(u,env) = nu; nth(x,env) = nx; nth(y,env) = ny; nth(z,env) = nz;
      u \<in> nat; x < length(env); y < length(env); z \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> satisfies_is_a(##A,nu,nx,ny,nz) \<longleftrightarrow>
       sats(A, satisfies_is_a_fm(u,x,y,z), env)"
by simp

theorem satisfies_is_a_reflection:
     "REFLECTS[\<lambda>x. satisfies_is_a(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. satisfies_is_a(##Lset(i),f(x),g(x),h(x),g'(x))]"
  unfolding satisfies_is_a_def 
apply (intro FOL_reflections is_lambda_reflection bool_of_o_reflection 
             nth_reflection is_list_reflection)
done


subsubsection\<open>The Operator \<^term>\<open>satisfies_is_b\<close>, Internalized\<close>

(* satisfies_is_b(M,A) \<equiv> 
    \<lambda>x y zz. \<forall>lA[M]. is_list(M,A,lA) \<longrightarrow>
             is_lambda(M, lA, 
                \<lambda>env z. is_bool_of_o(M, 
                      \<exists>nx[M]. is_nth(M,x,env,nx) \<and> is_nth(M,y,env,nx), z),
                zz) *)

definition
  satisfies_is_b_fm :: "[i,i,i,i]\<Rightarrow>i" where
 "satisfies_is_b_fm(A,x,y,z) \<equiv>
   Forall(
     Implies(is_list_fm(succ(A),0),
       lambda_fm(
         bool_of_o_fm(Exists(And(nth_fm(x#+5,2,0), nth_fm(y#+5,2,0))), 0), 
         0, succ(z))))"

lemma satisfies_is_b_type [TC]:
     "\<lbrakk>A \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk>
      \<Longrightarrow> satisfies_is_b_fm(A,x,y,z) \<in> formula"
by (simp add: satisfies_is_b_fm_def)

lemma sats_satisfies_is_b_fm [simp]:
   "\<lbrakk>u \<in> nat; x < length(env); y < length(env); z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, satisfies_is_b_fm(u,x,y,z), env) \<longleftrightarrow>
        satisfies_is_b(##A, nth(u,env), nth(x,env), nth(y,env), nth(z,env))"
apply (frule_tac x=x in lt_length_in_nat, assumption)  
apply (frule_tac x=y in lt_length_in_nat, assumption)  
apply (simp add: satisfies_is_b_fm_def satisfies_is_b_def sats_lambda_fm 
                 sats_bool_of_o_fm)
done

lemma satisfies_is_b_iff_sats:
  "\<lbrakk>nth(u,env) = nu; nth(x,env) = nx; nth(y,env) = ny; nth(z,env) = nz;
      u \<in> nat; x < length(env); y < length(env); z \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> satisfies_is_b(##A,nu,nx,ny,nz) \<longleftrightarrow>
       sats(A, satisfies_is_b_fm(u,x,y,z), env)"
by simp

theorem satisfies_is_b_reflection:
     "REFLECTS[\<lambda>x. satisfies_is_b(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. satisfies_is_b(##Lset(i),f(x),g(x),h(x),g'(x))]"
  unfolding satisfies_is_b_def 
apply (intro FOL_reflections is_lambda_reflection bool_of_o_reflection 
             nth_reflection is_list_reflection)
done


subsubsection\<open>The Operator \<^term>\<open>satisfies_is_c\<close>, Internalized\<close>

(* satisfies_is_c(M,A,h) \<equiv> 
    \<lambda>p q zz. \<forall>lA[M]. is_list(M,A,lA) \<longrightarrow>
             is_lambda(M, lA, \<lambda>env z. \<exists>hp[M]. \<exists>hq[M]. 
                 (\<exists>rp[M]. is_depth_apply(M,h,p,rp) \<and> fun_apply(M,rp,env,hp)) \<and> 
                 (\<exists>rq[M]. is_depth_apply(M,h,q,rq) \<and> fun_apply(M,rq,env,hq)) \<and> 
                 (\<exists>pq[M]. is_and(M,hp,hq,pq) \<and> is_not(M,pq,z)),
                zz) *)

definition
  satisfies_is_c_fm :: "[i,i,i,i,i]\<Rightarrow>i" where
 "satisfies_is_c_fm(A,h,p,q,zz) \<equiv>
   Forall(
     Implies(is_list_fm(succ(A),0),
       lambda_fm(
         Exists(Exists(
          And(Exists(And(depth_apply_fm(h#+7,p#+7,0), fun_apply_fm(0,4,2))),
          And(Exists(And(depth_apply_fm(h#+7,q#+7,0), fun_apply_fm(0,4,1))),
              Exists(And(and_fm(2,1,0), not_fm(0,3))))))),
         0, succ(zz))))"

lemma satisfies_is_c_type [TC]:
     "\<lbrakk>A \<in> nat; h \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat\<rbrakk>
      \<Longrightarrow> satisfies_is_c_fm(A,h,x,y,z) \<in> formula"
by (simp add: satisfies_is_c_fm_def)

lemma sats_satisfies_is_c_fm [simp]:
   "\<lbrakk>u \<in> nat; v \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, satisfies_is_c_fm(u,v,x,y,z), env) \<longleftrightarrow>
        satisfies_is_c(##A, nth(u,env), nth(v,env), nth(x,env), 
                            nth(y,env), nth(z,env))"  
by (simp add: satisfies_is_c_fm_def satisfies_is_c_def sats_lambda_fm)

lemma satisfies_is_c_iff_sats:
  "\<lbrakk>nth(u,env) = nu; nth(v,env) = nv; nth(x,env) = nx; nth(y,env) = ny; 
      nth(z,env) = nz;
      u \<in> nat; v \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> satisfies_is_c(##A,nu,nv,nx,ny,nz) \<longleftrightarrow>
       sats(A, satisfies_is_c_fm(u,v,x,y,z), env)"
by simp

theorem satisfies_is_c_reflection:
     "REFLECTS[\<lambda>x. satisfies_is_c(L,f(x),g(x),h(x),g'(x),h'(x)),
               \<lambda>i x. satisfies_is_c(##Lset(i),f(x),g(x),h(x),g'(x),h'(x))]"
  unfolding satisfies_is_c_def 
apply (intro FOL_reflections function_reflections is_lambda_reflection
             extra_reflections nth_reflection depth_apply_reflection 
             is_list_reflection)
done

subsubsection\<open>The Operator \<^term>\<open>satisfies_is_d\<close>, Internalized\<close>

(* satisfies_is_d(M,A,h) \<equiv> 
    \<lambda>p zz. \<forall>lA[M]. is_list(M,A,lA) \<longrightarrow>
             is_lambda(M, lA, 
                \<lambda>env z. \<exists>rp[M]. is_depth_apply(M,h,p,rp) \<and> 
                    is_bool_of_o(M, 
                           \<forall>x[M]. \<forall>xenv[M]. \<forall>hp[M]. 
                              x\<in>A \<longrightarrow> is_Cons(M,x,env,xenv) \<longrightarrow> 
                              fun_apply(M,rp,xenv,hp) \<longrightarrow> number1(M,hp),
                  z),
               zz) *)

definition
  satisfies_is_d_fm :: "[i,i,i,i]\<Rightarrow>i" where
 "satisfies_is_d_fm(A,h,p,zz) \<equiv>
   Forall(
     Implies(is_list_fm(succ(A),0),
       lambda_fm(
         Exists(
           And(depth_apply_fm(h#+5,p#+5,0),
               bool_of_o_fm(
                Forall(Forall(Forall(
                 Implies(Member(2,A#+8),
                  Implies(Cons_fm(2,5,1),
                   Implies(fun_apply_fm(3,1,0), number1_fm(0))))))), 1))),
         0, succ(zz))))"

lemma satisfies_is_d_type [TC]:
     "\<lbrakk>A \<in> nat; h \<in> nat; x \<in> nat; z \<in> nat\<rbrakk>
      \<Longrightarrow> satisfies_is_d_fm(A,h,x,z) \<in> formula"
by (simp add: satisfies_is_d_fm_def)

lemma sats_satisfies_is_d_fm [simp]:
   "\<lbrakk>u \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, satisfies_is_d_fm(u,x,y,z), env) \<longleftrightarrow>
        satisfies_is_d(##A, nth(u,env), nth(x,env), nth(y,env), nth(z,env))"  
by (simp add: satisfies_is_d_fm_def satisfies_is_d_def sats_lambda_fm
              sats_bool_of_o_fm)

lemma satisfies_is_d_iff_sats:
  "\<lbrakk>nth(u,env) = nu; nth(x,env) = nx; nth(y,env) = ny; nth(z,env) = nz;
      u \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> satisfies_is_d(##A,nu,nx,ny,nz) \<longleftrightarrow>
       sats(A, satisfies_is_d_fm(u,x,y,z), env)"
by simp

theorem satisfies_is_d_reflection:
     "REFLECTS[\<lambda>x. satisfies_is_d(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. satisfies_is_d(##Lset(i),f(x),g(x),h(x),g'(x))]"
  unfolding satisfies_is_d_def 
apply (intro FOL_reflections function_reflections is_lambda_reflection
             extra_reflections nth_reflection depth_apply_reflection 
             is_list_reflection)
done


subsubsection\<open>The Operator \<^term>\<open>satisfies_MH\<close>, Internalized\<close>

(* satisfies_MH \<equiv> 
    \<lambda>M A u f zz. 
         \<forall>fml[M]. is_formula(M,fml) \<longrightarrow>
             is_lambda (M, fml, 
               is_formula_case (M, satisfies_is_a(M,A), 
                                satisfies_is_b(M,A), 
                                satisfies_is_c(M,A,f), satisfies_is_d(M,A,f)),
               zz) *)

definition
  satisfies_MH_fm :: "[i,i,i,i]\<Rightarrow>i" where
 "satisfies_MH_fm(A,u,f,zz) \<equiv>
   Forall(
     Implies(is_formula_fm(0),
       lambda_fm(
         formula_case_fm(satisfies_is_a_fm(A#+7,2,1,0), 
                         satisfies_is_b_fm(A#+7,2,1,0), 
                         satisfies_is_c_fm(A#+7,f#+7,2,1,0), 
                         satisfies_is_d_fm(A#+6,f#+6,1,0), 
                         1, 0),
         0, succ(zz))))"

lemma satisfies_MH_type [TC]:
     "\<lbrakk>A \<in> nat; u \<in> nat; x \<in> nat; z \<in> nat\<rbrakk>
      \<Longrightarrow> satisfies_MH_fm(A,u,x,z) \<in> formula"
by (simp add: satisfies_MH_fm_def)

lemma sats_satisfies_MH_fm [simp]:
   "\<lbrakk>u \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
    \<Longrightarrow> sats(A, satisfies_MH_fm(u,x,y,z), env) \<longleftrightarrow>
        satisfies_MH(##A, nth(u,env), nth(x,env), nth(y,env), nth(z,env))"  
by (simp add: satisfies_MH_fm_def satisfies_MH_def sats_lambda_fm
              sats_formula_case_fm)

lemma satisfies_MH_iff_sats:
  "\<lbrakk>nth(u,env) = nu; nth(x,env) = nx; nth(y,env) = ny; nth(z,env) = nz;
      u \<in> nat; x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)\<rbrakk>
   \<Longrightarrow> satisfies_MH(##A,nu,nx,ny,nz) \<longleftrightarrow>
       sats(A, satisfies_MH_fm(u,x,y,z), env)"
by simp 

lemmas satisfies_reflections =
       is_lambda_reflection is_formula_reflection 
       is_formula_case_reflection
       satisfies_is_a_reflection satisfies_is_b_reflection 
       satisfies_is_c_reflection satisfies_is_d_reflection

theorem satisfies_MH_reflection:
     "REFLECTS[\<lambda>x. satisfies_MH(L,f(x),g(x),h(x),g'(x)),
               \<lambda>i x. satisfies_MH(##Lset(i),f(x),g(x),h(x),g'(x))]"
  unfolding satisfies_MH_def 
apply (intro FOL_reflections satisfies_reflections)
done


subsection\<open>Lemmas for Instantiating the Locale \<open>M_satisfies\<close>\<close>


subsubsection\<open>The \<^term>\<open>Member\<close> Case\<close>

lemma Member_Reflects:
 "REFLECTS[\<lambda>u. \<exists>v[L]. v \<in> B \<and> (\<exists>bo[L]. \<exists>nx[L]. \<exists>ny[L].
          v \<in> lstA \<and> is_nth(L,x,v,nx) \<and> is_nth(L,y,v,ny) \<and>
          is_bool_of_o(L, nx \<in> ny, bo) \<and> pair(L,v,bo,u)),
   \<lambda>i u. \<exists>v \<in> Lset(i). v \<in> B \<and> (\<exists>bo \<in> Lset(i). \<exists>nx \<in> Lset(i). \<exists>ny \<in> Lset(i).
             v \<in> lstA \<and> is_nth(##Lset(i), x, v, nx) \<and> 
             is_nth(##Lset(i), y, v, ny) \<and>
          is_bool_of_o(##Lset(i), nx \<in> ny, bo) \<and> pair(##Lset(i), v, bo, u))]"
by (intro FOL_reflections function_reflections nth_reflection 
          bool_of_o_reflection)


lemma Member_replacement:
    "\<lbrakk>L(A); x \<in> nat; y \<in> nat\<rbrakk>
     \<Longrightarrow> strong_replacement
         (L, \<lambda>env z. \<exists>bo[L]. \<exists>nx[L]. \<exists>ny[L]. 
              env \<in> list(A) \<and> is_nth(L,x,env,nx) \<and> is_nth(L,y,env,ny) \<and> 
              is_bool_of_o(L, nx \<in> ny, bo) \<and>
              pair(L, env, bo, z))"
apply (rule strong_replacementI)
apply (rule_tac u="{list(A),B,x,y}" 
         in gen_separation_multi [OF Member_Reflects], 
       auto)
apply (rule_tac env="[list(A),B,x,y]" in DPow_LsetI)
apply (rule sep_rules nth_iff_sats is_bool_of_o_iff_sats | simp)+
done


subsubsection\<open>The \<^term>\<open>Equal\<close> Case\<close>

lemma Equal_Reflects:
 "REFLECTS[\<lambda>u. \<exists>v[L]. v \<in> B \<and> (\<exists>bo[L]. \<exists>nx[L]. \<exists>ny[L].
          v \<in> lstA \<and> is_nth(L, x, v, nx) \<and> is_nth(L, y, v, ny) \<and>
          is_bool_of_o(L, nx = ny, bo) \<and> pair(L, v, bo, u)),
   \<lambda>i u. \<exists>v \<in> Lset(i). v \<in> B \<and> (\<exists>bo \<in> Lset(i). \<exists>nx \<in> Lset(i). \<exists>ny \<in> Lset(i).
             v \<in> lstA \<and> is_nth(##Lset(i), x, v, nx) \<and> 
             is_nth(##Lset(i), y, v, ny) \<and>
          is_bool_of_o(##Lset(i), nx = ny, bo) \<and> pair(##Lset(i), v, bo, u))]"
by (intro FOL_reflections function_reflections nth_reflection 
          bool_of_o_reflection)


lemma Equal_replacement:
    "\<lbrakk>L(A); x \<in> nat; y \<in> nat\<rbrakk>
     \<Longrightarrow> strong_replacement
         (L, \<lambda>env z. \<exists>bo[L]. \<exists>nx[L]. \<exists>ny[L]. 
              env \<in> list(A) \<and> is_nth(L,x,env,nx) \<and> is_nth(L,y,env,ny) \<and> 
              is_bool_of_o(L, nx = ny, bo) \<and>
              pair(L, env, bo, z))"
apply (rule strong_replacementI)
apply (rule_tac u="{list(A),B,x,y}" 
         in gen_separation_multi [OF Equal_Reflects], 
       auto)
apply (rule_tac env="[list(A),B,x,y]" in DPow_LsetI)
apply (rule sep_rules nth_iff_sats is_bool_of_o_iff_sats | simp)+
done

subsubsection\<open>The \<^term>\<open>Nand\<close> Case\<close>

lemma Nand_Reflects:
    "REFLECTS [\<lambda>x. \<exists>u[L]. u \<in> B \<and>
               (\<exists>rpe[L]. \<exists>rqe[L]. \<exists>andpq[L]. \<exists>notpq[L].
                 fun_apply(L, rp, u, rpe) \<and> fun_apply(L, rq, u, rqe) \<and>
                 is_and(L, rpe, rqe, andpq) \<and> is_not(L, andpq, notpq) \<and>
                 u \<in> list(A) \<and> pair(L, u, notpq, x)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and>
     (\<exists>rpe \<in> Lset(i). \<exists>rqe \<in> Lset(i). \<exists>andpq \<in> Lset(i). \<exists>notpq \<in> Lset(i).
       fun_apply(##Lset(i), rp, u, rpe) \<and> fun_apply(##Lset(i), rq, u, rqe) \<and>
       is_and(##Lset(i), rpe, rqe, andpq) \<and> is_not(##Lset(i), andpq, notpq) \<and>
       u \<in> list(A) \<and> pair(##Lset(i), u, notpq, x))]"
  unfolding is_and_def is_not_def 
apply (intro FOL_reflections function_reflections)
done

lemma Nand_replacement:
    "\<lbrakk>L(A); L(rp); L(rq)\<rbrakk>
     \<Longrightarrow> strong_replacement
         (L, \<lambda>env z. \<exists>rpe[L]. \<exists>rqe[L]. \<exists>andpq[L]. \<exists>notpq[L]. 
               fun_apply(L,rp,env,rpe) \<and> fun_apply(L,rq,env,rqe) \<and> 
               is_and(L,rpe,rqe,andpq) \<and> is_not(L,andpq,notpq) \<and> 
               env \<in> list(A) \<and> pair(L, env, notpq, z))"
apply (rule strong_replacementI)
apply (rule_tac u="{list(A),B,rp,rq}" 
         in gen_separation_multi [OF Nand_Reflects],
       auto)
apply (rule_tac env="[list(A),B,rp,rq]" in DPow_LsetI)
apply (rule sep_rules is_and_iff_sats is_not_iff_sats | simp)+
done


subsubsection\<open>The \<^term>\<open>Forall\<close> Case\<close>

lemma Forall_Reflects:
 "REFLECTS [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>bo[L]. u \<in> list(A) \<and>
                 is_bool_of_o (L,
     \<forall>a[L]. \<forall>co[L]. \<forall>rpco[L]. a \<in> A \<longrightarrow>
                is_Cons(L,a,u,co) \<longrightarrow> fun_apply(L,rp,co,rpco) \<longrightarrow> 
                number1(L,rpco),
                           bo) \<and> pair(L,u,bo,x)),
 \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>bo \<in> Lset(i). u \<in> list(A) \<and>
        is_bool_of_o (##Lset(i),
 \<forall>a \<in> Lset(i). \<forall>co \<in> Lset(i). \<forall>rpco \<in> Lset(i). a \<in> A \<longrightarrow>
            is_Cons(##Lset(i),a,u,co) \<longrightarrow> fun_apply(##Lset(i),rp,co,rpco) \<longrightarrow> 
            number1(##Lset(i),rpco),
                       bo) \<and> pair(##Lset(i),u,bo,x))]"
  unfolding is_bool_of_o_def 
apply (intro FOL_reflections function_reflections Cons_reflection)
done

lemma Forall_replacement:
   "\<lbrakk>L(A); L(rp)\<rbrakk>
    \<Longrightarrow> strong_replacement
        (L, \<lambda>env z. \<exists>bo[L]. 
              env \<in> list(A) \<and> 
              is_bool_of_o (L, 
                            \<forall>a[L]. \<forall>co[L]. \<forall>rpco[L]. 
                               a\<in>A \<longrightarrow> is_Cons(L,a,env,co) \<longrightarrow>
                               fun_apply(L,rp,co,rpco) \<longrightarrow> number1(L, rpco), 
                            bo) \<and>
              pair(L,env,bo,z))"
apply (rule strong_replacementI)
apply (rule_tac u="{A,list(A),B,rp}" 
         in gen_separation_multi [OF Forall_Reflects],
       auto)
apply (rule_tac env="[A,list(A),B,rp]" in DPow_LsetI)
apply (rule sep_rules is_bool_of_o_iff_sats Cons_iff_sats | simp)+
done

subsubsection\<open>The \<^term>\<open>transrec_replacement\<close> Case\<close>

lemma formula_rec_replacement_Reflects:
 "REFLECTS [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>y[L]. pair(L, u, y, x) \<and>
             is_wfrec (L, satisfies_MH(L,A), mesa, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>y \<in> Lset(i). pair(##Lset(i), u, y, x) \<and>
             is_wfrec (##Lset(i), satisfies_MH(##Lset(i),A), mesa, u, y))]"
by (intro FOL_reflections function_reflections satisfies_MH_reflection 
          is_wfrec_reflection) 

lemma formula_rec_replacement: 
      \<comment> \<open>For the \<^term>\<open>transrec\<close>\<close>
   "\<lbrakk>n \<in> nat; L(A)\<rbrakk> \<Longrightarrow> transrec_replacement(L, satisfies_MH(L,A), n)"
apply (rule L.transrec_replacementI, simp add: L.nat_into_M)
apply (rule strong_replacementI)
apply (rule_tac u="{B,A,n,Memrel(eclose({n}))}"
         in gen_separation_multi [OF formula_rec_replacement_Reflects],
       auto simp add: L.nat_into_M)
apply (rule_tac env="[B,A,n,Memrel(eclose({n}))]" in DPow_LsetI)
apply (rule sep_rules satisfies_MH_iff_sats is_wfrec_iff_sats | simp)+
done


subsubsection\<open>The Lambda Replacement Case\<close>

lemma formula_rec_lambda_replacement_Reflects:
 "REFLECTS [\<lambda>x. \<exists>u[L]. u \<in> B \<and>
     mem_formula(L,u) \<and>
     (\<exists>c[L].
         is_formula_case
          (L, satisfies_is_a(L,A), satisfies_is_b(L,A),
           satisfies_is_c(L,A,g), satisfies_is_d(L,A,g),
           u, c) \<and>
         pair(L,u,c,x)),
  \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> mem_formula(##Lset(i),u) \<and>
     (\<exists>c \<in> Lset(i).
         is_formula_case
          (##Lset(i), satisfies_is_a(##Lset(i),A), satisfies_is_b(##Lset(i),A),
           satisfies_is_c(##Lset(i),A,g), satisfies_is_d(##Lset(i),A,g),
           u, c) \<and>
         pair(##Lset(i),u,c,x))]"
by (intro FOL_reflections function_reflections mem_formula_reflection
          is_formula_case_reflection satisfies_is_a_reflection
          satisfies_is_b_reflection satisfies_is_c_reflection
          satisfies_is_d_reflection)  

lemma formula_rec_lambda_replacement: 
      \<comment> \<open>For the \<^term>\<open>transrec\<close>\<close>
   "\<lbrakk>L(g); L(A)\<rbrakk> \<Longrightarrow>
    strong_replacement (L, 
       \<lambda>x y. mem_formula(L,x) \<and>
             (\<exists>c[L]. is_formula_case(L, satisfies_is_a(L,A),
                                  satisfies_is_b(L,A),
                                  satisfies_is_c(L,A,g),
                                  satisfies_is_d(L,A,g), x, c) \<and>
             pair(L, x, c, y)))" 
apply (rule strong_replacementI)
apply (rule_tac u="{B,A,g}"
         in gen_separation_multi [OF formula_rec_lambda_replacement_Reflects], 
       auto)
apply (rule_tac env="[A,g,B]" in DPow_LsetI)
apply (rule sep_rules mem_formula_iff_sats
          formula_case_iff_sats satisfies_is_a_iff_sats
          satisfies_is_b_iff_sats satisfies_is_c_iff_sats
          satisfies_is_d_iff_sats | simp)+
done


subsection\<open>Instantiating \<open>M_satisfies\<close>\<close>

lemma M_satisfies_axioms_L: "M_satisfies_axioms(L)"
  apply (rule M_satisfies_axioms.intro)
       apply (assumption | rule
         Member_replacement Equal_replacement 
         Nand_replacement Forall_replacement
         formula_rec_replacement formula_rec_lambda_replacement)+
  done

theorem M_satisfies_L: "M_satisfies(L)"
  apply (rule M_satisfies.intro)
   apply (rule M_eclose_L)
  apply (rule M_satisfies_axioms_L)
  done

text\<open>Finally: the point of the whole theory!\<close>
lemmas satisfies_closed = M_satisfies.satisfies_closed [OF M_satisfies_L]
   and satisfies_abs = M_satisfies.satisfies_abs [OF M_satisfies_L]

end
