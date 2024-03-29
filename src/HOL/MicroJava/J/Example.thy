(*  Title:      HOL/MicroJava/J/Example.thy
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>Example MicroJava Program\<close>

theory Example imports SystemClasses Eval begin

text \<open>
The following example MicroJava program includes:
 class declarations with inheritance, hiding of fields, and overriding of
  methods (with refined result type), 
 instance creation, local assignment, sequential composition,
 method call with dynamic binding, literal values,
 expression statement, local access, type cast, field assignment (in part), 
 skip.

\begin{verbatim}
class Base {
  boolean vee;
  Base foo(Base x) {return x;}
}

class Ext extends Base {
  int vee;
  Ext foo(Base x) {((Ext)x).vee=1; return null;}
}

class Example {
  public static void main (String args[]) {
    Base e=new Ext();
    e.foo(null);
  }
}
\end{verbatim}
\<close>

datatype cnam' = Base' | Ext'
datatype vnam' = vee' | x' | e'

text \<open>
  \<open>cnam'\<close> and \<open>vnam'\<close> are intended to be isomorphic 
  to \<open>cnam\<close> and \<open>vnam\<close>
\<close>

axiomatization cnam' :: "cnam' => cname"
where
  inj_cnam':  "(cnam' x = cnam' y) = (x = y)" and
  surj_cnam': "\<exists>m. n = cnam' m"

axiomatization vnam' :: "vnam' => vnam"
where
  inj_vnam':  "(vnam' x = vnam' y) = (x = y)" and
  surj_vnam': "\<exists>m. n = vnam' m"

declare inj_cnam' [simp] inj_vnam' [simp]

abbreviation Base :: cname
  where "Base == cnam' Base'"
abbreviation Ext :: cname
  where "Ext == cnam' Ext'"
abbreviation vee :: vname
  where "vee == VName (vnam' vee')"
abbreviation x :: vname
  where "x == VName (vnam' x')"
abbreviation e :: vname
  where "e == VName (vnam' e')"

axiomatization where
  Base_not_Object: "Base \<noteq> Object" and
  Ext_not_Object:  "Ext  \<noteq> Object" and
  Base_not_Xcpt:   "Base \<noteq> Xcpt z" and
  Ext_not_Xcpt:    "Ext  \<noteq> Xcpt z" and
  e_not_This:      "e \<noteq> This"  

declare Base_not_Object [simp] Ext_not_Object [simp]
declare Base_not_Xcpt [simp] Ext_not_Xcpt [simp]
declare e_not_This [simp]
declare Base_not_Object [symmetric, simp]
declare Ext_not_Object  [symmetric, simp]
declare Base_not_Xcpt [symmetric, simp]
declare Ext_not_Xcpt  [symmetric, simp]

definition foo_Base :: java_mb
  where "foo_Base == ([x],[],Skip,LAcc x)"

definition foo_Ext :: java_mb
  where "foo_Ext == ([x],[],Expr( {Ext}Cast Ext
               (LAcc x)..vee:=Lit (Intg Numeral1)),
           Lit Null)"

consts foo ::  mname

definition BaseC :: "java_mb cdecl"
  where "BaseC == (Base, (Object, 
           [(vee, PrimT Boolean)], 
           [((foo,[Class Base]),Class Base,foo_Base)]))"

definition ExtC :: "java_mb cdecl"
  where "ExtC  == (Ext,  (Base  ,
           [(vee, PrimT Integer)], 
           [((foo,[Class Base]),Class Ext,foo_Ext)]))"

definition test ::  stmt
  where "test == Expr(e::=NewC Ext);;
                    Expr({Base}LAcc e..foo({[Class Base]}[Lit Null]))"

consts
  a :: loc
  b :: loc

abbreviation
  NP  :: xcpt where
  "NP == NullPointer"

abbreviation
  tprg  ::"java_mb prog" where
  "tprg == [ObjectC, BaseC, ExtC, ClassCastC, NullPointerC, OutOfMemoryC]"

abbreviation
  obj1  :: obj where
  "obj1 == (Ext, Map.empty((vee, Base)\<mapsto>Bool False, (vee, Ext )\<mapsto>Intg 0))"

abbreviation "s0 == Norm    (Map.empty, Map.empty)"
abbreviation "s1 == Norm    (Map.empty(a\<mapsto>obj1),Map.empty(e\<mapsto>Addr a))"
abbreviation "s2 == Norm    (Map.empty(a\<mapsto>obj1),Map.empty(x\<mapsto>Null, This\<mapsto>Addr a))"
abbreviation "s3 == (Some NP, Map.empty(a\<mapsto>obj1),Map.empty(e\<mapsto>Addr a))"

lemmas map_of_Cons = map_of.simps(2)

lemma map_of_Cons1 [simp]: "map_of ((aa,bb)#ps) aa = Some bb"
apply (simp (no_asm))
done
lemma map_of_Cons2 [simp]: "aa\<noteq>k ==> map_of ((k,bb)#ps) aa = map_of ps aa"
apply (simp (no_asm_simp))
done
declare map_of_Cons [simp del] \<comment> \<open>sic!\<close>

lemma class_tprg_Object [simp]: "class tprg Object = Some (undefined, [], [])"
apply (unfold ObjectC_def class_def)
apply (simp (no_asm))
done

lemma class_tprg_NP [simp]: "class tprg (Xcpt NP) = Some (Object, [], [])"
apply (unfold ObjectC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def BaseC_def ExtC_def class_def)
apply (simp (no_asm))
done

lemma class_tprg_OM [simp]: "class tprg (Xcpt OutOfMemory) = Some (Object, [], [])"
apply (unfold ObjectC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def BaseC_def ExtC_def class_def)
apply (simp (no_asm))
done

lemma class_tprg_CC [simp]: "class tprg (Xcpt ClassCast) = Some (Object, [], [])"
apply (unfold ObjectC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def BaseC_def ExtC_def class_def)
apply (simp (no_asm))
done

lemma class_tprg_Base [simp]: 
"class tprg Base = Some (Object,  
    [(vee, PrimT Boolean)],  
          [((foo, [Class Base]), Class Base, foo_Base)])"
apply (unfold ObjectC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def BaseC_def ExtC_def class_def)
apply (simp (no_asm))
done

lemma class_tprg_Ext [simp]: 
"class tprg Ext = Some (Base,  
    [(vee, PrimT Integer)],  
          [((foo, [Class Base]), Class Ext, foo_Ext)])"
apply (unfold ObjectC_def BaseC_def ExtC_def class_def)
apply (simp (no_asm))
done

lemma not_Object_subcls [elim!]: "(Object, C) \<in> (subcls1 tprg)\<^sup>+ ==> R"
apply (auto dest!: tranclD subcls1D)
done

lemma subcls_ObjectD [dest!]: "tprg\<turnstile>Object\<preceq>C C ==> C = Object"
apply (erule rtrancl_induct)
apply  auto
apply (drule subcls1D)
apply auto
done

lemma not_Base_subcls_Ext [elim!]: "(Base, Ext) \<in> (subcls1 tprg)\<^sup>+  ==> R"
apply (auto dest!: tranclD subcls1D)
done

lemma class_tprgD: 
"class tprg C = Some z ==> C=Object \<or> C=Base \<or> C=Ext \<or> C=Xcpt NP \<or> C=Xcpt ClassCast \<or> C=Xcpt OutOfMemory"
apply (unfold ObjectC_def ClassCastC_def NullPointerC_def OutOfMemoryC_def BaseC_def ExtC_def class_def)
apply (auto split: if_split_asm simp add: map_of_Cons)
done

lemma not_class_subcls_class [elim!]: "(C, C) \<in> (subcls1 tprg)\<^sup>+ ==> R"
apply (auto dest!: tranclD subcls1D)
apply (frule class_tprgD)
apply (auto dest!:)
apply (drule rtranclD)
apply auto
done

lemma unique_classes: "unique tprg"
apply (simp (no_asm) add: ObjectC_def BaseC_def ExtC_def NullPointerC_def ClassCastC_def OutOfMemoryC_def)
done

lemmas subcls_direct = subcls1I [THEN r_into_rtrancl [where r="subcls1 G"]] for G

lemma Ext_subcls_Base [simp]: "tprg\<turnstile>Ext\<preceq>C Base"
apply (rule subcls_direct)
apply auto
done

lemma Ext_widen_Base [simp]: "tprg\<turnstile>Class Ext\<preceq> Class Base"
apply (rule widen.subcls)
apply (simp (no_asm))
done

declare ty_expr_ty_exprs_wt_stmt.intros [intro!]

lemma acyclic_subcls1': "acyclic (subcls1 tprg)"
apply (rule acyclicI)
apply safe
done

lemmas wf_subcls1' = acyclic_subcls1' [THEN finite_subcls1 [THEN finite_acyclic_wf_converse]]

lemmas fields_rec' = wf_subcls1' [THEN [2] fields_rec_lemma]

lemma fields_Object [simp]: "fields (tprg, Object) = []"
apply (subst fields_rec')
apply   auto
done

declare is_class_def [simp]

lemma fields_Base [simp]: "fields (tprg,Base) = [((vee, Base), PrimT Boolean)]"
apply (subst fields_rec')
apply   auto
done

lemma fields_Ext [simp]: 
  "fields (tprg, Ext)  = [((vee, Ext ), PrimT Integer)] @ fields (tprg, Base)"
apply (rule trans)
apply  (rule fields_rec')
apply   auto
done

lemmas method_rec' = wf_subcls1' [THEN [2] method_rec_lemma]

lemma method_Object [simp]: "method (tprg,Object) = map_of []"
apply (subst method_rec')
apply  auto
done

lemma method_Base [simp]: "method (tprg, Base) = map_of  
  [((foo, [Class Base]), Base, (Class Base, foo_Base))]"
apply (rule trans)
apply  (rule method_rec')
apply  auto
done

lemma method_Ext [simp]: "method (tprg, Ext) = (method (tprg, Base) ++ map_of  
  [((foo, [Class Base]), Ext , (Class Ext, foo_Ext))])"
apply (rule trans)
apply  (rule method_rec')
apply  auto
done

lemma wf_foo_Base: 
"wf_mdecl wf_java_mdecl tprg Base ((foo, [Class Base]), (Class Base, foo_Base))"
apply (unfold wf_mdecl_def wf_mhead_def wf_java_mdecl_def foo_Base_def)
apply auto
done

lemma wf_foo_Ext: 
"wf_mdecl wf_java_mdecl tprg Ext ((foo, [Class Base]), (Class Ext, foo_Ext))"
apply (unfold wf_mdecl_def wf_mhead_def wf_java_mdecl_def foo_Ext_def)
apply auto
apply  (rule ty_expr_ty_exprs_wt_stmt.Cast)
prefer 2
apply   (simp)
apply   (rule_tac [2] cast.subcls)
apply   (unfold field_def)
apply   auto
done

lemma wf_ObjectC: 
"ws_cdecl tprg ObjectC \<and> 
  wf_cdecl_mdecl wf_java_mdecl tprg ObjectC \<and> wf_mrT tprg ObjectC"
apply (unfold ws_cdecl_def wf_cdecl_mdecl_def 
  wf_mrT_def wf_fdecl_def ObjectC_def)
apply (simp (no_asm))
done

lemma wf_NP:
"ws_cdecl tprg NullPointerC \<and>
  wf_cdecl_mdecl wf_java_mdecl tprg NullPointerC \<and> wf_mrT tprg NullPointerC"
apply (unfold ws_cdecl_def wf_cdecl_mdecl_def 
  wf_mrT_def wf_fdecl_def NullPointerC_def)
apply (simp add: class_def)
apply (fold NullPointerC_def class_def)
apply auto
done

lemma wf_OM:
"ws_cdecl tprg OutOfMemoryC \<and>
  wf_cdecl_mdecl wf_java_mdecl tprg OutOfMemoryC \<and> wf_mrT tprg OutOfMemoryC"
apply (unfold ws_cdecl_def wf_cdecl_mdecl_def 
  wf_mrT_def wf_fdecl_def OutOfMemoryC_def)
apply (simp add: class_def)
apply (fold OutOfMemoryC_def class_def)
apply auto
done

lemma wf_CC:
"ws_cdecl tprg ClassCastC \<and>
  wf_cdecl_mdecl wf_java_mdecl tprg ClassCastC \<and> wf_mrT tprg ClassCastC"
apply (unfold ws_cdecl_def wf_cdecl_mdecl_def 
  wf_mrT_def wf_fdecl_def ClassCastC_def)
apply (simp add: class_def)
apply (fold ClassCastC_def class_def)
apply auto
done

lemma wf_BaseC: 
"ws_cdecl tprg BaseC \<and>
  wf_cdecl_mdecl wf_java_mdecl tprg BaseC \<and> wf_mrT tprg BaseC"
apply (unfold ws_cdecl_def wf_cdecl_mdecl_def
  wf_mrT_def wf_fdecl_def BaseC_def)
apply (simp (no_asm))
apply (fold BaseC_def)
apply (rule mp) defer apply (rule wf_foo_Base)
apply (auto simp add: wf_mdecl_def)
done


lemma wf_ExtC: 
"ws_cdecl tprg ExtC \<and>
  wf_cdecl_mdecl wf_java_mdecl tprg ExtC \<and> wf_mrT tprg ExtC"
apply (unfold ws_cdecl_def wf_cdecl_mdecl_def
  wf_mrT_def wf_fdecl_def ExtC_def)
apply (simp (no_asm))
apply (fold ExtC_def)
apply (rule mp) defer apply (rule wf_foo_Ext)
apply (auto simp add: wf_mdecl_def)
apply (drule rtranclD)
apply auto
done


lemma [simp]: "fst ObjectC = Object" by (simp add: ObjectC_def)

lemma wf_tprg: 
"wf_prog wf_java_mdecl tprg"
apply (unfold wf_prog_def ws_prog_def Let_def)
apply (simp add: wf_ObjectC wf_BaseC wf_ExtC wf_NP wf_OM wf_CC unique_classes)
apply (rule wf_syscls)
apply (simp add: SystemClasses_def)
done

lemma appl_methds_foo_Base: 
"appl_methds tprg Base (foo, [NT]) =  
  {((Class Base, Class Base), [Class Base])}"
apply (unfold appl_methds_def)
apply (simp (no_asm))
done

lemma max_spec_foo_Base: "max_spec tprg Base (foo, [NT]) =  
  {((Class Base, Class Base), [Class Base])}"
apply (unfold max_spec_def)
apply (auto simp add: appl_methds_foo_Base)
done

lemmas t = ty_expr_ty_exprs_wt_stmt.intros
schematic_goal wt_test: "(tprg, Map.empty(e\<mapsto>Class Base))\<turnstile>  
  Expr(e::=NewC Ext);; Expr({Base}LAcc e..foo({?pTs'}[Lit Null]))\<surd>"
apply (rule ty_expr_ty_exprs_wt_stmt.intros) \<comment> \<open>;;\<close>
apply  (rule t) \<comment> \<open>Expr\<close>
apply  (rule t) \<comment> \<open>LAss\<close>
apply    simp \<comment> \<open>\<open>e \<noteq> This\<close>\<close>
apply    (rule t) \<comment> \<open>LAcc\<close>
apply     (simp (no_asm))
apply    (simp (no_asm))
apply   (rule t) \<comment> \<open>NewC\<close>
apply   (simp (no_asm))
apply  (simp (no_asm))
apply (rule t) \<comment> \<open>Expr\<close>
apply (rule t) \<comment> \<open>Call\<close>
apply   (rule t) \<comment> \<open>LAcc\<close>
apply    (simp (no_asm))
apply   (simp (no_asm))
apply  (rule t) \<comment> \<open>Cons\<close>
apply   (rule t) \<comment> \<open>Lit\<close>
apply   (simp (no_asm))
apply  (rule t) \<comment> \<open>Nil\<close>
apply (simp (no_asm))
apply (rule max_spec_foo_Base)
done


lemmas e = NewCI eval_evals_exec.intros
declare if_split [split del]
declare init_vars_def [simp] c_hupd_def [simp] cast_ok_def [simp]
schematic_goal exec_test: 
" [|new_Addr (heap (snd s0)) = (a, None)|] ==>  
  tprg\<turnstile>s0 -test-> ?s"
apply (unfold test_def)
\<comment> \<open>?s = s3\<close>
apply (rule e) \<comment> \<open>;;\<close>
apply  (rule e) \<comment> \<open>Expr\<close>
apply  (rule e) \<comment> \<open>LAss\<close>
apply   (rule e) \<comment> \<open>NewC\<close>
apply    force
apply   force
apply  (simp (no_asm))
apply (erule thin_rl)
apply (rule e) \<comment> \<open>Expr\<close>
apply (rule e) \<comment> \<open>Call\<close>
apply       (rule e) \<comment> \<open>LAcc\<close>
apply      force
apply     (rule e) \<comment> \<open>Cons\<close>
apply      (rule e) \<comment> \<open>Lit\<close>
apply     (rule e) \<comment> \<open>Nil\<close>
apply    (simp (no_asm))
apply   (force simp add: foo_Ext_def)
apply  (simp (no_asm))
apply  (rule e) \<comment> \<open>Expr\<close>
apply  (rule e) \<comment> \<open>FAss\<close>
apply       (rule e) \<comment> \<open>Cast\<close>
apply        (rule e) \<comment> \<open>LAcc\<close>
apply       (simp (no_asm))
apply      (simp (no_asm))
apply     (simp (no_asm))
apply     (rule e) \<comment> \<open>XcptE\<close>
apply    (simp (no_asm))
apply   (rule surjective_pairing [symmetric, THEN[2]trans], subst prod.inject, force)
apply  (simp (no_asm))
apply (simp (no_asm))
apply (rule e) \<comment> \<open>XcptE\<close>
done

end
