(*  Title:      HOL/Bali/Evaln.thy
    ID:         $Id$
    Author:     David von Oheimb and Norbert Schirmer
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)
header {* Operational evaluation (big-step) semantics of Java expressions and 
          statements
*}

theory Evaln = TypeSafe:


text {*
Variant of @{term eval} relation with counter for bounded recursive depth. 
In principal @{term evaln} could replace @{term eval}.

Validity of the axiomatic semantics builds on @{term evaln}. 
For recursive method calls the axiomatic semantics rule assumes the method ok 
to derive a proof for the body. To prove the method rule sound we need to 
perform induction on the recursion depth. 
For the completeness proof of the axiomatic semantics the notion of the most
general formula is used. The most general formula right now builds on the 
ordinary evaluation relation @{term eval}. 
So sometimes we have to switch between @{term evaln} and @{term eval} and vice 
versa. To make
this switch easy @{term evaln} also does all the technical accessibility tests 
@{term check_field_access} and @{term check_method_access} like @{term eval}. 
If it would omit them @{term evaln} and @{term eval} would only be equivalent 
for welltyped, and definitely assigned terms.
*}

consts

  evaln	:: "prog \<Rightarrow> (state \<times> term \<times> nat \<times> vals \<times> state) set"

syntax

  evaln	:: "[prog, state, term,        nat, vals * state] => bool"
				("_|-_ -_>-_-> _"   [61,61,80,   61,61] 60)
  evarn	:: "[prog, state, var  , vvar        , nat, state] => bool"
				("_|-_ -_=>_-_-> _" [61,61,90,61,61,61] 60)
  eval_n:: "[prog, state, expr , val         , nat, state] => bool"
				("_|-_ -_->_-_-> _" [61,61,80,61,61,61] 60)
  evalsn:: "[prog, state, expr list, val list, nat, state] => bool"
				("_|-_ -_#>_-_-> _" [61,61,61,61,61,61] 60)
  execn	:: "[prog, state, stmt ,               nat, state] => bool"
				("_|-_ -_-_-> _"    [61,61,65,   61,61] 60)

syntax (xsymbols)

  evaln	:: "[prog, state, term,         nat, vals \<times> state] \<Rightarrow> bool"
				("_\<turnstile>_ \<midarrow>_\<succ>\<midarrow>_\<rightarrow> _"   [61,61,80,   61,61] 60)
  evarn	:: "[prog, state, var  , vvar         , nat, state] \<Rightarrow> bool"
				("_\<turnstile>_ \<midarrow>_=\<succ>_\<midarrow>_\<rightarrow> _" [61,61,90,61,61,61] 60)
  eval_n:: "[prog, state, expr , val ,          nat, state] \<Rightarrow> bool"
				("_\<turnstile>_ \<midarrow>_-\<succ>_\<midarrow>_\<rightarrow> _" [61,61,80,61,61,61] 60)
  evalsn:: "[prog, state, expr list, val  list, nat, state] \<Rightarrow> bool"
				("_\<turnstile>_ \<midarrow>_\<doteq>\<succ>_\<midarrow>_\<rightarrow> _" [61,61,61,61,61,61] 60)
  execn	:: "[prog, state, stmt ,                nat, state] \<Rightarrow> bool"
				("_\<turnstile>_ \<midarrow>_\<midarrow>_\<rightarrow> _"     [61,61,65,   61,61] 60)

translations

  "G\<turnstile>s \<midarrow>t    \<succ>\<midarrow>n\<rightarrow>  w___s' " == "(s,t,n,w___s') \<in> evaln G"
  "G\<turnstile>s \<midarrow>t    \<succ>\<midarrow>n\<rightarrow> (w,  s')" <= "(s,t,n,w,  s') \<in> evaln G"
  "G\<turnstile>s \<midarrow>t    \<succ>\<midarrow>n\<rightarrow> (w,x,s')" <= "(s,t,n,w,x,s') \<in> evaln G"
  "G\<turnstile>s \<midarrow>c     \<midarrow>n\<rightarrow> (x,s')" <= "G\<turnstile>s \<midarrow>In1r  c\<succ>\<midarrow>n\<rightarrow> (\<diamondsuit>    ,x,s')"
  "G\<turnstile>s \<midarrow>c     \<midarrow>n\<rightarrow>    s' " == "G\<turnstile>s \<midarrow>In1r  c\<succ>\<midarrow>n\<rightarrow> (\<diamondsuit>    ,  s')"
  "G\<turnstile>s \<midarrow>e-\<succ>v  \<midarrow>n\<rightarrow> (x,s')" <= "G\<turnstile>s \<midarrow>In1l e\<succ>\<midarrow>n\<rightarrow> (In1 v ,x,s')"
  "G\<turnstile>s \<midarrow>e-\<succ>v  \<midarrow>n\<rightarrow>    s' " == "G\<turnstile>s \<midarrow>In1l e\<succ>\<midarrow>n\<rightarrow> (In1 v ,  s')"
  "G\<turnstile>s \<midarrow>e=\<succ>vf \<midarrow>n\<rightarrow> (x,s')" <= "G\<turnstile>s \<midarrow>In2  e\<succ>\<midarrow>n\<rightarrow> (In2 vf,x,s')"
  "G\<turnstile>s \<midarrow>e=\<succ>vf \<midarrow>n\<rightarrow>    s' " == "G\<turnstile>s \<midarrow>In2  e\<succ>\<midarrow>n\<rightarrow> (In2 vf,  s')"
  "G\<turnstile>s \<midarrow>e\<doteq>\<succ>v  \<midarrow>n\<rightarrow> (x,s')" <= "G\<turnstile>s \<midarrow>In3  e\<succ>\<midarrow>n\<rightarrow> (In3 v ,x,s')"
  "G\<turnstile>s \<midarrow>e\<doteq>\<succ>v  \<midarrow>n\<rightarrow>    s' " == "G\<turnstile>s \<midarrow>In3  e\<succ>\<midarrow>n\<rightarrow> (In3 v ,  s')"


inductive "evaln G" intros

--{* propagation of abrupt completion *}

  Abrupt:   "G\<turnstile>(Some xc,s) \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (arbitrary3 t,(Some xc,s))"


--{* evaluation of variables *}

  LVar:	"G\<turnstile>Norm s \<midarrow>LVar vn=\<succ>lvar vn s\<midarrow>n\<rightarrow> Norm s"

  FVar:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>Init statDeclC\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>e-\<succ>a\<midarrow>n\<rightarrow> s2;
	  (v,s2') = fvar statDeclC stat fn a s2;
          s3 = check_field_access G accC statDeclC fn stat a s2'\<rbrakk> \<Longrightarrow>
	  G\<turnstile>Norm s0 \<midarrow>{accC,statDeclC,stat}e..fn=\<succ>v\<midarrow>n\<rightarrow> s3"

  AVar:	"\<lbrakk>G\<turnstile> Norm s0 \<midarrow>e1-\<succ>a\<midarrow>n\<rightarrow> s1 ; G\<turnstile>s1 \<midarrow>e2-\<succ>i\<midarrow>n\<rightarrow> s2; 
	  (v,s2') = avar G i a s2\<rbrakk> \<Longrightarrow>
	              G\<turnstile>Norm s0 \<midarrow>e1.[e2]=\<succ>v\<midarrow>n\<rightarrow> s2'"




--{* evaluation of expressions *}

  NewC:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>Init C\<midarrow>n\<rightarrow> s1;
	  G\<turnstile>     s1 \<midarrow>halloc (CInst C)\<succ>a\<rightarrow> s2\<rbrakk> \<Longrightarrow>
	                          G\<turnstile>Norm s0 \<midarrow>NewC C-\<succ>Addr a\<midarrow>n\<rightarrow> s2"

  NewA:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>init_comp_ty T\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>e-\<succ>i'\<midarrow>n\<rightarrow> s2; 
	  G\<turnstile>abupd (check_neg i') s2 \<midarrow>halloc (Arr T (the_Intg i'))\<succ>a\<rightarrow> s3\<rbrakk> \<Longrightarrow>
	                        G\<turnstile>Norm s0 \<midarrow>New T[e]-\<succ>Addr a\<midarrow>n\<rightarrow> s3"

  Cast:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1;
	  s2 = abupd (raise_if (\<not>G,snd s1\<turnstile>v fits T) ClassCast) s1\<rbrakk> \<Longrightarrow>
			        G\<turnstile>Norm s0 \<midarrow>Cast T e-\<succ>v\<midarrow>n\<rightarrow> s2"

  Inst:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1;
	  b = (v\<noteq>Null \<and> G,store s1\<turnstile>v fits RefT T)\<rbrakk> \<Longrightarrow>
			      G\<turnstile>Norm s0 \<midarrow>e InstOf T-\<succ>Bool b\<midarrow>n\<rightarrow> s1"

  Lit:			   "G\<turnstile>Norm s \<midarrow>Lit v-\<succ>v\<midarrow>n\<rightarrow> Norm s"

  UnOp: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1\<rbrakk> 
         \<Longrightarrow> G\<turnstile>Norm s0 \<midarrow>UnOp unop e-\<succ>(eval_unop unop v)\<midarrow>n\<rightarrow> s1"

  BinOp: "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e1-\<succ>v1\<midarrow>n\<rightarrow> s1; 
           G\<turnstile>s1 \<midarrow>(if need_second_arg binop v1 then (In1l e2) else (In1r Skip))
            \<succ>\<midarrow>n\<rightarrow> (In1 v2,s2)\<rbrakk> 
         \<Longrightarrow> G\<turnstile>Norm s0 \<midarrow>BinOp binop e1 e2-\<succ>(eval_binop binop v1 v2)\<midarrow>n\<rightarrow> s2"

  Super:		   "G\<turnstile>Norm s \<midarrow>Super-\<succ>val_this s\<midarrow>n\<rightarrow> Norm s"

  Acc:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>va=\<succ>(v,f)\<midarrow>n\<rightarrow> s1\<rbrakk> \<Longrightarrow>
	                          G\<turnstile>Norm s0 \<midarrow>Acc va-\<succ>v\<midarrow>n\<rightarrow> s1"

  Ass:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>va=\<succ>(w,f)\<midarrow>n\<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>e-\<succ>v     \<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow>
				   G\<turnstile>Norm s0 \<midarrow>va:=e-\<succ>v\<midarrow>n\<rightarrow> assign f v s2"

  Cond:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e0-\<succ>b\<midarrow>n\<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow>
			    G\<turnstile>Norm s0 \<midarrow>e0 ? e1 : e2-\<succ>v\<midarrow>n\<rightarrow> s2"

  Call:	
  "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<midarrow>n\<rightarrow> s2;
    D = invocation_declclass G mode (store s2) a' statT \<lparr>name=mn,parTs=pTs\<rparr>; 
    s3=init_lvars G D \<lparr>name=mn,parTs=pTs\<rparr> mode a' vs s2;
    s3' = check_method_access G accC statT mode \<lparr>name=mn,parTs=pTs\<rparr> a' s3;
    G\<turnstile>s3'\<midarrow>Methd D \<lparr>name=mn,parTs=pTs\<rparr>-\<succ>v\<midarrow>n\<rightarrow> s4
   \<rbrakk>
   \<Longrightarrow> 
    G\<turnstile>Norm s0 \<midarrow>{accC,statT,mode}e\<cdot>mn({pTs}args)-\<succ>v\<midarrow>n\<rightarrow> (restore_lvars s2 s4)"

  Methd:"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>body G D sig-\<succ>v\<midarrow>n\<rightarrow> s1\<rbrakk> \<Longrightarrow>
				G\<turnstile>Norm s0 \<midarrow>Methd D sig-\<succ>v\<midarrow>Suc n\<rightarrow> s1"

  Body:	"\<lbrakk>G\<turnstile>Norm s0\<midarrow>Init D\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>c\<midarrow>n\<rightarrow> s2;
          s3 = (if (\<exists> l. abrupt s2 = Some (Jump (Break l)) \<or>  
                         abrupt s2 = Some (Jump (Cont l)))
                  then abupd (\<lambda> x. Some (Error CrossMethodJump)) s2 
                  else s2)\<rbrakk>\<Longrightarrow>
         G\<turnstile>Norm s0 \<midarrow>Body D c
          -\<succ>the (locals (store s2) Result)\<midarrow>n\<rightarrow>abupd (absorb Ret) s3"

--{* evaluation of expression lists *}

  Nil:
				"G\<turnstile>Norm s0 \<midarrow>[]\<doteq>\<succ>[]\<midarrow>n\<rightarrow> Norm s0"

  Cons:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e -\<succ> v \<midarrow>n\<rightarrow> s1;
          G\<turnstile>     s1 \<midarrow>es\<doteq>\<succ>vs\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow>
			     G\<turnstile>Norm s0 \<midarrow>e#es\<doteq>\<succ>v#vs\<midarrow>n\<rightarrow> s2"


--{* execution of statements *}

  Skip:	 			    "G\<turnstile>Norm s \<midarrow>Skip\<midarrow>n\<rightarrow> Norm s"

  Expr:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1\<rbrakk> \<Longrightarrow>
				  G\<turnstile>Norm s0 \<midarrow>Expr e\<midarrow>n\<rightarrow> s1"

  Lab:  "\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c \<midarrow>n\<rightarrow> s1\<rbrakk> \<Longrightarrow>
                             G\<turnstile>Norm s0 \<midarrow>l\<bullet> c\<midarrow>n\<rightarrow> abupd (absorb l) s1"

  Comp:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1 \<midarrow>n\<rightarrow> s1;
	  G\<turnstile>     s1 \<midarrow>c2 \<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow>
				 G\<turnstile>Norm s0 \<midarrow>c1;; c2\<midarrow>n\<rightarrow> s2"

  If:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<midarrow>n\<rightarrow> s1;
	  G\<turnstile>     s1\<midarrow>(if the_Bool b then c1 else c2)\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow>
		       G\<turnstile>Norm s0 \<midarrow>If(e) c1 Else c2 \<midarrow>n\<rightarrow> s2"

  Loop:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<midarrow>n\<rightarrow> s1;
	  if the_Bool b 
             then (G\<turnstile>s1 \<midarrow>c\<midarrow>n\<rightarrow> s2 \<and> 
                   G\<turnstile>(abupd (absorb (Cont l)) s2) \<midarrow>l\<bullet> While(e) c\<midarrow>n\<rightarrow> s3)
	     else s3 = s1\<rbrakk> \<Longrightarrow>
			      G\<turnstile>Norm s0 \<midarrow>l\<bullet> While(e) c\<midarrow>n\<rightarrow> s3"
  
  Jmp: "G\<turnstile>Norm s \<midarrow>Jmp j\<midarrow>n\<rightarrow> (Some (Jump j), s)"
  
  Throw:"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<midarrow>n\<rightarrow> s1\<rbrakk> \<Longrightarrow>
				 G\<turnstile>Norm s0 \<midarrow>Throw e\<midarrow>n\<rightarrow> abupd (throw a') s1"

  Try:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2;
	  if G,s2\<turnstile>catch tn then G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<midarrow>n\<rightarrow> s3 else s3 = s2\<rbrakk>
          \<Longrightarrow>
		  G\<turnstile>Norm s0 \<midarrow>Try c1 Catch(tn vn) c2\<midarrow>n\<rightarrow> s3"

  Fin:	"\<lbrakk>G\<turnstile>Norm s0 \<midarrow>c1\<midarrow>n\<rightarrow> (x1,s1);
	  G\<turnstile>Norm s1 \<midarrow>c2\<midarrow>n\<rightarrow> s2;
          s3=(if (\<exists> err. x1=Some (Error err)) 
              then (x1,s1) 
              else abupd (abrupt_if (x1\<noteq>None) x1) s2)\<rbrakk> \<Longrightarrow>
              G\<turnstile>Norm s0 \<midarrow>c1 Finally c2\<midarrow>n\<rightarrow> s3"
  
  Init:	"\<lbrakk>the (class G C) = c;
	  if inited C (globs s0) then s3 = Norm s0
	  else (G\<turnstile>Norm (init_class_obj G C s0)
	          \<midarrow>(if C = Object then Skip else Init (super c))\<midarrow>n\<rightarrow> s1 \<and>
	        G\<turnstile>set_lvars empty s1 \<midarrow>init c\<midarrow>n\<rightarrow> s2 \<and> 
                s3 = restore_lvars s1 s2)\<rbrakk>
          \<Longrightarrow>
		 G\<turnstile>Norm s0 \<midarrow>Init C\<midarrow>n\<rightarrow> s3"
monos
  if_def2


declare split_if     [split del] split_if_asm     [split del]
        option.split [split del] option.split_asm [split del]
        not_None_eq [simp del] 
        split_paired_All [simp del] split_paired_Ex [simp del]
ML_setup {*
simpset_ref() := simpset() delloop "split_all_tac"
*}
inductive_cases evaln_cases: "G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> vs'"

inductive_cases evaln_elim_cases:
	"G\<turnstile>(Some xc, s) \<midarrow>t                        \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r Skip                      \<succ>\<midarrow>n\<rightarrow> xs'"
        "G\<turnstile>Norm s \<midarrow>In1r (Jmp j)                   \<succ>\<midarrow>n\<rightarrow> xs'"
        "G\<turnstile>Norm s \<midarrow>In1r (l\<bullet> c)                    \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In3  ([])                      \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In3  (e#es)                    \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Lit w)                   \<succ>\<midarrow>n\<rightarrow> vs'"
        "G\<turnstile>Norm s \<midarrow>In1l (UnOp unop e)             \<succ>\<midarrow>n\<rightarrow> vs'"
        "G\<turnstile>Norm s \<midarrow>In1l (BinOp binop e1 e2)       \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In2  (LVar vn)                 \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Cast T e)                \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (e InstOf T)              \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Super)                   \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Acc va)                  \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r (Expr e)                  \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1r (c1;; c2)                 \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Methd C sig)             \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Body D c)                \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1l (e0 ? e1 : e2)            \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r (If(e) c1 Else c2)        \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1r (l\<bullet> While(e) c)           \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1r (c1 Finally c2)           \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1r (Throw e)                 \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In1l (NewC C)                  \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (New T[e])                \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l (Ass va e)                \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r (Try c1 Catch(tn vn) c2)  \<succ>\<midarrow>n\<rightarrow> xs'"
	"G\<turnstile>Norm s \<midarrow>In2  ({accC,statDeclC,stat}e..fn) \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In2  (e1.[e2])                 \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1l ({accC,statT,mode}e\<cdot>mn({pT}p)) \<succ>\<midarrow>n\<rightarrow> vs'"
	"G\<turnstile>Norm s \<midarrow>In1r (Init C)                  \<succ>\<midarrow>n\<rightarrow> xs'"
        "G\<turnstile>Norm s \<midarrow>In1r (Init C)                  \<succ>\<midarrow>n\<rightarrow> xs'"

declare split_if     [split] split_if_asm     [split] 
        option.split [split] option.split_asm [split]
        not_None_eq [simp] 
        split_paired_All [simp] split_paired_Ex [simp]
ML_setup {*
simpset_ref() := simpset() addloop ("split_all_tac", split_all_tac)
*}
lemma evaln_Inj_elim: "G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (w,s') \<Longrightarrow> case t of In1 ec \<Rightarrow>  
  (case ec of Inl e \<Rightarrow> (\<exists>v. w = In1 v) | Inr c \<Rightarrow> w = \<diamondsuit>)  
  | In2 e \<Rightarrow> (\<exists>v. w = In2 v) | In3 e \<Rightarrow> (\<exists>v. w = In3 v)"
apply (erule evaln_cases , auto)
apply (induct_tac "t")
apply   (induct_tac "a")
apply auto
done

text {* The following simplification procedures set up the proper injections of
 terms and their corresponding values in the evaluation relation:
 E.g. an expression 
 (injection @{term In1l} into terms) always evaluates to ordinary values 
 (injection @{term In1} into generalised values @{term vals}). 
*}

ML_setup {*
fun enf nam inj rhs =
let
  val name = "evaln_" ^ nam ^ "_eq"
  val lhs = "G\<turnstile>s \<midarrow>" ^ inj ^ " t\<succ>\<midarrow>n\<rightarrow> (w, s')"
  val () = qed_goal name (the_context()) (lhs ^ " = (" ^ rhs ^ ")") 
	(K [Auto_tac, ALLGOALS (ftac (thm "evaln_Inj_elim")) THEN Auto_tac])
  fun is_Inj (Const (inj,_) $ _) = true
    | is_Inj _                   = false
  fun pred (_ $ (Const ("Pair",_) $ _ $ (Const ("Pair", _) $ _ $ 
    (Const ("Pair", _) $ _ $ (Const ("Pair", _) $ x $ _ )))) $ _ ) = is_Inj x
in
  cond_simproc name lhs pred (thm name)
end;

val evaln_expr_proc = enf "expr" "In1l" "\<exists>v.  w=In1 v  \<and> G\<turnstile>s \<midarrow>t-\<succ>v \<midarrow>n\<rightarrow> s'";
val evaln_var_proc  = enf "var"  "In2"  "\<exists>vf. w=In2 vf \<and> G\<turnstile>s \<midarrow>t=\<succ>vf\<midarrow>n\<rightarrow> s'";
val evaln_exprs_proc= enf "exprs""In3"  "\<exists>vs. w=In3 vs \<and> G\<turnstile>s \<midarrow>t\<doteq>\<succ>vs\<midarrow>n\<rightarrow> s'";
val evaln_stmt_proc = enf "stmt" "In1r" "     w=\<diamondsuit>      \<and> G\<turnstile>s \<midarrow>t     \<midarrow>n\<rightarrow> s'";
Addsimprocs [evaln_expr_proc,evaln_var_proc,evaln_exprs_proc,evaln_stmt_proc];

bind_thms ("evaln_AbruptIs", sum3_instantiate (thm "evaln.Abrupt"))
*}
declare evaln_AbruptIs [intro!]

lemma evaln_Callee: "G\<turnstile>Norm s\<midarrow>In1l (Callee l e)\<succ>\<midarrow>n\<rightarrow> (v,s') = False"
proof -
  { fix s t v s'
    assume eval: "G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s')" and
         normal: "normal s" and
         callee: "t=In1l (Callee l e)"
    then have "False"
    proof (induct)
    qed (auto)
  }
  then show ?thesis
    by (cases s') fastsimp 
qed

lemma evaln_InsInitE: "G\<turnstile>Norm s\<midarrow>In1l (InsInitE c e)\<succ>\<midarrow>n\<rightarrow> (v,s') = False"
proof -
  { fix s t v s'
    assume eval: "G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s')" and
         normal: "normal s" and
         callee: "t=In1l (InsInitE c e)"
    then have "False"
    proof (induct)
    qed (auto)
  }
  then show ?thesis
    by (cases s') fastsimp
qed

lemma evaln_InsInitV: "G\<turnstile>Norm s\<midarrow>In2 (InsInitV c w)\<succ>\<midarrow>n\<rightarrow> (v,s') = False"
proof -
  { fix s t v s'
    assume eval: "G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s')" and
         normal: "normal s" and
         callee: "t=In2 (InsInitV c w)"
    then have "False"
    proof (induct)
    qed (auto)
  }  
  then show ?thesis
    by (cases s') fastsimp
qed

lemma evaln_FinA: "G\<turnstile>Norm s\<midarrow>In1r (FinA a c)\<succ>\<midarrow>n\<rightarrow> (v,s') = False"
proof -
  { fix s t v s'
    assume eval: "G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s')" and
         normal: "normal s" and
         callee: "t=In1r (FinA a c)"
    then have "False"
    proof (induct)
    qed (auto)
  } 
  then show ?thesis
    by (cases s') fastsimp
qed

lemma evaln_abrupt_lemma: "G\<turnstile>s \<midarrow>e\<succ>\<midarrow>n\<rightarrow> (v,s') \<Longrightarrow> 
 fst s = Some xc \<longrightarrow> s' = s \<and> v = arbitrary3 e"
apply (erule evaln_cases , auto)
done

lemma evaln_abrupt: 
 "\<And>s'. G\<turnstile>(Some xc,s) \<midarrow>e\<succ>\<midarrow>n\<rightarrow> (w,s') = (s' = (Some xc,s) \<and>  
  w=arbitrary3 e \<and> G\<turnstile>(Some xc,s) \<midarrow>e\<succ>\<midarrow>n\<rightarrow> (arbitrary3 e,(Some xc,s)))"
apply auto
apply (frule evaln_abrupt_lemma, auto)+
done

ML {*
local
  fun is_Some (Const ("Pair",_) $ (Const ("Datatype.option.Some",_) $ _)$ _) =true
    | is_Some _ = false
  fun pred (_ $ (Const ("Pair",_) $
     _ $ (Const ("Pair", _) $ _ $ (Const ("Pair", _) $ _ $
       (Const ("Pair", _) $ _ $ x)))) $ _ ) = is_Some x
in
  val evaln_abrupt_proc = 
 cond_simproc "evaln_abrupt" "G\<turnstile>(Some xc,s) \<midarrow>e\<succ>\<midarrow>n\<rightarrow> (w,s')" pred (thm "evaln_abrupt")
end;
Addsimprocs [evaln_abrupt_proc]
*}

lemma evaln_LitI: "G\<turnstile>s \<midarrow>Lit v-\<succ>(if normal s then v else arbitrary)\<midarrow>n\<rightarrow> s"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: evaln.Lit)

lemma CondI: 
 "\<And>s1. \<lbrakk>G\<turnstile>s \<midarrow>e-\<succ>b\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow> 
  G\<turnstile>s \<midarrow>e ? e1 : e2-\<succ>(if normal s1 then v else arbitrary)\<midarrow>n\<rightarrow> s2"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: evaln.Cond)

lemma evaln_SkipI [intro!]: "G\<turnstile>s \<midarrow>Skip\<midarrow>n\<rightarrow> s"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: evaln.Skip)

lemma evaln_ExprI: "G\<turnstile>s \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s' \<Longrightarrow> G\<turnstile>s \<midarrow>Expr e\<midarrow>n\<rightarrow> s'"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: evaln.Expr)

lemma evaln_CompI: "\<lbrakk>G\<turnstile>s \<midarrow>c1\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>c2\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow> G\<turnstile>s \<midarrow>c1;; c2\<midarrow>n\<rightarrow> s2"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: evaln.Comp)

lemma evaln_IfI: 
 "\<lbrakk>G\<turnstile>s \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1; G\<turnstile>s1 \<midarrow>(if the_Bool v then c1 else c2)\<midarrow>n\<rightarrow> s2\<rbrakk> \<Longrightarrow> 
  G\<turnstile>s \<midarrow>If(e) c1 Else c2\<midarrow>n\<rightarrow> s2"
apply (case_tac "s", case_tac "a = None")
by (auto intro!: evaln.If)

lemma evaln_SkipD [dest!]: "G\<turnstile>s \<midarrow>Skip\<midarrow>n\<rightarrow> s' \<Longrightarrow> s' = s" 
by (erule evaln_cases, auto)

lemma evaln_Skip_eq [simp]: "G\<turnstile>s \<midarrow>Skip\<midarrow>n\<rightarrow> s' = (s = s')"
apply auto
done




section {* evaln implies eval *}

lemma evaln_eval:  
  assumes evaln: "G\<turnstile>s0 \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s1)" 
  shows "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)"
using evaln 
proof (induct)
  case (Loop b c e l n s0 s1 s2 s3)
  have "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<rightarrow> s1".
  moreover
  have "if the_Bool b
        then (G\<turnstile>s1 \<midarrow>c\<rightarrow> s2) \<and> 
             G\<turnstile>abupd (absorb (Cont l)) s2 \<midarrow>l\<bullet> While(e) c\<rightarrow> s3
        else s3 = s1"
    using Loop.hyps by simp
  ultimately show ?case by (rule eval.Loop)
next
  case (Try c1 c2 n s0 s1 s2 s3 C vn)
  have "G\<turnstile>Norm s0 \<midarrow>c1\<rightarrow> s1".
  moreover
  have "G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2".
  moreover
  have "if G,s2\<turnstile>catch C then G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<rightarrow> s3 else s3 = s2"
    using Try.hyps by simp
  ultimately show ?case by (rule eval.Try)
next
  case (Init C c n s0 s1 s2 s3)
  have "the (class G C) = c".
  moreover
  have "if inited C (globs s0) 
           then s3 = Norm s0
           else G\<turnstile>Norm ((init_class_obj G C) s0) 
                  \<midarrow>(if C = Object then Skip else Init (super c))\<rightarrow> s1 \<and>
                G\<turnstile>(set_lvars empty) s1 \<midarrow>init c\<rightarrow> s2 \<and>
                s3 = (set_lvars (locals (store s1))) s2"
    using Init.hyps by simp
  ultimately show ?case by (rule eval.Init)
qed (rule eval.intros,(assumption+ | assumption?))+

lemma Suc_le_D_lemma: "\<lbrakk>Suc n <= m'; (\<And>m. n <= m \<Longrightarrow> P (Suc m)) \<rbrakk> \<Longrightarrow> P m'"
apply (frule Suc_le_D)
apply fast
done

lemma evaln_nonstrict [rule_format (no_asm), elim]: 
  "\<And>ws. G\<turnstile>s \<midarrow>t\<succ>\<midarrow>n\<rightarrow> ws \<Longrightarrow> \<forall>m. n\<le>m \<longrightarrow> G\<turnstile>s \<midarrow>t\<succ>\<midarrow>m\<rightarrow> ws"
apply (simp (no_asm_simp) only: split_tupled_all)
apply (erule evaln.induct)
apply (tactic {* ALLGOALS (EVERY'[strip_tac, TRY o etac (thm "Suc_le_D_lemma"),
  REPEAT o smp_tac 1, 
  resolve_tac (thms "evaln.intros") THEN_ALL_NEW TRY o atac]) *})
(* 3 subgoals *)
apply (auto split del: split_if)
done

lemmas evaln_nonstrict_Suc = evaln_nonstrict [OF _ le_refl [THEN le_SucI]]

lemma evaln_max2: "\<lbrakk>G\<turnstile>s1 \<midarrow>t1\<succ>\<midarrow>n1\<rightarrow> ws1; G\<turnstile>s2 \<midarrow>t2\<succ>\<midarrow>n2\<rightarrow> ws2\<rbrakk> \<Longrightarrow> 
             G\<turnstile>s1 \<midarrow>t1\<succ>\<midarrow>max n1 n2\<rightarrow> ws1 \<and> G\<turnstile>s2 \<midarrow>t2\<succ>\<midarrow>max n1 n2\<rightarrow> ws2"
by (fast intro: le_maxI1 le_maxI2)

corollary evaln_max2E [consumes 2]:
  "\<lbrakk>G\<turnstile>s1 \<midarrow>t1\<succ>\<midarrow>n1\<rightarrow> ws1; G\<turnstile>s2 \<midarrow>t2\<succ>\<midarrow>n2\<rightarrow> ws2; 
    \<lbrakk>G\<turnstile>s1 \<midarrow>t1\<succ>\<midarrow>max n1 n2\<rightarrow> ws1;G\<turnstile>s2 \<midarrow>t2\<succ>\<midarrow>max n1 n2\<rightarrow> ws2 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by (drule (1) evaln_max2) simp


lemma evaln_max3: 
"\<lbrakk>G\<turnstile>s1 \<midarrow>t1\<succ>\<midarrow>n1\<rightarrow> ws1; G\<turnstile>s2 \<midarrow>t2\<succ>\<midarrow>n2\<rightarrow> ws2; G\<turnstile>s3 \<midarrow>t3\<succ>\<midarrow>n3\<rightarrow> ws3\<rbrakk> \<Longrightarrow>
 G\<turnstile>s1 \<midarrow>t1\<succ>\<midarrow>max (max n1 n2) n3\<rightarrow> ws1 \<and>
 G\<turnstile>s2 \<midarrow>t2\<succ>\<midarrow>max (max n1 n2) n3\<rightarrow> ws2 \<and> 
 G\<turnstile>s3 \<midarrow>t3\<succ>\<midarrow>max (max n1 n2) n3\<rightarrow> ws3"
apply (drule (1) evaln_max2, erule thin_rl)
apply (fast intro!: le_maxI1 le_maxI2)
done

corollary evaln_max3E: 
"\<lbrakk>G\<turnstile>s1 \<midarrow>t1\<succ>\<midarrow>n1\<rightarrow> ws1; G\<turnstile>s2 \<midarrow>t2\<succ>\<midarrow>n2\<rightarrow> ws2; G\<turnstile>s3 \<midarrow>t3\<succ>\<midarrow>n3\<rightarrow> ws3;
   \<lbrakk>G\<turnstile>s1 \<midarrow>t1\<succ>\<midarrow>max (max n1 n2) n3\<rightarrow> ws1;
    G\<turnstile>s2 \<midarrow>t2\<succ>\<midarrow>max (max n1 n2) n3\<rightarrow> ws2; 
    G\<turnstile>s3 \<midarrow>t3\<succ>\<midarrow>max (max n1 n2) n3\<rightarrow> ws3
   \<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
by (drule (2) evaln_max3) simp


lemma le_max3I1: "(n2::nat) \<le> max n1 (max n2 n3)"
proof -
  have "n2 \<le> max n2 n3"
    by (rule le_maxI1)
  also
  have "max n2 n3 \<le> max n1 (max n2 n3)"
    by (rule le_maxI2)
  finally
  show ?thesis .
qed

lemma le_max3I2: "(n3::nat) \<le> max n1 (max n2 n3)"
proof -
  have "n3 \<le> max n2 n3"
    by (rule le_maxI2)
  also
  have "max n2 n3 \<le> max n1 (max n2 n3)"
    by (rule le_maxI2)
  finally
  show ?thesis .
qed

ML {*
Delsimprocs [wt_expr_proc,wt_var_proc,wt_exprs_proc,wt_stmt_proc]
*}

section {* eval implies evaln *}
lemma eval_evaln: 
  assumes eval: "G\<turnstile>s0 \<midarrow>t\<succ>\<rightarrow> (v,s1)"
  shows  "\<exists>n. G\<turnstile>s0 \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (v,s1)"
using eval 
proof (induct)
  case (Abrupt s t xc)
  obtain n where
    "G\<turnstile>(Some xc, s) \<midarrow>t\<succ>\<midarrow>n\<rightarrow> (arbitrary3 t, Some xc, s)"
    by (rules intro: evaln.Abrupt)
  then show ?case ..
next
  case Skip
  show ?case by (blast intro: evaln.Skip)
next
  case (Expr e s0 s1 v)
  then obtain n where
    "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1"
    by (rules)
  then have "G\<turnstile>Norm s0 \<midarrow>Expr e\<midarrow>n\<rightarrow> s1"
    by (rule evaln.Expr) 
  then show ?case ..
next
  case (Lab c l s0 s1)
  then obtain n where
    "G\<turnstile>Norm s0 \<midarrow>c\<midarrow>n\<rightarrow> s1"
    by (rules)
  then have "G\<turnstile>Norm s0 \<midarrow>l\<bullet> c\<midarrow>n\<rightarrow> abupd (absorb l) s1"
    by (rule evaln.Lab)
  then show ?case ..
next
  case (Comp c1 c2 s0 s1 s2)
  then obtain n1 n2 where
    "G\<turnstile>Norm s0 \<midarrow>c1\<midarrow>n1\<rightarrow> s1"
    "G\<turnstile>s1 \<midarrow>c2\<midarrow>n2\<rightarrow> s2"
    by (rules)
  then have "G\<turnstile>Norm s0 \<midarrow>c1;; c2\<midarrow>max n1 n2\<rightarrow> s2"
    by (blast intro: evaln.Comp dest: evaln_max2 )
  then show ?case ..
next
  case (If b c1 c2 e s0 s1 s2)
  then obtain n1 n2 where
    "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<midarrow>n1\<rightarrow> s1"
    "G\<turnstile>s1 \<midarrow>(if the_Bool b then c1 else c2)\<midarrow>n2\<rightarrow> s2"
    by (rules)
  then have "G\<turnstile>Norm s0 \<midarrow>If(e) c1 Else c2\<midarrow>max n1 n2\<rightarrow> s2"
    by (blast intro: evaln.If dest: evaln_max2)
  then show ?case ..
next
  case (Loop b c e l s0 s1 s2 s3)
  from Loop.hyps obtain n1 where
    "G\<turnstile>Norm s0 \<midarrow>e-\<succ>b\<midarrow>n1\<rightarrow> s1"
    by (rules)
  moreover from Loop.hyps obtain n2 where
    "if the_Bool b 
        then (G\<turnstile>s1 \<midarrow>c\<midarrow>n2\<rightarrow> s2 \<and> 
              G\<turnstile>(abupd (absorb (Cont l)) s2)\<midarrow>l\<bullet> While(e) c\<midarrow>n2\<rightarrow> s3)
	else s3 = s1"
    by simp (rules intro: evaln_nonstrict le_maxI1 le_maxI2)
  ultimately
  have "G\<turnstile>Norm s0 \<midarrow>l\<bullet> While(e) c\<midarrow>max n1 n2\<rightarrow> s3"
    apply -
    apply (rule evaln.Loop)
    apply   (rules intro: evaln_nonstrict intro: le_maxI1)

    apply   (auto intro: evaln_nonstrict intro: le_maxI2)
    done
  then show ?case ..
next
  case (Jmp j s)
  have "G\<turnstile>Norm s \<midarrow>Jmp j\<midarrow>n\<rightarrow> (Some (Jump j), s)"
    by (rule evaln.Jmp)
  then show ?case ..
next
  case (Throw a e s0 s1)
  then obtain n where
    "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a\<midarrow>n\<rightarrow> s1"
    by (rules)
  then have "G\<turnstile>Norm s0 \<midarrow>Throw e\<midarrow>n\<rightarrow> abupd (throw a) s1"
    by (rule evaln.Throw)
  then show ?case ..
next 
  case (Try catchC c1 c2 s0 s1 s2 s3 vn)
  from Try.hyps obtain n1 where
    "G\<turnstile>Norm s0 \<midarrow>c1\<midarrow>n1\<rightarrow> s1"
    by (rules)
  moreover 
  have sxalloc: "G\<turnstile>s1 \<midarrow>sxalloc\<rightarrow> s2" .
  moreover
  from Try.hyps obtain n2 where
    "if G,s2\<turnstile>catch catchC then G\<turnstile>new_xcpt_var vn s2 \<midarrow>c2\<midarrow>n2\<rightarrow> s3 else s3 = s2"
    by fastsimp 
  ultimately
  have "G\<turnstile>Norm s0 \<midarrow>Try c1 Catch(catchC vn) c2\<midarrow>max n1 n2\<rightarrow> s3"
    by (auto intro!: evaln.Try le_maxI1 le_maxI2)
  then show ?case ..
next
  case (Fin c1 c2 s0 s1 s2 s3 x1)
  from Fin obtain n1 n2 where 
    "G\<turnstile>Norm s0 \<midarrow>c1\<midarrow>n1\<rightarrow> (x1, s1)"
    "G\<turnstile>Norm s1 \<midarrow>c2\<midarrow>n2\<rightarrow> s2"
    by rules
  moreover
  have s3: "s3 = (if \<exists>err. x1 = Some (Error err) 
                     then (x1, s1)
                     else abupd (abrupt_if (x1 \<noteq> None) x1) s2)" .
  ultimately 
  have 
    "G\<turnstile>Norm s0 \<midarrow>c1 Finally c2\<midarrow>max n1 n2\<rightarrow> s3"
    by (blast intro: evaln.Fin dest: evaln_max2)
  then show ?case ..
next
  case (Init C c s0 s1 s2 s3)
  have     cls: "the (class G C) = c" .
  moreover from Init.hyps obtain n where
      "if inited C (globs s0) then s3 = Norm s0
       else (G\<turnstile>Norm (init_class_obj G C s0)
	      \<midarrow>(if C = Object then Skip else Init (super c))\<midarrow>n\<rightarrow> s1 \<and>
	           G\<turnstile>set_lvars empty s1 \<midarrow>init c\<midarrow>n\<rightarrow> s2 \<and> 
                   s3 = restore_lvars s1 s2)"
    by (auto intro: evaln_nonstrict le_maxI1 le_maxI2)
  ultimately have "G\<turnstile>Norm s0 \<midarrow>Init C\<midarrow>n\<rightarrow> s3"
    by (rule evaln.Init)
  then show ?case ..
next
  case (NewC C a s0 s1 s2)
  then obtain n where 
    "G\<turnstile>Norm s0 \<midarrow>Init C\<midarrow>n\<rightarrow> s1"
    by (rules)
  with NewC 
  have "G\<turnstile>Norm s0 \<midarrow>NewC C-\<succ>Addr a\<midarrow>n\<rightarrow> s2"
    by (rules intro: evaln.NewC)
  then show ?case ..
next
  case (NewA T a e i s0 s1 s2 s3)
  then obtain n1 n2 where 
    "G\<turnstile>Norm s0 \<midarrow>init_comp_ty T\<midarrow>n1\<rightarrow> s1"
    "G\<turnstile>s1 \<midarrow>e-\<succ>i\<midarrow>n2\<rightarrow> s2"      
    by (rules)
  moreover
  have "G\<turnstile>abupd (check_neg i) s2 \<midarrow>halloc Arr T (the_Intg i)\<succ>a\<rightarrow> s3" .
  ultimately
  have "G\<turnstile>Norm s0 \<midarrow>New T[e]-\<succ>Addr a\<midarrow>max n1 n2\<rightarrow> s3"
    by (blast intro: evaln.NewA dest: evaln_max2)
  then show ?case ..
next
  case (Cast castT e s0 s1 s2 v)
  then obtain n where
    "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1"
    by (rules)
  moreover 
  have "s2 = abupd (raise_if (\<not> G,snd s1\<turnstile>v fits castT) ClassCast) s1" .
  ultimately
  have "G\<turnstile>Norm s0 \<midarrow>Cast castT e-\<succ>v\<midarrow>n\<rightarrow> s2"
    by (rule evaln.Cast)
  then show ?case ..
next
  case (Inst T b e s0 s1 v)
  then obtain n where
    "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1"
    by (rules)
  moreover 
  have "b = (v \<noteq> Null \<and> G,snd s1\<turnstile>v fits RefT T)" .
  ultimately
  have "G\<turnstile>Norm s0 \<midarrow>e InstOf T-\<succ>Bool b\<midarrow>n\<rightarrow> s1"
    by (rule evaln.Inst)
  then show ?case ..
next
  case (Lit s v)
  have "G\<turnstile>Norm s \<midarrow>Lit v-\<succ>v\<midarrow>n\<rightarrow> Norm s"
    by (rule evaln.Lit)
  then show ?case ..
next
  case (UnOp e s0 s1 unop v )
  then obtain n where
    "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n\<rightarrow> s1"
    by (rules)
  hence "G\<turnstile>Norm s0 \<midarrow>UnOp unop e-\<succ>eval_unop unop v\<midarrow>n\<rightarrow> s1"
    by (rule evaln.UnOp)
  then show ?case ..
next
  case (BinOp binop e1 e2 s0 s1 s2 v1 v2)
  then obtain n1 n2 where 
    "G\<turnstile>Norm s0 \<midarrow>e1-\<succ>v1\<midarrow>n1\<rightarrow> s1"
    "G\<turnstile>s1 \<midarrow>(if need_second_arg binop v1 then In1l e2
               else In1r Skip)\<succ>\<midarrow>n2\<rightarrow> (In1 v2, s2)"    
    by (rules)
  hence "G\<turnstile>Norm s0 \<midarrow>BinOp binop e1 e2-\<succ>(eval_binop binop v1 v2)\<midarrow>max n1 n2
          \<rightarrow> s2"
    by (blast intro!: evaln.BinOp dest: evaln_max2)
  then show ?case ..
next
  case (Super s )
  have "G\<turnstile>Norm s \<midarrow>Super-\<succ>val_this s\<midarrow>n\<rightarrow> Norm s"
    by (rule evaln.Super)
  then show ?case ..
next
  case (Acc f s0 s1 v va)
  then obtain n where
    "G\<turnstile>Norm s0 \<midarrow>va=\<succ>(v, f)\<midarrow>n\<rightarrow> s1"
    by (rules)
  then
  have "G\<turnstile>Norm s0 \<midarrow>Acc va-\<succ>v\<midarrow>n\<rightarrow> s1"
    by (rule evaln.Acc)
  then show ?case ..
next
  case (Ass e f s0 s1 s2 v var w)
  then obtain n1 n2 where 
    "G\<turnstile>Norm s0 \<midarrow>var=\<succ>(w, f)\<midarrow>n1\<rightarrow> s1"
    "G\<turnstile>s1 \<midarrow>e-\<succ>v\<midarrow>n2\<rightarrow> s2"      
    by (rules)
  then
  have "G\<turnstile>Norm s0 \<midarrow>var:=e-\<succ>v\<midarrow>max n1 n2\<rightarrow> assign f v s2"
    by (blast intro: evaln.Ass dest: evaln_max2)
  then show ?case ..
next
  case (Cond b e0 e1 e2 s0 s1 s2 v)
  then obtain n1 n2 where 
    "G\<turnstile>Norm s0 \<midarrow>e0-\<succ>b\<midarrow>n1\<rightarrow> s1"
    "G\<turnstile>s1 \<midarrow>(if the_Bool b then e1 else e2)-\<succ>v\<midarrow>n2\<rightarrow> s2"
    by (rules)
  then
  have "G\<turnstile>Norm s0 \<midarrow>e0 ? e1 : e2-\<succ>v\<midarrow>max n1 n2\<rightarrow> s2"
    by (blast intro: evaln.Cond dest: evaln_max2)
  then show ?case ..
next
  case (Call invDeclC a' accC' args e mn mode pTs' s0 s1 s2 s3 s3' s4 statT 
        v vs)
  then obtain n1 n2 where
    "G\<turnstile>Norm s0 \<midarrow>e-\<succ>a'\<midarrow>n1\<rightarrow> s1"
    "G\<turnstile>s1 \<midarrow>args\<doteq>\<succ>vs\<midarrow>n2\<rightarrow> s2"
    by rules
  moreover
  have "invDeclC = invocation_declclass G mode (store s2) a' statT 
                       \<lparr>name=mn,parTs=pTs'\<rparr>" .
  moreover
  have "s3 = init_lvars G invDeclC \<lparr>name=mn,parTs=pTs'\<rparr> mode a' vs s2" .
  moreover
  have "s3'=check_method_access G accC' statT mode \<lparr>name=mn,parTs=pTs'\<rparr> a' s3".
  moreover 
  from Call.hyps
  obtain m where 
    "G\<turnstile>s3' \<midarrow>Methd invDeclC \<lparr>name=mn, parTs=pTs'\<rparr>-\<succ>v\<midarrow>m\<rightarrow> s4"
    by rules
  ultimately
  have "G\<turnstile>Norm s0 \<midarrow>{accC',statT,mode}e\<cdot>mn( {pTs'}args)-\<succ>v\<midarrow>max n1 (max n2 m)\<rightarrow> 
            (set_lvars (locals (store s2))) s4"
    by (auto intro!: evaln.Call le_maxI1 le_max3I1 le_max3I2)
  thus ?case ..
next
  case (Methd D s0 s1 sig v )
  then obtain n where
    "G\<turnstile>Norm s0 \<midarrow>body G D sig-\<succ>v\<midarrow>n\<rightarrow> s1"
    by rules
  then have "G\<turnstile>Norm s0 \<midarrow>Methd D sig-\<succ>v\<midarrow>Suc n\<rightarrow> s1"
    by (rule evaln.Methd)
  then show ?case ..
next
  case (Body D c s0 s1 s2 s3 )
  from Body.hyps obtain n1 n2 where 
    evaln_init: "G\<turnstile>Norm s0 \<midarrow>Init D\<midarrow>n1\<rightarrow> s1" and
    evaln_c: "G\<turnstile>s1 \<midarrow>c\<midarrow>n2\<rightarrow> s2"
    by (rules)
  moreover
  have "s3 = (if \<exists>l. fst s2 = Some (Jump (Break l)) \<or> 
                     fst s2 = Some (Jump (Cont l))
                 then abupd (\<lambda>x. Some (Error CrossMethodJump)) s2 
                 else s2)".
  ultimately
  have
     "G\<turnstile>Norm s0 \<midarrow>Body D c-\<succ>the (locals (store s2) Result)\<midarrow>max n1 n2
       \<rightarrow> abupd (absorb Ret) s3"
    by (rules intro: evaln.Body dest: evaln_max2)
  then show ?case ..
next
  case (LVar s vn )
  obtain n where
    "G\<turnstile>Norm s \<midarrow>LVar vn=\<succ>lvar vn s\<midarrow>n\<rightarrow> Norm s"
    by (rules intro: evaln.LVar)
  then show ?case ..
next
  case (FVar a accC e fn s0 s1 s2 s2' s3 stat statDeclC v)
  then obtain n1 n2 where
    "G\<turnstile>Norm s0 \<midarrow>Init statDeclC\<midarrow>n1\<rightarrow> s1"
    "G\<turnstile>s1 \<midarrow>e-\<succ>a\<midarrow>n2\<rightarrow> s2"
    by rules
  moreover
  have "s3 = check_field_access G accC statDeclC fn stat a s2'" 
       "(v, s2') = fvar statDeclC stat fn a s2" .
  ultimately
  have "G\<turnstile>Norm s0 \<midarrow>{accC,statDeclC,stat}e..fn=\<succ>v\<midarrow>max n1 n2\<rightarrow> s3"
    by (rules intro: evaln.FVar dest: evaln_max2)
  then show ?case ..
next
  case (AVar a e1 e2 i s0 s1 s2 s2' v )
  then obtain n1 n2 where 
    "G\<turnstile>Norm s0 \<midarrow>e1-\<succ>a\<midarrow>n1\<rightarrow> s1"
    "G\<turnstile>s1 \<midarrow>e2-\<succ>i\<midarrow>n2\<rightarrow> s2"      
    by rules
  moreover 
  have "(v, s2') = avar G i a s2" .
  ultimately 
  have "G\<turnstile>Norm s0 \<midarrow>e1.[e2]=\<succ>v\<midarrow>max n1 n2\<rightarrow> s2'"
    by (blast intro!: evaln.AVar dest: evaln_max2)
  then show ?case ..
next
  case (Nil s0)
  show ?case by (rules intro: evaln.Nil)
next
  case (Cons e es s0 s1 s2 v vs)
  then obtain n1 n2 where 
    "G\<turnstile>Norm s0 \<midarrow>e-\<succ>v\<midarrow>n1\<rightarrow> s1"
    "G\<turnstile>s1 \<midarrow>es\<doteq>\<succ>vs\<midarrow>n2\<rightarrow> s2"      
    by rules
  then
  have "G\<turnstile>Norm s0 \<midarrow>e # es\<doteq>\<succ>v # vs\<midarrow>max n1 n2\<rightarrow> s2"
    by (blast intro!: evaln.Cons dest: evaln_max2)
  then show ?case ..
qed
       
end
