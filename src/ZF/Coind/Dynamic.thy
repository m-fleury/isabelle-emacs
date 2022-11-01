(*  Title:      ZF/Coind/Dynamic.thy
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

theory Dynamic imports Values begin

consts
  EvalRel :: i
inductive
  domains "EvalRel" \<subseteq> "ValEnv * Exp * Val"
  intros
    eval_constI:
      " \<lbrakk>ve \<in> ValEnv; c \<in> Const\<rbrakk> \<Longrightarrow>   
       <ve,e_const(c),v_const(c)>:EvalRel"
    eval_varI:
      " \<lbrakk>ve \<in> ValEnv; x \<in> ExVar; x \<in> ve_dom(ve)\<rbrakk> \<Longrightarrow>   
       <ve,e_var(x),ve_app(ve,x)>:EvalRel" 
    eval_fnI:
      " \<lbrakk>ve \<in> ValEnv; x \<in> ExVar; e \<in> Exp\<rbrakk> \<Longrightarrow>   
       <ve,e_fn(x,e),v_clos(x,e,ve)>:EvalRel "  
    eval_fixI:
      " \<lbrakk>ve \<in> ValEnv; x \<in> ExVar; e \<in> Exp; f \<in> ExVar; cl \<in> Val;   
          v_clos(x,e,ve_owr(ve,f,cl))=cl\<rbrakk> \<Longrightarrow>   
       <ve,e_fix(f,x,e),cl>:EvalRel " 
    eval_appI1:
      " \<lbrakk>ve \<in> ValEnv; e1 \<in> Exp; e2 \<in> Exp; c1 \<in> Const; c2 \<in> Const;   
          <ve,e1,v_const(c1)>:EvalRel;   
          <ve,e2,v_const(c2)>:EvalRel\<rbrakk> \<Longrightarrow>   
       <ve,e_app(e1,e2),v_const(c_app(c1,c2))>:EvalRel "
    eval_appI2:
      " \<lbrakk>ve \<in> ValEnv; vem \<in> ValEnv; e1 \<in> Exp; e2 \<in> Exp; em \<in> Exp; xm \<in> ExVar; v \<in> Val;   
          <ve,e1,v_clos(xm,em,vem)>:EvalRel;   
          <ve,e2,v2>:EvalRel;   
          <ve_owr(vem,xm,v2),em,v>:EvalRel\<rbrakk> \<Longrightarrow>   
       <ve,e_app(e1,e2),v>:EvalRel "
  type_intros c_appI ve_appI ve_empI ve_owrI Exp.intros Val_ValEnv.intros

end
