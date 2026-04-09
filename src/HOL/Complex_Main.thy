section \<open>Comprehensive Complex Theory\<close>

theory Complex_Main
imports
  Complex
  MacLaurin
  Binomial_Plus
  "CVC/cvc5_dsl_rewrites/Extra_Rewrites"
  "CVC/SMT_CVC_Real"
begin

notation floor (\<open>(\<open>open_block notation=\<open>mixfix floor\<close>\<close>\<lfloor>_\<rfloor>)\<close>)

(*repeated to be independant of the import order*)
no_notation
  ordLeq2 (infix \<open><=o\<close> 50) and
  ordLeq3 (infix \<open>\<le>o\<close> 50) and
  ordLess2 (infix \<open><o\<close> 50) and
  ordIso2 (infix \<open>=o\<close> 50) and
  card_of (\<open>(\<open>open_block notation=\<open>mixfix card_of\<close>\<close>|_|)\<close>) and
  BNF_Cardinal_Arithmetic.csum (infixr \<open>+c\<close> 65) and
  BNF_Cardinal_Arithmetic.cprod (infixr \<open>*c\<close> 80) and
  BNF_Cardinal_Arithmetic.cexp (infixr \<open>^c\<close> 90) and
  BNF_Def.convol (\<open>(\<open>indent=1 notation=\<open>mixfix convol\<close>\<close>\<langle>_,/ _\<rangle>)\<close>)

end