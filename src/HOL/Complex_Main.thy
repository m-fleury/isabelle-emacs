section \<open>Comprehensive Complex Theory\<close>

theory Complex_Main
imports
  Complex
  MacLaurin
  Binomial_Plus
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

bundle lattice_syntax
begin

notation
  bot  (\<open>\<bottom>\<close>) and
  top  (\<open>\<top>\<close>) and
  inf  (infixl \<open>\<sqinter>\<close> 70) and
  sup  (infixl \<open>\<squnion>\<close> 65) and
  Inf  (\<open>(\<open>open_block notation=\<open>prefix \<Sqinter>\<close>\<close>\<Sqinter> _)\<close> [900] 900) and
  Sup  (\<open>(\<open>open_block notation=\<open>prefix \<Squnion>\<close>\<close>\<Squnion> _)\<close> [900] 900)

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           (\<open>(\<open>indent=3 notation=\<open>binder \<Sqinter>\<close>\<close>\<Sqinter>_./ _)\<close> [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  (\<open>(\<open>indent=3 notation=\<open>binder \<Sqinter>\<close>\<close>\<Sqinter>_\<in>_./ _)\<close> [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           (\<open>(\<open>indent=3 notation=\<open>binder \<Squnion>\<close>\<close>\<Squnion>_./ _)\<close> [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  (\<open>(\<open>indent=3 notation=\<open>binder \<Squnion>\<close>\<close>\<Squnion>_\<in>_./ _)\<close> [0, 0, 10] 10)

end

unbundle no lattice_syntax
end