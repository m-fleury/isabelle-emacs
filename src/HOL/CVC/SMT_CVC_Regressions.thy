theory SMT_CVC_Regressions
  imports SMT_CVC
begin

declare[[smt_trace]]

(*String Translation*)

(*

(declare-fun x$ () String)
(declare-fun y$ () String)
(assert (! (not (not (= x$ y$))) :named a0))
*)


lemma "(x::string)\<noteq>(y::string)"
  apply (smt (cvc5))
  oops

ML \<open>
val x = @{term "''hi''"}

\<close>
lemma "''hi''\<noteq>''bye''"
  apply (smt (cvc5))

end
(*
("t",
 Const ("String.char.Char", "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> char") $ Const ("HOL.False", "bool") $ Const ("HOL.False", "bool") $
   Const ("HOL.False", "bool") $ Const ("HOL.True", "bool") $ Const ("HOL.False", "bool") $ Const ("HOL.True", "bool") $ Const ("HOL.True", "bool") $
   Const ("HOL.False", "bool")) (line 109 of "/home/lachnitt/Sources/isabelle-git/isabelle-emacs/src/HOL/CVC/ML/SMT_string.ML") 
("ts",
 [Const ("List.list.Cons", "char \<Rightarrow> char list \<Rightarrow> char list") $
    (Const ("String.char.Char", "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> char") $ Const ("HOL.True", "bool") $ Const ("HOL.False", "bool") $
      Const ("HOL.False", "bool") $ Const ("HOL.True", "bool") $ Const ("HOL.False", "bool") $ Const ("HOL.True", "bool") $ Const ("HOL.True", "bool") $
      Const ("HOL.False", "bool")) $
    Const ("List.list.Nil", "char list")]) 


val x =
   Const ("List.list.Cons", "char \<Rightarrow> char list \<Rightarrow> char list") $
     (Const ("String.char.Char", "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> char") $ Const ("HOL.False", "bool") $ Const ("HOL.False", "bool") $
       Const ("HOL.False", "bool") $ Const ("HOL.True", "bool") $ Const ("HOL.False", "bool") $ Const ("HOL.True", "bool") $ Const ("HOL.True", "bool") $
       Const ("HOL.False", "bool")) $
     (Const ("List.list.Cons", "char \<Rightarrow> char list \<Rightarrow> char list") $
       (Const ("String.char.Char", "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> char") $ Const ("HOL.True", "bool") $ Const ("HOL.False", "bool") $
         Const ("HOL.False", "bool") $ Const ("HOL.True", "bool") $ Const ("HOL.False", "bool") $ Const ("HOL.True", "bool") $ Const ("HOL.True", "bool") $
         Const ("HOL.False", "bool")) $
       Const ("List.list.Nil", "char list")):
   term*)