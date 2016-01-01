(*  Title:      FOLP/ex/Intuitionistic.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Intuitionistic First-Order Logic.

Single-step commands:
by (IntPr.step_tac 1)
by (biresolve_tac safe_brls 1);
by (biresolve_tac haz_brls 1);
by (assume_tac 1);
by (IntPr.safe_tac 1);
by (IntPr.mp_tac 1);
by (IntPr.fast_tac 1);
*)

(*Note: for PROPOSITIONAL formulae...
  ~A is classically provable iff it is intuitionistically provable.  
  Therefore A is classically provable iff ~~A is intuitionistically provable.

Let Q be the conjuction of the propositions A|~A, one for each atom A in
P.  If P is provable classically, then clearly P&Q is provable
intuitionistically, so ~~(P&Q) is also provable intuitionistically.
The latter is intuitionistically equivalent to ~~P&~~Q, hence to ~~P,
since ~~Q is intuitionistically provable.  Finally, if P is a negation then
~~P is intuitionstically equivalent to P.  [Andy Pitts]
*)

theory Intuitionistic
imports IFOLP
begin

schematic_goal "?p : ~~(P&Q) <-> ~~P & ~~Q"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

schematic_goal "?p : ~~~P <-> ~P"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

schematic_goal "?p : ~~((P --> Q | R)  -->  (P-->Q) | (P-->R))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

schematic_goal "?p : (P<->Q) <-> (Q<->P)"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)


subsection \<open>Lemmas for the propositional double-negation translation\<close>

schematic_goal "?p : P --> ~~P"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

schematic_goal "?p : ~~(~~P --> P)"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

schematic_goal "?p : ~~P & ~~(P --> Q) --> ~~Q"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)


subsection \<open>The following are classically but not constructively valid\<close>

(*The attempt to prove them terminates quickly!*)
schematic_goal "?p : ((P-->Q) --> P)  -->  P"
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
  oops

schematic_goal "?p : (P&Q-->R)  -->  (P-->R) | (Q-->R)"
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
  oops


subsection \<open>Intuitionistic FOL: propositional problems based on Pelletier\<close>

text "Problem ~~1"
schematic_goal "?p : ~~((P-->Q)  <->  (~Q --> ~P))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem ~~2"
schematic_goal "?p : ~~(~~P  <->  P)"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem 3"
schematic_goal "?p : ~(P-->Q) --> (Q-->P)"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem ~~4"
schematic_goal "?p : ~~((~P-->Q)  <->  (~Q --> P))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem ~~5"
schematic_goal "?p : ~~((P|Q-->P|R) --> P|(Q-->R))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem ~~6"
schematic_goal "?p : ~~(P | ~P)"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem ~~7"
schematic_goal "?p : ~~(P | ~~~P)"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem ~~8.  Peirce's law"
schematic_goal "?p : ~~(((P-->Q) --> P)  -->  P)"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem 9"
schematic_goal "?p : ((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem 10"
schematic_goal "?p : (Q-->R) --> (R-->P&Q) --> (P-->(Q|R)) --> (P<->Q)"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "11.  Proved in each direction (incorrectly, says Pelletier!!) "
schematic_goal "?p : P<->P"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem ~~12.  Dijkstra's law  "
schematic_goal "?p : ~~(((P <-> Q) <-> R)  <->  (P <-> (Q <-> R)))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

schematic_goal "?p : ((P <-> Q) <-> R)  -->  ~~(P <-> (Q <-> R))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem 13.  Distributive law"
schematic_goal "?p : P | (Q & R)  <-> (P | Q) & (P | R)"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem ~~14"
schematic_goal "?p : ~~((P <-> Q) <-> ((Q | ~P) & (~Q|P)))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem ~~15"
schematic_goal "?p : ~~((P --> Q) <-> (~P | Q))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem ~~16"
schematic_goal "?p : ~~((P-->Q) | (Q-->P))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem ~~17"
schematic_goal "?p : ~~(((P & (Q-->R))-->S) <-> ((~P | Q | S) & (~P | ~R | S)))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)  \<comment> slow


subsection \<open>Examples with quantifiers\<close>

text "The converse is classical in the following implications..."

schematic_goal "?p : (EX x. P(x)-->Q)  -->  (ALL x. P(x)) --> Q"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

schematic_goal "?p : ((ALL x. P(x))-->Q) --> ~ (ALL x. P(x) & ~Q)"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

schematic_goal "?p : ((ALL x. ~P(x))-->Q)  -->  ~ (ALL x. ~ (P(x)|Q))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

schematic_goal "?p : (ALL x. P(x)) | Q  -->  (ALL x. P(x) | Q)"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

schematic_goal "?p : (EX x. P --> Q(x)) --> (P --> (EX x. Q(x)))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)


text "The following are not constructively valid!"
text "The attempt to prove them terminates quickly!"

schematic_goal "?p : ((ALL x. P(x))-->Q) --> (EX x. P(x)-->Q)"
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
  oops

schematic_goal "?p : (P --> (EX x. Q(x))) --> (EX x. P-->Q(x))"
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
  oops

schematic_goal "?p : (ALL x. P(x) | Q) --> ((ALL x. P(x)) | Q)"
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
  oops

schematic_goal "?p : (ALL x. ~~P(x)) --> ~~(ALL x. P(x))"
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
  oops

(*Classically but not intuitionistically valid.  Proved by a bug in 1986!*)
schematic_goal "?p : EX x. Q(x) --> (ALL x. Q(x))"
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
  oops


subsection "Hard examples with quantifiers"

text \<open>
  The ones that have not been proved are not known to be valid!
  Some will require quantifier duplication -- not currently available.
\<close>

text "Problem ~~18"
schematic_goal "?p : ~~(EX y. ALL x. P(y)-->P(x))" oops
(*NOT PROVED*)

text "Problem ~~19"
schematic_goal "?p : ~~(EX x. ALL y z. (P(y)-->Q(z)) --> (P(x)-->Q(x)))" oops
(*NOT PROVED*)

text "Problem 20"
schematic_goal "?p : (ALL x y. EX z. ALL w. (P(x)&Q(y)-->R(z)&S(w)))      
    --> (EX x y. P(x) & Q(y)) --> (EX z. R(z))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem 21"
schematic_goal "?p : (EX x. P-->Q(x)) & (EX x. Q(x)-->P) --> ~~(EX x. P<->Q(x))" oops
(*NOT PROVED*)

text "Problem 22"
schematic_goal "?p : (ALL x. P <-> Q(x))  -->  (P <-> (ALL x. Q(x)))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem ~~23"
schematic_goal "?p : ~~ ((ALL x. P | Q(x))  <->  (P | (ALL x. Q(x))))"
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text "Problem 24"
schematic_goal "?p : ~(EX x. S(x)&Q(x)) & (ALL x. P(x) --> Q(x)|R(x)) &   
     (~(EX x. P(x)) --> (EX x. Q(x))) & (ALL x. Q(x)|R(x) --> S(x))   
    --> ~~(EX x. P(x)&R(x))"
(*Not clear why fast_tac, best_tac, ASTAR and ITER_DEEPEN all take forever*)
  apply (tactic "IntPr.safe_tac @{context}")
  apply (erule impE)
   apply (tactic "IntPr.fast_tac @{context} 1")
  apply (tactic "IntPr.fast_tac @{context} 1")
  done

text "Problem 25"
schematic_goal "?p : (EX x. P(x)) &   
        (ALL x. L(x) --> ~ (M(x) & R(x))) &   
        (ALL x. P(x) --> (M(x) & L(x))) &    
        ((ALL x. P(x)-->Q(x)) | (EX x. P(x)&R(x)))   
    --> (EX x. Q(x)&P(x))"
  by (tactic "IntPr.best_tac @{context} 1")

text "Problem 29.  Essentially the same as Principia Mathematica *11.71"
schematic_goal "?p : (EX x. P(x)) & (EX y. Q(y))   
    --> ((ALL x. P(x)-->R(x)) & (ALL y. Q(y)-->S(y))   <->      
         (ALL x y. P(x) & Q(y) --> R(x) & S(y)))"
  by (tactic "IntPr.fast_tac @{context} 1")

text "Problem ~~30"
schematic_goal "?p : (ALL x. (P(x) | Q(x)) --> ~ R(x)) &  
        (ALL x. (Q(x) --> ~ S(x)) --> P(x) & R(x))   
    --> (ALL x. ~~S(x))"
  by (tactic "IntPr.fast_tac @{context} 1")

text "Problem 31"
schematic_goal "?p : ~(EX x. P(x) & (Q(x) | R(x))) &  
        (EX x. L(x) & P(x)) &  
        (ALL x. ~ R(x) --> M(x))   
    --> (EX x. L(x) & M(x))"
  by (tactic "IntPr.fast_tac @{context} 1")

text "Problem 32"
schematic_goal "?p : (ALL x. P(x) & (Q(x)|R(x))-->S(x)) &  
        (ALL x. S(x) & R(x) --> L(x)) &  
        (ALL x. M(x) --> R(x))   
    --> (ALL x. P(x) & M(x) --> L(x))"
  by (tactic "IntPr.best_tac @{context} 1") \<comment> slow

text "Problem 39"
schematic_goal "?p : ~ (EX x. ALL y. F(y,x) <-> ~F(y,y))"
  by (tactic "IntPr.best_tac @{context} 1")

text "Problem 40.  AMENDED"
schematic_goal "?p : (EX y. ALL x. F(x,y) <-> F(x,x)) -->   
              ~(ALL x. EX y. ALL z. F(z,y) <-> ~ F(z,x))"
  by (tactic "IntPr.best_tac @{context} 1") \<comment> slow

text "Problem 44"
schematic_goal "?p : (ALL x. f(x) -->                                    
              (EX y. g(y) & h(x,y) & (EX y. g(y) & ~ h(x,y))))  &        
              (EX x. j(x) & (ALL y. g(y) --> h(x,y)))                    
              --> (EX x. j(x) & ~f(x))"
  by (tactic "IntPr.best_tac @{context} 1")

text "Problem 48"
schematic_goal "?p : (a=b | c=d) & (a=c | b=d) --> a=d | b=c"
  by (tactic "IntPr.best_tac @{context} 1")

text "Problem 51"
schematic_goal
    "?p : (EX z w. ALL x y. P(x,y) <->  (x=z & y=w)) -->   
     (EX z. ALL x. EX w. (ALL y. P(x,y) <-> y=w) <-> x=z)"
  by (tactic "IntPr.best_tac @{context} 1") \<comment> \<open>60 seconds\<close>

text "Problem 56"
schematic_goal "?p : (ALL x. (EX y. P(y) & x=f(y)) --> P(x)) <-> (ALL x. P(x) --> P(f(x)))"
  by (tactic "IntPr.best_tac @{context} 1")

text "Problem 57"
schematic_goal
    "?p : P(f(a,b), f(b,c)) & P(f(b,c), f(a,c)) &  
     (ALL x y z. P(x,y) & P(y,z) --> P(x,z))    -->   P(f(a,b), f(a,c))"
  by (tactic "IntPr.best_tac @{context} 1")

text "Problem 60"
schematic_goal "?p : ALL x. P(x,f(x)) <-> (EX y. (ALL z. P(z,y) --> P(z,f(x))) & P(x,y))"
  by (tactic "IntPr.best_tac @{context} 1")

end
