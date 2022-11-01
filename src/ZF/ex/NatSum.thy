(*  Title:      ZF/ex/NatSum.thy
    Author:     Tobias Nipkow & Lawrence C Paulson

A summation operator. sum(f,n+1) is the sum of all f(i), i=0...n.

Note: n is a natural number but the sum is an integer,
                            and f maps integers to integers

Summing natural numbers, squares, cubes, etc.

Originally demonstrated permutative rewriting, but add_ac is no longer needed
  thanks to new simprocs.

Thanks to Sloane's On-Line Encyclopedia of Integer Sequences,
  http://www.research.att.com/\<not>njas/sequences/
*)


theory NatSum imports ZF begin

consts sum :: "[i\<Rightarrow>i, i] \<Rightarrow> i"
primrec 
  "sum (f,0) = #0"
  "sum (f, succ(n)) = f($#n) $+ sum(f,n)"

declare zadd_zmult_distrib [simp]  zadd_zmult_distrib2 [simp]
declare zdiff_zmult_distrib [simp] zdiff_zmult_distrib2 [simp]

(*The sum of the first n odd numbers equals n squared.*)
lemma sum_of_odds: "n \<in> nat \<Longrightarrow> sum (\<lambda>i. i $+ i $+ #1, n) = $#n $* $#n"
by (induct_tac "n", auto)

(*The sum of the first n odd squares*)
lemma sum_of_odd_squares:
     "n \<in> nat \<Longrightarrow> #3 $* sum (\<lambda>i. (i $+ i $+ #1) $* (i $+ i $+ #1), n) =  
      $#n $* (#4 $* $#n $* $#n $- #1)"
by (induct_tac "n", auto)

(*The sum of the first n odd cubes*)
lemma sum_of_odd_cubes:
     "n \<in> nat  
      \<Longrightarrow> sum (\<lambda>i. (i $+ i $+ #1) $* (i $+ i $+ #1) $* (i $+ i $+ #1), n) =  
          $#n $* $#n $* (#2 $* $#n $* $#n $- #1)"
by (induct_tac "n", auto)

(*The sum of the first n positive integers equals n(n+1)/2.*)
lemma sum_of_naturals:
     "n \<in> nat \<Longrightarrow> #2 $* sum(\<lambda>i. i, succ(n)) = $#n $* $#succ(n)"
by (induct_tac "n", auto)

lemma sum_of_squares:
     "n \<in> nat \<Longrightarrow> #6 $* sum (\<lambda>i. i$*i, succ(n)) =  
                  $#n $* ($#n $+ #1) $* (#2 $* $#n $+ #1)"
by (induct_tac "n", auto)

lemma sum_of_cubes:
     "n \<in> nat \<Longrightarrow> #4 $* sum (\<lambda>i. i$*i$*i, succ(n)) =  
                  $#n $* $#n $* ($#n $+ #1) $* ($#n $+ #1)"
by (induct_tac "n", auto)

(** Sum of fourth powers **)

lemma sum_of_fourth_powers:
     "n \<in> nat \<Longrightarrow> #30 $* sum (\<lambda>i. i$*i$*i$*i, succ(n)) =  
                    $#n $* ($#n $+ #1) $* (#2 $* $#n $+ #1) $*  
                    (#3 $* $#n $* $#n $+ #3 $* $#n $- #1)"
by (induct_tac "n", auto)

end
