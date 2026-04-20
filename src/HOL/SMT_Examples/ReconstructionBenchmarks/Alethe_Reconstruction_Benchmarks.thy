theory Alethe_Reconstruction_Benchmarks

imports Main

begin

declare [[smt_trace=false,smt_statistics=true,smt_verbose=false]]

(* and pos *)

lemma and_pos_62: "\<bar>x :: real\<bar> + \<bar>y\<bar> \<ge> \<bar>x + y\<bar>" supply[[smt_trace=false,smt_verbose=false]] by (smt (cvc5_proof)) 

(* ---------------------------------------- *)

experiment
begin

lemma and_pos_115:
 "eq_set (List.coset xs) (set ys) = rhs"
    if "\<And>ys. subset' (List.coset xs) (set ys) = (let n = card (UNIV::'a set) in 0 < n \<and> card (set (xs @ ys)) = n)"
      and "\<And>uu A. (uu::'a) \<in> - A \<Longrightarrow> uu \<notin> A"
      and "\<And>uu. card (set (uu::'a list)) = length (remdups uu)"
      and "\<And>uu. finite (set (uu::'a list))"
      and "\<And>uu. (uu::'a) \<in> UNIV"
      and "(UNIV::'a set) \<noteq> {}"
      and "\<And>c A B P. \<lbrakk>(c::'a) \<in> A \<union> B; c \<in> A \<Longrightarrow> P; c \<in> B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
      and "\<And>a b. (a::nat) + b = b + a"
      and "\<And>a b. ((a::nat) = a + b) = (b = 0)"
      and "card' (set xs) = length (remdups xs)"
      and "card' = (card :: 'a set \<Rightarrow> nat)"
      and "\<And>A B. \<lbrakk>finite (A::'a set); finite B\<rbrakk> \<Longrightarrow> card A + card B = card (A \<union> B) + card (A \<inter> B)"
      and "\<And>A. (card (A::'a set) = 0) = (A = {} \<or> infinite A)"
      and "\<And>A. \<lbrakk>finite (UNIV::'a set); card (A::'a set) = card (UNIV::'a set)\<rbrakk> \<Longrightarrow> A = UNIV"
      and "\<And>xs. - List.coset (xs::'a list) = set xs"
      and "\<And>xs. - set (xs::'a list) = List.coset xs"
      and "\<And>A B. (A \<inter> B = {}) = (\<forall>x. (x::'a) \<in> A \<longrightarrow> x \<notin> B)"
      and "eq_set = (=)"
      and "\<And>A. finite (A::'a set) \<Longrightarrow> finite (- A) = finite (UNIV::'a set)"
      and "rhs \<equiv> let n = card (UNIV::'a set) in if n = 0 then False else let xs' = remdups xs; ys' = remdups ys in length xs' + length ys' = n \<and> (\<forall>x\<in>set xs'. x \<notin> set ys') \<and> (\<forall>y\<in>set ys'. y \<notin> set xs')"
      and "\<And>xs ys. set ((xs::'a list) @ ys) = set xs \<union> set ys"
      and "\<And>A B. ((A::'a set) = B) = (A \<subseteq> B \<and> B \<subseteq> A)"
      and "\<And>xs. set (remdups (xs::'a list)) = set xs"
      and "subset' = (\<subseteq>)"
      and "\<And>A B. (\<And>x. (x::'a) \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
      and "\<And>A B. \<lbrakk>(A::'a set) \<subseteq> B; B \<subseteq> A\<rbrakk> \<Longrightarrow> A = B"
      and "\<And>A ys. (A \<subseteq> List.coset ys) = (\<forall>y\<in>set ys. (y::'a) \<notin> A)"
  using that by (smt (cvc5_proof)) 
end

(* ---------------------------------------- *)

context
  fixes
   round_up :: "int \<Rightarrow> real \<Rightarrow> real"and
   round_down :: "int \<Rightarrow> real \<Rightarrow> real" and
   powr :: \<open>real \<Rightarrow> real \<Rightarrow> real\<close> (infix "powr" 80)
  assumes powr_gt_zero: \<open>\<And>a b :: real. 0 < x powr a \<longleftrightarrow> x \<noteq> 0\<close>
   and powr_minus_divide: "\<And>a x :: real. x powr (- a) = 1/(x powr a)"
   and round_up_diff_round_down: \<open>\<And>prec (x::real). round_up prec x - round_down prec x
    \<le> 2 powr (- real_of_int prec)\<close> 
   and round_down_uminus_eq: \<open>\<And>prec x. round_down p (- x) = - round_up p x\<close>
   and round_up: \<open>\<And>prec x. x \<le> round_up prec x\<close>
   and round_up_diff_round_down: \<open>\<And>prec x. round_up prec x - round_down prec x \<le> 2 powr (- real_of_int prec)\<close>

begin

lemma and_pos_378:
  assumes "x < 1 / 2" \<open>p > 0\<close>
     \<open>1 / 2 * 2 powr real_of_int p \<le> 2 powr real_of_int p - 1\<close> 
     \<open>x * 2 powr real_of_int p < 1 / 2 * 2 powr real_of_int p\<close>
  shows "round_up p x < 1"
  using comm_semiring_class.distrib divide_divide_eq_right
 mult.assoc mult.commute mult_cancel_left1 mult_cancel_right mult_cancel_right2
 mult_less_cancel_left_pos mult_minus_left nonzero_eq_divide_eq nonzero_mult_div_cancel_left
 nonzero_mult_div_cancel_right powr_gt_zero powr_minus_divide round_down_uminus_eq
 round_up round_up_diff_round_down times_divide_eq_right assms
   supply [[smt_trace]] by (smt (cvc5))
end

(* ---------------------------------------- *)

context
  fixes centered_divide :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>  (infixl \<open>cdiv\<close> 70) and
    centered_modulo :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close>  (infixl \<open>cmod\<close> 70)
begin

declare[[cvc5_options="--dag-thres=0 --proof-format-mode=alethe --proof-granularity=dsl-rewrite --proof-alethe-experimental --proof-prune-input --full-saturate-quant --proof-alethe-define-skolems --proof-elim-subtypes --no-stats --sat-random-seed=1 --lang=smt2"]]
lemma and_pos_407 [simp]:
  assumes
       "\<forall>(b::int) (a::int) c::int. b * (a div b) + a mod b + c = a + c"
       "\<forall>k::int. k cdiv (0::int) = (0::int)"
       "\<forall>(k::int) l::int. k cdiv l * l + k cmod l = k"
       "\<forall>(k::int) l::int.
          k cmod l = (k + (if l < (0::int) then - l else l) div (2::int)) mod (if l < (0::int) then - l else l) - (if l < (0::int) then - l else l) div (2::int)"
       "\<forall>(A::int) n::int. A = A div n * n + A mod n"
       "\<forall>a::int. even a = (a mod (2::int) = (0::int))"
       "\<forall>k::int. ((0::int) \<le> k div (2::int)) = ((0::int) \<le> k)"
       "\<forall>(k::int) l::int. (0::int) \<le> k \<and> k < l \<longrightarrow> k mod l = k"
       "\<forall>(c::int) b::int. (c = b * c) = (c = (0::int) \<or> b = (1::int))"
       "\<forall>(a::int) b::int. a \<noteq> (0::int) \<longrightarrow> a * b div a = b"
       "\<forall>a::int. odd a = (a mod (2::int) = (1::int))"
       shows
  \<open>0 cdiv k = 0\<close>
    by (smt (cvc5) assms)
end

(* 
Old 
or_neg: 34 occurrences, 1 ms 1/4th time, 1 ms mean time, 2 ms 3/4th time, 2 ms maximum time, 38 ms total time
and_pos: 62 occurrences, 0 ms 1/4th time, 0 ms mean time, 1 ms 3/4th time, 1 ms maximum time, 31 ms total time

or_neg: 39 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 5 ms total time
and_pos: 102 occurrences, 0 ms 1/4th time, 0 ms mean time, 1 ms 3/4th time, 2 ms maximum time, 35 ms total time

or_neg: 225 occurrences, 3 ms 1/4th time, 9 ms mean time, 29 ms 3/4th time, 35 ms maximum time, 3037 ms total time
and_pos: 378 occurrences, 2 ms 1/4th time, 4 ms mean time, 13 ms 3/4th time, 15 ms maximum time, 2288 ms total time

or_neg: 196 occurrences, 0 ms 1/4th time, 1 ms mean time, 1 ms 3/4th time, 2 ms maximum time, 143 ms total time
and_pos: 407 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 23 ms total time
*)
(* 
New 
or_neg: 34 occurrences, 1 ms 1/4th time, 1 ms mean time, 1 ms 3/4th time, 1 ms maximum time, 28 ms total time
and_pos: 62 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 11 ms total time

or_neg: 39 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 4 ms total time
and_pos: 102 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 23 ms total time

or_neg: 225 occurrences, 3 ms 1/4th time, 8 ms mean time, 21 ms 3/4th time, 47 ms maximum time, 2516 ms total time
and_pos: 378 occurrences, 2 ms 1/4th time, 4 ms mean time, 9 ms 3/4th time, 14 ms maximum time, 2121 ms total time

or_neg: 196 occurrences, 0 ms 1/4th time, 1 ms mean time, 1 ms 3/4th time, 2 ms maximum time, 133 ms total time
and_pos: 407 occurrences, 0 ms 1/4th time, 0 ms mean time, 0 ms 3/4th time, 1 ms maximum time, 27 ms total time
*)

end