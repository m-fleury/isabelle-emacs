(*  Title:   HOL/Ring_and_Field.thy
    ID:      $Id$
    Author:  Gertrud Bauer and Markus Wenzel, TU Muenchen
    License: GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {*
  \title{Ring and field structures}
  \author{Gertrud Bauer and Markus Wenzel}
*}

theory Ring_and_Field = Inductive:

text{*Lemmas and extension to semirings by L. C. Paulson*}

subsection {* Abstract algebraic structures *}

axclass semiring \<subseteq> zero, one, plus, times
  add_assoc: "(a + b) + c = a + (b + c)"
  add_commute: "a + b = b + a"
  left_zero [simp]: "0 + a = a"

  mult_assoc: "(a * b) * c = a * (b * c)"
  mult_commute: "a * b = b * a"
  mult_1 [simp]: "1 * a = a"

  left_distrib: "(a + b) * c = a * c + b * c"
  zero_neq_one [simp]: "0 \<noteq> 1"

axclass ring \<subseteq> semiring, minus
  left_minus [simp]: "- a + a = 0"
  diff_minus: "a - b = a + (-b)"

axclass ordered_semiring \<subseteq> semiring, linorder
  add_left_mono: "a \<le> b ==> c + a \<le> c + b"
  mult_strict_left_mono: "a < b ==> 0 < c ==> c * a < c * b"

axclass ordered_ring \<subseteq> ordered_semiring, ring
  abs_if: "\<bar>a\<bar> = (if a < 0 then -a else a)"

axclass field \<subseteq> ring, inverse
  left_inverse [simp]: "a \<noteq> 0 ==> inverse a * a = 1"
  divide_inverse:      "b \<noteq> 0 ==> a / b = a * inverse b"

axclass ordered_field \<subseteq> ordered_ring, field

axclass division_by_zero \<subseteq> zero, inverse
  inverse_zero: "inverse 0 = 0"
  divide_zero: "a / 0 = 0"


subsection {* Derived rules for addition *}

lemma right_zero [simp]: "a + 0 = (a::'a::semiring)"
proof -
  have "a + 0 = 0 + a" by (simp only: add_commute)
  also have "... = a" by simp
  finally show ?thesis .
qed

lemma add_left_commute: "a + (b + c) = b + (a + (c::'a::semiring))"
  by (rule mk_left_commute [of "op +", OF add_assoc add_commute])

theorems add_ac = add_assoc add_commute add_left_commute

lemma right_minus [simp]: "a + -(a::'a::ring) = 0"
proof -
  have "a + -a = -a + a" by (simp add: add_ac)
  also have "... = 0" by simp
  finally show ?thesis .
qed

lemma right_minus_eq: "(a - b = 0) = (a = (b::'a::ring))"
proof
  have "a = a - b + b" by (simp add: diff_minus add_ac)
  also assume "a - b = 0"
  finally show "a = b" by simp
next
  assume "a = b"
  thus "a - b = 0" by (simp add: diff_minus)
qed

lemma diff_self [simp]: "a - (a::'a::ring) = 0"
  by (simp add: diff_minus)

lemma add_left_cancel [simp]:
     "(a + b = a + c) = (b = (c::'a::ring))"
proof
  assume eq: "a + b = a + c"
  then have "(-a + a) + b = (-a + a) + c"
    by (simp only: eq add_assoc)
  thus "b = c" by simp
next
  assume eq: "b = c"
  thus "a + b = a + c" by simp
qed

lemma add_right_cancel [simp]:
     "(b + a = c + a) = (b = (c::'a::ring))"
  by (simp add: add_commute)

lemma minus_minus [simp]: "- (- (a::'a::ring)) = a"
  proof (rule add_left_cancel [of "-a", THEN iffD1])
    show "(-a + -(-a) = -a + a)"
    by simp
  qed

lemma equals_zero_I: "a+b = 0 ==> -a = (b::'a::ring)"
apply (rule right_minus_eq [THEN iffD1, symmetric])
apply (simp add: diff_minus add_commute) 
done

lemma minus_zero [simp]: "- 0 = (0::'a::ring)"
by (simp add: equals_zero_I)

lemma neg_equal_iff_equal [simp]: "(-a = -b) = (a = (b::'a::ring))" 
  proof 
    assume "- a = - b"
    then have "- (- a) = - (- b)"
      by simp
    thus "a=b" by simp
  next
    assume "a=b"
    thus "-a = -b" by simp
  qed

lemma neg_equal_0_iff_equal [simp]: "(-a = 0) = (a = (0::'a::ring))"
by (subst neg_equal_iff_equal [symmetric], simp)

lemma neg_0_equal_iff_equal [simp]: "(0 = -a) = (0 = (a::'a::ring))"
by (subst neg_equal_iff_equal [symmetric], simp)


subsection {* Derived rules for multiplication *}

lemma mult_1_right [simp]: "a * (1::'a::semiring) = a"
proof -
  have "a * 1 = 1 * a" by (simp add: mult_commute)
  also have "... = a" by simp
  finally show ?thesis .
qed

lemma mult_left_commute: "a * (b * c) = b * (a * (c::'a::semiring))"
  by (rule mk_left_commute [of "op *", OF mult_assoc mult_commute])

theorems mult_ac = mult_assoc mult_commute mult_left_commute

lemma right_inverse [simp]: "a \<noteq> 0 ==>  a * inverse (a::'a::field) = 1"
proof -
  have "a * inverse a = inverse a * a" by (simp add: mult_ac)
  also assume "a \<noteq> 0"
  hence "inverse a * a = 1" by simp
  finally show ?thesis .
qed

lemma right_inverse_eq: "b \<noteq> 0 ==> (a / b = 1) = (a = (b::'a::field))"
proof
  assume neq: "b \<noteq> 0"
  {
    hence "a = (a / b) * b" by (simp add: divide_inverse mult_ac)
    also assume "a / b = 1"
    finally show "a = b" by simp
  next
    assume "a = b"
    with neq show "a / b = 1" by (simp add: divide_inverse)
  }
qed

lemma divide_self [simp]: "a \<noteq> 0 ==> a / (a::'a::field) = 1"
  by (simp add: divide_inverse)

lemma mult_left_zero [simp]: "0 * a = (0::'a::ring)"
proof -
  have "0*a + 0*a = 0*a + 0"
    by (simp add: left_distrib [symmetric])
  thus ?thesis by (simp only: add_left_cancel)
qed

lemma mult_right_zero [simp]: "a * 0 = (0::'a::ring)"
  by (simp add: mult_commute)


subsection {* Distribution rules *}

lemma right_distrib: "a * (b + c) = a * b + a * (c::'a::semiring)"
proof -
  have "a * (b + c) = (b + c) * a" by (simp add: mult_ac)
  also have "... = b * a + c * a" by (simp only: left_distrib)
  also have "... = a * b + a * c" by (simp add: mult_ac)
  finally show ?thesis .
qed

theorems ring_distrib = right_distrib left_distrib

lemma minus_add_distrib [simp]: "- (a + b) = -a + -(b::'a::ring)"
apply (rule equals_zero_I)
apply (simp add: add_ac) 
done

lemma minus_mult_left: "- (a * b) = (-a) * (b::'a::ring)"
apply (rule equals_zero_I)
apply (simp add: left_distrib [symmetric]) 
done

lemma minus_mult_right: "- (a * b) = a * -(b::'a::ring)"
apply (rule equals_zero_I)
apply (simp add: right_distrib [symmetric]) 
done

lemma right_diff_distrib: "a * (b - c) = a * b - a * (c::'a::ring)"
by (simp add: right_distrib diff_minus 
              minus_mult_left [symmetric] minus_mult_right [symmetric]) 


subsection {* Ordering rules *}

lemma add_right_mono: "a \<le> (b::'a::ordered_semiring) ==> a + c \<le> b + c"
by (simp add: add_commute [of _ c] add_left_mono)

text {* non-strict, in both arguments *}
lemma add_mono: "[|a \<le> b;  c \<le> d|] ==> a + c \<le> b + (d::'a::ordered_semiring)"
  apply (erule add_right_mono [THEN order_trans])
  apply (simp add: add_commute add_left_mono)
  done

lemma le_imp_neg_le:
   assumes "a \<le> (b::'a::ordered_ring)" shows "-b \<le> -a"
  proof -
  have "-a+a \<le> -a+b"
    by (rule add_left_mono) 
  then have "0 \<le> -a+b"
    by simp
  then have "0 + (-b) \<le> (-a + b) + (-b)"
    by (rule add_right_mono) 
  thus ?thesis
    by (simp add: add_assoc)
  qed

lemma neg_le_iff_le [simp]: "(-b \<le> -a) = (a \<le> (b::'a::ordered_ring))"
  proof 
    assume "- b \<le> - a"
    then have "- (- a) \<le> - (- b)"
      by (rule le_imp_neg_le)
    thus "a\<le>b" by simp
  next
    assume "a\<le>b"
    thus "-b \<le> -a" by (rule le_imp_neg_le)
  qed

lemma neg_le_0_iff_le [simp]: "(-a \<le> 0) = (0 \<le> (a::'a::ordered_ring))"
by (subst neg_le_iff_le [symmetric], simp)

lemma neg_0_le_iff_le [simp]: "(0 \<le> -a) = (a \<le> (0::'a::ordered_ring))"
by (subst neg_le_iff_le [symmetric], simp)

lemma neg_less_iff_less [simp]: "(-b < -a) = (a < (b::'a::ordered_ring))"
by (force simp add: order_less_le) 

lemma neg_less_0_iff_less [simp]: "(-a < 0) = (0 < (a::'a::ordered_ring))"
by (subst neg_less_iff_less [symmetric], simp)

lemma neg_0_less_iff_less [simp]: "(0 < -a) = (a < (0::'a::ordered_ring))"
by (subst neg_less_iff_less [symmetric], simp)

lemma mult_strict_right_mono:
     "[|a < b; 0 < c|] ==> a * c < b * (c::'a::ordered_semiring)"
by (simp add: mult_commute [of _ c] mult_strict_left_mono)

lemma mult_left_mono:
     "[|a \<le> b; 0 \<le> c|] ==> c * a \<le> c * (b::'a::ordered_ring)"
  apply (case_tac "c=0", simp)
  apply (force simp add: mult_strict_left_mono order_le_less) 
  done

lemma mult_right_mono:
     "[|a \<le> b; 0 \<le> c|] ==> a*c \<le> b * (c::'a::ordered_ring)"
  by (simp add: mult_left_mono mult_commute [of _ c]) 

lemma mult_strict_left_mono_neg:
     "[|b < a; c < 0|] ==> c * a < c * (b::'a::ordered_ring)"
apply (drule mult_strict_left_mono [of _ _ "-c"])
apply (simp_all add: minus_mult_left [symmetric]) 
done

lemma mult_strict_right_mono_neg:
     "[|b < a; c < 0|] ==> a * c < b * (c::'a::ordered_ring)"
apply (drule mult_strict_right_mono [of _ _ "-c"])
apply (simp_all add: minus_mult_right [symmetric]) 
done

lemma mult_left_mono_neg:
     "[|b \<le> a; c \<le> 0|] ==> c * a \<le> c * (b::'a::ordered_ring)"
apply (drule mult_left_mono [of _ _ "-c"]) 
apply (simp_all add: minus_mult_left [symmetric]) 
done

lemma mult_right_mono_neg:
     "[|b \<le> a; c \<le> 0|] ==> a * c \<le> b * (c::'a::ordered_ring)"
  by (simp add: mult_left_mono_neg mult_commute [of _ c]) 

text{*Strict monotonicity in both arguments*}
lemma mult_strict_mono:
     "[|a<b; c<d; 0<b; 0<c|] ==> a * c < b * (d::'a::ordered_semiring)"
apply (erule mult_strict_right_mono [THEN order_less_trans], assumption)
apply (erule mult_strict_left_mono, assumption)
done

lemma mult_mono:
     "[|a \<le> b; c \<le> d; 0 \<le> b; 0 \<le> c|] 
      ==> a * c  \<le>  b * (d::'a::ordered_ring)"
apply (erule mult_right_mono [THEN order_trans], assumption)
apply (erule mult_left_mono, assumption)
done


subsection{*Cancellation Laws for Relationships With a Common Factor*}

text{*Cancellation laws for @{term "c*a < c*b"} and @{term "a*c < b*c"},
   also with the relations @{text "\<le>"} and equality.*}

lemma mult_less_cancel_right:
    "(a*c < b*c) = ((0 < c & a < b) | (c < 0 & b < (a::'a::ordered_ring)))"
apply (case_tac "c = 0")
apply (auto simp add: linorder_neq_iff mult_strict_right_mono 
                      mult_strict_right_mono_neg)
apply (auto simp add: linorder_not_less 
                      linorder_not_le [symmetric, of "a*c"]
                      linorder_not_le [symmetric, of a])
apply (erule_tac [!] notE)
apply (auto simp add: order_less_imp_le mult_right_mono 
                      mult_right_mono_neg)
done

lemma mult_less_cancel_left:
    "(c*a < c*b) = ((0 < c & a < b) | (c < 0 & b < (a::'a::ordered_ring)))"
by (simp add: mult_commute [of c] mult_less_cancel_right)

lemma mult_le_cancel_right:
     "(a*c \<le> b*c) = ((0<c --> a\<le>b) & (c<0 --> b \<le> (a::'a::ordered_ring)))"
by (simp add: linorder_not_less [symmetric] mult_less_cancel_right)

lemma mult_le_cancel_left:
     "(c*a \<le> c*b) = ((0<c --> a\<le>b) & (c<0 --> b \<le> (a::'a::ordered_ring)))"
by (simp add: mult_commute [of c] mult_le_cancel_right)

text{*Cancellation of equalities with a common factor*}
lemma mult_cancel_right [simp]:
     "(a*c = b*c) = (c = (0::'a::ordered_ring) | a=b)"
apply (cut_tac linorder_less_linear [of 0 c])
apply (force dest: mult_strict_right_mono_neg mult_strict_right_mono
             simp add: linorder_neq_iff)
done

lemma mult_cancel_left [simp]:
     "(c*a = c*b) = (c = (0::'a::ordered_ring) | a=b)"
by (simp add: mult_commute [of c] mult_cancel_right)


subsection{* Products of Signs *}

lemma mult_pos: "[| (0::'a::ordered_ring) < a; 0 < b |] ==> 0 < a*b"
by (drule mult_strict_left_mono [of 0 b], auto)

lemma mult_pos_neg: "[| (0::'a::ordered_ring) < a; b < 0 |] ==> a*b < 0"
by (drule mult_strict_left_mono [of b 0], auto)

lemma mult_neg: "[| a < (0::'a::ordered_ring); b < 0 |] ==> 0 < a*b"
by (drule mult_strict_right_mono_neg, auto)

lemma zero_less_mult_pos: "[| 0 < a*b; 0 < a|] ==> 0 < (b::'a::ordered_ring)"
apply (case_tac "b\<le>0") 
 apply (auto simp add: order_le_less linorder_not_less)
apply (drule_tac mult_pos_neg [of a b]) 
 apply (auto dest: order_less_not_sym)
done

lemma zero_less_mult_iff:
     "((0::'a::ordered_ring) < a*b) = (0 < a & 0 < b | a < 0 & b < 0)"
apply (auto simp add: order_le_less linorder_not_less mult_pos mult_neg)
apply (blast dest: zero_less_mult_pos) 
apply (simp add: mult_commute [of a b]) 
apply (blast dest: zero_less_mult_pos) 
done

lemma mult_eq_0_iff [simp]: "(a*b = (0::'a::ordered_ring)) = (a = 0 | b = 0)"
apply (case_tac "a < 0")
apply (auto simp add: linorder_not_less order_le_less linorder_neq_iff)
apply (force dest: mult_strict_right_mono_neg mult_strict_right_mono)+
done

lemma zero_le_mult_iff:
     "((0::'a::ordered_ring) \<le> a*b) = (0 \<le> a & 0 \<le> b | a \<le> 0 & b \<le> 0)"
by (auto simp add: eq_commute [of 0] order_le_less linorder_not_less
                   zero_less_mult_iff)

lemma mult_less_0_iff:
     "(a*b < (0::'a::ordered_ring)) = (0 < a & b < 0 | a < 0 & 0 < b)"
apply (insert zero_less_mult_iff [of "-a" b]) 
apply (force simp add: minus_mult_left[symmetric]) 
done

lemma mult_le_0_iff:
     "(a*b \<le> (0::'a::ordered_ring)) = (0 \<le> a & b \<le> 0 | a \<le> 0 & 0 \<le> b)"
apply (insert zero_le_mult_iff [of "-a" b]) 
apply (force simp add: minus_mult_left[symmetric]) 
done

lemma zero_le_square: "(0::'a::ordered_ring) \<le> a*a"
by (simp add: zero_le_mult_iff linorder_linear) 

lemma zero_less_one: "(0::'a::ordered_ring) < 1"
apply (insert zero_le_square [of 1]) 
apply (simp add: order_less_le) 
done


subsection {* Absolute Value *}

text{*But is it really better than just rewriting with @{text abs_if}?*}
lemma abs_split:
     "P(abs(a::'a::ordered_ring)) = ((0 \<le> a --> P a) & (a < 0 --> P(-a)))"
by (force dest: order_less_le_trans simp add: abs_if linorder_not_less)

lemma abs_zero [simp]: "abs 0 = (0::'a::ordered_ring)"
by (simp add: abs_if)

lemma abs_mult: "abs (x * y) = abs x * abs (y::'a::ordered_ring)" 
apply (case_tac "x=0 | y=0", force) 
apply (auto elim: order_less_asym
            simp add: abs_if mult_less_0_iff linorder_neq_iff
                  minus_mult_left [symmetric] minus_mult_right [symmetric])  
done

lemma abs_eq_0 [simp]: "(abs x = 0) = (x = (0::'a::ordered_ring))"
by (simp add: abs_if)

lemma zero_less_abs_iff [simp]: "(0 < abs x) = (x ~= (0::'a::ordered_ring))"
by (simp add: abs_if linorder_neq_iff)


subsection {* Fields *}


end
