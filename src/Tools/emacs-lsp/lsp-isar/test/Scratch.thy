theory Scratch
imports Main
begin

lemma \<open>\<forall>x. P x\<close>
  oops

text \<open>This is another test.
  There are multiple things to do.
  \<close>

notepad
begin
  fix S T :: 'a
  have \<open>T = S\<close>
    if \<open>S = T\<close>
    for S
    using that
    by auto

  have \<open>T = S\<close>
    if \<open>S = T\<close>
    for S
    unfolding that
    by auto
end

datatype finite_type = A | B

instantiation finite_type :: finite
begin
lemma UNIV_finite_type: \<open>UNIV = {A, B}\<close>
  apply auto
  using finite_type.exhaust by blast

instance
  apply standard
  unfolding UNIV_finite_type
  apply auto
  done
end

proposition
  fixes x
  assumes
    \<open>P x\<close> and
    \<open>Q x\<close>
  obtains y z where
    \<open>y = P x\<close> and
    \<open>z = Q x\<close> and
    \<open>True\<close>
  using TrueI
  oops

lemma \<open>P x\<close>
proof -
  have \<open>P x\<close>
    if \<open>P x\<close>
    for x
  proof -
    have \<open>P x\<close>
      if \<open>P x\<close>
      for x
      by (use that in auto)
    have \<open>True\<close>
      by auto
    show ?thesis
      using that by auto
  qed
  then show \<open>?thesis\<close>
    oops

lemma \<open>True\<close>
  ..

lemma \<open>P x\<close> if \<open>P x\<close>
proof -
  show \<open>P x\<close>
    by (use that in auto)
qed

lemma \<open>P x\<close> for x :: \<open>nat list\<close>
proof (induction x)
  case Nil
  then show ?case sorry
next
  case (Cons a x)
  have H: \<open>P \<Longrightarrow> P\<close> for P
    by auto
  show ?case
    apply -
    apply (rule H)
    sorry
qed


lemma \<open>P x\<close> for x :: \<open>nat list\<close>
proof -
  show \<open>P x\<close> for x
  proof (induction x)
    case Nil
    then show ?case sorry
  next
    case (Cons a x)
    then show ?case sorry
  qed
qed

section \<open>There is more\<close>
subsection \<open>Indented to the right\<close>

notepad
begin
  have P if "P ==> P" for P
    apply (rule that)
    subgoal sorry
    done
end

lemma name_with_boundary: \<open>P \<Longrightarrow> P\<close>
  by auto

lemma \<open>P \<Longrightarrow> P\<close>
  apply (rule
    name_with_boundary)
  oops


section \<open>Known indentation bugs\<close>
notepad
begin
  have P if "P \<Longrightarrow> P" "P" for P
    apply (rule that)
    subgoal apply (rule that(2))
    done \<comment> \<open>This done is wrong, but I cannot fix it without knowdegde from the goals.\<close>
    done
end

text \<open>The labels in the following predicate is wrongly indented, but jEdit is not better:\<close>
inductive rtranclp :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> for r :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  base:
  \<open>rtranclp r a a\<close> |
  step:
  \<open>rtranclp r a c\<close>
  if
    \<open>r a b\<close>
    \<open>rtranclp r b c\<close>


section \<open>Test part\<close>

lemma False
  by auto

lemma True
  by simp

lemma True
  by simp

end
