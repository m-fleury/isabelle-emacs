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


end
