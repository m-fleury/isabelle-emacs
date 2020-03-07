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

end
