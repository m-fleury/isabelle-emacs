theory Scrath_With_A_Very_Very_Very_Long_Name
imports Main
begin
lemma False
  try0
  oops


lemma
  \<open>False \<close>
  if \<open>\<And>P. P \<Longrightarrow> P\<close>
  apply (rule that)
  sorry
    thm impI
end 