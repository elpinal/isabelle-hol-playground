theory Chapter3
imports Chapter1And2
begin

locale open_cover = topological_space +
  fixes F :: "'a set set"
  assumes F_opens: "F \<subseteq> opens"
  and covers: "\<Union>F = carrier"

locale subcover = super: open_cover +
  fixes S :: "'a set set"
  assumes "S \<subseteq> F"
  and covers: "\<Union>S = carrier"

locale compact_space = topological_space +
  assumes every_cover_has_finite_subcover: "\<lbrakk>open_cover carrier opens F\<rbrakk> \<Longrightarrow> \<exists>S. subcover carrier opens F S \<and> finite S"

end
