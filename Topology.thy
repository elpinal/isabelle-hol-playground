theory Topology
  imports Main HOL.Real "HOL-Library.FuncSet"
begin

locale topological_space =
  fixes carrier :: "'a set"
  and opens :: "'a set set"
  assumes open_subsets [intro]: "opens ⊆ Pow carrier"
  and union_closed [intro]: "⟦ A ⊆ opens ⟧ ⟹ ⋃ A ∈ opens"
  and binary_inter_closed [intro]: "⟦ X ∈ opens; Y ∈ opens ⟧ ⟹ (X ∩ Y) ∈ opens"
  and nullary_inter_closed [intro, simp]: "carrier ∈ opens"
begin

lemma empty_set_is_open [intro, simp]: "{} ∈ opens"
proof -
  from union_closed[of "{}"] have "⋃ {} ∈ opens" by simp
  thus ?thesis by simp
qed

lemma point_in_open_is_in_carrier [intro, simp]:
  fixes x U
  assumes "x ∈ U"
  and "U ∈ opens"
  shows "x ∈ carrier"
proof
  from assms show "x ∈ U" by auto
next
  from assms show "U ⊆ carrier"
    using open_subsets by auto
qed

lemma binary_union_closed:
  assumes "X ∈ opens"
  and "Y ∈ opens"
  shows "(X ∪ Y) ∈ opens"
proof -
  have "{X, Y} ⊆ opens" using assms by auto
  then have "⋃ {X, Y} ∈ opens" by (fact union_closed)
  then show ?thesis by auto
qed

definition closed_sets :: "'a set set" where
"closed_sets = {carrier - U | U. U ∈ opens}"

lemma closed_subsets [intro]: "closed_sets ⊆ Pow carrier"
  by (auto simp: closed_sets_def)

end

locale indiscrete_space =
  fixes S :: "'a set"

sublocale indiscrete_space ⊆ topological_space S "{{}, S}"
  by unfold_locales auto

locale discrete_space =
  fixes S :: "'a set"

sublocale discrete_space ⊆ topological_space S "Pow S"
  by unfold_locales auto

locale map =
  fixes α :: "'a => 'b"
  and S :: "'a set"
  and T :: "'b set"
  assumes "α ∈ S →⇩E T"

locale continuous_function =
  map α X Y +
  source: topological_space X OX +
  target: topological_space Y OY
  for α :: "'a => 'b"
  and X Y OX OY +
  assumes preimages_are_open: "[| U ∈ OY |] ==> α -` U ∩ X ∈ OX"
  (* Preimages may be larger than X, so we need to use intersection. *)

locale empty_space

sublocale empty_space ⊆ topological_space "{}" "{{}}"
  by unfold_locales auto

(* TODO: uniqueness *)
locale empty_space_is_initial = target: topological_space
begin
sublocale continuous_function
  where X = "{}"
    and OX = "{{}}"
    and Y = carrier
    and OY = opens
    and α = "λ x. undefined"
  by (unfold_locales, auto)
end

locale singleton_space =
  fixes x :: "'a"

sublocale singleton_space ⊆ topological_space "{x}" "{{}, {x}}"
  by unfold_locales auto

(* TODO: uniqueness *)
locale singleton_space_is_terminal =
  target: singleton_space + source: topological_space
begin
sublocale continuous_function
  where X = carrier
    and OX = opens
    and Y = "{x}"
    and OY = "{{}, {x}}"
    and α = "λv ∈ carrier. x"
proof (unfold_locales, auto)
  have "(λv∈carrier. x) -` {x} ∩ carrier = carrier" by auto
  thus "(λv∈carrier. x) -` {x} ∩ carrier ∈ opens" by auto
qed
end

locale subspace =
  super: topological_space X OX
  for S X OX +
  assumes sub: "S ⊆ X"
begin
sublocale topological_space S "{U ∩ S | U. U ∈ OX}" (* (λU. U ∩ S) ` OX *)
proof (unfold_locales, blast)
  (* https://proofwiki.org/wiki/Topological_Subspace_is_Topological_Space *)
  fix A :: "'a set set"
  assume 0: "A ⊆ {U ∩ S | U. U ∈ OX}"
  let ?A1 = "{V ∈ OX. V ∩ S ⊆ ⋃ A}"
  let ?U1 = "⋃ ?A1"
  have "?U1 ∈ OX" by auto
  have "?U1 ∩ S = (⋃C ∈ ?A1. C ∩ S)" by (rule Int_Union2)
  have "(⋃C ∈ ?A1. C ∩ S) ⊆ ⋃ A" by auto
  have 1: "C ⊆ ⋃ A" if "C ∈ A" for C
    proof
      fix x :: "'a"
      assume "x ∈ C"
      then show "x ∈ ⋃ A" using `C ∈ A` by auto
    qed
  have 2: "∃V ∈ OX. C = V ∩ S" if "C ∈ A" for C
    proof -
      from 0 `C ∈ A` obtain U where "C = U ∩ S ∧ U ∈ OX" by auto
      then show ?thesis by auto
    qed
  have 4: "∃V ∈ ?A1. C = V ∩ S" if "C ∈ A" for C
    proof -
      from 2 `C ∈ A` obtain U where 3: "U ∈ OX ∧ C = U ∩ S" by auto
      from this 1 `C ∈ A` have "U ∈ ?A1" by auto
      from this 3 show ?thesis by auto
    qed
  have 5: "V ⊆ ?U1" if "V ∈ ?A1" for V
    proof
      fix x :: "'a"
      assume "x ∈ V"
      then show "x ∈ ?U1" using `V ∈ ?A1` by auto
    qed
  then have "T ⊆ ?U1 ∩ S" if "T ∈ A" for T
    proof -
      from 4 obtain V where 6: "V ∈ ?A1 ∧ T = V ∩ S" using `T ∈ A` by auto
      from 5 this have "V ⊆ ?U1" by auto
      then have "V ∩ S ⊆ ?U1 ∩ S" by (auto simp: Int_mono)
      then show ?thesis using 6 by auto
    qed
  then have 7: "⋃ A ⊆ ?U1 ∩ S" by auto
  have "?U1 ∩ S ⊆ ⋃ A"
    proof
      fix x :: "'a"
      assume 8: "x ∈ ?U1 ∩ S"
      then obtain R where "x ∈ R ∧ R ∈ ?A1" by auto
      then have "x ∈ R ∩ S" "R ∩ S ⊆ ⋃ A" using 8 by auto
      then show "x ∈ ⋃ A" by auto
    qed
  then have "⋃ A = ?U1 ∩ S" using 7 by auto
  then show "⋃ A ∈ {U ∩ S | U. U ∈ OX}" using `?U1 ∈ OX` by auto
next
  fix X Y :: "'a set"
  assume 0: "X ∈ {U ∩ S | U. U ∈ OX}" "Y ∈ {U ∩ S | U. U ∈ OX}"
  then obtain U V where 1: "X = U ∩ S ∧ U ∈ OX" "Y = V ∩ S ∧ V ∈ OX"
    by auto
  then have 2: "U ∩ V ∈ OX" by auto
  from 1 have "X ∩ Y = U ∩ V ∩ S" by auto
  from this 2 show "X ∩ Y ∈ {U ∩ S | U. U ∈ OX}" by auto
next
  have "S = X ∩ S" using sub by auto
  then show "S ∈ {U ∩ S | U. U ∈ OX}" by auto
qed
end

locale alternative_topological_space =
  fixes carrier :: "'a set"
  and neigh :: "'a => 'a set set"
  assumes neigh_carrier [intro, simp]: "neigh ∈ carrier →⇩E Pow (Pow carrier)"
  and at_least_1_neigh [intro, simp]: "[| x ∈ carrier |] ==> neigh x ≠ {}"
  and neigh_of [intro]: "[| x ∈ carrier; N ∈ neigh x |] ==> x ∈ N"
  and inter_closed [intro, simp]: "[| x ∈ carrier; N1 ∈ neigh x; N2 ∈ neigh x |] ==> N1 ∩ N2 ∈ neigh x"
  and enlarge [intro]: "[| x ∈ carrier; N ∈ neigh x; U ⊆ carrier; N ⊆ U |] ==> U ∈ neigh x"
  and interior [intro]: "[| x ∈ carrier; N ∈ neigh x |] ==> { z:N . N ∈ neigh z } ∈ neigh x"

locale alternative_discrete_space =
  fixes S :: "'a set"
begin
sublocale alternative_topological_space "S" "λx∈S. {N : Pow S. x ∈ N}"
  by unfold_locales auto
end

context alternative_topological_space begin

lemma neigh_codomain:
  fixes x
  assumes "x ∈ carrier"
  shows "neigh x ∈ Pow (Pow carrier)"
proof (rule PiE_mem[where ?S = carrier])
  show "neigh ∈ carrier →⇩E Pow (Pow carrier)" by auto
next
  show "x ∈ carrier" by (fact assms)
qed

lemma carrier_is_neigh [simp]:
  assumes "x ∈ carrier"
  shows "carrier ∈ neigh x"
proof -
  from assms have "∃N. N ∈ neigh x" by (auto simp: ex_in_conv)
  then obtain N where 0: "N ∈ neigh x" by auto
  have "neigh x ∈ Pow (Pow carrier)"
    apply (rule PiE_mem[where ?S = "carrier" and ?T = "λ a. Pow (Pow carrier)"])
     apply auto
    apply (rule assms)
    done
  then have "neigh x ⊆ Pow carrier" by simp
  then have "R ∈ neigh x ==> R ∈ Pow carrier" for R by blast
  from this 0 have "N ∈ Pow carrier" by blast
  then have "N ⊆ carrier" by simp
  from assms 0 this show "carrier ∈ neigh x" by (simp add: enlarge)
qed

definition opens :: "'a set set" where
"opens = {U : Pow carrier. ∀x ∈ U. U ∈ neigh x}"

lemma opens_iff:
  shows "U ∈ opens ⟷ U ∈ Pow carrier ∧ (∀x ∈ U. U ∈ neigh x)"
  unfolding opens_def by auto

lemma point_in_alt_open_is_in_carrier [intro, simp]:
  fixes x U
  assumes "x ∈ U"
  and "U ∈ opens"
  shows "x ∈ carrier"
  using assms opens_def by force

theorem topo: "topological_space carrier opens"
  by (unfold_locales, auto simp: opens_def)

end

context topological_space begin

definition neigh :: "'a => 'a set set" where
"neigh = (λ x ∈ carrier. {N:Pow carrier. ∃U ∈ opens. x ∈ U ∧ U ⊆ N})"

lemma neigh_fun: "neigh ∈ carrier →⇩E Pow (Pow carrier)"
proof
  fix x :: "'a"
  assume "x ∈ carrier"
  then have "neigh x ⊆ Pow carrier" unfolding neigh_def by auto
  then show "neigh x ∈ Pow (Pow carrier)" by simp
next
  fix x :: "'a"
  assume "x ∉ carrier"
  then show "neigh x = undefined" unfolding neigh_def by auto
qed

theorem alter: "alternative_topological_space carrier neigh"
proof (unfold_locales)
  show "neigh ∈ carrier →⇩E Pow (Pow carrier)" by (simp add: neigh_fun)
next
  fix x :: "'a"
  assume "x ∈ carrier"
  then have "carrier ∈ neigh x" unfolding neigh_def by auto
  then show "neigh x ≠ {}" by (auto simp: ex_in_conv)
  fix x :: "'a"
  and N
  assume "x ∈ carrier" and "N ∈ neigh x"
  then show "x ∈ N" unfolding neigh_def by auto
next
  fix x :: "'a"
  and N1 N2
  assume 0: "x ∈ carrier"
  and 1: "N1 ∈ neigh x" "N2 ∈ neigh x"
  then obtain U1 U2 where 4: "U1 ∈ opens ∧ x ∈ U1 ∧ U1 ⊆ N1" "U2 ∈ opens ∧ x ∈ U2 ∧ U2 ⊆ N2"
    unfolding neigh_def by auto
  then have "x ∈ U1 ∩ U2 ∧ U1 ∩ U2 ⊆ N1 ∩ N2" by auto
  from this 4 have "U1 ∩ U2 ∈ opens ∧ (x ∈ U1 ∩ U2 ∧ U1 ∩ U2 ⊆ N1 ∩ N2)"
    by (auto simp: binary_inter_closed)
  then have 3: "∃U ∈ opens. x ∈ U ∧ U ⊆ N1 ∩ N2" by (auto simp: bexI[where ?x = "U1 ∩ U2"])
  from 0 1 have 2: "N1 ∈ Pow carrier" "N2 ∈ Pow carrier"
    unfolding neigh_def by auto
  from 2 have "N1 ∩ N2 ∈ Pow carrier"
    by auto
  from this 3 have "N1 ∩ N2 ∈ Pow carrier ∧ (∃U ∈ opens. x ∈ U ∧ U ⊆ N1 ∩ N2)"
    by auto
  from this have "N1 ∩ N2 ∈ {N. N ∈ Pow carrier ∧ (∃U ∈ opens. x ∈ U ∧ U ⊆ N1 ∩ N2)}"
    by (auto simp: CollectI[where ?a = "N1 ∩ N2" and ?P = "λz. z ∈ Pow carrier ∧ (∃U. x ∈ U ∧ U ⊆ N1 ∩ N2)"])
  from this 0 show "N1 ∩ N2 ∈ neigh x" unfolding neigh_def by auto
next
  fix x :: "'a"
    and N U
  assume 4: "x ∈ carrier"
    and 5: "N ∈ neigh x"
    and 3: "U ⊆ carrier"
    and "N ⊆ U"
  from 4 5 obtain V where 1: "V ∈ opens ∧ x ∈ V ∧ V ⊆ N"
    unfolding neigh_def by auto
  from `N ⊆ U` 1 have "V ⊆ U" by auto
  from 1 this have "∃V ∈ opens. x ∈ V ∧ V ⊆ U" by auto
  from 4 3 this show "U ∈ neigh x" unfolding neigh_def by auto
next
  fix x :: "'a"
    and N
  assume 1: "x ∈ carrier" "N ∈ neigh x"
  then obtain U where 0: "N ∈ Pow carrier ∧ U ∈ opens ∧ x ∈ U ∧ U ⊆ N"
    unfolding neigh_def by auto
  then have "{z ∈ N. N ∈ neigh z} ⊆ carrier" by auto
  have "U ⊆ {z ∈ N. N ∈ neigh z}"
  proof
    fix y :: "'a"
    assume "y ∈ U"
    then have "y ∈ N" using 0 by auto
    from `y ∈ U` this 0 have 3: "y ∈ carrier" by auto
    have "y ∈ U ∧ U ⊆ N" using 0 `y ∈ U` by auto
    then have "∃U ∈ opens. y ∈ U ∧ U ⊆ N" using 0 by auto
    then have "N ∈ neigh y" using 0 3 unfolding neigh_def by auto
    then show "y ∈ {z ∈ N. N ∈ neigh z}" using `y ∈ N` by auto
  qed
  from this 0 have "∃U ∈ opens. x ∈ U ∧ U ⊆ {z ∈ N. N ∈ neigh z}" by auto
  then show "{z ∈ N. N ∈ neigh z} ∈ neigh x" using 1 unfolding neigh_def by auto
qed

interpretation alt: alternative_topological_space carrier neigh
  by (rule alter)

theorem top_of_alt: "alt.opens = opens"
proof
  (* https://proofwiki.org/wiki/Set_is_Open_iff_Neighborhood_of_all_its_Points *)
  {
    fix U
    assume 2: "U ∈ alt.opens"
    then have 4: "U ∈ Pow carrier" "∀x ∈ U. U ∈ neigh x"
      unfolding alt.opens_def by auto
    let ?A = "{T:opens. ∃x. x ∈ T ∧ T ⊆ U}"
    have "T ⊆ U" if "T ∈ ?A" for T
      proof -
        from `T ∈ ?A` show "T ⊆ U" by auto
      qed
    have 0: "⋃ ?A ⊆ U" by auto
    have 1: "U ⊆ ⋃ ?A"
      proof
        fix x :: "'a"
        assume "x ∈ U"
        have 5: "U ∈ neigh x" using `x ∈ U` 4 by auto
        have "x ∈ carrier" using `x ∈ U` 2 by auto
        from this 5 have "U ∈ Pow carrier ∧ (∃V∈opens. x ∈ V ∧ V ⊆ U)"
          unfolding neigh_def by auto
        then obtain V where "V ∈ opens ∧ x ∈ V ∧ V ⊆ U" by auto
        then show "x ∈ ⋃ ?A" by auto
      qed
    from 0 1 have 3: "U = ⋃ ?A" by auto
    have "⋃ ?A ∈ opens" using 0 2 by auto
    then have "U ∈ opens" using 3 by auto
  }
  then show "alt.opens ⊆ opens" by auto
next
  {
    fix U
    assume 1: "U ∈ opens"
    then have 0: "U ∈ Pow carrier" using open_subsets by auto
    have "U ∈ neigh x" if "x ∈ U" for x
      proof
        from `x ∈ U` `U ∈ Pow carrier` show "x ∈ carrier"
          by auto
      next
        have "U ∈ opens ∧ x ∈ U ∧ U ⊆ U" using 1 `x ∈ U` by auto
        then have "∃V ∈ opens. x ∈ V ∧ V ⊆ U" by auto
        then show "U ∈ neigh x" unfolding neigh_def using 0 by auto
      next
        show "U ⊆ carrier" using 0 by simp
      next
        show "U ⊆ U" by simp
      qed
    then have "∀x ∈ U. U ∈ neigh x" by auto
    then have 3: "U ∈ Pow carrier ∧ (∀x ∈ U. U ∈ neigh x)" using 0 by auto
    then have "U ∈ alt.opens" unfolding alt.opens_def by auto
  }
  then show "opens ⊆ alt.opens" by auto
qed

sublocale alt: alternative_topological_space carrier neigh
  rewrites "alt.opens = opens"
proof (rule alter, rule top_of_alt)
qed

end

context alternative_topological_space begin

interpretation top: topological_space carrier opens
  by (simp add: topo)

theorem alt_of_top:
  "top.neigh = neigh"
proof (rule extensionalityI[where ?A = carrier])
  show "top.neigh ∈ extensional carrier"
    by (simp add: top.neigh_def)
next
  show "neigh ∈ extensional carrier"
    by (metis IntD2 extensional_funcset_def neigh_carrier)
next
  fix x :: "'a"
  assume 0: "x ∈ carrier"
  show "top.neigh x = neigh x"
  proof
    {
      fix N
      assume "N ∈ top.neigh x"
      then have 2: "N ∈ Pow carrier ∧ (∃U ∈ opens. x ∈ U ∧ U ⊆ N)"
        using 0 unfolding top.neigh_def by auto
      then obtain U where 1: "U ∈ opens ∧ x ∈ U ∧ U ⊆ N" by auto
      then have "U ∈ neigh x" unfolding opens_def by auto
      then have "N ∈ neigh x" using 0 1 2 by auto
    }
    then show "top.neigh x ⊆ neigh x" by auto
  next
    {
      fix N
      assume 1: "N ∈ neigh x"
      have 2: "neigh x ∈ Pow (Pow carrier)" using 0 by (rule neigh_codomain)
      from 1 have 3: "{z:N. N ∈ neigh z} ∈ neigh x" using 0 by auto
      then have 4: "{z:N. N ∈ neigh z} ∈ opens"
        using 2 unfolding opens_def by auto
      from 0 3 have "x ∈ {z:N. N ∈ neigh z}" by (rule neigh_of)
      then have "{z:N. N ∈ neigh z} ∈ opens ∧ x ∈ {z:N. N ∈ neigh z} ∧ {z:N. N ∈ neigh z} ⊆ N"
        using 4 by auto
      then have "∃U ∈ opens. x ∈ U ∧ U ⊆ N" by (auto simp: bexI[where ?x = "{z:N. N ∈ neigh z}"])
      then have "N ∈ top.neigh x"
        using 0 1 2 unfolding top.neigh_def by auto
    }
    then show "neigh x ⊆ top.neigh x" by auto
  qed
qed

sublocale topological_space carrier opens
  rewrites "top.neigh = neigh"
  by (rule topo, rule alt_of_top)

end

locale basis_for = topological_space +
  fixes B
  assumes collection_of_opens [intro]: "B ⊆ opens"
  and every_open_is_union [intro]: "[| U ∈ opens |] ==> ∃X ⊆ B. U = ⋃ X"

locale basis =
  fixes carrier :: "'a set"
  and B :: "'a set set"
  assumes basis_carrier [intro]: "B ⊆ Pow carrier"
  and inter_closed [intro]: "[| X ∈ B; Y ∈ B |] ==> X ∩ Y ∈ B"
  and covers [intro, simp]: "carrier = ⋃ B"
begin

definition opens :: "'a set set" where
"opens = {⋃ C | C. C ⊆ B}"

lemma opens_are_subsets: "opens ⊆ Pow carrier"
  by (smt (verit) PowI Union_mono basis.opens_def basis_axioms basis_def mem_Collect_eq subsetI)

sublocale basis_for carrier opens B
proof (unfold_locales, fact opens_are_subsets)
  fix A
  assume "A ⊆ opens"
  then have 0: "X ∈ A ==> ∃C. X = ⋃ C ∧ C ⊆ B" for X
    unfolding opens_def by auto
  let ?A1 = "{X∈B. ∃C. (X ∈ C) ∧ (⋃ C ∈ A)}"
  {
    {
      fix x
      assume "x ∈ ⋃ A"
      then obtain X where 2: "x ∈ X" "X ∈ A" by auto
      then obtain C where 1: "X = ⋃ C" "C ⊆ B" using 0 by auto
      then obtain Y where 3: "x ∈ Y" "Y ∈ C" using `x ∈ X` by auto
      then have "Y ∈ B" using 1 by auto
      moreover have "∃C. (Y ∈ C) ∧ (⋃ C ∈ A)" using 3(2) 1(1) 2(2) by auto
      ultimately have "Y ∈ ?A1" by auto
      then have "x ∈ ⋃ ?A1" using 3(1) by auto
    }
    then have "⋃ A ⊆ ⋃ ?A1" by blast
  }
  moreover
  {
    {
      fix x
      assume "x ∈ ⋃ ?A1"
      then obtain X where 0: "x ∈ X" "X ∈ B" "∃C. (X ∈ C) ∧ (⋃ C ∈ A)" by auto
      then obtain C where 1: "X ∈ C" "⋃ C ∈ A" by auto
      then have "x ∈ ⋃ C" using 0(1) by auto
      then have "x ∈ ⋃ A" using 1(2) by auto
    }
    then have "⋃ ?A1 ⊆ ⋃ A" by blast
  }
  ultimately have "⋃ A = ⋃ ?A1" by auto
  thus "⋃ A ∈ opens" unfolding opens_def by auto
next
  fix X Y
  assume "X ∈ opens" "Y ∈ opens"
  then obtain C D where 0: "X = ⋃ C" "C ⊆ B" "Y = ⋃ D" "D ⊆ B"
    unfolding opens_def by auto
  let ?K = "{ P ∩ Q | P Q. P ∈ C ∧ Q ∈ D}"
  from 0 have "?K ⊆ B" by (auto simp: inter_closed)
  {
    fix x
    have "x ∈ X ∩ Y ⟷ x ∈ X ∧ x ∈ Y" by auto
    also have "... ⟷ (∃c. x ∈ c ∧ c ∈ C) ∧ (∃d. x ∈ d ∧ d ∈ D)"
      using "0"(1) "0"(3) by blast
    also have "... ⟷ (∃c d. x ∈ c ∩ d ∧ c ∈ C ∧ d ∈ D)" by blast
    also have "... ⟷ (∃PQ ∈ ?K. x ∈ PQ)" by blast
    also have "... ⟷ x ∈ ⋃ ?K" by blast
    finally have "x ∈ X ∩ Y ⟷ x ∈ ⋃ ?K" .
  }
  then have "X ∩ Y = ⋃ ?K" by blast
  then show "X ∩ Y ∈ opens" using `?K ⊆ B` unfolding opens_def by auto
next
  show "carrier ∈ opens" using opens_def by auto
next
  show "B ⊆ opens" unfolding opens_def by auto
next
  fix U
  assume "U ∈ opens"
  then show "∃X ⊆ B. U = ⋃ X" unfolding opens_def by auto
qed

end

locale real_line
begin

definition open_interval :: "real * real => real set" where
"open_interval = (λ(x,y). {r. x < r ∧ r < y})"

definition open_intervals :: "real set set" where
"open_intervals = {open_interval (x, y) | x y. True}"

lemma open_interval_iff [intro]:
  "r ∈ open_interval p ⟷ fst p < r ∧ r < snd p"
  unfolding open_interval_def by auto

lemma open_intervals_iff [intro]:
  "I ∈ open_intervals ⟷ (∃p. I = open_interval p)"
  unfolding open_intervals_def by auto

sublocale basis "UNIV :: real set" "open_intervals"
proof (unfold_locales, auto)
  fix X Y
  assume "X ∈ open_intervals" "Y ∈ open_intervals"
  then obtain v w x y where
    "X = open_interval (v, w)"
    "Y = open_interval (x, y)"
    by (auto simp: open_intervals_iff)
  then have "X ∩ Y = {r. v < r ∧ r < w ∧ x < r ∧ r < y}"
    unfolding open_interval_def by auto
  moreover have "(v < r ∧ r < w ∧ x < r ∧ r < y) = (max v x < r ∧ r < min w y)"
    for r by arith
  ultimately have "X ∩ Y = {r. max v x < r ∧ r < min w y}" by auto
  then have "X ∩ Y = open_interval (max v x, min w y)"
    unfolding open_interval_def by auto
  then have "∃p. X ∩ Y = open_interval p" by blast
  then show "X ∩ Y ∈ open_intervals" by (auto simp: open_intervals_iff)
next
  fix x :: real
  have "x - 1 < x ∧ x < x + 1" by arith
  then have "x ∈ open_interval (x - 1, x + 1)"
    by (auto simp: open_interval_iff)
  then show "∃I ∈ open_intervals. x ∈ I"
    by (intro bexI, auto simp: open_intervals_iff)
qed

lemma open_interval_is_open [intro]: "open_interval (x, y) ∈ opens"
  using collection_of_opens open_intervals_iff by blast

lemma "open_interval (0, 1) ∈ opens"
  by (fact open_interval_is_open)

lemma "open_interval (0, 1) ∪ open_interval (3, 10) ∈ opens"
  by (auto simp: binary_union_closed open_interval_is_open)

lemma open_interval_is_neigh [intro]:
  assumes "0 < d"
  shows "open_interval (c - d, c + d) ∈ neigh c" (is "?N ∈ neigh c")
proof -
  have "c ∈ open_interval (c - (d / 2), c + (d / 2))"
    (is "c ∈ open_interval (?x, ?y)")
    using assms
    by (auto simp: open_interval_iff)
  moreover have "open_interval (?x, ?y) ⊆ ?N"
    by (auto simp: open_interval_iff)
  ultimately have "∃U∈opens. c ∈ U ∧ U ⊆ ?N" by auto
  then have "?N ∈ {N ∈ Pow UNIV. ∃U∈opens. c ∈ U ∧ U ⊆ N}" by blast
  then show ?thesis unfolding neigh_def by auto
qed

lemma real_neigh:
  assumes "0 < d"
  and "open_interval (c - d, c + d) ⊆ N" (is "?I ⊆ N")
  shows "N ∈ neigh c"
proof (intro alt.enlarge[where ?x = "c" and ?N = "?I" and ?U = "N"])
  show "c ∈ UNIV" by blast
next
  show "?I ∈ neigh c" using assms(1) by blast
next
  show "N ⊆ UNIV" by blast
next
  show "?I ⊆ N" by (fact assms)
qed

lemma "{r. 0 ≤ r ∧ r < 10} ∈ neigh 5" (is "?X ∈ neigh 5")
proof -
  have "(0 :: real) < 5" by arith
  moreover have "open_interval (0, 10) ⊆ ?X"
    by (auto simp: open_interval_iff)
  ultimately show ?thesis
    by (metis (full_types) cancel_comm_monoid_add_class.diff_cancel numeral_Bit0 real_neigh)
qed

end

context topological_space begin
definition limit_point :: "'a set => 'a => bool" where
"limit_point A p ⟷ (∀N. N ∈ neigh p --> (∃x ∈ N. x ∈ A - {p}))"

lemma limit_point_iff [intro, simp]:
  "limit_point A p ⟷ (∀N. N ∈ neigh p --> (∃x ∈ N. x ∈ A - {p}))"
  by (fact limit_point_def)
end

(* Strongly closed *)
locale closed = topological_space +
  fixes A
  assumes is_closed [intro]: "A ∈ closed_sets"

(* Weakly closed *)
locale contains_all_its_limit_points = topological_space +
  fixes A
  assumes subset [intro]: "A ⊆ carrier"
  and limit_point_in_A [intro]: "[|p ∈ carrier; limit_point A p|] ==> p ∈ A"

context closed begin

sublocale contains_all_its_limit_points carrier opens A
proof (unfold_locales)
  have "closed_sets ∈ Pow (Pow carrier)" by (auto simp: closed_subsets)
  then show "A ⊆ carrier" using is_closed by auto
next
  fix p
  assume "p ∈ carrier" "limit_point A p"
  then have 0: "∀N. N ∈ neigh p --> (∃x ∈ N. x ∈ A - {p})" by auto
  from is_closed obtain U where 1: "A = carrier - U" "U ∈ opens"
    by (auto simp: closed_sets_def)
  have "False" if "p ∈ U"
    proof -
      from 1(2) have "U ∈ Pow carrier" "∀x ∈ U. U ∈ neigh x"
        by (auto simp: alt.opens_iff)
      then have "U ∈ neigh p" using `p ∈ U` by fast
      then obtain x where 2: "x ∈ U" "x ∈ A - {p}" using 0 by blast
      then have "x ∈ A" by fast
      then show "False" using 2(1) 1(1) by blast
    qed
  then show "p ∈ A" using `p ∈ carrier` 1(1) by blast
qed

end

context contains_all_its_limit_points begin

(* Classical! *)
interpretation closed carrier opens A
proof
  have "carrier - (carrier - A) = carrier ∩ A"
    by (fact Diff_Diff_Int)
  then have 4: "carrier - (carrier - A) = A"
    using subset by blast
  have "∀x ∈ carrier - A. carrier - A ∈ neigh x"
  proof
    fix x
    assume 3: "x ∈ carrier - A"
    then have 0: "x ∈ carrier" "x ∉ A" by auto
    from this(1) have "limit_point A x ⟹ x ∈ A"
      by auto
    then have "limit_point A x ⟹ False"
      using 0(2) by blast
    then have "∃N. N ∈ neigh x ∧ ¬ (∃y ∈ N. y ∈ A - {x})"
      by auto
    then obtain N where 2: "N ∈ neigh x" "¬ (∃y ∈ N. y ∈ A - {x})" by auto
    then have 1: "∀y ∈ N. y ∉ A - {x}" by auto
    have "∀y ∈ N. y ∈ carrier" using 2(1) 0(1)
      using alt.neigh_codomain by auto
    moreover
    {
      have "A - {x} = A" using 3 by auto
      then have "∀y ∈ N. y ∉ A" using 1 by auto
    }
    ultimately have "∀y ∈ N. y ∈ carrier - A" by auto
    then have "N ⊆ carrier - A" by auto
    then show "carrier - A ∈ neigh x" using alt.enlarge 0(1) 2(1) by auto
  qed
  then have "carrier - A ∈ opens" using alt.opens_iff by auto
  then show "A ∈ closed_sets" using 4 unfolding closed_sets_def by auto
qed

end

end
