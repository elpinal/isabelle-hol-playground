theory Chapter1And2
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
  have "⋀ C. C ∈ A ⟹ ∃V ∈ OX. C = V ∩ S" using 0 by auto
  then have 4: "⋀ C. C ∈ A ⟹ ∃V ∈ ?A1. C = V ∩ S" by auto
  have 5: "⋀ V. V ∈ ?A1 ⟹ V ⊆ ?U1" by auto
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
(* This definition does not require p to be in the carrier. *)

lemma limit_point_iff [intro, simp]:
  "limit_point A p ⟷ (∀N. N ∈ neigh p --> (∃x ∈ N. x ∈ A - {p}))"
  by (fact limit_point_def)

lemma limit_point_monotone:
  assumes "p ∈ carrier"
  and "A ⊆ B"
  and "limit_point A p"
  shows "limit_point B p"
proof simp
  {
    fix N
    assume "N ∈ neigh p"
    then obtain x where 0: "x ∈ N" "x ∈ A - {p}" using assms(3) by auto
    then have "x ∈ B" using assms(2) by auto
    moreover have "x ≠ p" using 0 by auto
    ultimately have "∃x ∈ N. x ∈ B ∧ x ≠ p"
      using 0(1) by auto
  }
  then show "∀N. N ∈ neigh p ⟶ (∃x∈N. x ∈ B ∧ x ≠ p)" by auto
qed

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

locale subset_of_topological_space = topological_space +
  fixes A
  assumes subset [intro]: "A ⊆ carrier"
begin

definition closure :: "'a set" where
"closure = A ∪ {p ∈ carrier. limit_point A p}"

lemma closure_iff [simp]: "p ∈ closure ⟷ p ∈ A ∨ (p ∈ carrier ∧ limit_point A p)"
  by (simp add: closure_def)

lemma closure_subset [intro]: "closure ⊆ carrier"
  using closure_iff subset by blast

(* Classical! *)
lemma closure_is_closed [intro]: "closure ∈ closed_sets"
proof -
  have "∀p ∈ carrier - closure. carrier - closure ∈ neigh p"
  proof
    fix y
    assume "y ∈ carrier - closure"
    then have 1: "y ∈ carrier" "y ∉ closure" by auto
    then have 2: "y ∉ A" "¬ (y ∈ carrier ∧ limit_point A y)"
      using closure_iff by auto
    then have "y ∉ carrier ∨ ¬ (limit_point A y)"
      by blast
    then have "¬ (limit_point A y)" using 1(1) by blast
    then obtain N where 3: "N ∈ neigh y" "∀x ∈ N. x ∉ A - {y}"
      using limit_point_iff by auto
    then obtain U where 4: "U ∈ opens" "y ∈ U" "U ⊆ N"
      unfolding neigh_def using 1(1) by auto
    from 3 have "N ∩ A = {}" using 2(1) by auto
    then have 0: "U ∩ A = {}"
      using 4(3) by auto
    moreover
    {
      have "∀x ∈ U. U ∈ neigh x" using 4(1) using alt.opens_iff by auto
      then have "∀p ∈ U. limit_point A p --> (∃x ∈ U. x ∈ A - {p})"
        using limit_point_iff by blast
      then have "∀p ∈ U. limit_point A p --> (U ∩ A ≠ {})" by auto
      then have "U ∩ {p ∈ carrier. limit_point A p} = {}"
        using 0 by blast
    }
    ultimately have "U ∩ closure = {}" using closure_iff
      by blast
    then have "U ⊆ carrier - closure"
      using `U ∈ opens` by blast
    then show "carrier - closure ∈ neigh y"
      using 4(1) 4(2) alt.opens_iff point_in_open_is_in_carrier
      by auto
  qed
  moreover have "carrier - closure ∈ Pow carrier" by (auto simp: closure_subset)
  ultimately have "carrier - closure ∈ opens" by (auto simp: alt.opens_iff)
  then show "closure ∈ closed_sets"
    using closure_subset closed_sets_def by auto
qed

(* Classical! It depends on closure_is_closed. *)
lemma closure_eq_int_closed_containing:
  "closure = ⋂ {C ∈ closed_sets. A ⊆ C}"
proof -
  have "⋀B. B ∈ closed_sets ==> A ⊆ B ==> closure ⊆ B"
  proof -
    fix B
    assume 0: "B ∈ closed_sets" "A ⊆ B"
    then have "{p ∈ carrier. limit_point A p} ⊆ {p ∈ carrier. limit_point B p}"
      using limit_point_monotone by auto
    moreover
    {
      interpret cl: closed carrier opens B by (unfold_locales, fact 0(1))
      have "{p ∈ carrier. limit_point B p} ⊆ B" by (auto simp: cl.limit_point_in_A)
    }
    ultimately have "{p ∈ carrier. limit_point A p} ⊆ B" by auto
    then show "closure ⊆ B" using `A ⊆ B` using closure_iff by auto
  qed
  then have "closure ⊆ ⋂ {C ∈ closed_sets. A ⊆ C}"
    using Inter_greatest by auto
  then show ?thesis by auto
qed

corollary "closure_eq_closed_sets":
  assumes "closure = A"
  shows "A ∈ closed_sets"
  using closure_is_closed assms by auto

definition dense :: bool where
"dense ⟷ (closure = carrier)"

lemma
  assumes "dense"
  and "U ∈ opens"
  and "A ∩ U = {}"
  shows "U = {}"
proof -
  let ?C = "carrier - U"
  have "A ⊆ ?C" using assms(3) subset by auto
  moreover have "?C ∈ closed_sets"
    using assms(2) closed_sets_def by auto
  ultimately have "carrier ⊆ ?C"
    using closure_eq_int_closed_containing assms(1) dense_def by blast
  moreover have "?C ⊆ carrier" using closed_subsets by auto
  ultimately have "?C = carrier" by blast
  thus "U = {}"
    using assms(2) by blast
qed

definition interior :: "'a set" where
"interior = ⋃ {U ∈ opens. U ⊆ A}"

lemma "interior = {x ∈ carrier. A ∈ neigh x}"
proof (intro subset_antisym, intro subsetI)
  fix x
  assume 0: "x ∈ interior"
  then have "x ∈ carrier" using interior_def by auto
  moreover {
    from 0 obtain U where "U ∈ opens" "U ⊆ A" "x ∈ U" using interior_def by auto
    then have "A ∈ neigh x" using alt.enlarge neigh_def subset by auto
  }
  ultimately show "x ∈ {x ∈ carrier. A ∈ neigh x}" by auto
next
  {
    fix x
    assume "x ∈ {x ∈ carrier. A ∈ neigh x}"
    then obtain U where "x ∈ U" "U ⊆ A" "U ∈ opens"
      using neigh_def by fastforce
    then have "x ∈ interior" using interior_def by auto
  }
  thus "{x ∈ carrier. A ∈ neigh x} ⊆ interior" by auto
qed

lemma
  assumes "A ∈ opens"
  shows "interior = A"
  using assms interior_def by auto

definition frontier :: "'a set" where
"frontier = closure - interior"

end

locale subset_of_topological_space_and_comp =
  subset_of_topological_space carrier opens A +
  comp: subset_of_topological_space carrier opens "carrier - A"
  for carrier opens A
begin

(* Perhaps classical *)
lemma comp_interior_closure_comp: "carrier - interior = comp.closure"
proof (intro subset_antisym, intro subsetI)
  fix x
  assume "x ∈ carrier - interior"
  then have 0: "x ∈ carrier" "x ∉ interior" by auto
  then have "⋀U. U ∈ opens ==> U ⊆ A ==> x ∉ U"
    using interior_def by blast
  then have 1: "⋀U. U ∈ opens ==> U ⊆ A ==> x ∈ carrier - U"
    using 0(1) by blast
  have "x ∈ C" if 2: "C ∈ closed_sets" "carrier - A ⊆ C" for C
  proof -
    from 2(1) obtain U where 3: "U ∈ opens" "C = carrier - U"
      using closed_sets_def by auto
    then have "U ⊆ A" using 2(2) by auto
    thus "x ∈ C" using 1 3 by auto
  qed
  thus "x ∈ comp.closure"
    using comp.closure_eq_int_closed_containing by auto
next
  {
    fix x
    assume 0: "x ∈ comp.closure"
    hence "x ∈ carrier" by auto
    moreover {
      fix U
      assume 1: "U ∈ opens" "U ⊆ A"
      then have 3: "carrier - U ∈ closed_sets" (is "?C ∈ closed_sets")
        using closed_sets_def by auto
      from 1 have 4: "carrier - A ⊆ ?C" by auto
      hence "x ∈ ?C"
        using 0 comp.closure_eq_int_closed_containing 3 by auto
      then have "x ∉ U" using 1(2) by fast
    }
    ultimately have "x ∈ carrier - interior" using interior_def by auto
  }
  thus "comp.closure ⊆ carrier - interior" by auto
qed
end

locale frontier_in_terms_of_set_complement =
  subset_of_topological_space carrier opens A +
  comp: subset_of_topological_space carrier opens "carrier - A"
  for carrier opens A
begin

definition frontier_by_closures :: "'a set" where
"frontier_by_closures = closure ∩ comp.closure"

definition frontier_by_interiors :: "'a set" where
"frontier_by_interiors = carrier - interior - comp.interior"

interpretation sc1: subset_of_topological_space_and_comp carrier opens A
  by (simp add:
    comp.subset_of_topological_space_axioms
    subset_of_topological_space_and_comp_def
    subset_of_topological_space_axioms
  )

interpretation sc2: subset_of_topological_space_and_comp carrier opens "carrier - A"
  by (simp add:
    subset_of_topological_space_and_comp_def
    subset_of_topological_space_axioms.intro
    subset_of_topological_space_def
    topological_space_axioms
  )

lemma "frontier = frontier_by_closures"
proof -
  have "frontier = closure - interior" using frontier_def by simp
  also have "... = closure ∩ (- interior)" by blast
  also have "... = closure ∩ (carrier - interior)"
    using closure_subset by force
  also have "... = closure ∩ comp.closure"
    using sc1.comp_interior_closure_comp by simp
  finally have "frontier = closure ∩ comp.closure" by auto
  thus "frontier = frontier_by_closures" by (simp add: frontier_by_closures_def)
qed

lemma "frontier = frontier_by_interiors"
proof (simp add: frontier_def frontier_by_interiors_def)
  have "closure = carrier - comp.interior"
    using sc2.comp_interior_closure_comp
    by (simp add: Diff_Diff_Int Int_absorb1 subset)
  thus "closure - interior = carrier - interior - comp.interior" by blast
qed

end

locale metric_space =
  fixes carrier :: "'a set"
  and distance :: "'a * 'a => real"
  assumes distance_dom [intro]: "distance ∈ carrier × carrier →⇩E UNIV"
  and zero_if [simp]: "distance (x, x) = 0"
  and zero_only_if [intro]: "[| distance (x, y) = 0 |] ==> x = y"
  and distance_non_negative [intro]: "distance (x, y) >= 0"
  and sym [intro]: "distance (x, y) = distance (y, x)"
  and triangle_inequality [intro]: "distance (x, z) <= distance (x, y) + distance (y, z)"
begin

definition ball :: "'a => real => 'a set" where
"ball x r = {y ∈ carrier. distance (x, y) <= r}"

lemma ball_is_subset_of_carrier: "ball x r ⊆ carrier"
  unfolding ball_def by auto

lemma ball_leq [intro]:
  assumes "r <= s"
  shows "ball x r ⊆ ball x s"
  using ball_def assms
  by fastforce

definition opens :: "'a set set" where
"opens = {U ∈ Pow carrier. ∀x ∈ U. ∃r. r > 0 ∧ ball x r ⊆ U}"

lemma carrier_is_open: "carrier ∈ opens"
  unfolding opens_def
  using ball_is_subset_of_carrier
  by (simp add: gt_ex)

lemma opens_are_closed_under_intersection:
  assumes "U ∈ opens" "V ∈ opens"
  shows "U ∩ V ∈ opens"
proof -
  have "⋀ x. x ∈ U ∩ V ⟹ ∃r. r > 0 ∧ ball x r ⊆ U ∩ V"
  proof -
    fix x
    assume "x ∈ U ∩ V"
    then have 0: "x ∈ U" "x ∈ V" by auto
    obtain r where
      1: "r > 0" "ball x r ⊆ U"
      using 0(1) assms(1) by (auto simp: opens_def)
    obtain s where
      2: "s > 0" "ball x s ⊆ V"
      using 0(2) assms(2) by (auto simp: opens_def)
    {
      have "min r s ≤ r" by arith
      then have "ball x (min r s) ⊆ U"
        using ball_leq 1(2) by blast
    } moreover {
      have "min r s ≤ s" by arith
      then have "ball x (min r s) ⊆ V"
        using ball_leq 2(2) by blast
    }
    ultimately have "ball x (min r s) ⊆ U ∩ V" by auto
    moreover have "min r s > 0" using 1(1) 2(1) by arith
    ultimately show "∃r. r > 0 ∧ ball x r ⊆ U ∩ V"
      by (auto intro: exI[where ?x = "min r s"])
  qed
  then show ?thesis using assms by (auto simp: opens_def)
qed

lemma opens_are_closed_under_union:
  assumes "A ⊆ opens"
  shows "⋃ A ∈ opens"
proof -
  {
    fix x
    assume "x ∈ ⋃ A"
    then obtain U where 0: "U ∈ opens" "U ∈ A" "x ∈ U"
      using assms by auto
    then obtain r where "r > 0" "ball x r ⊆ U" by (auto simp: opens_def)
    moreover have "U ⊆ ⋃ A" using 0(2) by auto
    ultimately have "ball x r ⊆ ⋃ A" by auto
    then have "∃ r. r > 0 ∧ ball x r ⊆ ⋃ A"
      using `r > 0` by auto
  }
  then show ?thesis using opens_def assms by auto
qed

sublocale topological_space carrier opens
  using carrier_is_open opens_are_closed_under_intersection opens_are_closed_under_union
  by (unfold_locales, auto simp: opens_def)

end


end
