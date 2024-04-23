/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Ivan Sergeev
-/
import Mathlib.Data.Matroid.Restrict

/-!
# Direct sum of matroids

## Main definitions

* `indepMatroidDirectSum` constructs an `IndepMatroid` that is the direct sum of two `IndepMatroid`
  instances on disjoint ground sets
* `matroidDirectSum` constructs a `Matroid` that is the direct sum of two `Matroid` instances on
  disjoint ground sets (a wrapper around `indepMatroidDirectSum`)
-/

variable {α : Type*}

lemma Set.union_inters_of_subset_union {A B C : Set α} (hA : A ⊆ B ∪ C) :
    A ∩ B ∪ A ∩ C = A := by
  aesop

lemma Set.subset_inter_of_redundant_right {A B C D : Set α} (hADB : A ∪ D ⊆ B) (hAC : A ⊆ C) :
    A ⊆ B ∩ C :=
  Set.subset_inter ((Set.subset_union_left A D).trans hADB) hAC

lemma Set.subset_inter_of_redundant_left {A B C D : Set α} (hDAB : D ∪ A ⊆ B) (hAC : A ⊆ C) :
    A ⊆ B ∩ C :=
  Set.subset_inter ((Set.subset_union_right D A).trans hDAB) hAC

lemma Set.union_inter_aux {A B C D : Set α} (hAB : A ⊆ B) : A ∪ C ∩ D ⊆ B ∪ (A ∪ C ∩ D) ∩ D := by
  simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_union]
  tauto

lemma Set.inter_union_aux {A B C D : Set α} (hAB : A ⊆ B) : C ∩ D ∪ A ⊆ (C ∩ D ∪ A) ∩ D ∪ B := by
  simp only [Set.subset_def, Set.mem_inter_iff, Set.mem_union]
  tauto

lemma Set.union_inter_supset_left_of_disjoint {I₁ I₂ E₁ E₂ : Set α}
    (hE : E₁ ∩ E₂ = ∅) (hI : I₂ ⊆ E₂) :
    (I₁ ∪ I₂) ∩ E₁ = E₁ ∩ I₁ := by
  rw [Set.union_inter_distrib_right]
  conv => rhs; rw [Set.inter_comm]
  convert Set.union_empty _
  simp only [Set.ext_iff, Set.subset_def] at *
  aesop

lemma Set.union_inter_supset_right_of_disjoint {I₁ I₂ E₁ E₂ : Set α}
    (hE : E₁ ∩ E₂ = ∅) (hI : I₁ ⊆ E₁) :
    (I₁ ∪ I₂) ∩ E₂ = E₂ ∩ I₂ := by
  rw [Set.union_comm]
  rw [Set.inter_comm] at hE
  exact Set.union_inter_supset_left_of_disjoint hE hI

lemma Set.subset_iff_subsets_of_disjoint {A B E₁ E₂ : Set α} (hA : A ⊆ E₁ ∪ E₂) :
    A ⊆ B ↔ A ∩ E₁ ⊆ B ∩ E₁ ∧ A ∩ E₂ ⊆ B ∩ E₂ := by
  constructor
  · simp only [Set.subset_def] at *
    aesop
  · intro ⟨hABE₁, hABE₂⟩ x hx
    simp only [Set.ext_iff, Set.subset_def] at *
    cases hA x hx with
    | inl hE₁ => exact (hABE₁ x ⟨hx, hE₁⟩).left
    | inr hE₂ => exact (hABE₂ x ⟨hx, hE₂⟩).left

lemma Set.between_inter {I T X : Set α} (hIT : I ⊆ T) (hTX : T ⊆ X) (E : Set α) :
    I ∩ E ⊆ T ∩ E ∧ T ∩ E ⊆ X ∩ E :=
  ⟨Set.inter_subset_inter_left E hIT, Set.inter_subset_inter_left E hTX⟩

lemma Set.union_inter_eq_fst {S₁ S₂ E₁ E₂ X₁ X₂ : Set α}
    (hE : E₁ ∩ E₂ = ∅) (hX₁ : S₁ ⊆ X₁ ∩ E₁) (hX₂ : S₂ ⊆ X₂ ∩ E₂) :
    (S₁ ∪ S₂) ∩ E₁ = S₁ := by
  rw [Set.union_inter_distrib_right]
  rw [Set.subset_inter_iff] at hX₁ hX₂
  convert Set.union_empty S₁
  · symm
    rw [Set.left_eq_inter]
    exact hX₁.right
  · rw [← Set.subset_empty_iff] at hE ⊢
    apply (Set.inter_subset_inter_left E₁ hX₂.right).trans
    rwa [Set.inter_comm] at hE

lemma Set.union_inter_eq_snd {S₁ S₂ E₁ E₂ X₁ X₂ : Set α}
    (hE : E₁ ∩ E₂ = ∅) (hX₁ : S₁ ⊆ X₁ ∩ E₁) (hX₂ : S₂ ⊆ X₂ ∩ E₂) :
    (S₁ ∪ S₂) ∩ E₂ = S₂ := by
  rw [Set.union_comm]
  rw [Set.inter_comm] at hE
  exact Set.union_inter_eq_fst hE hX₂ hX₁

set_option linter.unusedVariables false in
/-- Direct sum of matroids as a set operation. -/
@[nolint unusedArguments]
def indepDirectSum {M₁ M₂ : IndepMatroid α} (hME : M₁.E ∩ M₂.E = ∅) (I : Set α) : Prop :=
  ∃ I₁ I₂ : Set α, I₁ ∪ I₂ = I ∧ M₁.Indep I₁ ∧ M₂.Indep I₂

lemma indepDirectSum.ground {M₁ M₂ : IndepMatroid α} {I : Set α} {hME : M₁.E ∩ M₂.E = ∅}
    (hI : indepDirectSum hME I) :
    I ⊆ M₁.E ∪ M₂.E := by
  obtain ⟨_, _, rfl, hM₁, hM₂⟩ := hI
  exact Set.union_subset_union (M₁.subset_ground _ hM₁) (M₂.subset_ground _ hM₂)

lemma indepDirectSum.leftIndep {M₁ M₂ : IndepMatroid α} {hME : M₁.E ∩ M₂.E = ∅} {I : Set α}
    (hI : indepDirectSum hME I) :
    M₁.Indep (I ∩ M₁.E) := by
  obtain ⟨I₁, I₂, rfl, hI₁, hI₂⟩ := hI
  convert M₁.indep_subset hI₁ (Set.inter_subset_right M₁.E I₁) using 1
  exact Set.union_inter_supset_left_of_disjoint hME (M₂.subset_ground I₂ hI₂)

lemma indepDirectSum.rightIndep {M₁ M₂ : IndepMatroid α} {hME : M₁.E ∩ M₂.E = ∅} {I : Set α}
    (hI : indepDirectSum hME I) :
    M₂.Indep (I ∩ M₂.E) := by
  obtain ⟨I₁, I₂, rfl, hI₁, hI₂⟩ := hI
  convert M₂.indep_subset hI₂ (Set.inter_subset_right M₂.E I₂) using 1
  exact Set.union_inter_supset_right_of_disjoint hME (M₁.subset_ground I₁ hI₁)

lemma indepDirectSum_iff {M₁ M₂ : IndepMatroid α} (hME : M₁.E ∩ M₂.E = ∅)
    {I : Set α} (hI : I ⊆ M₁.E ∪ M₂.E) :
    indepDirectSum hME I ↔ M₁.Indep (I ∩ M₁.E) ∧ M₂.Indep (I ∩ M₂.E) :=
  ⟨fun hid => ⟨hid.leftIndep, hid.rightIndep⟩, fun ⟨hM₁, hM₂⟩ => ⟨I ∩ M₁.E, I ∩ M₂.E, by aesop⟩⟩

lemma maximals_indepDirectSum_iff {M₁ M₂ : IndepMatroid α}
    (hME : M₁.E ∩ M₂.E = ∅) (I : Set α) :
    I ∈ maximals (· ⊆ ·) {I | indepDirectSum hME I} ↔
      I ⊆ M₁.E ∪ M₂.E ∧
        I ∩ M₁.E ∈ maximals (· ⊆ ·) M₁.Indep ∧
        I ∩ M₂.E ∈ maximals (· ⊆ ·) M₂.Indep := by
  dsimp only [maximals, Set.mem_setOf_eq]
  constructor
  · intro hyp
    have I_grounded : I ⊆ M₁.E ∪ M₂.E := hyp.left.ground
    rw [indepDirectSum_iff hME I_grounded] at hyp
    obtain ⟨⟨hM₁, hM₂⟩, hB⟩ := hyp
    have I_as : I = I ∩ M₁.E ∪ I ∩ M₂.E := (Set.union_inters_of_subset_union I_grounded).symm
    constructor
    · exact I_grounded
    constructor
    · constructor
      · exact hM₁
      · intro B₁ hB₁ hI₁
        rw [I_as, Set.union_inter_distrib_right, Set.inter_assoc, Set.inter_assoc,
            Set.inter_comm M₂.E, hME, Set.inter_empty, Set.union_empty, Set.inter_self]
        exact Set.subset_inter_of_redundant_right
          (hB ⟨B₁, I ∩ M₂.E, rfl, hB₁, hM₂⟩ (I_as ▸ Set.union_inter_aux hI₁))
          (M₁.subset_ground _ hB₁)
    · constructor
      · exact hM₂
      · intro B₂ hB₂ hI₂
        rw [I_as, Set.union_inter_distrib_right, Set.inter_assoc, Set.inter_assoc,
            hME, Set.inter_empty, Set.empty_union, Set.inter_self]
        exact Set.subset_inter_of_redundant_left
          (hB ⟨I ∩ M₁.E, B₂, rfl, hM₁, hB₂⟩ (I_as ▸ Set.inter_union_aux hI₂))
          (M₂.subset_ground _ hB₂)
  · intro ⟨I_grounded, ⟨hI₁, hB₁⟩, ⟨hI₂, hB₂⟩⟩
    have I_indep : indepDirectSum hME I :=
      ⟨_, _, Set.union_inters_of_subset_union I_grounded, hI₁, hI₂⟩
    rw [indepDirectSum_iff hME I_indep.ground]
    constructor
    · exact ⟨hI₁, hI₂⟩
    · intro B hB hIB
      rw [Set.subset_iff_subsets_of_disjoint hB.ground]
      constructor
      · exact hB₁ hB.leftIndep (Set.inter_subset_inter_left M₁.E hIB)
      · exact hB₂ hB.rightIndep (Set.inter_subset_inter_left M₂.E hIB)

/-- Direct sum of matroids as a matroid defined by the independence axioms. -/
def indepMatroidDirectSum {M₁ M₂ : IndepMatroid α} (hME : M₁.E ∩ M₂.E = ∅) : IndepMatroid α :=
  IndepMatroid.mk
    (M₁.E ∪ M₂.E)
    (indepDirectSum hME)
    ⟨∅, ∅, Set.union_self ∅, M₁.indep_empty, M₂.indep_empty⟩
    (fun A B hMB hAB => by
      have hA : A ⊆ M₁.E ∪ M₂.E := hAB.trans hMB.ground
      rw [indepDirectSum_iff hME hA]
      rw [indepDirectSum_iff hME hMB.ground] at hMB
      rw [Set.subset_iff_subsets_of_disjoint hA] at hAB
      obtain ⟨hE₁, hE₂⟩ := hAB
      obtain ⟨hB₁, hB₂⟩ := hMB
      exact ⟨M₁.indep_subset hB₁ hE₁, M₂.indep_subset hB₂ hE₂⟩
    )
    (by
      intro I B hI I_not_max B_max
      rw [maximals_indepDirectSum_iff hME] at B_max
      obtain ⟨- , hB₁, hB₂⟩ := B_max
      have I_grounded := hI.ground
      rw [maximals_indepDirectSum_iff hME] at I_not_max
      rw [indepDirectSum_iff hME hI.ground] at hI
      simp only [I_grounded, not_true_eq_false, false_or, not_and_or] at I_not_max
      cases I_not_max with
      | inl hI₁ =>
        obtain ⟨x, hxBmI, M₁_aug⟩ := M₁.indep_aug hI.left hI₁ hB₁
        use x
        constructor
        · simp only [Set.ext_iff, Set.subset_def] at *
          aesop
        rw [indepDirectSum_iff]
        constructor
        · convert M₁_aug using 1
          simp only [Set.ext_iff, Set.subset_def] at *
          aesop
        convert hI.right using 1
        · simp only [Set.ext_iff, Set.subset_def] at *
          aesop
        simp only [Set.ext_iff, Set.subset_def] at *
        aesop
      | inr hI₂ =>
        obtain ⟨x, hxBmI, M₂_aug⟩ := M₂.indep_aug hI.right hI₂ hB₂
        use x
        constructor
        · simp only [Set.ext_iff, Set.subset_def] at *
          aesop
        rw [indepDirectSum_iff]
        constructor
        swap
        · convert M₂_aug using 1
          simp only [Set.ext_iff, Set.subset_def] at *
          aesop
        convert hI.left using 1
        · simp only [Set.ext_iff, Set.subset_def] at *
          aesop
        simp only [Set.ext_iff, Set.subset_def] at *
        aesop
    )
    (by
      intro X hX I hI hIX
      have I_grounded := hI.ground
      rw [indepDirectSum_iff hME I_grounded] at hI
      obtain ⟨hI₁, hI₂⟩ := hI
      obtain ⟨S₁, ⟨hMS₁, hIMS₁, hSE₁⟩, hS₁⟩ :=
        M₁.indep_maximal (X ∩ M₁.E) (Set.inter_subset_right X M₁.E) _ hI₁ (by
          rw [Set.subset_iff_subsets_of_disjoint I_grounded] at hIX
          exact hIX.left
        )
      obtain ⟨S₂, ⟨hMS₂, hIMS₂, hSE₂⟩, hS₂⟩ :=
        M₂.indep_maximal (X ∩ M₂.E) (Set.inter_subset_right X M₂.E) _ hI₂ (by
          rw [Set.subset_iff_subsets_of_disjoint I_grounded] at hIX
          exact hIX.right
        )
      by_contra! contr
      unfold maximals at contr
      rw [Set.eq_empty_iff_forall_not_mem] at contr
      specialize contr (S₁ ∪ S₂)
      simp at contr
      obtain ⟨T, hTS₂, hTS₁, hTX, hIT, T_indep, T_big⟩ :=
        contr
          ⟨S₁, S₂, rfl, hMS₁, hMS₂⟩
          (by
            rw [Set.subset_iff_subsets_of_disjoint I_grounded]
            constructor
            · convert hIMS₁
              exact Set.union_inter_eq_fst hME hSE₁ hSE₂
            · convert hIMS₂
              exact Set.union_inter_eq_snd hME hSE₁ hSE₂
          )
          (Set.subset_inter_iff.mp hSE₁).left
          (Set.subset_inter_iff.mp hSE₂).left
      apply T_big
      have hT₁S₁ := hS₁ ⟨T_indep.leftIndep, Set.between_inter hIT hTX M₁.E⟩ (by
        convert Set.inter_subset_inter_left M₁.E hTS₁
        simp_all
      )
      have hT₂S₂ := hS₂ ⟨T_indep.rightIndep, Set.between_inter hIT hTX M₂.E⟩ (by
        convert Set.inter_subset_inter_left M₂.E hTS₂
        simp_all
      )
      convert Set.union_subset_union hT₁S₁ hT₂S₂
      rw [← Set.inter_union_distrib_left, Set.left_eq_inter]
      exact hTX.trans hX
    )
    (fun _ => (·.ground))

/-- Direct sum of matroids as a matroid. -/
def matroidDirectSum {M₁ M₂ : Matroid α} (hME : M₁.E ∩ M₂.E = ∅) : Matroid α :=
  (indepMatroidDirectSum hME').matroid where
  hME' : (M₁.restrictIndepMatroid _).E ∩ (M₂.restrictIndepMatroid _).E = ∅ := hME
