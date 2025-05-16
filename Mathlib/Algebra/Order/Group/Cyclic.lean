/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic linearly ordered groups

This file contains basic results about cyclic linearly ordered groups and their subgroups.

The definitions `LinearOrderedCommGroup.Subgroup.genLTOne` (*resp.*
`LinearOrderedCommGroup.genLTOone`) yields a generator of a non-trivial subgroup of a linearly
ordered commutative group with (*resp.* of a non-trivial linearly ordered commutative group) that
is strictly less than `1`. The corresponding additive definitions are also provided.
-/

noncomputable section

namespace LinearOrderedCommGroup

open LinearOrderedCommGroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [IsCyclic G]

namespace Subgroup

variable (H : Subgroup G) [Nontrivial H]

@[to_additive exists_neg_generator]
lemma exists_generator_lt_one : ∃ (a : G), a < 1 ∧ Subgroup.zpowers a = H := by
  obtain ⟨a, ha⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp H.isCyclic
  obtain ha1 | rfl | ha1 := lt_trichotomy a 1
  · exact ⟨a, ha1, ha⟩
  · rw [Subgroup.zpowers_one_eq_bot] at ha
    exact absurd ha.symm <| (H.nontrivial_iff_ne_bot).mp inferInstance
  · use a⁻¹, Left.inv_lt_one_iff.mpr ha1
    rw [Subgroup.zpowers_inv, ha]

/-- Given a subgroup of a cyclic linearly ordered commutative group, this is a generator of
the subgroup that is `< 1`. -/
@[to_additive negGen "Given an additive subgroup of an additive cyclic linearly ordered
commutative group, this is a negative generator of the subgroup."]
protected noncomputable def genLTOne : G := H.exists_generator_lt_one.choose

@[to_additive negGen_neg]
lemma genLTOne_lt_one (H : Subgroup G) [Nontrivial H] : H.genLTOne < 1 :=
  H.exists_generator_lt_one.choose_spec.1

@[to_additive (attr := simp) negGen_zmultiples_eq_top]
lemma genLTOne_zpowers_eq_top (H : Subgroup G) [Nontrivial H] : Subgroup.zpowers H.genLTOne = H :=
  H.exists_generator_lt_one.choose_spec.2

lemma genLTOne_val_eq_genLTOne : ((⊤ : Subgroup H).genLTOne) = H.genLTOne := by
  set γ := H.genLTOne with hγ
  set η := ((⊤ : Subgroup H).genLTOne) with hη
  have h1 (x : H) : ∃ k : ℤ, η ^ k = x := by
    have uno := Subgroup.genLTOne_zpowers_eq_top (G := H) (H := ⊤)
    have tre : IsCyclic H := by
      apply isCyclic_iff_exists_zpowers_eq_top (α := H)|>.mpr
      use η
    rw [← Subgroup.mem_zpowers_iff (G := H) (h := x) (g := η)]
    rw [uno]
    trivial
  replace h1 (x : G) : x ∈ H → ∃ k : ℤ, η ^ k = x := by
    intro hx
    obtain ⟨k, hk⟩ := h1 ⟨x, hx⟩
    use k
    norm_cast
    rw [hk]
  have h2 := genLTOne_zpowers_eq_top (G := G) (H := H)
  replace h2 (x : G) : x ∈ H → ∃ k : ℤ, γ ^ k = x := by
    rw [← Subgroup.mem_zpowers_iff (g := γ) (h := x)]
    intro h_mem
    rwa [h2]
  have main : Subgroup.zpowers ↑η = Subgroup.zpowers γ := by
    ext y
    refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
    · rw [Subgroup.mem_zpowers_iff]
      apply h2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← hk]
      apply Subgroup.zpow_mem
      simp only [SetLike.coe_mem]
    · rw [H.genLTOne_zpowers_eq_top] at hy
      obtain ⟨k, hk⟩ := h1 y hy
      rw [Subgroup.mem_zpowers_iff]
      use k
  rw [Subgroup.zpowers_eq_zpowers_iff] at main
  rcases main with _ | h
  · assumption
  have hγ_lt := H.genLTOne_lt_one
  have hη_lt := (⊤ : Subgroup H).genLTOne_lt_one
  rw [← hη] at hη_lt
  rw [← hγ, ← h] at hγ_lt
  rw [inv_lt_one'] at hγ_lt
  exact (not_lt_of_lt hγ_lt hη_lt).elim

end Subgroup

variable (G) [Nontrivial G]

/-- Given a cyclic linearly ordered commutative group, this is a generator that is `< 1`. -/
@[to_additive negGen "Given an additive cyclic linearly ordered commutative group, this is a
negative generator of it."]
noncomputable def genLTOne : G := (⊤ : Subgroup G).genLTOne

@[to_additive (attr := simp) negGen_eq_of_top]
lemma genLTOne_eq_of_top : genLTOne G = (⊤ : Subgroup G).genLTOne := rfl

@[to_additive negGen_neg]
lemma genLTOne_lt_one : genLTOne G < 1 := (⊤ : Subgroup G).genLTOne_lt_one

lemma genLTOne_unique (g : G) : g < 1 ∧ Subgroup.zpowers g = ⊤ → g = genLTOne G := by
  rintro ⟨hg_lt, hg_top⟩
  rw [← (⊤ : Subgroup G).genLTOne_zpowers_eq_top] at hg_top
  rcases Subgroup.zpowers_eq_zpowers_iff.mp hg_top with _ | h
  · assumption
  rw [← one_lt_inv', h] at hg_lt
  exact (not_lt_of_lt hg_lt <| Subgroup.genLTOne_lt_one _).elim


end LinearOrderedCommGroup
