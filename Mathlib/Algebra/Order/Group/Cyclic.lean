/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic linearly ordered groups

This file contains basic results about cyclic linearly ordered groups and cyclic subgroups of
linearly ordered groups.

The definitions `LinearOrderedCommGroup.Subgroup.genLTOne` (*resp.*
`LinearOrderedCommGroup.genLTOone`) yields a generator of a non-trivial subgroup of a linearly
ordered commutative group with (*resp.* of a non-trivial linearly ordered commutative group) that
is strictly less than `1`. The corresponding additive definitions are also provided.
-/

noncomputable section

namespace LinearOrderedCommGroup

open LinearOrderedCommGroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

namespace Subgroup

@[to_additive]
lemma zpowers_eq_zpowers_iff {x y : G} :
    Subgroup.zpowers x = Subgroup.zpowers y ↔ x = y ∨ x⁻¹ = y := by
  rw [iff_comm]
  constructor
  · rintro (rfl|rfl) <;> simp
  intro h
  have hx : x ∈ Subgroup.zpowers y := by simp [← h]
  have hy : y ∈ Subgroup.zpowers x := by simp [h]
  rw [Subgroup.mem_zpowers_iff] at hx hy
  obtain ⟨k, rfl⟩ := hy
  obtain ⟨l, hl⟩ := hx
  wlog hx1 : 1 < x
  · push_neg at hx1
    rcases hx1.eq_or_lt with rfl|hx1
    · simp
    · specialize this (x := x⁻¹) (-k) (by simp [h]) (-l) (by simp [hl]) (by simp [hx1])
      simpa [or_comm] using this
  simp only [← zpow_mul] at hl
  replace hl : x ^ (k * l) = x ^ (1 : ℤ) := by simp [hl]
  rw [zpow_right_inj hx1, Int.mul_eq_one_iff_eq_one_or_neg_one] at hl
  refine hl.imp ?_ ?_ <;>
  simp +contextual

variable (H : Subgroup G) [Nontrivial H] [hH : IsCyclic H]

@[to_additive exists_neg_generator]
lemma exists_generator_lt_one : ∃ (a : G), a < 1 ∧ Subgroup.zpowers a = H := by
  obtain ⟨a, ha⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp hH
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
lemma genLTOne_lt_one : H.genLTOne < 1 :=
  H.exists_generator_lt_one.choose_spec.1

@[to_additive (attr := simp) negGen_zmultiples_eq_top]
lemma genLTOne_zpowers_eq_top : Subgroup.zpowers H.genLTOne = H :=
  H.exists_generator_lt_one.choose_spec.2

lemma genLTOne_unique (g : G) : g < 1 ∧ Subgroup.zpowers g = H → g = H.genLTOne := by
  rintro ⟨hg_lt, hg_top⟩
  rw [← H.genLTOne_zpowers_eq_top] at hg_top
  rcases Subgroup.zpowers_eq_zpowers_iff.mp hg_top with _ | h
  · assumption
  rw [← one_lt_inv', h] at hg_lt
  exact (not_lt_of_gt hg_lt <| Subgroup.genLTOne_lt_one _).elim

end Subgroup

section IsCyclic

variable (G) [Nontrivial G] [IsCyclic G]

/-- Given a cyclic linearly ordered commutative group, this is a generator that is `< 1`. -/
@[to_additive negGen "Given an additive cyclic linearly ordered commutative group, this is a
negative generator of it."]
noncomputable def genLTOne : G := (⊤ : Subgroup G).genLTOne

@[to_additive (attr := simp) negGen_eq_of_top]
lemma genLTOne_eq_of_top : genLTOne G = (⊤ : Subgroup G).genLTOne := rfl

lemma genLTOne_unique (g : G) : g < 1 ∧ Subgroup.zpowers g = ⊤ → g = genLTOne G :=
  (⊤ : Subgroup G).genLTOne_unique g

end IsCyclic

end LinearOrderedCommGroup
