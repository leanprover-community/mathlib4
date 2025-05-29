/-
Copyright (c) 2025 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
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

end Subgroup

variable (G) [Nontrivial G]

/-- Given a cyclic linearly ordered commutative group, this is a generator that is `< 1`. -/
@[to_additive negGen "Given an additive cyclic linearly ordered commutative group, this is a
negative generator of it."]
noncomputable def genLTOne : G := (⊤ : Subgroup G).genLTOne

@[to_additive (attr := simp) negGen_eq_of_top]
lemma genLTOne_eq_of_top : genLTOne G = (⊤ : Subgroup G).genLTOne := rfl

end LinearOrderedCommGroup
