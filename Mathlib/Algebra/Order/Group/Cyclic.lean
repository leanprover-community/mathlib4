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
@[to_additive negGen /-- Given an additive subgroup of an additive cyclic linearly ordered
commutative group, this is a negative generator of the subgroup. -/]
protected noncomputable def genLTOne : G := H.exists_generator_lt_one.choose

@[to_additive negGen_neg]
lemma genLTOne_lt_one : H.genLTOne < 1 :=
  H.exists_generator_lt_one.choose_spec.1

@[to_additive (attr := simp) negGen_zmultiples_eq_top]
lemma genLTOne_zpowers_eq_top : Subgroup.zpowers H.genLTOne = H :=
  H.exists_generator_lt_one.choose_spec.2

lemma genLTOne_mem : H.genLTOne ∈ H := by
  nth_rewrite 1 [← H.genLTOne_zpowers_eq_top]
  exact Subgroup.mem_zpowers (Subgroup.genLTOne H)

lemma genLTOne_unique {g : G} (hg : g < 1) (hH : Subgroup.zpowers g = H) : g = H.genLTOne := by
  have hg' : ¬ IsOfFinOrder g := not_isOfFinOrder_of_isMulTorsionFree (ne_of_lt hg)
  rw [← H.genLTOne_zpowers_eq_top] at hH
  rcases (Subgroup.zpowers_eq_zpowers_iff hg').mp hH with _ | h
  · assumption
  rw [← one_lt_inv', h] at hg
  exact (not_lt_of_gt hg <| Subgroup.genLTOne_lt_one _).elim

lemma genLTOne_unique_of_zpowers_eq {g1 g2 : G} (hg1 : g1 < 1) (hg2 : g2 < 1)
    (h : Subgroup.zpowers g1 = Subgroup.zpowers g2) : g1 = g2 := by
  rcases (Subgroup.zpowers g2).bot_or_nontrivial with (h' | h')
  · rw [h'] at h
    simp_all only [Subgroup.zpowers_eq_bot]
  · have h1 : IsCyclic ↥(Subgroup.zpowers g2) := by
      rw [Subgroup.isCyclic_iff_exists_zpowers_eq_top]; use g2
    have h2 : Nontrivial ↥(Subgroup.zpowers g1) := by rw [h]; exact h'
    have h3 : IsCyclic ↥(Subgroup.zpowers g1) := by rw [h]; exact h1
    simp only [(Subgroup.zpowers g2).genLTOne_unique hg1 h]
    simp only [← h]
    simp only [(Subgroup.zpowers g1).genLTOne_unique hg2 h.symm]

end Subgroup

section IsCyclic

variable (G) [Nontrivial G] [IsCyclic G]

/-- Given a cyclic linearly ordered commutative group, this is a generator that is `< 1`. -/
@[to_additive negGen /-- Given an additive cyclic linearly ordered commutative group, this is a
negative generator of it. -/]
noncomputable def genLTOne : G := (⊤ : Subgroup G).genLTOne

@[to_additive (attr := simp) negGen_eq_of_top]
lemma genLTOne_eq_of_top : genLTOne G = (⊤ : Subgroup G).genLTOne := rfl

lemma genLTOne_unique {g : G} (hg : g < 1) (htop : Subgroup.zpowers g = ⊤) : g = genLTOne G :=
  (⊤ : Subgroup G).genLTOne_unique hg htop

end IsCyclic

end LinearOrderedCommGroup
