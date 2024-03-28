/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Set.Basic

/-! # Sets of objects which respects isomorphisms

This file introduces the type class `S.RespectsIso` for `S : Set C`
with `C` is category.

-/

open CategoryTheory

variable {C : Type*} [Category C]

namespace Set

variable (S T : Set C)

/-- A set `S : Set C` respects isomorphisms if whenever `X ∈ S`, then all the
objects that are isomorphic to `X` also belong to `S`.  -/
class RespectsIso : Prop where
  condition {X Y : C} (_ : X ≅ Y) (_ : X ∈ S) : Y ∈ S

lemma mem_of_iso [S.RespectsIso] {X Y : C} (e : X ≅ Y) (hX : X ∈ S) : Y ∈ S :=
  RespectsIso.condition e hX

lemma mem_iff_of_iso [S.RespectsIso] {X Y : C} (e : X ≅ Y) : X ∈ S ↔ Y ∈ S :=
  ⟨S.mem_of_iso e, S.mem_of_iso e.symm⟩

/-- The closure by isomorphisms of a set of objects in a category. -/
def isoClosure : Set C := fun X => ∃ (Y : C) (_ : Y ∈ S), Nonempty (X ≅ Y)

lemma subset_isoClosure : S ⊆ S.isoClosure := fun X hX => ⟨X, hX, ⟨Iso.refl X⟩⟩

variable {S T} in
lemma monotone_isoClosure (h : S ⊆ T) : S.isoClosure ⊆ T.isoClosure := by
  rintro X ⟨X', hX', ⟨e⟩⟩
  exact ⟨X', h hX', ⟨e⟩⟩

lemma isoClosure_eq_self [S.RespectsIso] : S.isoClosure = S := by
  apply subset_antisymm
  · intro X ⟨Y, hY, ⟨e⟩⟩
    exact S.mem_of_iso e.symm hY
  · exact S.subset_isoClosure

lemma isoClosure_subset_iff [T.RespectsIso] : S.isoClosure ⊆ T ↔ S ⊆ T :=
  ⟨(subset_isoClosure S).trans,
    fun h => (monotone_isoClosure h).trans (by rw [isoClosure_eq_self])⟩

instance (S : Set C) : S.isoClosure.RespectsIso where
  condition := by
    rintro X Y e ⟨Z, hZ, ⟨f⟩⟩
    exact ⟨Z, hZ, ⟨e.symm.trans f⟩⟩

end Set
