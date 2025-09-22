/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
import Mathlib.Logic.Small.Basic

/-!
# Smallness of a property of objects

-/

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- A property of objects is small relative to a universe `w`
if the corresponding subtype is. -/
protected abbrev Small (P : ObjectProperty C) : Prop := _root_.Small.{w} (Subtype P)

instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    Small.{w} P.FullSubcategory :=
  small_of_surjective (f := fun (x : Subtype P) ↦ ⟨x.1, x.2⟩) (fun x ↦ ⟨⟨x.1, x.2⟩, rfl⟩)

lemma small_of_le {P Q : ObjectProperty C} [ObjectProperty.Small.{w} Q] (h : P ≤ Q) :
    ObjectProperty.Small.{w} P :=
  small_of_injective (Subtype.map_injective h Function.injective_id)

instance {P Q : ObjectProperty C} [ObjectProperty.Small.{w} Q] :
    ObjectProperty.Small.{w} (P ⊓ Q) :=
  small_of_le inf_le_right

instance {P Q : ObjectProperty C} [ObjectProperty.Small.{w} P] :
    ObjectProperty.Small.{w} (P ⊓ Q) :=
  small_of_le inf_le_left

protected class EssentiallySmall (P : ObjectProperty C) : Prop where
  exists_small_le (P) : ∃ (Q : ObjectProperty C) (_ : ObjectProperty.Small.{w} Q),
    P ≤ Q.isoClosure

instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    ObjectProperty.EssentiallySmall.{w} P where
  exists_small_le := ⟨P, inferInstance, le_isoClosure P⟩

instance (P : ObjectProperty C) [ObjectProperty.Small.{w} P] :
    ObjectProperty.EssentiallySmall.{w} P.isoClosure where
  exists_small_le := ⟨P, inferInstance, by rfl⟩

lemma EssentiallySmall.exists_small (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [ObjectProperty.EssentiallySmall.{w} P] :
    ∃ (P₀ : ObjectProperty C) (_ : ObjectProperty.Small.{w} P₀), P = P₀.isoClosure := by
  obtain ⟨Q, _, hQ⟩ := exists_small_le P
  refine ⟨Q ⊓ P, inferInstance, le_antisymm ?_ ?_⟩
  · intro X hX
    obtain ⟨Y, hY, ⟨e⟩⟩ := hQ _ hX
    refine ⟨Y, ?_, ⟨e⟩⟩
    simp only [prop_inf_iff]
    exact ⟨hY, P.prop_of_iso e hX⟩
  · conv_rhs => rw [← P.isoClosure_eq_self]
    exact monotone_isoClosure inf_le_right

end CategoryTheory.ObjectProperty
