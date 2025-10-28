/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# Small sets in the category of structured arrows

Here we prove a technical result about small sets in the category of structured arrows that will
be used in the proof of the Special Adjoint Functor Theorem.
-/

namespace CategoryTheory

-- morphism levels before object levels. See note [category theory universes].
universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace StructuredArrow

variable {S : D} {T : C ⥤ D}

instance small_inverseImage_proj_of_locallySmall
    {P : ObjectProperty C} [ObjectProperty.Small.{v₁} P] [LocallySmall.{v₁} D] :
    ObjectProperty.Small.{v₁} (P.inverseImage (proj S T)) := by
  suffices P.inverseImage (proj S T) = .ofObj fun f : Σ (G : Subtype P), S ⟶ T.obj G => mk f.2 by
    rw [this]
    infer_instance
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff, proj_obj, ObjectProperty.ofObj_iff,
    Sigma.exists, Subtype.exists, exists_prop]
  exact ⟨fun h ↦ ⟨_, h, _, rfl⟩, by rintro ⟨_, h, _, rfl⟩; exact h⟩

@[deprecated (since := "2025-10-07")] alias small_proj_preimage_of_locallySmall :=
  small_inverseImage_proj_of_locallySmall

end StructuredArrow

namespace CostructuredArrow

variable {S : C ⥤ D} {T : D}

instance small_inverseImage_proj_of_locallySmall
    {P : ObjectProperty C} [ObjectProperty.Small.{v₁} P] [LocallySmall.{v₁} D] :
    ObjectProperty.Small.{v₁} (P.inverseImage (proj S T)) := by
  suffices P.inverseImage (proj S T) = .ofObj fun f : Σ (G : Subtype P), S.obj G ⟶ T => mk f.2 by
    rw [this]
    infer_instance
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff, proj_obj, ObjectProperty.ofObj_iff,
    Sigma.exists, Subtype.exists, exists_prop]
  exact ⟨fun h ↦ ⟨_, h, _, rfl⟩, by rintro ⟨_, h, _, rfl⟩; exact h⟩

@[deprecated (since := "2025-10-07")] alias small_proj_preimage_of_locallySmall :=
  small_inverseImage_proj_of_locallySmall
end CostructuredArrow

end CategoryTheory
