/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Objects that are local with respect to a property of morphisms

Given `W : MorphismProperty C`, we define `W.isLocal : ObjectProperty C`
which is the property of objects `Z` such that for any `f : X ⟶ Y` satisfying `W`,
the precomposition with `f` gives a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.
(In the file `CategoryTheory.Localization.Bousfield`, it is shown that this is
part of a Galois connection, with "dual" construction
`Localization.LeftBousfield.W : ObjectProperty C → MorphismProperty C`.)

-/

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (W : MorphismProperty C)

/-- Given `W : MorphismProperty C`, this is the property of `W`-local objects, i.e.
the objects `Z` such that for any `f : X ⟶ Y` such that `W f` holds, the precomposition
with `f` gives a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.
(See the file `CategoryTheory.Localization.Bousfield` for the "dual" construction
`Localization.LeftBousfield.W : ObjectProperty C → MorphismProperty C`.) -/
def isLocal : ObjectProperty C :=
  fun Z ↦ ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    W f → Function.Bijective (fun (g : _ ⟶ Z) ↦ f ≫ g)

lemma isLocal_iff (Z : C) :
    W.isLocal Z ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
      W f → Function.Bijective (fun (g : _ ⟶ Z) ↦ f ≫ g) := Iff.rfl

instance : W.isLocal.IsClosedUnderIsomorphisms where
  of_iso {Z Z'} e hZ X Y f hf := by
    rw [← Function.Bijective.of_comp_iff _ (Iso.homToEquiv e).bijective]
    convert (Iso.homToEquiv e).bijective.comp (hZ f hf) using 1
    aesop

instance (J : Type u') [Category.{v'} J] :
    W.isLocal.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := fun Z ⟨p⟩ X Y f hf ↦ by
    refine ⟨fun g₁ g₂ h ↦ p.isLimit.hom_ext
      (fun j ↦ (p.prop_diag_obj j f hf).1 (by simp [reassoc_of% h])), fun g ↦ ?_⟩
    choose app h using fun j ↦ (p.prop_diag_obj j f hf).2 (g ≫ p.π.app j)
    exact ⟨p.isLimit.lift (Cone.mk _
      { app := app
        naturality _ _ a := (p.prop_diag_obj _ f hf).1
          (by simp [reassoc_of% h, h, p.w a]) }),
      p.isLimit.hom_ext (fun j ↦ by simp [p.isLimit.fac, h])⟩

end MorphismProperty

end CategoryTheory
