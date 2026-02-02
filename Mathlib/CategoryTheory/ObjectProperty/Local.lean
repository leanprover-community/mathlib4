/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Objects that are local with respect to a property of morphisms

Given `W : MorphismProperty C`, we define `W.isLocal : ObjectProperty C`
which is the property of objects `Z` such that for any `f : X ⟶ Y` satisfying `W`,
the precomposition with `f` gives a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.
(In the file `Mathlib/CategoryTheory/Localization/Bousfield.lean`, it is shown that this is
part of a Galois connection, with "dual" construction
`ObjectProperty.isLocal : ObjectProperty C → MorphismProperty C`.)

We also introduce the dual notion `W.isColocal : ObjectProperty C`.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (W : MorphismProperty C)

/-- Given `W : MorphismProperty C`, this is the property of `W`-local objects, i.e.
the objects `Z` such that for any `f : X ⟶ Y` such that `W f` holds, the precomposition
with `f` gives a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.
(See the file `Mathlib/CategoryTheory/Localization/Bousfield.lean` for the "dual" construction
`ObjectProperty.isLocal : ObjectProperty C → MorphismProperty C`.) -/
def isLocal : ObjectProperty C :=
  fun Z ↦ ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    W f → Function.Bijective (fun (g : _ ⟶ Z) ↦ f ≫ g)

lemma isLocal_iff (Z : C) :
    W.isLocal Z ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
      W f → Function.Bijective (fun (g : _ ⟶ Z) ↦ f ≫ g) := Iff.rfl

/-- Given `W : MorphismProperty C`, this is the property of `W`-colocal objects, i.e.
the objects `X` such that for any `g : Y ⟶ Z` such that `W g` holds, the postcomposition
with `g` gives a bijection `(X ⟶ Y) ≃ (X ⟶ Z)`.
(See the file `Mathlib/CategoryTheory/Localization/Bousfield.lean` for the "dual" construction
`ObjectProperty.isColocal : ObjectProperty C → MorphismProperty C`.) -/
def isColocal : ObjectProperty C :=
  fun X ↦ ∀ ⦃Y Z : C⦄ (g : Y ⟶ Z),
    W g → Function.Bijective (fun (f : X ⟶ _) ↦ f ≫ g)

lemma isColocal_iff (X : C) :
    W.isColocal X ↔ ∀ ⦃Y Z : C⦄ (g : Y ⟶ Z),
      W g → Function.Bijective (fun (f : X ⟶ Y) ↦ f ≫ g) := Iff.rfl

instance : W.isLocal.IsClosedUnderIsomorphisms where
  of_iso {Z Z'} e hZ X Y f hf := by
    rw [← Function.Bijective.of_comp_iff _ (Iso.homToEquiv e).bijective]
    convert (Iso.homToEquiv e).bijective.comp (hZ f hf) using 1
    aesop

instance : W.isColocal.IsClosedUnderIsomorphisms where
  of_iso {X X'} e hX Y Z g hg := by
    rw [← Function.Bijective.of_comp_iff _ (Iso.homFromEquiv e).bijective]
    convert (Iso.homFromEquiv e).bijective.comp (hX g hg) using 1
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

instance (J : Type u') [Category.{v'} J] :
    W.isColocal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := fun X ⟨p⟩ Y Z g hg ↦ by
    refine ⟨fun f₁ f₂ h ↦ p.isColimit.hom_ext
      (fun j ↦ (p.prop_diag_obj j g hg).1 (by simp [h])), fun f ↦ ?_⟩
    choose app h using fun j ↦ (p.prop_diag_obj j g hg).2 (p.ι.app j ≫ f)
    exact ⟨p.isColimit.desc (Cocone.mk _
      { app := app
        naturality _ _ a := (p.prop_diag_obj _ g hg).1
          (by simp [h]) }),
      p.isColimit.hom_ext (fun j ↦ by simp [p.isColimit.fac_assoc, h])⟩

end MorphismProperty

end CategoryTheory
