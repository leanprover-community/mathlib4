/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Objects that are orthogonal to a property of morphisms

Given `W : MorphismProperty C`, we define `W.rightOrthogonal : ObjectProperty C`
which is the property of objects `Z` such that for any `f : X ⟶ Y` satisfying `W`,
the precomposition with `f` gives a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.
(In the file `CategoryTheory.Localization.Bousfield`, it is shown that this is
part of a Galois connection, with "dual" construction
`Localization.LeftBousfield.W : ObjectProperty C → MorphismProperty C`.)

-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (W : MorphismProperty C)

/-- The (right) orthogonal of `W : MorphismProperty C` is the property of objects `Z`
such that for any `f : X ⟶ Y` such that `W f` holds, the precomposition
with `f` gives a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.
(See the file `CategoryTheory.Localization.Bousfield` for the "dual" construction
`Localization.LeftBousfield.W : ObjectProperty C → MorphismProperty C`.) -/
def rightOrthogonal : ObjectProperty C :=
  fun Z ↦ ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    W f → Function.Bijective (fun (g : _ ⟶ Z) ↦ f ≫ g)

lemma rightOrthogonal_iff (Z : C) :
    W.rightOrthogonal Z ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
      W f → Function.Bijective (fun (g : _ ⟶ Z) ↦ f ≫ g) := Iff.rfl

instance : W.rightOrthogonal.IsClosedUnderIsomorphisms where
  of_iso {Z Z'} e hZ X Y f hf := by
    rw [← Function.Bijective.of_comp_iff _ (Iso.homToEquiv e).bijective]
    convert (Iso.homToEquiv e).bijective.comp (hZ f hf) using 1
    aesop

end MorphismProperty

end CategoryTheory
