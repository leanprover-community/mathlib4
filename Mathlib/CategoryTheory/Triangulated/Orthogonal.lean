/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Orthogonal of triangulated subcategories

Let `P` be a triangulated subcategory of a pretriangulated category `C`. We show
that `P.rightOrthogonal` (which consists of objects `Y` with no nonzero
map `X ⟶ Y` with `X` satisfying `P`) is a triangulated subcategory. The dual result
for `P.leftOrthogonal` is also obtained.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)

section

variable {M : Type*} [AddGroup M] [HasShift C M] [HasZeroMorphisms C]

instance [P.IsStableUnderShift M] : P.rightOrthogonal.IsStableUnderShift M where
  isStableUnderShiftBy n := ⟨fun Y hY X f hX ↦ by
    obtain ⟨g, rfl⟩ := ((shiftEquiv C n).symm.toAdjunction.homEquiv _ _).surjective f
    simp [hY g (P.le_shift (-n) _ hX), Adjunction.homEquiv_unit]⟩

instance [P.IsStableUnderShift M] : P.leftOrthogonal.IsStableUnderShift M where
  isStableUnderShiftBy n := ⟨fun X hX Y f hY ↦ by
    obtain ⟨g, rfl⟩ := ((shiftEquiv C n).toAdjunction.homEquiv _ _).symm.surjective f
    simp [hX g (P.le_shift (-n) _ hY), Adjunction.homEquiv_counit]⟩

end

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

instance : P.rightOrthogonal.IsTriangulatedClosed₂ :=
  .mk' (fun T hT h₁ h₃ X f hX ↦ by
    obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT f (h₃ _ hX)
    simp [h₁ g hX])

instance : P.leftOrthogonal.IsTriangulatedClosed₂ :=
  .mk' (fun T hT h₁ h₃ Y f hY ↦ by
    obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.yoneda_exact₂ T hT f (h₁ _ hY)
    simp [h₃ g hY])

instance [P.IsStableUnderShift ℤ] : P.rightOrthogonal.IsTriangulated where

instance [P.IsStableUnderShift ℤ] : P.leftOrthogonal.IsTriangulated where

example [P.IsTriangulated] : P.rightOrthogonal.IsTriangulated := inferInstance

example [P.IsTriangulated] : P.leftOrthogonal.IsTriangulated := inferInstance

end ObjectProperty

end CategoryTheory
