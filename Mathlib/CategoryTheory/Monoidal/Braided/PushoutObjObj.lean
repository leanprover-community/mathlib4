/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Pushout-tensor-products and the braiding

In this file, we introduce a definition `Functor.PushoutObjObj.flipTensor`
which switches the two morphisms involved in pushout-tensor-products
in a braided category.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite

namespace CategoryTheory.Functor.PushoutObjObj

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
  {X₁ Y₁ X₂ Y₂ : C} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
  (sq : (curriedTensor C).PushoutObjObj f₁ f₂)

/-- In a braided monoidal category, from a `Functor.PushoutObjObj` structure for
the bifunctor `curriedTensor` and two morphism `f₁` and `f₂`, one may
obtain a similar structure for `f₂` and `f₁`. -/
@[simps!]
def flipTensor : (curriedTensor C).PushoutObjObj f₂ f₁ :=
  sq.flip.ofNatIso (BraidedCategory.curriedBraidingNatIso _).symm

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma flipTensor_ι : dsimp% sq.flipTensor.ι = sq.ι ≫ (β_ _ _).inv := by
  simp [flipTensor]

end CategoryTheory.Functor.PushoutObjObj
