/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Sites.Descent.PullbackStruct
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Monad.Comonadicity

/-!
# Descent data and coalgebras...

-/

namespace CategoryTheory

open Bicategory Limits

@[simps]
def Bicategory.Adjunction.toCategory {C D : Cat} {F : C ⟶ D} {G : D ⟶ C}
    (adj : Bicategory.Adjunction F G) :
    CategoryTheory.Adjunction F G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    have := congr_app adj.left_triangle X
    dsimp [leftZigzag, bicategoricalComp] at this
    simpa [Cat.associator_hom_app, Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app] using this
  right_triangle_components X := by
    have := congr_app adj.right_triangle X
    dsimp [rightZigzag, bicategoricalComp] at this
    simpa [Cat.associator_inv_app, Cat.leftUnitor_inv_app] using this

variable {C : Type*} [Category C]

namespace Pseudofunctor

variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) (Adj Cat)) {X S  : C} (f : X ⟶ S)

def descentDataEquivCoalgebra (sq : ChosenPullback f f) (diag : sq.Diagonal)
  (sq₃ : ChosenPullback₃ sq sq sq) :
    (F.comp Adj.forget₁).DescentData (fun (_ : Unit) ↦ f) ≌
      (F.map f.op.toLoc).adj.toCategory.toComonad.Coalgebra := sorry

end Pseudofunctor

end CategoryTheory
