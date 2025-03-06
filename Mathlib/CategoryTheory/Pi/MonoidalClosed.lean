/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Pi.Monoidal


/-!
# The pointwise closed monoidal strucutre on the product of families of closed monoidal categories

Given a family of closed monoidal categories `C i`, we show that the product of these categories
is a closed monoidal category with the pointwise structure.

-/

namespace CategoryTheory

namespace Pi

open Category MonoidalCategory ihom

universe w₁ v₁ u₁

variable {I : Type w₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
[∀ i, MonoidalCategory (C i)] [∀ i, MonoidalClosed (C i)]

/-- The internal hom functor `X ⟶[∀ i, C i] -` -/
@[simps!]
def closedIhom (X : ∀ i, C i) : (∀ i, C i) ⥤ (∀ i, C i) where
  obj Y := fun i ↦ (X i ⟶[C i] Y i)
  map {Y Z} f := fun i ↦ (ihom (X i)).map (f i)

/-- The unit for the adjunction `(tensorLeft X) ⊣ (closedIhom X)`. -/
@[simps]
def closedUnit (X : ∀ i, C i) : 𝟭 (∀ i, C i) ⟶ tensorLeft X ⋙ (closedIhom X) where
  app Y := fun i ↦ (ihom.coev (X i)).app (Y i)

/-- The counit for the adjunction `(tensorLeft X) ⊣ (closedIhom X)`. -/
@[simps]
def closedCounit (X : ∀ i, C i) : (closedIhom X) ⋙ tensorLeft X ⟶ 𝟭 (∀ i, C i) where
  app Y := fun i ↦ (ihom.ev (X i)).app (Y i)

/-- `Pi.monoidalClosed C` equipps the product of a family of closed monoidal categories with
a pointwise closed monoidal structure. -/
instance monoidalClosed : MonoidalClosed (∀ i, C i) where
    closed X := {
      rightAdj := closedIhom X
      adj := {
        unit := closedUnit X
        counit := closedCounit X
      }
    }

end Pi

end CategoryTheory
