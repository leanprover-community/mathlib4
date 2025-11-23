/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Center.Basic

/-!
# The center of an additive category

-/

universe v u

namespace CategoryTheory

namespace CatCenter

variable {C : Type u} [Category.{v} C] [Preadditive C]

@[simp]
lemma app_add (z₁ z₂ : CatCenter C) (X : C) :
    (z₁ + z₂).app X = z₁.app X + z₂.app X := rfl

end CatCenter

end CategoryTheory
