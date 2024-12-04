/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Endomorphism

/-!
# Center of a category

-/
universe v u w

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C]

abbrev CatCenter := End (𝟭 C)

namespace CatCenter

variable {C}

@[ext]
lemma ext (x y : CatCenter C) (h : ∀ (X : C), x.app X = y.app X) : x = y :=
  NatTrans.ext (funext h)

/-- `(x * y).app X = y.app X ≫ x.app X`. -/
lemma mul_app' (x y : CatCenter C) (X : C) : (x * y).app X = y.app X ≫ x.app X := rfl

lemma mul_app (x y : CatCenter C) (X : C) : (x * y).app X = x.app X ≫ y.app X := by
  rw [mul_app']
  exact x.naturality (y.app X)

lemma mul_comm (x y : CatCenter C) : x * y = y * x := by
  ext X
  rw [mul_app' x y, mul_app y x]

end CatCenter

end CategoryTheory
