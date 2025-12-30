/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
<<<<<<< HEAD
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Center.Basic
=======
module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Center.Basic
>>>>>>> origin/master

/-!
# The center of an additive category

-/

<<<<<<< HEAD
=======
@[expose] public section

>>>>>>> origin/master
universe v u

namespace CategoryTheory

namespace CatCenter

variable {C : Type u} [Category.{v} C] [Preadditive C]

@[simp]
lemma app_add (z₁ z₂ : CatCenter C) (X : C) :
    (z₁ + z₂).app X = z₁.app X + z₂.app X := rfl

<<<<<<< HEAD
=======
@[simp]
lemma app_sub (z₁ z₂ : CatCenter C) (X : C) :
    (z₁ - z₂).app X = z₁.app X - z₂.app X := rfl

@[simp]
lemma app_neg (z : CatCenter C) (X : C) :
    (-z).app X = - z.app X := rfl

>>>>>>> origin/master
end CatCenter

end CategoryTheory
