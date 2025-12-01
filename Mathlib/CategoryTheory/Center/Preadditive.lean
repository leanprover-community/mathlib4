/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# The center of an additive category

-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace CatCenter

variable {C : Type u} [Category.{v} C] [Preadditive C]

@[simp]
lemma app_add (z₁ z₂ : CatCenter C) (X : C) :
    (z₁ + z₂).app X = z₁.app X + z₂.app X := rfl

@[simp]
lemma app_sub (z₁ z₂ : CatCenter C) (X : C) :
    (z₁ - z₂).app X = z₁.app X - z₂.app X := rfl

@[simp]
lemma app_neg (z : CatCenter C) (X : C) :
    (-z).app X = - z.app X := rfl

@[simp]
lemma app_neg_one_zpow (n : ℤ) (X : C) :
    ((-1) ^ n : (CatCenter C)ˣ).val.app X = n.negOnePow • 𝟙 X := by
  obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ := Int.even_or_odd n
  · simp [zpow_add, ← mul_zpow, Int.negOnePow_even _ (Even.add_self n)]
  · rw [Int.negOnePow_odd _ (by exact odd_two_mul_add_one n)]
    simp [Units.smul_def, zpow_add, Int.two_mul, ← mul_zpow]

end CatCenter

end CategoryTheory
