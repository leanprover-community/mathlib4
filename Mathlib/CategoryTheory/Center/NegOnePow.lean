/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Center.Preadditive
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Powers of `-1` in the center of a preadditive category

-/
set_option backward.defeqAttrib.useBackward true

public section

universe v u

namespace CategoryTheory.CatCenter

variable {C : Type u} [Category.{v} C] [Preadditive C]

open scoped IsMulCommutative in
@[simp]
lemma app_neg_one_zpow (n : ℤ) (X : C) :
    ((-1) ^ n : (CatCenter C)ˣ).val.app X = n.negOnePow • 𝟙 X := by
  obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ := Int.even_or_odd n
  · simp [zpow_add, ← mul_zpow, Int.negOnePow_even _ (Even.add_self n)]
  · rw [Int.negOnePow_odd _ (by exact odd_two_mul_add_one n)]
    simp [Units.smul_def, zpow_add, Int.two_mul, ← mul_zpow]

end CategoryTheory.CatCenter
