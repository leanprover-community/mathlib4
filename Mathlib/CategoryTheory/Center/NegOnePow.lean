/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Center.Preadditive
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Powers of `-1` in the center of a preadditive category

-/

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
