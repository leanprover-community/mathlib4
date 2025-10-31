/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Algebra.Polynomial.Monic

/-!
# `Monic` does not necessarily imply `IsRegular` in a `Semiring` with no opposites

This counterexample shows that the hypothesis `Ring R` cannot be changed to `Semiring R` in
`Polynomial.Monic.isRegular`.

The example is very simple.

The coefficient Semiring is the Semiring `N₃` of the natural numbers `{0, 1, 2, 3}` where the
standard addition and standard multiplication are truncated at `3`.

The products `(X + 2) * (X + 2)` and `(X + 2) * (X + 3)` are equal to
`X ^ 2 + 4 * X + 4` and `X ^ 2 + 5 * X + 6` respectively.

By truncation, `4, 5, 6` all mean `3` in `N`.
It follows that multiplication by `(X + 2)` is not injective.
-/
open Polynomial

namespace Counterexample.NonRegular

/-- `N₃` is going to be a `CommSemiring` where addition and multiplication are truncated at `3`. -/
inductive N₃
  | zero
  | one
  | two
  | more

namespace N₃

instance : Zero N₃ := ⟨zero⟩
instance : One N₃ := ⟨one⟩

/-- Truncated addition on `N₃`. -/
instance : Add N₃ where
  add
  | 0, x => x
  | x, 0 => x
  | 1, 1 => two
  | _, _ => more

/-- Truncated multiplication on `N₃`. -/
instance : Mul N₃ where
  mul
  | 1, x => x
  | x, 1 => x
  | 0, _ => 0
  | _, 0 => 0
  | _, _ => more

instance : CommMonoid N₃ where
  mul_assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
  one_mul := by rintro ⟨⟩ <;> rfl
  mul_one := by rintro ⟨⟩ <;> rfl
  mul_comm := by rintro ⟨⟩ ⟨⟩ <;> rfl

instance : CommSemiring N₃ :=
  { (inferInstance : CommMonoid N₃) with
    add_assoc := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
    zero_add  := by rintro ⟨⟩ <;> rfl
    add_zero  := by rintro ⟨⟩ <;> rfl
    add_comm  := by rintro ⟨⟩ ⟨⟩ <;> rfl
    left_distrib := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
    right_distrib := by rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl
    zero_mul := by rintro ⟨⟩ <;> rfl
    mul_zero := by rintro ⟨⟩ <;> rfl
    nsmul := nsmulRec }

theorem X_add_two_mul_X_add_two : (X + C 2 : N₃[X]) * (X + C 2) = (X + C 2) * (X + C 3) := by
  simp only [mul_add, add_mul, X_mul, add_assoc]
  apply congr_arg
  rw [← add_assoc, ← add_mul, ← C_add, ← C_mul, ← C_mul]
  rw [← add_assoc, ← add_mul, ← C_add]
  rfl

/-! The main example: multiplication by the polynomial `X + 2` is not injective,
yet the polynomial is monic. -/

theorem monic_X_add_two : Monic (X + C 2 : N₃[X]) := by
  unfold Monic leadingCoeff
  nontriviality
  rw [natDegree_X_add_C 2]
  simp only [coeff_C, coeff_add, coeff_X_one, ite_false, add_zero, reduceCtorEq]

theorem not_isLeftRegular_X_add_two : ¬ IsLeftRegular (X + C 2 : N₃[X]) := by
  intro h
  have H := h X_add_two_mul_X_add_two
  apply_fun (coeff · 0) at H
  simp only [coeff_add, coeff_X_zero, zero_add, coeff_C, ite_true] at H
  cases H

/-- The statement of the counterexample: not all monic polynomials over semirings are regular. -/
theorem not_monic_implies_isLeftRegular :
    ¬∀ {R : Type} [Semiring R] (p : R[X]), Monic p → IsLeftRegular p :=
  fun h => not_isLeftRegular_X_add_two (h _ monic_X_add_two)

end N₃

end Counterexample.NonRegular
