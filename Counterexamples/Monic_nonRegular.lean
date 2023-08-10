/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Data.Polynomial.Monic

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

/-- `N₃` is going to be a `Commsemiring` where addition and multiplication are truncated at `3`. -/
inductive N₃
  | zero
  | one
  | two
  | more

namespace N₃

instance : Zero N₃ := ⟨zero⟩
instance : One N₃ := ⟨one⟩

/-- Truncated addition on `N₃`. -/
def add : N₃ → N₃ → N₃
  | 0, x => x
  | x, 0 => x
  | 1, 1 => two
  | _, _ => more

/-- Truncated multiplication on `N₃`. -/
def mul : N₃ → N₃ → N₃
  | 1, x => x
  | x, 1 => x
  | 0, _ => 0
  | _, 0 => 0
  | _, _ => more

instance : CommSemiring N₃ :=
{ add := add
  add_assoc := by rintro ⟨⟩ <;> rintro ⟨⟩ <;> rintro ⟨⟩ <;> rfl
  zero_add  := by rintro ⟨⟩ <;> rfl
  add_zero  := by rintro ⟨⟩ <;> rfl
  add_comm  := by rintro ⟨⟩ <;> rintro ⟨⟩ <;> rfl
  mul := mul
  left_distrib := by rintro ⟨⟩ <;> rintro ⟨⟩ <;> rintro ⟨⟩ <;> rfl
  right_distrib := by rintro ⟨⟩ <;> rintro ⟨⟩ <;> rintro ⟨⟩ <;> rfl
  mul_assoc := by rintro ⟨⟩ <;> rintro ⟨⟩ <;> rintro ⟨⟩ <;> rfl
  mul_comm := by rintro ⟨⟩ <;> rintro ⟨⟩ <;> rfl
  zero_mul := by rintro ⟨⟩ <;> rfl
  mul_zero := by rintro ⟨⟩ <;> rfl
  one_mul := by rintro ⟨⟩ <;> rfl
  mul_one := by rintro ⟨⟩ <;> rfl }

theorem mul_example : (X + C 2 : N₃[X]) * (X + C 2) = (X + C 2) * (X + C 3) := by
  simp only [mul_add, add_mul, X_mul, add_assoc]
  apply congr_arg
  rw [← add_assoc, ← add_mul, ← C_add, ← C_mul, ← C_mul]
  rw [← add_assoc, ← add_mul, ← C_add]
  rfl

/-- The main example: multiplication by the polynomial `X + 2` is not injective,
yet the polynomial is monic. -/
theorem Monic_and_nonLeftRegular : Monic (X + C 2 : N₃[X]) ∧ ¬ IsLeftRegular (X + C 2 : N₃[X]) := by
  constructor
  · unfold Monic leadingCoeff
    nontriviality
    rw [natDegree_X_add_C 2]
    simp only [natDegree_X_add_C 2, coeff_C, coeff_add, coeff_X_one, ite_false, add_zero]
  · unfold IsLeftRegular Function.Injective
    simp only [not_forall, exists_prop]
    refine ⟨(X + C 2), (X + C 3), mul_example, ?_⟩
    by_contra H
    apply_fun (coeff · 0) at H
    simp only [coeff_add, coeff_X_zero, zero_add, coeff_C, ite_true] at H
    cases H

end N₃

end Counterexample.NonRegular
