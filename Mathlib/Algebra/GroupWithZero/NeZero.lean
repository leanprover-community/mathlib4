/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero

/-!
# `NeZero 1` in a nontrivial `MulZeroOneClass`.

This file exists to minimize the dependencies of `Mathlib/Algebra/GroupWithZero/Defs.lean`,
which is a part of the algebraic hierarchy used by basic tactics.
-/

assert_not_exists DenselyOrdered Ring

universe u

variable {M₀ M₀' : Type*} [MulZeroOneClass M₀] [Nontrivial M₀]

/-- In a nontrivial monoid with zero, zero and one are different. -/
instance NeZero.one : NeZero (1 : M₀) := ⟨by
  intro h
  rcases exists_pair_ne M₀ with ⟨x, y, hx⟩
  apply hx
  calc
    x = 1 * x := by rw [one_mul]
    _ = 0 := by rw [h, zero_mul]
    _ = 1 * y := by rw [h, zero_mul]
    _ = y := by rw [one_mul]⟩

/-- Pullback a `Nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
theorem domain_nontrivial [Zero M₀'] [One M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    Nontrivial M₀' :=
  ⟨⟨0, 1, mt (congr_arg f) <| by
    rw [zero, one]
    exact zero_ne_one⟩⟩

section GroupWithZero

variable {G₀ : Type*} [GroupWithZero G₀] {a : G₀}

-- Porting note: used `simpa` to prove `False` in lean3
theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by
  have := mul_inv_cancel₀ h
  simp only [a_eq_0, mul_zero, zero_ne_one] at this

@[simp high] -- should take priority over `IsUnit.inv_mul_cancel`
theorem inv_mul_cancel₀ (h : a ≠ 0) : a⁻¹ * a = 1 :=
  calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
    _ = 1 := by simp [inv_ne_zero h]

end GroupWithZero
