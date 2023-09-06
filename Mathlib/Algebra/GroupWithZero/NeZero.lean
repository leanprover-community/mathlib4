/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero

#align_import algebra.group_with_zero.defs from "leanprover-community/mathlib"@"2f3994e1b117b1e1da49bcfb67334f33460c3ce4"

/-!
# `NeZero 1` in a nontrivial `MulZeroOneClass`.

This file exists to minimize the dependencies of `Mathlib.Algebra.GroupWithZero.Defs`,
which is a part of the algebraic hierarchy used by basic tactics.
-/

universe u

set_option autoImplicit true

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

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
#align ne_zero.one NeZero.one

/-- Pullback a `Nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
theorem pullback_nonzero [Zero M₀'] [One M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    Nontrivial M₀' :=
  ⟨⟨0, 1, mt (congr_arg f) <| by
    rw [zero, one]
    exact zero_ne_one⟩⟩
#align pullback_nonzero pullback_nonzero

section GroupWithZero

variable [GroupWithZero G₀] {a b c g h x : G₀}

-- Porting note: used `simpa` to prove `False` in lean3
theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by
  have := mul_inv_cancel h
  simp only [a_eq_0, mul_zero, zero_ne_one] at this
#align inv_ne_zero inv_ne_zero

@[simp]
theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
  calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
    _ = 1 := by simp [inv_ne_zero h]
#align inv_mul_cancel inv_mul_cancel

end GroupWithZero
