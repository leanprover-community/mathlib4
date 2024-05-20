/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.GroupWithZero.Hom

#align_import algebra.group_power.ring from "leanprover-community/mathlib"@"fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e"

/-!
# Power operations on monoids with zero, semirings, and rings

This file provides additional lemmas about the natural power operator on rings and semirings.
Further lemmas about ordered semirings and rings can be found in `Algebra.GroupPower.Order`.
-/

variable {R S M : Type*}

section CommMonoidWithZero

variable [CommMonoidWithZero M] {n : ℕ} (hn : n ≠ 0)

/-- We define `x ↦ x^n` (for positive `n : ℕ`) as a `MonoidWithZeroHom` -/
def powMonoidWithZeroHom : M →*₀ M :=
  { powMonoidHom n with map_zero' := zero_pow hn }
#align pow_monoid_with_zero_hom powMonoidWithZeroHom

@[simp]
theorem coe_powMonoidWithZeroHom : (powMonoidWithZeroHom hn : M → M) = fun x ↦ (x^n : M) := rfl
#align coe_pow_monoid_with_zero_hom coe_powMonoidWithZeroHom

@[simp]
theorem powMonoidWithZeroHom_apply (a : M) : powMonoidWithZeroHom hn a = a ^ n :=
  rfl
#align pow_monoid_with_zero_hom_apply powMonoidWithZeroHom_apply

end CommMonoidWithZero

theorem pow_dvd_pow_iff [CancelCommMonoidWithZero R] {x : R} {n m : ℕ} (h0 : x ≠ 0)
    (h1 : ¬IsUnit x) : x ^ n ∣ x ^ m ↔ n ≤ m := by
  constructor
  · intro h
    rw [← not_lt]
    intro hmn
    apply h1
    have : x ^ m * x ∣ x ^ m * 1 := by
      rw [← pow_succ, mul_one]
      exact (pow_dvd_pow _ (Nat.succ_le_of_lt hmn)).trans h
    rwa [mul_dvd_mul_iff_left, ← isUnit_iff_dvd_one] at this
    apply pow_ne_zero m h0
  · apply pow_dvd_pow
#align pow_dvd_pow_iff pow_dvd_pow_iff
