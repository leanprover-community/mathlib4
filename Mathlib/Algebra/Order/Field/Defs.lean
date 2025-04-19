/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Field.Defs

/-!
# Linear ordered (semi)fields

A linear ordered (semi)field is a (semi)field equipped with a linear order such that
* addition respects the order: `a ≤ b → c + a ≤ c + b`;
* multiplication of positives is positive: `0 < a → 0 < b → 0 < a * b`;
* `0 < 1`.

## Main Definitions

* `LinearOrderedSemifield`: Typeclass for linear order semifields.
* `LinearOrderedField`: Typeclass for linear ordered fields.
-/

-- Guard against import creep.
assert_not_exists MonoidHom

variable {K : Type*}

set_option linter.deprecated false in
/-- A linear ordered semifield is a field with a linear order respecting the operations. -/
@[deprecated "Use `[Semifield K] [LinearOrder K] [IsStrictOrderedRing K]` instead."
  (since := "2025-04-10")]
structure LinearOrderedSemifield (K : Type*) extends LinearOrderedCommSemiring K, Semifield K

set_option linter.deprecated false in
/-- A linear ordered field is a field with a linear order respecting the operations. -/
@[deprecated "Use `[Field K] [LinearOrder K] [IsStrictOrderedRing K]` instead."
  (since := "2025-04-10")]
structure LinearOrderedField (K : Type*) extends LinearOrderedCommRing K, Field K

attribute [nolint docBlame] LinearOrderedSemifield.toSemifield LinearOrderedField.toField

variable [Semifield K] [LinearOrder K] {a b c : K}

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel`. -/
lemma mul_inv_le_one [ZeroLEOneClass K] : a * a⁻¹ ≤ 1 := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel`. -/
lemma inv_mul_le_one [ZeroLEOneClass K] : a⁻¹ * a ≤ 1 := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel_left`. -/
lemma mul_inv_left_le (hb : 0 ≤ b) : a * (a⁻¹ * b) ≤ b := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel_left`. -/
lemma le_mul_inv_left (hb : b ≤ 0) : b ≤ a * (a⁻¹ * b) := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel_left`. -/
lemma inv_mul_left_le (hb : 0 ≤ b) : a⁻¹ * (a * b) ≤ b := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel_left`. -/
lemma le_inv_mul_left (hb : b ≤ 0) : b ≤ a⁻¹ * (a * b) := by
  obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `mul_inv_cancel_right`. -/
lemma mul_inv_right_le (ha : 0 ≤ a) : a * b * b⁻¹ ≤ a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `mul_inv_cancel_right`. -/
lemma le_mul_inv_right (ha : a ≤ 0) : a ≤ a * b * b⁻¹ := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `inv_mul_cancel_right`. -/
lemma inv_mul_right_le (ha : 0 ≤ a) : a * b⁻¹ * b ≤ a := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `b ≠ 0`. See `inv_mul_cancel_right`. -/
lemma le_inv_mul_right (ha : a ≤ 0) : a ≤ a * b⁻¹ * b := by
  obtain rfl | hb := eq_or_ne b 0 <;> simp [*]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_left`. -/
lemma mul_div_mul_left_le (h : 0 ≤ a / b) : c * a / (c * b) ≤ a / b := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_left`. -/
lemma le_mul_div_mul_left (h : a / b ≤ 0) : a / b ≤ c * a / (c * b) := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_left _ _ hc]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_right`. -/
lemma mul_div_mul_right_le (h : 0 ≤ a / b) : a * c / (b * c) ≤ a / b := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]

/-- Equality holds when `c ≠ 0`. See `mul_div_mul_right`. -/
lemma le_mul_div_mul_right (h : a / b ≤ 0) : a / b ≤ a * c / (b * c) := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa
  · rw [mul_div_mul_right _ _ hc]
