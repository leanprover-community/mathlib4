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

variable {α : Type*}

/-- A linear ordered semifield is a field with a linear order respecting the operations. -/
class LinearOrderedSemifield (α : Type*) extends LinearOrderedCommSemiring α, Semifield α

/-- A linear ordered field is a field with a linear order respecting the operations. -/
class LinearOrderedField (α : Type*) extends LinearOrderedCommRing α, Field α

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedField.toLinearOrderedSemifield [LinearOrderedField α] :
    LinearOrderedSemifield α :=
  { LinearOrderedRing.toLinearOrderedSemiring, ‹LinearOrderedField α› with }

variable [LinearOrderedSemifield α] {a b : α}

/-- Equality holds when `a ≠ 0`. See `mul_inv_cancel`. -/
lemma mul_inv_le_one : a * a⁻¹ ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

/-- Equality holds when `a ≠ 0`. See `inv_mul_cancel`. -/
lemma inv_mul_le_one : a⁻¹ * a ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]

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
