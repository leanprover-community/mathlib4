/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Defs

#align_import algebra.order.field.defs from "leanprover-community/mathlib"@"655994e298904d7e5bbd1e18c95defd7b543eb94"

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
#align linear_ordered_semifield LinearOrderedSemifield

/-- A linear ordered field is a field with a linear order respecting the operations. -/
class LinearOrderedField (α : Type*) extends LinearOrderedCommRing α, Field α
#align linear_ordered_field LinearOrderedField

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedField.toLinearOrderedSemifield [LinearOrderedField α] :
    LinearOrderedSemifield α :=
  { LinearOrderedRing.toLinearOrderedSemiring, ‹LinearOrderedField α› with }
#align linear_ordered_field.to_linear_ordered_semifield LinearOrderedField.toLinearOrderedSemifield

variable [LinearOrderedSemifield α] {a b : α}

@[simp] lemma inv_pos : 0 < a⁻¹ ↔ 0 < a :=
  suffices ∀ a : α, 0 < a → 0 < a⁻¹ from ⟨fun h ↦ inv_inv a ▸ this _ h, this a⟩
  fun a ha ↦ flip lt_of_mul_lt_mul_left ha.le <| by simp [ne_of_gt ha, zero_lt_one]
#align inv_pos inv_pos

alias ⟨_, inv_pos_of_pos⟩ := inv_pos
#align inv_pos_of_pos inv_pos_of_pos

@[simp] lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]
#align inv_nonneg inv_nonneg

alias ⟨_, inv_nonneg_of_nonneg⟩ := inv_nonneg
#align inv_nonneg_of_nonneg inv_nonneg_of_nonneg

@[simp] lemma inv_lt_zero : a⁻¹ < 0 ↔ a < 0 := by simp only [← not_le, inv_nonneg]
#align inv_lt_zero inv_lt_zero

@[simp] lemma inv_nonpos : a⁻¹ ≤ 0 ↔ a ≤ 0 := by simp only [← not_lt, inv_pos]
#align inv_nonpos inv_nonpos

lemma one_div_pos : 0 < 1 / a ↔ 0 < a := inv_eq_one_div a ▸ inv_pos
#align one_div_pos one_div_pos

lemma one_div_neg : 1 / a < 0 ↔ a < 0 := inv_eq_one_div a ▸ inv_lt_zero
#align one_div_neg one_div_neg

lemma one_div_nonneg : 0 ≤ 1 / a ↔ 0 ≤ a := inv_eq_one_div a ▸ inv_nonneg
#align one_div_nonneg one_div_nonneg

lemma one_div_nonpos : 1 / a ≤ 0 ↔ a ≤ 0 := inv_eq_one_div a ▸ inv_nonpos
#align one_div_nonpos one_div_nonpos

lemma div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]; exact mul_pos ha (inv_pos.2 hb)
#align div_pos div_pos

lemma div_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [div_eq_mul_inv]; exact mul_nonneg ha (inv_nonneg.2 hb)
#align div_nonneg div_nonneg

lemma div_nonpos_of_nonpos_of_nonneg (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonpos_of_nonneg ha (inv_nonneg.2 hb)
#align div_nonpos_of_nonpos_of_nonneg div_nonpos_of_nonpos_of_nonneg

lemma div_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)
#align div_nonpos_of_nonneg_of_nonpos div_nonpos_of_nonneg_of_nonpos

lemma zpow_nonneg (ha : 0 ≤ a) : ∀ n : ℤ, 0 ≤ a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_nonneg ha _
  | -(n + 1 : ℕ) => by rw [zpow_neg, inv_nonneg, zpow_natCast]; exact pow_nonneg ha _
#align zpow_nonneg zpow_nonneg

lemma zpow_pos_of_pos (ha : 0 < a) : ∀ n : ℤ, 0 < a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_pos ha _
  | -(n + 1 : ℕ) => by rw [zpow_neg, inv_pos, zpow_natCast]; exact pow_pos ha _
#align zpow_pos_of_pos zpow_pos_of_pos
