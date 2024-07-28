/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Basic

/-!
# Basic facts for unbundled linear ordered (semi)fields

-/

-- Guard against import creep.
assert_not_exists OrderedCommMonoid
assert_not_exists MonoidHom

variable {α : Type*}

variable [Semifield α] [LinearOrder α] [PosMulReflectLT α] [ZeroLEOneClass α] {a b : α}

@[simp] lemma inv_pos : 0 < a⁻¹ ↔ 0 < a :=
  suffices ∀ a : α, 0 < a → 0 < a⁻¹ from ⟨fun h ↦ inv_inv a ▸ this _ h, this a⟩
  fun a ha ↦ flip lt_of_mul_lt_mul_left ha.le <| by simp [ne_of_gt ha, zero_lt_one]

alias ⟨_, inv_pos_of_pos⟩ := inv_pos

@[simp] lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a := by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

alias ⟨_, inv_nonneg_of_nonneg⟩ := inv_nonneg

@[simp] lemma inv_lt_zero : a⁻¹ < 0 ↔ a < 0 := by simp only [← not_le, inv_nonneg]

@[simp] lemma inv_nonpos : a⁻¹ ≤ 0 ↔ a ≤ 0 := by simp only [← not_lt, inv_pos]

lemma one_div_pos : 0 < 1 / a ↔ 0 < a := inv_eq_one_div a ▸ inv_pos

lemma one_div_neg : 1 / a < 0 ↔ a < 0 := inv_eq_one_div a ▸ inv_lt_zero

lemma one_div_nonneg : 0 ≤ 1 / a ↔ 0 ≤ a := inv_eq_one_div a ▸ inv_nonneg

lemma one_div_nonpos : 1 / a ≤ 0 ↔ a ≤ 0 := inv_eq_one_div a ▸ inv_nonpos

lemma div_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]; exact mul_pos ha (inv_pos.2 hb)

lemma div_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [div_eq_mul_inv]; exact mul_nonneg ha (inv_nonneg.2 hb)

lemma div_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonpos_of_nonneg ha (inv_nonneg.2 hb)

lemma div_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)

lemma zpow_nonneg [PosMulMono α] (ha : 0 ≤ a) : ∀ n : ℤ, 0 ≤ a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_nonneg ha _
  | -(n + 1 : ℕ) => by rw [zpow_neg, inv_nonneg, zpow_natCast]; exact pow_nonneg ha _

lemma zpow_pos_of_pos [PosMulStrictMono α] (ha : 0 < a) : ∀ n : ℤ, 0 < a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_pos ha _
  | -(n + 1 : ℕ) => by rw [zpow_neg, inv_pos, zpow_natCast]; exact pow_pos ha _
