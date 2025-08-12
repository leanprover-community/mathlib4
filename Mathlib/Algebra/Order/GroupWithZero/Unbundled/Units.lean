/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.Order.Monoid.Unbundled.Units
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.ZeroLEOne

/-! # Lemmas about units in a monoid with zero -/

section MonoidWithZero

variable {M : Type*} [MonoidWithZero M]

section LE

variable [LE M] [MulLeftMono M] [ZeroLEOneClass M]
variable {a b : M}

@[simp] lemma zero_le' : 0 ≤ a := by
  simpa only [mul_zero, mul_one] using mul_le_mul_left' zero_le_one a

end LE

section PartialOrder

variable [PartialOrder M] [MulLeftMono M] [ZeroLEOneClass M]
variable {a b : M}

@[simp]
theorem not_lt_zero' : ¬a < 0 :=
  not_lt_of_ge zero_le'

@[simp]
theorem le_zero_iff : a ≤ 0 ↔ a = 0 :=
  ⟨fun h ↦ le_antisymm h zero_le', fun h ↦ h ▸ le_rfl⟩

theorem pos_iff : 0 < a ↔ a ≠ 0 :=
  ⟨ne_of_gt, fun h ↦ lt_of_le_of_ne zero_le' h.symm⟩

theorem ne_zero_of_lt (h : b < a) : a ≠ 0 := fun h1 ↦ not_lt_zero' <| show b < 0 from h1 ▸ h

@[simp]
theorem Units.zero_lt [Nontrivial M] (u : Mˣ) : (0 : M) < u :=
  pos_iff.2 u.ne_zero

-- theorem mul_inv_lt_of_lt_mul₀ {c : Mˣ} (h : a < b * c) : a * c⁻¹ < b := by
--   contrapose! h
--   simpa only [inv_inv] using mul_inv_le_of_le_mul₀ zero_le' zero_le' h

-- theorem inv_mul_lt_of_lt_mul₀ (h : a < b * c) : b⁻¹ * a < c := by
--   rw [mul_comm] at *
--   exact mul_inv_lt_of_lt_mul₀ h

-- theorem lt_of_mul_lt_mul_of_le₀ (h : a * b < c * d) (hc : 0 < c) (hh : c ≤ a) : b < d := by
--   have ha : a ≠ 0 := ne_of_gt (lt_of_lt_of_le hc hh)
--   rw [← inv_le_inv₀ (zero_lt_iff.2 ha) hc] at hh
--   simpa [inv_mul_cancel_left₀ ha, inv_mul_cancel_left₀ hc.ne']
--     using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hh  h zero_le' (inv_pos.2 hc)

end PartialOrder

end MonoidWithZero
