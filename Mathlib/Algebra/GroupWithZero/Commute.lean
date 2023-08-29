/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.GroupWithZero.Semiconj
import Mathlib.Algebra.Group.Commute
import Mathlib.Tactic.Nontriviality

#align_import algebra.group_with_zero.commute from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Lemmas about commuting elements in a `MonoidWithZero` or a `GroupWithZero`.

-/


variable {α M₀ G₀ M₀' G₀' F F' : Type*}

variable [MonoidWithZero M₀]

namespace Ring

open Classical

theorem mul_inverse_rev' {a b : M₀} (h : Commute a b) :
    inverse (a * b) = inverse b * inverse a := by
  by_cases hab : IsUnit (a * b)
  -- ⊢ inverse (a * b) = inverse b * inverse a
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.isUnit_mul_iff.mp hab
    -- ⊢ inverse (↑a * ↑b) = inverse ↑b * inverse ↑a
    rw [← Units.val_mul, inverse_unit, inverse_unit, inverse_unit, ← Units.val_mul, mul_inv_rev]
    -- 🎉 no goals
  obtain ha | hb := not_and_or.mp (mt h.isUnit_mul_iff.mpr hab)
  -- ⊢ inverse (a * b) = inverse b * inverse a
  · rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]
    -- 🎉 no goals
  · rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]
    -- 🎉 no goals
#align ring.mul_inverse_rev' Ring.mul_inverse_rev'

theorem mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) :
    Ring.inverse (a * b) = inverse b * inverse a :=
  mul_inverse_rev' (Commute.all _ _)
#align ring.mul_inverse_rev Ring.mul_inverse_rev

end Ring

theorem Commute.ring_inverse_ring_inverse {a b : M₀} (h : Commute a b) :
    Commute (Ring.inverse a) (Ring.inverse b) :=
  (Ring.mul_inverse_rev' h.symm).symm.trans <| (congr_arg _ h.symm.eq).trans <|
    Ring.mul_inverse_rev' h
#align commute.ring_inverse_ring_inverse Commute.ring_inverse_ring_inverse

namespace Commute

@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0 :=
  SemiconjBy.zero_right a
#align commute.zero_right Commute.zero_right

@[simp]
theorem zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a :=
  SemiconjBy.zero_left a a
#align commute.zero_left Commute.zero_left

variable [GroupWithZero G₀] {a b c : G₀}

@[simp]
theorem inv_left_iff₀ : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff₀
#align commute.inv_left_iff₀ Commute.inv_left_iff₀

theorem inv_left₀ (h : Commute a b) : Commute a⁻¹ b :=
  inv_left_iff₀.2 h
#align commute.inv_left₀ Commute.inv_left₀

@[simp]
theorem inv_right_iff₀ : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff₀
#align commute.inv_right_iff₀ Commute.inv_right_iff₀

theorem inv_right₀ (h : Commute a b) : Commute a b⁻¹ :=
  inv_right_iff₀.2 h
#align commute.inv_right₀ Commute.inv_right₀

@[simp]
theorem div_right (hab : Commute a b) (hac : Commute a c) : Commute a (b / c) :=
  SemiconjBy.div_right hab hac
#align commute.div_right Commute.div_right

@[simp]
theorem div_left (hac : Commute a c) (hbc : Commute b c) : Commute (a / b) c := by
  rw [div_eq_mul_inv]
  -- ⊢ Commute (a * b⁻¹) c
  exact hac.mul_left hbc.inv_left₀
  -- 🎉 no goals
#align commute.div_left Commute.div_left

end Commute
