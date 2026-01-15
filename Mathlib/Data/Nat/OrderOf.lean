/-
Copyright (c) 2026 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
-/
module

public import Mathlib.Data.Nat.Totient

/-!
# Order of an element

This file defines the order function on `ℕ`.


## Main definitions

* `Nat.orderOf n a` is the smallest positive `k` such that `a ^ k - 1` divides n if it exists.
* `Nat.orderOf_le_totient` the order is less or equal to the Euler's totient `φ`.
-/

@[expose] public section

namespace Nat

/-- `n.orderOf a` is the smallest positive `k` such that `a ^ k - 1` divides n if it exists. -/
noncomputable def orderOf (n a : ℕ) : ℕ := _root_.orderOf (a : (ZMod n))

theorem orderOf_coe {n a : ℕ} (h : a.Coprime n) :
    n.orderOf a = _root_.orderOf (ZMod.unitOfCoprime a h) := by
  unfold orderOf _root_.orderOf
  rw [(Function.minimalPeriod_eq_minimalPeriod_iff (g := ((ZMod.unitOfCoprime a h) * ·))).mpr]
  intro y
  unfold Function.IsPeriodicPt Function.IsFixedPt at *
  simp only [mul_left_iterate, mul_one]
  grind [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, Units.val_injective]

theorem orderOf_dvd_totient {n a : ℕ} (h : a.Coprime n) : n.orderOf a ∣ φ n := by
  by_cases hc : n = 0
  · simp [hc]
  · haveI : NeZero n := NeZero.mk hc
    simp_rw [orderOf_coe h, ← ZMod.card_units_eq_totient n, orderOf_dvd_card]

/-- The order of an element is less or equal to the Euler's totient. -/
theorem orderOf_le_totient (n a : ℕ) [NeZero n] : n.orderOf a ≤ φ n := by
  by_cases hc : a.Coprime n
  · exact le_of_dvd (pos_of_neZero (φ n)) (orderOf_dvd_totient hc)
  · suffices n.orderOf a = 0 by grind
    apply orderOf_eq_zero
    contrapose! hc
    obtain ⟨ b , ⟨ _ , hb ⟩ ⟩ := IsOfFinOrder.exists_pow_eq_one hc
    replace hb := ModEq.gcd_eq <| (ZMod.natCast_eq_natCast_iff (a ^ b) 1 n).mp (by grind)
    simp only [gcd_one_left] at hb
    exact Coprime.coprime_mul_left (show (a ^ (b - 1) * a).Coprime n by
      suffices a ^ b = a * a ^ (b - 1) by grind
      nth_rw 1 [show b = 1 + (b - 1) by grind]
      grind)

end Nat
