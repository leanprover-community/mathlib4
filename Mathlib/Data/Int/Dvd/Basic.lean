/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Cast.Order
import Mathlib.Algebra.Ring.Divisibility.Basic

#align_import data.int.dvd.basic from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Basic lemmas about the divisibility relation in `ℤ`.
-/


open Nat

namespace Int

@[norm_cast]
theorem natCast_dvd_natCast {m n : ℕ} : (↑m : ℤ) ∣ ↑n ↔ m ∣ n :=
  ⟨fun ⟨a, ae⟩ =>
    m.eq_zero_or_pos.elim (fun m0 => by
      simp only [m0, Nat.cast_zero, zero_mul, cast_eq_zero] at ae
      simp [ae, m0]) fun m0l => by
      cases'
        eq_ofNat_of_zero_le
          (@nonneg_of_mul_nonneg_right ℤ _ m a (by simp [ae.symm]) (by simpa using m0l)) with
        k e
      subst a
      exact ⟨k, Int.ofNat.inj ae⟩,
    fun ⟨k, e⟩ => Dvd.intro k <| by rw [e, Int.ofNat_mul]⟩
#align int.coe_nat_dvd Int.natCast_dvd_natCast

theorem natCast_dvd {n : ℕ} {z : ℤ} : (↑n : ℤ) ∣ z ↔ n ∣ z.natAbs := by
  rcases natAbs_eq z with (eq | eq) <;> rw [eq] <;> simp [← natCast_dvd_natCast, Int.dvd_neg]
#align int.coe_nat_dvd_left Int.natCast_dvd

theorem dvd_natCast {n : ℕ} {z : ℤ} : z ∣ (↑n : ℤ) ↔ z.natAbs ∣ n := by
  rcases natAbs_eq z with (eq | eq) <;> rw [eq] <;> simp [← natCast_dvd_natCast, Int.neg_dvd]
#align int.coe_nat_dvd_right Int.dvd_natCast

#align int.le_of_dvd Int.le_of_dvd

#align int.eq_one_of_dvd_one Int.eq_one_of_dvd_one

#align int.eq_one_of_mul_eq_one_right Int.eq_one_of_mul_eq_one_right

#align int.eq_one_of_mul_eq_one_left Int.eq_one_of_mul_eq_one_left

#align int.dvd_antisymm Int.dvd_antisymm

-- 2024-04-02
@[deprecated] alias coe_nat_dvd := natCast_dvd_natCast
@[deprecated] alias coe_nat_dvd_right := dvd_natCast
@[deprecated] alias coe_nat_dvd_left := natCast_dvd

end Int
