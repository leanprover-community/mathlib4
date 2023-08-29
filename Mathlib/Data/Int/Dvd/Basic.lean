/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Cast.Basic

#align_import data.int.dvd.basic from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Basic lemmas about the divisibility relation in `ℤ`.
-/


open Nat

namespace Int

@[norm_cast]
theorem coe_nat_dvd {m n : ℕ} : (↑m : ℤ) ∣ ↑n ↔ m ∣ n :=
  ⟨fun ⟨a, ae⟩ =>
    m.eq_zero_or_pos.elim (fun m0 => by simp [m0] at ae; simp [ae, m0]) fun m0l => by
                                        -- ⊢ m ∣ n
                                                         -- 🎉 no goals
      cases'
        eq_ofNat_of_zero_le
          (@nonneg_of_mul_nonneg_right ℤ _ m a (by simp [ae.symm]) (by simpa using m0l)) with
        k e
      subst a
      -- ⊢ m ∣ n
      exact ⟨k, Int.ofNat.inj ae⟩,
      -- 🎉 no goals
    fun ⟨k, e⟩ => Dvd.intro k <| by rw [e, Int.ofNat_mul]⟩
                                    -- 🎉 no goals
#align int.coe_nat_dvd Int.coe_nat_dvd

theorem coe_nat_dvd_left {n : ℕ} {z : ℤ} : (↑n : ℤ) ∣ z ↔ n ∣ z.natAbs := by
  rcases natAbs_eq z with (eq | eq) <;> rw [eq] <;> simp [←coe_nat_dvd]
  -- ⊢ ↑n ∣ z ↔ n ∣ natAbs z
                                        -- ⊢ ↑n ∣ ↑(natAbs z) ↔ n ∣ natAbs ↑(natAbs z)
                                        -- ⊢ ↑n ∣ -↑(natAbs z) ↔ n ∣ natAbs (-↑(natAbs z))
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
#align int.coe_nat_dvd_left Int.coe_nat_dvd_left

theorem coe_nat_dvd_right {n : ℕ} {z : ℤ} : z ∣ (↑n : ℤ) ↔ z.natAbs ∣ n := by
  rcases natAbs_eq z with (eq | eq) <;> rw [eq] <;> simp [←coe_nat_dvd]
  -- ⊢ z ∣ ↑n ↔ natAbs z ∣ n
                                        -- ⊢ ↑(natAbs z) ∣ ↑n ↔ natAbs ↑(natAbs z) ∣ n
                                        -- ⊢ -↑(natAbs z) ∣ ↑n ↔ natAbs (-↑(natAbs z)) ∣ n
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
#align int.coe_nat_dvd_right Int.coe_nat_dvd_right

#align int.le_of_dvd Int.le_of_dvd

#align int.eq_one_of_dvd_one Int.eq_one_of_dvd_one

#align int.eq_one_of_mul_eq_one_right Int.eq_one_of_mul_eq_one_right

#align int.eq_one_of_mul_eq_one_left Int.eq_one_of_mul_eq_one_left

#align int.dvd_antisymm Int.dvd_antisymm

end Int
