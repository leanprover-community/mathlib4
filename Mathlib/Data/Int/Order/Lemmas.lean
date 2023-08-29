/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Int.Order.Basic
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.Ring.Abs

#align_import data.int.order.lemmas from "leanprover-community/mathlib"@"fc2ed6f838ce7c9b7c7171e58d78eaf7b438fb0e"

/-!
# Further lemmas about the integers
The distinction between this file and `Data.Int.Order.Basic` is not particularly clear.
They are separated by now to minimize the porting requirements for tactics during the transition to
mathlib4. After `data.rat.order` has been ported, please feel free to reorganize these two files.
-/


open Nat

namespace Int

/-! ### nat abs -/


variable {a b : ℤ} {n : ℕ}

theorem natAbs_eq_iff_mul_self_eq {a b : ℤ} : a.natAbs = b.natAbs ↔ a * a = b * b := by
  rw [← abs_eq_iff_mul_self_eq, abs_eq_natAbs, abs_eq_natAbs]
  -- ⊢ natAbs a = natAbs b ↔ ↑(natAbs a) = ↑(natAbs b)
  exact Int.coe_nat_inj'.symm
  -- 🎉 no goals
#align int.nat_abs_eq_iff_mul_self_eq Int.natAbs_eq_iff_mul_self_eq

#align int.eq_nat_abs_iff_mul_eq_zero Int.eq_natAbs_iff_mul_eq_zero

theorem natAbs_lt_iff_mul_self_lt {a b : ℤ} : a.natAbs < b.natAbs ↔ a * a < b * b := by
  rw [← abs_lt_iff_mul_self_lt, abs_eq_natAbs, abs_eq_natAbs]
  -- ⊢ natAbs a < natAbs b ↔ ↑(natAbs a) < ↑(natAbs b)
  exact Int.ofNat_lt.symm
  -- 🎉 no goals
#align int.nat_abs_lt_iff_mul_self_lt Int.natAbs_lt_iff_mul_self_lt

theorem natAbs_le_iff_mul_self_le {a b : ℤ} : a.natAbs ≤ b.natAbs ↔ a * a ≤ b * b := by
  rw [← abs_le_iff_mul_self_le, abs_eq_natAbs, abs_eq_natAbs]
  -- ⊢ natAbs a ≤ natAbs b ↔ ↑(natAbs a) ≤ ↑(natAbs b)
  exact Int.ofNat_le.symm
  -- 🎉 no goals
#align int.nat_abs_le_iff_mul_self_le Int.natAbs_le_iff_mul_self_le

theorem dvd_div_of_mul_dvd {a b c : ℤ} (h : a * b ∣ c) : b ∣ c / a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  -- ⊢ b ∣ c / 0
  · simp only [Int.ediv_zero, dvd_zero]
    -- 🎉 no goals
  rcases h with ⟨d, rfl⟩
  -- ⊢ b ∣ a * b * d / a
  refine' ⟨d, _⟩
  -- ⊢ a * b * d / a = b * d
  rw [mul_assoc, Int.mul_ediv_cancel_left _ ha]
  -- 🎉 no goals
#align int.dvd_div_of_mul_dvd Int.dvd_div_of_mul_dvd

/-! ### units -/


theorem eq_zero_of_abs_lt_dvd {m x : ℤ} (h1 : m ∣ x) (h2 : |x| < m) : x = 0 := by
  by_cases hm : m = 0
  -- ⊢ x = 0
  · subst m
    -- ⊢ x = 0
    exact zero_dvd_iff.mp h1
    -- 🎉 no goals
  rcases h1 with ⟨d, rfl⟩
  -- ⊢ m * d = 0
  apply mul_eq_zero_of_right
  -- ⊢ d = 0
  rw [← abs_lt_one_iff, ← mul_lt_iff_lt_one_right (abs_pos.mpr hm), ← abs_mul]
  -- ⊢ |m * d| < |m|
  exact lt_of_lt_of_le h2 (le_abs_self m)
  -- 🎉 no goals
#align int.eq_zero_of_abs_lt_dvd Int.eq_zero_of_abs_lt_dvd

end Int
