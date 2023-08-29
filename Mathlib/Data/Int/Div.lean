/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Data.Int.Dvd.Basic
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Algebra.Ring.Regular

#align_import data.int.div from "leanprover-community/mathlib"@"ee0c179cd3c8a45aa5bffbf1b41d8dbede452865"

/-!
# Lemmas relating `/` in `ℤ` with the ordering.
-/


open Nat

namespace Int

theorem eq_mul_div_of_mul_eq_mul_of_dvd_left {a b c d : ℤ} (hb : b ≠ 0) (hbc : b ∣ c)
    (h : b * a = c * d) : a = c / b * d := by
  cases' hbc with k hk
  -- ⊢ a = c / b * d
  subst hk
  -- ⊢ a = b * k / b * d
  rw [Int.mul_ediv_cancel_left _ hb]
  -- ⊢ a = k * d
  rw [mul_assoc] at h
  -- ⊢ a = k * d
  apply mul_left_cancel₀ hb h
  -- 🎉 no goals
#align int.eq_mul_div_of_mul_eq_mul_of_dvd_left Int.eq_mul_div_of_mul_eq_mul_of_dvd_left

/-- If an integer with larger absolute value divides an integer, it is
zero. -/
theorem eq_zero_of_dvd_of_natAbs_lt_natAbs {a b : ℤ} (w : a ∣ b) (h : natAbs b < natAbs a) :
    b = 0 := by
  rw [← natAbs_dvd, ← dvd_natAbs, coe_nat_dvd] at w
  -- ⊢ b = 0
  rw [← natAbs_eq_zero]
  -- ⊢ natAbs b = 0
  exact eq_zero_of_dvd_of_lt w h
  -- 🎉 no goals
#align int.eq_zero_of_dvd_of_nat_abs_lt_nat_abs Int.eq_zero_of_dvd_of_natAbs_lt_natAbs

theorem eq_zero_of_dvd_of_nonneg_of_lt {a b : ℤ} (w₁ : 0 ≤ a) (w₂ : a < b) (h : b ∣ a) : a = 0 :=
  eq_zero_of_dvd_of_natAbs_lt_natAbs h (natAbs_lt_natAbs_of_nonneg_of_lt w₁ w₂)
#align int.eq_zero_of_dvd_of_nonneg_of_lt Int.eq_zero_of_dvd_of_nonneg_of_lt

/-- If two integers are congruent to a sufficiently large modulus,
they are equal. -/
theorem eq_of_mod_eq_of_natAbs_sub_lt_natAbs {a b c : ℤ} (h1 : a % b = c)
    (h2 : natAbs (a - c) < natAbs b) : a = c :=
  eq_of_sub_eq_zero (eq_zero_of_dvd_of_natAbs_lt_natAbs (dvd_sub_of_emod_eq h1) h2)
#align int.eq_of_mod_eq_of_nat_abs_sub_lt_nat_abs Int.eq_of_mod_eq_of_natAbs_sub_lt_natAbs

theorem ofNat_add_negSucc_of_ge {m n : ℕ} (h : n.succ ≤ m) :
    ofNat m + -[n+1] = ofNat (m - n.succ) := by
  rw [negSucc_eq, ofNat_eq_cast, ofNat_eq_cast, ← Nat.cast_one, ← Nat.cast_add,
    ← sub_eq_add_neg, ← Nat.cast_sub h]
#align int.of_nat_add_neg_succ_of_nat_of_ge Int.ofNat_add_negSucc_of_ge

theorem natAbs_le_of_dvd_ne_zero {s t : ℤ} (hst : s ∣ t) (ht : t ≠ 0) : natAbs s ≤ natAbs t :=
  not_lt.mp (mt (eq_zero_of_dvd_of_natAbs_lt_natAbs hst) ht)
#align int.nat_abs_le_of_dvd_ne_zero Int.natAbs_le_of_dvd_ne_zero

end Int
