/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Further lemmas about the integers

The distinction between this file and `Data.Int.Order.Basic` is not particularly clear.
They are separated by now to minimize the porting requirements for tactics during the transition to
mathlib4. Please feel free to reorganize these two files.
-/

open Function Nat

namespace Int

/-! ### nat abs -/

theorem natAbs_eq_iff_mul_self_eq {a b : ℤ} : a.natAbs = b.natAbs ↔ a * a = b * b := by
  rw [← abs_eq_iff_mul_self_eq, abs_eq_natAbs, abs_eq_natAbs]
  exact Int.natCast_inj.symm

theorem natAbs_lt_iff_mul_self_lt {a b : ℤ} : a.natAbs < b.natAbs ↔ a * a < b * b := by
  rw [← abs_lt_iff_mul_self_lt, abs_eq_natAbs, abs_eq_natAbs]
  exact Int.ofNat_lt.symm

theorem natAbs_le_iff_mul_self_le {a b : ℤ} : a.natAbs ≤ b.natAbs ↔ a * a ≤ b * b := by
  rw [← abs_le_iff_mul_self_le, abs_eq_natAbs, abs_eq_natAbs]
  exact Int.ofNat_le.symm

/-! ### Integer sqrt -/

theorem abs_le_sqrt {a b : ℤ} (hn : 0 ≤ b) :
    |a| ≤ b.sqrt ↔ a * a ≤ b := by
  rw [← abs_mul_abs_self, eq_natCast_toNat.mpr hn, eq_natCast_toNat.mpr (abs_nonneg a),
    Int.sqrt_natCast, ← Int.natCast_mul, Nat.cast_le, Nat.cast_le, Nat.le_sqrt]

theorem abs_le_sqrt_iff_sq_le {a b : ℤ} (hn : 0 ≤ b) :
    |a| ≤ b.sqrt ↔ a ^ 2 ≤ b :=
  pow_two a ▸ abs_le_sqrt hn

end Int
