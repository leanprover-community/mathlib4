/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.Sqrt

/-!
# Square root on rational numbers

This file defines the square root function on rational numbers `Rat.sqrt`
and proves several theorems about it.

-/


namespace Rat

/-- Square root function on rational numbers, defined by taking the (integer) square root of the
numerator and the square root (on natural numbers) of the denominator. -/
@[pp_nodot]
def sqrt (q : ℚ) : ℚ := mkRat (Int.sqrt q.num) (Nat.sqrt q.den)

theorem sqrt_eq (q : ℚ) : Rat.sqrt (q * q) = |q| := by
  rw [sqrt, mul_self_num, mul_self_den, Int.sqrt_eq, Nat.sqrt_eq, abs_def, divInt_ofNat]

theorem exists_mul_self (x : ℚ) : (∃ q, q * q = x) ↔ Rat.sqrt x * Rat.sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, abs_mul_abs_self], fun h => ⟨Rat.sqrt x, h⟩⟩

lemma sqrt_nonneg (q : ℚ) : 0 ≤ Rat.sqrt q := mkRat_nonneg (Int.sqrt_nonneg _) _

/-- `IsSquare` can be decided on `ℚ` by checking against the square root. -/
instance : DecidablePred (IsSquare : ℚ → Prop) :=
  fun m => decidable_of_iff' (sqrt m * sqrt m = m) <| by
    simp_rw [← exists_mul_self m, IsSquare, eq_comm]

@[simp, norm_cast]
theorem sqrt_intCast (z : ℤ) : Rat.sqrt (z : ℚ) = Int.sqrt z := by
  simp only [sqrt, num_intCast, den_intCast, Nat.sqrt_one, mkRat_one]

@[simp, norm_cast]
theorem sqrt_natCast (n : ℕ) : Rat.sqrt (n : ℚ) = Nat.sqrt n := by
  rw [← Int.cast_natCast, sqrt_intCast, Int.sqrt_natCast, Int.cast_natCast]

@[simp]
theorem sqrt_ofNat (n : ℕ) : Rat.sqrt (ofNat(n) : ℚ) = Nat.sqrt (OfNat.ofNat n) :=
  sqrt_natCast _

end Rat
