/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Common

/-!
# Square root of integers

This file defines the square root function on integers. `Int.sqrt z` is the greatest integer `r`
such that `r * r ≤ z`. If `z ≤ 0`, then `Int.sqrt z = 0`.
-/


namespace Int

/-- `sqrt z` is the square root of an integer `z`. If `z` is positive, it returns the largest
integer `r` such that `r * r ≤ n`. If it is negative, it returns `0`. For example, `sqrt (-1) = 0`,
`sqrt 1 = 1`, `sqrt 2 = 1` -/
@[pp_nodot]
def sqrt (z : ℤ) : ℤ :=
  Nat.sqrt <| Int.toNat z

theorem sqrt_eq (n : ℤ) : sqrt (n * n) = n.natAbs := by
  rw [sqrt, ← natAbs_mul_self, toNat_natCast, Nat.sqrt_eq]

theorem exists_mul_self (x : ℤ) : (∃ n, n * n = x) ↔ sqrt x * sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, ← Int.natCast_mul, natAbs_mul_self], fun h => ⟨sqrt x, h⟩⟩

theorem sqrt_nonneg (n : ℤ) : 0 ≤ sqrt n :=
  natCast_nonneg _

@[simp, norm_cast]
theorem sqrt_natCast (n : ℕ) : Int.sqrt (n : ℤ) = Nat.sqrt n := by rw [sqrt, toNat_natCast]

@[simp]
theorem sqrt_ofNat (n : ℕ) : Int.sqrt ofNat(n) = Nat.sqrt ofNat(n) :=
  sqrt_natCast _

end Int
