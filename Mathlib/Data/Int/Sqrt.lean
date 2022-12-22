/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module data.int.sqrt
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Sqrt

/-!
# Square root of integers

This file defines the square root function on integers. `int.sqrt z` is the greatest integer `r`
such that `r * r ≤ z`. If `z ≤ 0`, then `int.sqrt z = 0`.
-/


namespace Int

/-- `sqrt z` is the square root of an integer `z`. If `z` is positive, it returns the largest
integer `r` such that `r * r ≤ n`. If it is negative, it returns `0`. For example, `sqrt (-1) = 0`,
`sqrt 1 = 1`, `sqrt 2 = 1` -/
@[pp_nodot]
def sqrt (z : ℤ) : ℤ :=
  Nat.sqrt <| Int.toNat z
#align int.sqrt Int.sqrt

theorem sqrt_eq (n : ℤ) : sqrt (n * n) = n.natAbs := by
  rw [sqrt, ← nat_abs_mul_self, to_nat_coe_nat, Nat.sqrt_eq]
#align int.sqrt_eq Int.sqrt_eq

theorem exists_mul_self (x : ℤ) : (∃ n, n * n = x) ↔ sqrt x * sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, ← Int.ofNat_mul, nat_abs_mul_self], fun h => ⟨sqrt x, h⟩⟩
#align int.exists_mul_self Int.exists_mul_self

theorem sqrt_nonneg (n : ℤ) : 0 ≤ sqrt n :=
  coe_nat_nonneg _
#align int.sqrt_nonneg Int.sqrt_nonneg

end Int

