/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.rat.sqrt
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rat.Order
import Mathbin.Data.Rat.Lemmas
import Mathbin.Data.Int.Sqrt

/-!
# Square root on rational numbers

This file defines the square root function on rational numbers `rat.sqrt`
and proves several theorems about it.

-/


namespace Rat

/-- Square root function on rational numbers, defined by taking the (integer) square root of the
numerator and the square root (on natural numbers) of the denominator. -/
@[pp_nodot]
def sqrt (q : ℚ) : ℚ :=
  Rat.mk (Int.sqrt q.num) (Nat.sqrt q.denom)
#align rat.sqrt Rat.sqrt

theorem sqrt_eq (q : ℚ) : Rat.sqrt (q * q) = |q| := by
  rw [sqrt, mul_self_num, mul_self_denom, Int.sqrt_eq, Nat.sqrt_eq, abs_def]
#align rat.sqrt_eq Rat.sqrt_eq

theorem exists_mul_self (x : ℚ) : (∃ q, q * q = x) ↔ Rat.sqrt x * Rat.sqrt x = x :=
  ⟨fun ⟨n, hn⟩ => by rw [← hn, sqrt_eq, abs_mul_abs_self], fun h => ⟨Rat.sqrt x, h⟩⟩
#align rat.exists_mul_self Rat.exists_mul_self

theorem sqrt_nonneg (q : ℚ) : 0 ≤ Rat.sqrt q :=
  nonneg_iff_zero_le.1 <|
    (divInt_nonneg _ <|
          Int.coe_nat_pos.2 <|
            Nat.pos_of_ne_zero fun H => pos_iff_ne_zero.1 q.Pos <| Nat.sqrt_eq_zero.1 H).2 <|
      Int.coe_nat_nonneg _
#align rat.sqrt_nonneg Rat.sqrt_nonneg

end Rat

