/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The integers, with addition, multiplication, and subtraction.
-/
import Mathlib.Mathport.Rename
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Init.ZeroOne
import Std.Data.Int.Lemmas

open Nat

-- TODO: backport?

-- @[inherit_doc]
notation "ℤ" => Int

namespace Int

protected theorem coe_nat_eq (n : ℕ) : ↑n = Int.ofNat n :=
  rfl

/-- The number `0 : ℤ`, as a standalone definition. -/
@[deprecated] protected def zero : ℤ := ofNat 0

/-- The number `1 : ℤ`, as a standalone definition. -/
@[deprecated] protected def one : ℤ := ofNat 1




protected theorem ofNat_add_out (m n : ℕ) : ↑m + ↑n = (↑(m + n) : ℤ) := rfl

protected theorem ofNat_mul_out (m n : ℕ) : ↑m * ↑n = (↑(m * n) : ℤ) := rfl

protected theorem ofNat_add_one_out (n : ℕ) : ↑n + (1 : ℤ) = ↑(succ n) := rfl




protected theorem neg_eq_neg {a b : ℤ} (h : -a = -b) : a = b := Int.neg_inj.1 h



@[deprecated natAbs_eq_zero]
theorem eq_zero_of_natAbs_eq_zero : ∀ {a : ℤ}, natAbs a = 0 → a = 0 := natAbs_eq_zero.1

@[deprecated natAbs_pos]
theorem natAbs_pos_of_ne_zero {a : ℤ} (h : a ≠ 0) : 0 < natAbs a := natAbs_pos.2 h







/-- The modulus of an integer by another as a natural. Uses the E-rounding convention. -/
def natMod (m n : ℤ) : ℕ := (m % n).toNat
