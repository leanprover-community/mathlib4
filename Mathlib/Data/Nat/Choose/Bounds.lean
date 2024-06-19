/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Rodriguez
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.CharZero
import Mathlib.Data.Nat.Cast.Order
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Ring.CharZero
import Mathlib.Data.Nat.Cast.Order

#align_import data.nat.choose.bounds from "leanprover-community/mathlib"@"550b58538991c8977703fdeb7c9d51a5aa27df11"

/-!
# Inequalities for binomial coefficients

This file proves exponential bounds on binomial coefficients. We might want to add here the
bounds `n^r/r^r ≤ n.choose r ≤ e^r n^r/r^r` in the future.

## Main declarations

* `Nat.choose_le_pow`: `n.choose r ≤ n^r / r!`
* `Nat.pow_le_choose`: `(n + 1 - r)^r / r! ≤ n.choose r`. Beware of the fishy ℕ-subtraction.
-/


open Nat

variable {α : Type*} [LinearOrderedSemifield α]

namespace Nat

theorem choose_le_pow (r n : ℕ) : (n.choose r : α) ≤ (n ^ r : α) / r ! := by
  rw [le_div_iff']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.descFactorial_le_pow r
  exact mod_cast r.factorial_pos
#align nat.choose_le_pow Nat.choose_le_pow

-- horrific casting is due to ℕ-subtraction
theorem pow_le_choose (r n : ℕ) : ((n + 1 - r : ℕ) ^ r : α) / r ! ≤ n.choose r := by
  rw [div_le_iff']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.pow_sub_le_descFactorial r
  exact mod_cast r.factorial_pos
#align nat.pow_le_choose Nat.pow_le_choose

end Nat
