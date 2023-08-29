/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Rodriguez
-/
import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Choose.Basic

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
  -- ⊢ ↑r ! * ↑(choose n r) ≤ ↑(n ^ r)
  · norm_cast
    -- ⊢ r ! * choose n r ≤ n ^ r
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    -- ⊢ descFactorial n r ≤ n ^ r
    exact n.descFactorial_le_pow r
    -- 🎉 no goals
  exact_mod_cast r.factorial_pos
  -- 🎉 no goals
#align nat.choose_le_pow Nat.choose_le_pow

-- horrific casting is due to ℕ-subtraction
theorem pow_le_choose (r n : ℕ) : ((n + 1 - r : ℕ) ^ r : α) / r ! ≤ n.choose r := by
  rw [div_le_iff']
  -- ⊢ ↑((n + 1 - r) ^ r) ≤ ↑r ! * ↑(choose n r)
  · norm_cast
    -- ⊢ (n + 1 - r) ^ r ≤ r ! * choose n r
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    -- ⊢ (n + 1 - r) ^ r ≤ descFactorial n r
    exact n.pow_sub_le_descFactorial r
    -- 🎉 no goals
  exact_mod_cast r.factorial_pos
  -- 🎉 no goals
#align nat.pow_le_choose Nat.pow_le_choose

end Nat
