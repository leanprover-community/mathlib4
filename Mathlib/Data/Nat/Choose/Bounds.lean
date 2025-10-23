/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Rodriguez
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Inequalities for binomial coefficients

This file proves exponential bounds on binomial coefficients. We might want to add here the
bounds `n^r/r^r ≤ n.choose r ≤ e^r n^r/r^r` in the future.

## Main declarations

* `Nat.choose_le_pow_div`: `n.choose r ≤ n^r / r!`
* `Nat.pow_le_choose`: `(n + 1 - r)^r / r! ≤ n.choose r`. Beware of the fishy ℕ-subtraction.
-/


open Nat

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {n k : ℕ}

namespace Nat

theorem choose_le_pow_div (r n : ℕ) : (n.choose r : α) ≤ (n ^ r : α) / r ! := by
  rw [le_div_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.descFactorial_le_pow r
  exact mod_cast r.factorial_pos

lemma choose_lt_pow_div (hn : n ≠ 0) (hk : 2 ≤ k) : (n.choose k : α) < (n ^ k : α) / k ! := by
  rw [lt_div_iff₀' (mod_cast k.factorial_pos)]
  norm_cast
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact descFactorial_lt_pow hn hk

lemma choose_le_descFactorial (n k : ℕ) : n.choose k ≤ n.descFactorial k := by
  rw [choose_eq_descFactorial_div_factorial]
  exact Nat.div_le_self _ _

lemma choose_lt_descFactorial (hk : 2 ≤ k) (hkn : k ≤ n) : n.choose k < n.descFactorial k := by
  rw [choose_eq_descFactorial_div_factorial]; exact Nat.div_lt_self (by simpa) (by simpa)

lemma choose_le_pow (n k : ℕ) : n.choose k ≤ n ^ k :=
  (choose_le_descFactorial n k).trans (descFactorial_le_pow n k)

lemma choose_lt_pow (hn : n ≠ 0) (hk : 2 ≤ k) : n.choose k < n ^ k :=
  (choose_le_descFactorial n k).trans_lt (descFactorial_lt_pow hn hk)

-- horrific casting is due to ℕ-subtraction
theorem pow_le_choose (r n : ℕ) : ((n + 1 - r : ℕ) ^ r : α) / r ! ≤ n.choose r := by
  rw [div_le_iff₀']
  · norm_cast
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact n.pow_sub_le_descFactorial r
  exact mod_cast r.factorial_pos

theorem choose_succ_le_two_pow (n k : ℕ) : (n + 1).choose k ≤ 2 ^ n := by
  by_cases lt : n + 1 < k
  · simp [choose_eq_zero_of_lt lt]
  · cases n with
    | zero => cases k <;> simp_all
    | succ n =>
      rcases k with - | k
      · rw [choose_zero_right]
        exact Nat.one_le_two_pow
      · rw [choose_succ_succ', two_pow_succ]
        exact Nat.add_le_add (choose_succ_le_two_pow n k) (choose_succ_le_two_pow n (k + 1))

theorem choose_lt_two_pow (n k : ℕ) (p : 0 < n) : n.choose k < 2 ^ n := by
  refine lt_of_le_of_lt ?_ (Nat.two_pow_pred_lt_two_pow p)
  rw [← Nat.sub_add_cancel p]
  exact choose_succ_le_two_pow (n - 1) k

theorem choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  obtain (rfl | hk) := eq_zero_or_pos k
  · simp [Nat.one_le_two_pow]
  · obtain (rfl | hn) := eq_zero_or_pos n
    · have : choose 0 k = 0 := by convert Nat.choose_zero_succ (k - 1); omega
      simp [this]
    · exact (Nat.choose_lt_two_pow _ _ hn).le

end Nat
