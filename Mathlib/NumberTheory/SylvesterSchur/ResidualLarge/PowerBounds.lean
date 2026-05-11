/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.Algebra.Group.Defs

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Power bounds for large residual Sylvester-Schur estimates

This file contains the algebraic cancellation and base-exponent estimates used by the large
residual estimates in the Sylvester-Schur proof.

## Main statements

* `self_le_four_pow_div_one_twenty_eight_add_one`: a coarse exponential upper bound on `n`.
* `two_pow_nineteen_mul_div_twelve_le_three_pow`: the binary-to-ternary comparison used in
  endpoint estimates.
* `four_pow_mul_two_pow_mul_four_pow_lt_three_pow_mul_four_pow`: the common power comparison for
  the central-offset residual estimate.
-/

@[expose] public section

namespace Nat.SylvesterSchur
namespace Internal

private lemma four_pow_eq_two_pow_two_mul (n : ℕ) : 4 ^ n = 2 ^ (2 * n) := by
  rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul]

/-- A coarse exponential upper bound used to absorb a factor of `n` in large residual
estimates. -/
lemma self_le_four_pow_div_one_twenty_eight_add_one {n : ℕ} (hn : 512 ≤ n) :
    n ≤ 4 ^ (n / 128 + 1) := by
  let m := n / 128
  have hm4 : 4 ≤ m := by
    dsimp [m]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 128)]
    omega
  have hnlt : n < 128 * (m + 1) := by
    dsimp [m]
    exact Nat.lt_mul_div_succ n (by norm_num : 0 < 128)
  have hmul_general : ∀ m : ℕ, 4 ≤ m → 128 * (m + 1) ≤ 4 ^ (m + 1) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
        calc
          128 * (m + 1 + 1) ≤ 4 * (128 * (m + 1)) := by nlinarith
          _ ≤ 4 * 4 ^ (m + 1) := Nat.mul_le_mul_left 4 ih
          _ = 4 ^ (m + 1 + 1) := by ring
  exact hnlt.le.trans (hmul_general m hm4)

/-- A binary-to-ternary comparison used to convert powers of `2` into powers of `3`. -/
lemma two_pow_nineteen_mul_div_twelve_le_three_pow (n : ℕ) :
    2 ^ (19 * (n / 12)) ≤ 3 ^ n := by
  let m := n / 12
  have hbase : 2 ^ 19 ≤ 3 ^ 12 := by norm_num
  have hm : 12 * m ≤ n := by
    dsimp [m]
    exact Nat.mul_div_le n 12
  calc
    2 ^ (19 * (n / 12)) = (2 ^ 19) ^ m := by
      dsimp [m]
      rw [pow_mul]
      norm_num
    _ ≤ (3 ^ 12) ^ m := Nat.pow_le_pow_left hbase m
    _ = 3 ^ (12 * m) := by rw [pow_mul]
    _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num : 0 < 3) hm

/-- The power comparison used after the central-offset residual estimate has been reduced to
exponents. -/
lemma four_pow_mul_two_pow_mul_four_pow_lt_three_pow_mul_four_pow
    {D E i n : ℕ} (hexp : 2 * D + i + 2 * E < 19 * (i / 12) + 2 * n) :
    4 ^ D * (2 ^ i * 4 ^ E) < 3 ^ i * 4 ^ n := by
  have hpow : 4 ^ D * (2 ^ i * 4 ^ E) = 2 ^ (2 * D + i + 2 * E) := by
    rw [four_pow_eq_two_pow_two_mul D, four_pow_eq_two_pow_two_mul E]
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  have hlt : 2 ^ (2 * D + i + 2 * E) < 2 ^ (19 * (i / 12) + 2 * n) :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) hexp
  have hright : 2 ^ (19 * (i / 12) + 2 * n) ≤ 3 ^ i * 4 ^ n := by
    calc
      2 ^ (19 * (i / 12) + 2 * n) = 2 ^ (19 * (i / 12)) * 2 ^ (2 * n) := by
        rw [pow_add]
      _ ≤ 3 ^ i * 2 ^ (2 * n) :=
        Nat.mul_le_mul_right (2 ^ (2 * n)) (two_pow_nineteen_mul_div_twelve_le_three_pow i)
      _ = 3 ^ i * 4 ^ n := by
        rw [four_pow_eq_two_pow_two_mul n]
  rw [hpow]
  exact hlt.trans_le hright

end Internal
end Nat.SylvesterSchur
