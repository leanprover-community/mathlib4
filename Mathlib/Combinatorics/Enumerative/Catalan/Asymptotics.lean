/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Asymptotics of the Catalan numbers

This file derives the asymptotic growth of the Catalan numbers from Stirling's formula, via the
asymptotics of the central binomial coefficient and the formula
`catalan n = Nat.centralBinom n / (n + 1)`.

## Main statements

* `isEquivalent_catalan`: `catalan n` is asymptotically equivalent to `4 ^ n / (√π * n ^ (3 / 2))`.
-/

public section

open scoped Topology Real Nat Asymptotics
open Filter Real Asymptotics

/-- The `n`th Catalan number is asymptotically equivalent to `4 ^ n / (√π * n ^ (3 / 2))`. -/
theorem isEquivalent_catalan :
    (fun n ↦ catalan n : ℕ → ℝ) ~[atTop] fun n ↦ 4 ^ n / (√π * n ^ (3 / 2 : ℝ)) := by
  have hadd : (fun n : ℕ ↦ (n : ℝ) + 1) ~[atTop] fun n ↦ (n : ℝ) :=
    IsEquivalent.refl.add_isLittleO <| isLittleO_const_left.2 <| Or.inr <|
      tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop
  refine ((Stirling.isEquivalent_centralBinom.div hadd).congr_left ?_).congr_right ?_
  · filter_upwards with n
    simp only [Pi.div_apply]
    rw [div_eq_iff (by positivity), mul_comm]
    exact_mod_cast (succ_mul_catalan_eq_centralBinom n).symm
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Pi.div_apply]
    rw [sqrt_mul pi_pos.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add hn', rpow_one,
      ← sqrt_eq_rpow]
    field_simp
