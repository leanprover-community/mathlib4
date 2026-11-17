/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Cubic Exponential Lower Bounds and Quartic-Pre-Factor Gaussian Decay

This file proves the elementary cubic lower bound `(1 + u / 3) ^ 3 ≤ Real.exp u` for `u ≥ 0`
by cubing `Real.add_one_le_exp (u / 3)`, and deduces that for any positive rate `σ > 0` and
scale `L > 0`, the quartic-weighted Gaussian damping factor `L ^ 4 * Real.exp (-(σ * L ^ 2))`
is bounded above by `27 / (σ ^ 3 * L ^ 2)`.

## Main results

* `ExponentialAreaScreening.cubic_div_twenty_seven_le_exp`:
  `u ^ 3 / 27 ≤ Real.exp u` for `0 ≤ u`.
* `ExponentialAreaScreening.quartic_mul_exp_neg_sq_le`:
  `L ^ 4 * Real.exp (-(σ * L ^ 2)) ≤ 27 / (σ ^ 3 * L ^ 2)` for `0 < σ` and `0 < L`.
-/

@[expose] public section

namespace ExponentialAreaScreening

/-- For any `u : ℝ`, `Real.exp (u / 3) ^ 3 = Real.exp u`. -/
theorem exp_div_three_cubed (u : ℝ) :
    (Real.exp (u / 3)) ^ 3 = Real.exp u := by
  have h1 : (Real.exp (u / 3)) ^ 3 =
      Real.exp (u / 3) * (Real.exp (u / 3) * Real.exp (u / 3)) := by ring
  rw [h1, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- For `0 ≤ u`, `(1 + u / 3) ^ 3 ≤ Real.exp u`. -/
theorem one_add_div_three_cubed_le_exp {u : ℝ} (hu : 0 ≤ u) :
    (1 + u / 3) ^ 3 ≤ Real.exp u := by
  rw [← exp_div_three_cubed u]
  have h_base : 1 + u / 3 ≤ Real.exp (u / 3) := by
    linarith [Real.add_one_le_exp (u / 3)]
  have h_nonneg : 0 ≤ 1 + u / 3 := by positivity
  exact pow_le_pow_left₀ h_nonneg h_base 3

/-- Pure cubic lower bound: for `0 ≤ u`, `u ^ 3 / 27 ≤ Real.exp u`. -/
theorem cubic_div_twenty_seven_le_exp {u : ℝ} (hu : 0 ≤ u) :
    u ^ 3 / 27 ≤ Real.exp u := by
  have h_expand : (1 + u / 3) ^ 3 = 1 + u + u ^ 2 / 3 + u ^ 3 / 27 := by ring
  have h_le : u ^ 3 / 27 ≤ (1 + u / 3) ^ 3 := by
    rw [h_expand]
    have h1 : 0 ≤ u ^ 2 / 3 := by positivity
    linarith
  exact le_trans h_le (one_add_div_three_cubed_le_exp hu)

/-- Quartic-weighted Gaussian decay: for `0 < σ` and `0 < L`,
`L ^ 4 * Real.exp (-(σ * L ^ 2)) ≤ 27 / (σ ^ 3 * L ^ 2)`. -/
theorem quartic_mul_exp_neg_sq_le {σ L : ℝ} (hσ : 0 < σ) (hL : 0 < L) :
    L ^ 4 * Real.exp (-(σ * L ^ 2)) ≤ 27 / (σ ^ 3 * L ^ 2) := by
  have hu : 0 ≤ σ * L ^ 2 := by positivity
  have h_cubic := cubic_div_twenty_seven_le_exp hu
  have h_cubic_id : (σ * L ^ 2) ^ 3 / 27 = (σ ^ 3 * L ^ 6) / 27 := by ring
  rw [h_cubic_id] at h_cubic
  rw [Real.exp_neg]
  have h_exp_pos : 0 < Real.exp (σ * L ^ 2) := Real.exp_pos _
  have h_denom_pos : 0 < σ ^ 3 * L ^ 2 := by positivity
  rw [← div_eq_mul_inv, div_le_div_iff₀ h_exp_pos h_denom_pos]
  nlinarith

end ExponentialAreaScreening
