/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The modified Bessel function of the first kind, integer order

The modified Bessel function of the first kind `I_n` for integer order
`n ≥ 0` is defined by its power series
`I_n(x) = ∑_{k≥0} (x/2)^(n+2k) / (k! · (n+k)!)`.
This file defines that series and proves it is summable for every order
`n` and every real argument `x`, by domination with the exponential
series.
-/

public section

open scoped Nat

/-- Power series of the modified Bessel function of the first kind, integer order
`n ≥ 0`: `I_n(x) = ∑_{k≥0} (x/2)^(n+2k) / (k! · (n+k)!)`. This is the genuine
series (not a stand-in); `noncomputable` only because it is a real `tsum`. -/
noncomputable def besselI_series (n : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, (x / 2) ^ (n + 2 * k) / ((Nat.factorial k : ℝ) * (Nat.factorial (n + k) : ℝ))

/-- The defining series of `besselI_series` is summable for every order `n` and
every real argument `x`. Proof: dominate term-by-term (in absolute value) by
`(|x/2|^n / n!) · (|x/2|^2)^k / k!`, a constant multiple of the exponential
series `∑ y^k/k!`, using `(n+k)! ≥ n!`. -/
theorem besselI_series_summable (n : ℕ) (x : ℝ) :
    Summable (fun k : ℕ =>
      (x / 2) ^ (n + 2 * k) / ((Nat.factorial k : ℝ) * (Nat.factorial (n + k) : ℝ))) := by
  set t : ℝ := x / 2
  -- Dominating summable series: a constant times the exponential series in |t|².
  have hsum :
      Summable (fun k : ℕ =>
        (|t| ^ n / (Nat.factorial n : ℝ)) * ((|t| ^ 2) ^ k / (Nat.factorial k : ℝ))) :=
    (Real.summable_pow_div_factorial (|t| ^ 2)).mul_left _
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hsum)
  intro k
  rw [Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (show (0 : ℝ) < (Nat.factorial k : ℝ) * (Nat.factorial (n + k) : ℝ) by positivity),
      pow_add, pow_mul, div_mul_div_comm,
      div_le_div_iff₀ (by positivity) (by positivity)]
  -- goal: A * (↑n! * ↑k!) ≤ A * (↑k! * ↑(n+k)!), with A = |t|^n * (|t|^2)^k ≥ 0
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- goal: ↑n! * ↑k! ≤ ↑k! * ↑(n+k)!
  rw [mul_comm (Nat.factorial n : ℝ) (Nat.factorial k : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact_mod_cast Nat.factorial_le (Nat.le_add_right n k)
