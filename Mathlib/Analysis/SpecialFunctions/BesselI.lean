/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
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
noncomputable def besselISeries (n : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, (x / 2) ^ (n + 2 * k) / ((Nat.factorial k : ℝ) * (Nat.factorial (n + k) : ℝ))

/-- The defining series of `besselISeries` is summable for every order `n` and
every real argument `x`. Proof: dominate term-by-term (in absolute value) by
`(|x/2|^n / n!) · (|x/2|^2)^k / k!`, a constant multiple of the exponential
series `∑ y^k/k!`, using `(n+k)! ≥ n!`. -/
theorem besselISeries_summable (n : ℕ) (x : ℝ) :
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

/-- Upper bound for the modified Bessel series: `I_n(x) ≤ (x/2)^n · exp((x/2)^2)`
for `x ≥ 0`. Proof: dominate each series term by dropping `(n+k)!` from the
denominator (using `(n+k)! ≥ 1`), and sum the resulting exponential series.
This gives the geometric decay in the Bessel order that underlies
summability. -/
theorem besselISeries_le_exp_bound (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    besselISeries n x ≤ (x / 2) ^ n * Real.exp ((x / 2) ^ 2) := by
  have hx2 : (0 : ℝ) ≤ x / 2 := div_nonneg hx two_pos.le
  have hsumm : Summable (fun k : ℕ =>
      (x / 2) ^ (n + 2 * k) / ((↑k.factorial) * (↑(n + k).factorial))) :=
    besselISeries_summable n x
  have hsumm_dom : Summable (fun k : ℕ =>
      (x / 2) ^ n * (((x / 2) ^ 2) ^ k / ↑k.factorial)) :=
    (Real.summable_pow_div_factorial ((x / 2) ^ 2)).mul_left _
  have hterm : ∀ k : ℕ,
      (x / 2) ^ (n + 2 * k) / ((↑k.factorial : ℝ) * ↑(n + k).factorial)
        ≤ (x / 2) ^ n * (((x / 2) ^ 2) ^ k / ↑k.factorial) := fun k => by
    rw [pow_add, pow_mul]
    have hkpos : (0 : ℝ) < ↑k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hA : (0 : ℝ) ≤ (x / 2) ^ n * ((x / 2) ^ 2) ^ k := by positivity
    have hle : (↑k.factorial : ℝ) ≤ ↑k.factorial * ↑(n + k).factorial :=
      le_mul_of_one_le_right hkpos.le
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    calc (x / 2) ^ n * ((x / 2) ^ 2) ^ k / (↑k.factorial * ↑(n + k).factorial)
        ≤ (x / 2) ^ n * ((x / 2) ^ 2) ^ k / ↑k.factorial :=
          div_le_div_of_nonneg_left hA hkpos hle
      _ = (x / 2) ^ n * (((x / 2) ^ 2) ^ k / ↑k.factorial) := by ring
  calc besselISeries n x
      = ∑' k : ℕ, (x / 2) ^ (n + 2 * k) / ((↑k.factorial) * (↑(n + k).factorial)) := rfl
    _ ≤ ∑' k : ℕ, (x / 2) ^ n * (((x / 2) ^ 2) ^ k / ↑k.factorial) :=
        Summable.tsum_le_tsum hterm hsumm hsumm_dom
    _ = (x / 2) ^ n * ∑' k : ℕ, ((x / 2) ^ 2) ^ k / ↑k.factorial := tsum_mul_left
    _ = (x / 2) ^ n * Real.exp ((x / 2) ^ 2) := by
        congr 1
        rw [Real.exp_eq_exp_ℝ]
        exact NormedSpace.expSeries_div_hasSum_exp ((x / 2) ^ 2) |>.tsum_eq
