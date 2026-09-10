/-
Copyright (c) 2026 Navin Dutta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Navin Dutta
-/
module

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Modified Bessel Functions of the First Kind

This file defines the modified Bessel function of the first kind,
`Real.besselI n x`, for natural-number order `n` and real argument `x ≥ 0`,
and establishes its basic analytic properties.

## Definition

For `n : ℕ` and `x : ℝ`, the modified Bessel function of the first kind is:
$$I_n(x) = \sum_{k=0}^{\infty} \frac{(x/2)^{n+2k}}{k!\,(n+k)!}$$

This series converges absolutely for all `x : ℝ`.

## Main results

* `Real.besselI_term_nonneg` : each summand is non-negative for `x ≥ 0`
* `Real.besselI_nonneg` : `I_n(x) ≥ 0` for `x ≥ 0`
* `Real.besselI_summable` : the series is summable for `x ≥ 0`
* `Real.besselI_upper_bound` : `I_n(x) ≤ (x/2)^n / n! · exp(x²/4)`
* `Real.le_besselI` : `(x/2)^n / n! ≤ I_n(x)` (the k=0 term lower bound)

## References

* [Watson, *A Treatise on the Theory of Bessel Functions*][watson1944]
* [Seiler, *Gauge Theories as a Problem of Constructive QFT*][seiler1982]
-/

open Nat Real

namespace Real

/-! ## Definition and basic nonnegativity -/

/-- The modified Bessel function of the first kind of integer order `n`:
$$I_n(x) = \sum_{k=0}^{\infty} \frac{(x/2)^{n+2k}}{k!\,(n+k)!}$$ -/
noncomputable def besselI (n : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, (x / 2) ^ (n + 2 * k) / ((k ! : ℝ) * (n + k) !)

/-- Each term of the Bessel series is non-negative for `x ≥ 0`. -/
theorem besselI_term_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ (x / 2) ^ (n + 2 * k) / ((k ! : ℝ) * (n + k) !) :=
  div_nonneg (by positivity) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- The modified Bessel function is non-negative for `x ≥ 0`. -/
theorem besselI_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ besselI n x :=
  tsum_nonneg (besselI_term_nonneg n hx)

/-! ## Summability -/

private theorem besselI_term_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x / 2) ^ (n + 2 * k) / ((k ! : ℝ) * (n + k) !)
    ≤ (x / 2) ^ n / (n ! : ℝ) * (((x / 2) ^ 2) ^ k / (k ! : ℝ)) := by
  have hk : (0 : ℝ) < k ! := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hn : (0 : ℝ) < n ! := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hfact : (n ! : ℝ) ≤ (n + k) ! :=
    Nat.cast_le.mpr (Nat.factorial_le (Nat.le_add_right n k))
  have hpos : 0 ≤ (x / 2) ^ n * ((x / 2) ^ 2) ^ k := by positivity
  rw [show (x / 2) ^ (n + 2 * k) = (x / 2) ^ n * ((x / 2) ^ 2) ^ k from by
        rw [pow_add, pow_mul]]
  rw [show (x / 2) ^ n / (n ! : ℝ) * (((x / 2) ^ 2) ^ k / (k ! : ℝ))
      = (x / 2) ^ n * ((x / 2) ^ 2) ^ k / ((n ! : ℝ) * k !) from by
        field_simp]
  apply div_le_div_of_nonneg_left hpos (mul_pos hn hk)
  calc (n ! : ℝ) * k ! ≤ (n + k) ! * k ! :=
        mul_le_mul_of_nonneg_right hfact (Nat.cast_nonneg _)
    _ = k ! * (n + k) ! := mul_comm _ _

/-- The Bessel series `I_n(x)` is summable for `x ≥ 0`. -/
theorem besselI_summable (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun k : ℕ => (x / 2) ^ (n + 2 * k) / ((k ! : ℝ) * (n + k) !)) := by
  apply Summable.of_nonneg_of_le (besselI_term_nonneg n hx) (besselI_term_le n hx)
  apply Summable.mul_left
  simpa [Nat.factorial] using Real.summable_pow_div_factorial ((x / 2) ^ 2)

/-! ## The exponential as a power series -/

/-- The real exponential equals the power series `∑' k, y^k / k!`. -/
theorem tsum_pow_div_factorial (y : ℝ) :
    ∑' k : ℕ, y ^ k / (k ! : ℝ) = exp y := by
  rw [Real.exp_eq_exp_ℝ]
  exact (congr_fun NormedSpace.exp_eq_tsum_div y).symm

/-! ## Bounds -/

/-- **Upper bound**: `I_n(x) ≤ (x/2)^n / n! · exp(x²/4)` for `x ≥ 0`.

This follows from the term-by-term estimate `(n+k)! ≥ n!` and the
exponential series identity. -/
theorem besselI_upper_bound (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    besselI n x ≤ (x / 2) ^ n / (n ! : ℝ) * exp (x ^ 2 / 4) := by
  unfold besselI
  have hdom : Summable (fun k : ℕ =>
      (x / 2) ^ n / (n ! : ℝ) * (((x / 2) ^ 2) ^ k / (k ! : ℝ))) :=
    Summable.mul_left _ (by simpa [Nat.factorial] using
      Real.summable_pow_div_factorial ((x / 2) ^ 2))
  calc ∑' k, (x / 2) ^ (n + 2 * k) / ((k ! : ℝ) * (n + k) !)
      ≤ ∑' k, (x / 2) ^ n / (n ! : ℝ) * (((x / 2) ^ 2) ^ k / (k ! : ℝ)) :=
          (besselI_summable n hx).tsum_le_tsum (besselI_term_le n hx) hdom
    _ = (x / 2) ^ n / (n ! : ℝ) * ∑' k, ((x / 2) ^ 2) ^ k / (k ! : ℝ) := by
          rw [tsum_mul_left]
    _ = (x / 2) ^ n / (n ! : ℝ) * exp ((x / 2) ^ 2) := by
          rw [tsum_pow_div_factorial]
    _ = (x / 2) ^ n / (n ! : ℝ) * exp (x ^ 2 / 4) := by
          norm_num [div_pow]

/-- **Lower bound**: `(x/2)^n / n! ≤ I_n(x)` for `x ≥ 0`.

This is the `k = 0` term of the series. -/
theorem le_besselI (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x / 2) ^ n / (n ! : ℝ) ≤ besselI n x := by
  have h0 : (x / 2) ^ n / (n ! : ℝ) =
      (x / 2) ^ (n + 2 * 0) / ((0 ! : ℝ) * (n + 0) !) := by simp
  rw [h0]
  exact (besselI_summable n hx).le_tsum 0 (fun k _ => besselI_term_nonneg n hx k)

end Real
