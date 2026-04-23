/-
Copyright (c) 2026 Lior Horesh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Horesh
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Exponential envelope for `(1 − p)^k`

This module records the clean primitive

`(1 − p)^k ≤ exp(−p · k)`

for `p ∈ [0, 1]` and `k ∈ ℕ`, together with its real-exponent variant
`(1 − p)^x ≤ exp(−p · x)` for `x ≥ 0`.  It unifies a boilerplate three-
line dance (`Real.one_sub_le_exp_neg` + `pow_le_pow_left₀` +
`Real.exp_nat_mul`) that recurs throughout analysis and probability
theory and is currently re-inlined at every call site.

## Main results

* `Real.one_sub_pow_le_exp_neg_mul` — natural-exponent envelope.
* `Real.one_sub_rpow_le_exp_neg_mul` — real-exponent envelope (`rpow`).

## Tags

exponential envelope, one minus p, sub-exponential, concentration
-/

@[expose] public section

namespace Real

/-- **Exponential envelope — natural exponent.**  For `p ≤ 1` and
`k : ℕ`, `(1 − p)^k ≤ exp(−p · k)`.

Standard primitive used throughout concentration inequalities
(Chernoff-bound derivation), depolarizing-channel contraction bounds,
and random-circuit analysis.  The proof is the composition of
`Real.one_sub_le_exp_neg` with `pow_le_pow_left₀` and
`Real.exp_nat_mul`. -/
theorem one_sub_pow_le_exp_neg_mul
    {p : ℝ} (hp1 : p ≤ 1) (k : ℕ) :
    (1 - p) ^ k ≤ Real.exp (-(p * k)) := by
  have hp0 : 0 ≤ 1 - p := by linarith
  have h1 : 1 - p ≤ Real.exp (-p) := Real.one_sub_le_exp_neg p
  have h2 : (1 - p) ^ k ≤ (Real.exp (-p)) ^ k :=
    pow_le_pow_left₀ hp0 h1 k
  have h3 : (Real.exp (-p)) ^ k = Real.exp (-(p * k)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  linarith

/-- **Exponential envelope — real exponent via `rpow`.**  For
`p ≤ 1` and `x ≥ 0`, `(1 − p)^x ≤ exp(−p · x)`.

`rpow` is preferred over `^ : ℝ → ℝ → ℝ` on the `(1-p) = 0` corner.
The proof reduces to `Real.rpow_le_rpow` on the base inequality
`1 − p ≤ exp(−p)`, followed by `Real.exp_mul` on the right-hand side. -/
theorem one_sub_rpow_le_exp_neg_mul
    {p : ℝ} (hp1 : p ≤ 1) {x : ℝ} (hx : 0 ≤ x) :
    (1 - p) ^ x ≤ Real.exp (-(p * x)) := by
  have h_base_nn : 0 ≤ 1 - p := by linarith
  have h_base_le : 1 - p ≤ Real.exp (-p) := Real.one_sub_le_exp_neg p
  have h_mono : (1 - p) ^ x ≤ (Real.exp (-p)) ^ x :=
    Real.rpow_le_rpow h_base_nn h_base_le hx
  have h_exp_rpow :
      (Real.exp (-p)) ^ x = Real.exp (-(p * x)) := by
    rw [← Real.exp_mul]
    ring_nf
  linarith

end Real
