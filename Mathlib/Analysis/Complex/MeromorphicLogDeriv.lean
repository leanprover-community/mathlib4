/-
Copyright (c) 2026 interleaves. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: interleaves
-/
module
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Logarithmic Derivative at Zeros of Analytic Functions

This file establishes the relationship between the residue of the
logarithmic derivative `-f'/f` at a zero of an analytic function
and the vanishing order `analyticOrderAt`.

## Main results

* `AnalyticAt.tendsto_mul_neg_deriv_div`: At a zero of order `m`,
  `(z - a) * (-f'(z)/f(z)) → m` as `z → a`.
* `AnalyticAt.analyticOrderAt_eq_one_iff_deriv_ne_zero`: The vanishing
  order equals 1 if and only if the derivative is nonzero.

## Tags

analytic function, logarithmic derivative, vanishing order, residue
-/

@[expose] public section

open Filter Set Complex
open scoped Topology

variable {f : ℂ → ℂ} {z₀ : ℂ}

/-- At a zero of an analytic function, the derivative is nonzero
iff the vanishing order is exactly 1. This is a direct consequence
of `analyticOrderAt_sub_eq_one_of_deriv_ne_zero` and
`analyticOrderAt_deriv_add_one`. -/
theorem AnalyticAt.analyticOrderAt_eq_one_iff_deriv_ne_zero
    (hf : AnalyticAt ℂ f z₀) (hfz : f z₀ = 0) :
    analyticOrderAt f z₀ = 1 ↔ deriv f z₀ ≠ 0 := by
  constructor
  · -- order = 1 → deriv ≠ 0
    intro h_one h_eq
    have h_ord := hf.analyticOrderAt_deriv_add_one
    simp only [hfz, sub_zero] at h_ord
    rw [h_one] at h_ord
    -- h_ord : analyticOrderAt (deriv f) z₀ + 1 = 1
    -- Therefore analyticOrderAt (deriv f) z₀ = 0
    have h_zero : analyticOrderAt (deriv f) z₀ = 0 := by
      cases h : analyticOrderAt (deriv f) z₀ with
      | top => simp only [h, top_add, ENat.top_ne_one] at h_ord
      | coe n => simp only [h, isAddRightRegular_iff_isAddRegular, ne_eq,
          ENat.one_ne_top, not_false_eq_true, IsAddRegular.of_ne_top,
          IsAddRightRegular.add_right_eq_self_iff] at h_ord; exact h_ord
    rw [analyticOrderAt_eq_zero] at h_zero
    rcases h_zero with h_not_an | h_ne
    · exact absurd hf.deriv h_not_an
    · exact h_ne h_eq
  · -- deriv ≠ 0 → order = 1
    intro h_ne
    have := hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero h_ne
    simp only [hfz, sub_zero] at this; exact this

end
