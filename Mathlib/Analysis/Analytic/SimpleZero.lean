/-
Copyright (c) 2026 PLACE TO STAND Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: interleaves
-/
module
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Simple Zeros of Analytic Functions

This file establishes properties of simple zeros (zeros of analytic order 1)
for analytic functions.

## Main results

* `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`: if `f` is analytic at `z₀`,
  `f z₀ = 0`, and `f' z₀ ≠ 0`, then the analytic order is exactly 1.
* `AnalyticAt.eventually_ne_of_deriv_ne_zero`: under the same hypotheses,
  `f` is nonzero in a punctured neighborhood.
* `AnalyticAt.tendsto_residue_simple_zero`: the logarithmic residue
  `(w - z₀) * f'(w) / f(w) → 1` as `w → z₀`.
-/

open Complex Filter Topology

public section SimpleZero

/-- At a zero with nonvanishing derivative, the analytic order is 1. -/
theorem AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hfz : f z₀ = 0) (hf' : deriv f z₀ ≠ 0) :
    analyticOrderAt f z₀ = 1 := by
  have h := hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hf'
  have : (fun w => f w - f z₀) =ᶠ[𝓝 z₀] f := by
    filter_upwards with w; simp [hfz]
  rwa [analyticOrderAt_congr this] at h

/-- At a simple zero, the function is nonzero in a punctured neighborhood. -/
theorem AnalyticAt.eventually_ne_of_deriv_ne_zero
    {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hfz : f z₀ = 0) (hf' : deriv f z₀ ≠ 0) :
    ∀ᶠ w in 𝓝[≠] z₀, f w ≠ 0 := by
  have h_ord := hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hfz hf'
  have h_ne_top : analyticOrderAt f z₀ ≠ ⊤ := by simp [h_ord]
  have h_not_ev : ¬(∀ᶠ z in 𝓝 z₀, f z = 0) :=
    fun h => h_ne_top (analyticOrderAt_eq_top.mpr h)
  exact (hf.eventually_eq_zero_or_eventually_ne_zero).resolve_left h_not_ev

/-- At a simple zero, the logarithmic residue `(w - z₀) * f'(w)/f(w)` tends to 1.
This is the key ingredient for computing residues of meromorphic functions. -/
theorem AnalyticAt.tendsto_residue_simple_zero
    {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hfz : f z₀ = 0) (hf' : deriv f z₀ ≠ 0) :
    Tendsto (fun w => (w - z₀) * (deriv f w / f w))
      (𝓝[≠] z₀) (𝓝 1) := by
  have h_slope : Tendsto (slope f z₀) (𝓝[≠] z₀) (𝓝 (deriv f z₀)) :=
    hasDerivAt_iff_tendsto_slope.mp hf.differentiableAt.hasDerivAt
  have h_deriv : Tendsto (deriv f) (𝓝[≠] z₀) (𝓝 (deriv f z₀)) :=
    hf.deriv.continuousAt.continuousWithinAt.tendsto
  have h_ratio : Tendsto (fun w => deriv f w / slope f z₀ w) (𝓝[≠] z₀) (𝓝 1) := by
    have := Filter.Tendsto.div h_deriv h_slope hf'
    rwa [div_self hf'] at this
  have h_ev : ∀ᶠ w in 𝓝[≠] z₀,
      deriv f w / slope f z₀ w = (w - z₀) * (deriv f w / f w) := by
    filter_upwards [hf.eventually_ne_of_deriv_ne_zero hfz hf', self_mem_nhdsWithin]
      with w hfw hw_ne
    have hw : w ≠ z₀ := Set.mem_compl_singleton_iff.mp hw_ne
    have hsub : w - z₀ ≠ 0 := sub_ne_zero.mpr hw
    simp only [slope, vsub_eq_sub, hfz, sub_zero, smul_eq_mul]
    field_simp [hsub, hfw]
  exact h_ratio.congr' h_ev

end SimpleZero
