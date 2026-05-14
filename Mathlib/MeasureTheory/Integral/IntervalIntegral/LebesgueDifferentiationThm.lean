/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Covering.OneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Lebesgue Differentiation Theorem (Interval Version)

This file proves the interval version of the Lebesgue Differentiation Theorem. There are two
versions in this file.

* `LocallyIntegrable.ae_hasDerivAt_integral` is the global version. It states that if `f : ℝ → ℝ`
  is locally integrable, then for almost every `x`, for any `c : ℝ`, the derivative of
  `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`.

* `IntervalIntegrable.ae_hasDerivAt_integral` is the local version. It states that if `f : ℝ → ℝ`
  is interval integrable on `a..b`, then for almost every `x ∈ uIcc a b`, for any `c ∈ uIcc a b`,
  the derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`.
-/

public section

open MeasureTheory Set Filter Function IsUnifLocDoublingMeasure

open scoped Topology

-- set_option trace.profiler true in
-- set_option Elab.async false in
-- #count_heartbeats in
-- befor: 7684 heartbeats,      0.603387s
-- after: 5235 heartbeats,      0.445507s
-- reduc: 2449 heartbeats(31%), 0.157880s(26%)
/-- The (global) interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → ℝ` is
locally integrable, then for almost every `x`, for any `c : ℝ`, the derivative of
`∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`. -/
theorem LocallyIntegrable.ae_hasDerivAt_integral {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ c, HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  have hg (x y : ℝ) : IntervalIntegrable f volume x y :=
    intervalIntegrable_iff.mpr <|
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have LDT := (vitaliFamily volume 1).ae_tendsto_average hf
  have h {a b : ℝ} : ∫ (t : ℝ) in Ioc a b, f t = ∫ (t : ℝ) in Icc a b, f t :=
    integral_Icc_eq_integral_Ioc (x := a) (y := b) (X := ℝ) |>.symm
  filter_upwards [LDT] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_left)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : y ≤ x := hy.le
    suffices -((y - x)⁻¹ * ∫ (t : ℝ) in Icc y x, f t) = (x - y)⁻¹ * ∫ (t : ℝ) in Icc y x, f t by
      simpa [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_ge, hy, h]
    rw [← neg_mul, neg_inv, neg_sub]
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_right)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : x ≤ y := hy.le
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_le, hy, h]

/-- The (local) interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → ℝ` is
interval integrable on `a..b`, then for almost every `x ∈ uIcc a b`, for any `c ∈ uIcc a b`, the
derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`. -/
theorem IntervalIntegrable.ae_hasDerivAt_integral {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    ∀ᵐ x, x ∈ uIcc a b → ∀ c ∈ uIcc a b, HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ @this f b a hf.symm (by linarith)
  rw [uIcc_of_le hab]
  have h₁ : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  let g (x : ℝ) := if x ∈ Ioc a b then f x else 0
  have hg : LocallyIntegrable g volume :=
    integrableOn_congr_fun (by grind [EqOn]) (by simp) |>.mpr hf.left
      |>.integrable_of_forall_notMem_eq_zero (by grind) |>.locallyIntegrable
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg, h₁, h₂] with x hx _ _ _
  intro c hc
  refine HasDerivWithinAt.hasDerivAt (s := Ioo a b) ?_ <|
    Ioo_mem_nhds (by grind) (by grind)
  rw [show f x = g x by grind]
  refine (hx c).hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  all_goals apply intervalIntegral.integral_congr_ae' <;> filter_upwards <;> grind
