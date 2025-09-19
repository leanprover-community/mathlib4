/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Covering.OneDim
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Lebesgue Differentiation Theorem (Interval Version)

This file proves the interval version of the Lebesgue Differentiation Theorem.
-/

open MeasureTheory Set Filter Function IsUnifLocDoublingMeasure

open scoped Topology

/-- The interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → ℝ` is integrable and
`c : ℝ`, then for almost every `x`, the derivative of `∫ (t : ℝ) in c..x, f t` at `x`
is equal to `f x`. -/
theorem Integrable.ae_eq_deriv_integral {f : ℝ → ℝ} (hf : Integrable f volume) (c : ℝ) :
    ∀ᵐ x, HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  have hg (x y : ℝ) : IntervalIntegrable f volume x y := by
    have : IntegrableOn f Set.univ volume := by simpa
    constructor <;> simp [this.mono_set]
  have LDT := (vitaliFamily volume 1).ae_tendsto_average hf.locallyIntegrable
  have {a b : ℝ} : ∫ (t : ℝ) in Ioc a b, f t = ∫ (t : ℝ) in Icc a b, f t :=
    integral_Icc_eq_integral_Ioc (x := a) (y := b) (X := ℝ) |>.symm
  filter_upwards [LDT] with x hx
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_left)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : y ≤ x := by grind
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_ge, hy, this]
    grind
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_right)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : x ≤ y := by grind
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_le, hy, this]

/-- The interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → ℝ` is integrable on
`uIoc a b`, and `c ∈ uIoc a b`, then for almost every `x ∈ uIcc a b`, the derivative of
`∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`. -/
theorem IntervalIntegrable.ae_eq_deriv_integral {f : ℝ → ℝ} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    ∀ᵐ x, x ∈ uIcc a b → HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ @this f b a c hf.symm (uIcc_comm a b ▸ hc) (by linarith)
  rw [uIcc_of_le hab] at hc ⊢
  have h₁ : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  let g (x : ℝ) := if x ∈ Ioc a b then f x else 0
  have hg : Integrable g volume :=
    integrableOn_congr_fun (by grind [EqOn]) (by simp) |>.mpr hf.left
      |>.integrable_of_forall_notMem_eq_zero (by grind)
  filter_upwards [Integrable.ae_eq_deriv_integral hg c, h₁, h₂] with x hx _ _ _
  refine HasDerivWithinAt.hasDerivAt (s := Ioo a b) ?_ <| Ioo_mem_nhds (by grind) (by grind)
  rw [show f x = g x by grind]
  refine hx.hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  all_goals apply intervalIntegral.integral_congr_ae' <;> filter_upwards <;> grind
