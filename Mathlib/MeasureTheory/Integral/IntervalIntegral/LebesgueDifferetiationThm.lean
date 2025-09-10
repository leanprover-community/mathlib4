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
  have hg0 : IntegrableOn f Set.univ volume := by simpa
  have hg1 (x y : ℝ) : IntegrableOn f (Icc x y) volume := by
    apply IntegrableOn.mono_set hg0; simp
  have hg2 (x y : ℝ) : IntervalIntegrable f volume x y := by
    unfold IntervalIntegrable; constructor <;> apply IntegrableOn.mono_set hg0 <;> simp
  have hfL : LocallyIntegrable f (volume) := by
    apply Integrable.locallyIntegrable; assumption
  have LDT := VitaliFamily.ae_tendsto_average (vitaliFamily (volume : Measure ℝ) 1) hfL
  have h1 {x0 y0 : ℝ} (hxy0 : x0 ≤ y0) :
      ∫ (t : ℝ) in Ioc x0 y0, f t = ∫ (t : ℝ) in Icc x0 y0, f t := by
    rw [fun (a b : ℝ) ↦ show a = b ↔ b - a = 0 by grind,
        ← MeasureTheory.integral_diff (by simp) (by apply hg1) Ioc_subset_Icc_self]
    simp [hxy0]
  filter_upwards [LDT] with x hx
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · rw [Filter.tendsto_congr' (f₂ := fun y ↦ ⨍ (t : ℝ) in Icc y x, f t)]
    · exact hx.comp (Real.tendsto_Icc_vitaliFamily_left x)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      replace hy : y ≤ x := by rw [mem_Iio] at hy; linarith
      simp only [slope, vsub_eq_sub, smul_eq_mul, average, MeasurableSet.univ,
        Measure.restrict_apply, univ_inter, Real.volume_Icc, integral_smul_measure,
        ENNReal.toReal_inv, sub_nonneg, hy, ENNReal.toReal_ofReal]
      rw [intervalIntegral.integral_interval_sub_left (by apply hg2) (by apply hg2),
          intervalIntegral.integral_of_ge hy,
          h1 hy,
          show (y - x)⁻¹ = -(x - y)⁻¹ by grind]
      ring
  · rw [Filter.tendsto_congr' (f₂ := fun y ↦ ⨍ (t : ℝ) in Icc x y, f t)]
    · exact hx.comp (Real.tendsto_Icc_vitaliFamily_right x)
    · filter_upwards [self_mem_nhdsWithin] with y hy
      replace hy : x ≤ y := by rw [mem_Ioi] at hy; linarith
      simp only [slope, vsub_eq_sub, smul_eq_mul, average, MeasurableSet.univ,
        Measure.restrict_apply, univ_inter, Real.volume_Icc, integral_smul_measure,
        ENNReal.toReal_inv, sub_nonneg, hy, ENNReal.toReal_ofReal]
      rw [intervalIntegral.integral_interval_sub_left (by apply hg2) (by apply hg2),
          intervalIntegral.integral_of_le hy,
          h1 hy,
          show (y - x)⁻¹ = -(x - y)⁻¹ by grind]

/-- The interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → ℝ` is integrable on
`uIoc a b`, and `c ∈ uIoc a b`, then for almost every `x ∈ uIcc a b`, the derivative of
`∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`. -/
theorem IntervalIntegrable.ae_eq_deriv_integral {f : ℝ → ℝ} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    ∀ᵐ x, x ∈ uIcc a b → HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ @this f b a c hf.symm (uIcc_comm a b ▸ hc) (by linarith)
  simp_rw [uIcc_of_le hab] at hc ⊢
  have h1 : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h2 : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  let g (x : ℝ) := if x ∈ Ioc a b then f x else 0
  have hg1 : Integrable g volume := by
    apply MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Ioc a b)
    · rw [MeasureTheory.integrableOn_congr_fun (g := f) (by simp +contextual [g, EqOn]) (by simp)]
      exact hf.left
    · simp +contextual [g]
  have hg2 := Integrable.ae_eq_deriv_integral hg1 c
  have hg3 : ∀ x ∈ Ioc a b, f x = g x := by simp +contextual [g, ↓reduceIte]
  have hg4 : ∀ (y z : ℝ), a ≤ y → z ≤ b → ∀ x ∈ Ioc y z, f x = g x := by
    intro y z hy hz x hx
    have : Ioc y z ⊆ Ioc a b := by gcongr
    exact hg3 x (this hx)
  filter_upwards [hg2, h1, h2] with x hx1 hx2 hx3 hx4
  have hx5 : x ∈ Ioo a b := by rw [← Icc_diff_both, mem_diff]; simp [hx2, hx3, hx4]
  have hx6 : x ∈ Ioc a b := by exact mem_Ioc_of_Ioo hx5
  rw [mem_Icc] at hc hx4
  apply HasDerivWithinAt.hasDerivAt (s := Ioo a b)
  · apply HasDerivAt.hasDerivWithinAt (s := Ioo a b) at hx1
    rw [show f x = g x by simp only [g, ↓reduceIte, hx6] ]
    apply HasDerivWithinAt.congr hx1; try (intro y hy; rw [mem_Ioo] at hy)
    all_goals apply intervalIntegral.integral_congr_ae'
    all_goals filter_upwards
    all_goals apply hg4
    all_goals linarith
  · rw [mem_Ioo] at hx5
    exact Ioo_mem_nhds hx5.left hx5.right
