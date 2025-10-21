/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Slope

/-!
# `f'` is interval integrable for certain classes of functions `f`

This file proves that:
* `MonotoneOn.intervalIntegrable_deriv` - If `f` is monotone on `a..b`, then `f'` is interval
integrable on `a..b`.
* `MonotoneOn.intervalIntegral_bound` - If `f` is monotone on `a..b`, then the integral of `f'` on
`a..b` is in `uIcc 0 (f b - f a)`.
* `BoundedVariationOn.intervalIntegrable_deriv` - If `f` has bounded variation on `a..b`,
then `f'` is interval integrable on `a..b`.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv` - If `f` is absolutely continuous on
`a..b`, then `f'` is interval integrable on `a..b`.

## Tags
interval integrable, monotone, bounded variation, absolutely continuous
-/

open MeasureTheory Set Filter

open scoped Topology

/-- If `f` is monotone on `a..b`, then `f'` is interval integrable on `a..b` and the integral of
`f'` on `a..b` is in between `0` and `f b - f a`. -/
theorem MonotoneOn.intervalIntegrable_deriv_intervalIntegral_bound {f : ℝ → ℝ} {a b : ℝ}
    (hf : MonotoneOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b ∧ ∫ x in a..b, deriv f x ∈ uIcc 0 (f b - f a) := by
  wlog hab : a ≤ b generalizing a b with h
  · specialize h (uIcc_comm a b ▸ hf) (by linarith)
    refine ⟨h.left.symm, ?_⟩
    · have : f b ≤ f a := hf (by simp) (by simp) (by linarith)
      rw [intervalIntegral.integral_symm, uIcc_of_ge (by linarith)]
      refine neg_mem_Icc_iff.mpr ?_
      simp only [neg_zero, neg_sub]
      rw [uIcc_of_le (by linarith)] at h
      exact h.right
  rw [uIcc_of_le hab] at hf
  let g (x : ℝ) : ℝ := f (max a (min x b))
  have hg : Monotone g := monotoneOn_univ.mp <| hf.comp (by grind [MonotoneOn]) (by grind [MapsTo])
  have hfg : EqOn f g (Ioo a b) := by grind [EqOn]
  replace hfg := hfg.deriv isOpen_Ioo
  have h₁ : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  let G (c x : ℝ) := slope g x (x + c)
  have hGf : ∀ᵐ x ∂volume.restrict (Icc a b),
      Filter.Tendsto (fun (n : ℕ) ↦ G (n : ℝ)⁻¹ x) Filter.atTop (𝓝 (deriv f x)) := by
    rw [MeasureTheory.ae_restrict_iff' (by measurability)]
    filter_upwards [hg.ae_differentiableAt, h₁, h₂] with x hx₁ hx₂ hx₃ hx₄
    rw [hfg (by grind)]
    exact hx₁.hasDerivAt.tendsto_slope.comp <|
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by convert tendsto_const_nhds.add tendsto_inverse_atTop_nhds_zero_nat; simp)
      (by simp [eventually_ne_atTop 0])
  have G_integrable (n : ℕ) : Integrable (G (↑n)⁻¹) (volume.restrict (Icc a b)) := by
    have := hg.monotoneOn (Icc a (b + (n : ℝ)⁻¹)) |>.intervalIntegrable_slope hab (by simp)
    exact intervalIntegrable_iff_integrableOn_Icc_of_le hab |>.mp this
  have hG (n : ℕ) : AEStronglyMeasurable (G (n : ℝ)⁻¹) (volume.restrict (Icc a b)) :=
    G_integrable n |>.aestronglyMeasurable
  have hG' : liminf (fun (n : ℕ) ↦ ∫⁻ (x : ℝ) in Icc a b, ‖G (n : ℝ)⁻¹ x‖ₑ) atTop ≤
      ENNReal.ofReal (f b - f a) := by
    calc
      _ = liminf (fun (n : ℕ) ↦ ENNReal.ofReal (∫ (x : ℝ) in Icc a b, (G (n : ℝ)⁻¹) x)) atTop := by
        apply Filter.liminf_congr
        filter_upwards with n
        rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (G_integrable n)]
        congr with y
        exact abs_eq_self.mpr (hg.monotoneOn univ |>.slope_nonneg trivial trivial)
      _ ≤ ENNReal.ofReal (g b - g a) := by
        refine Filter.liminf_le_of_frequently_le'
          (Filter.Frequently.of_forall fun n ↦ ENNReal.ofReal_le_ofReal ?_)
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
        convert hg.monotoneOn (Icc a (b + (n : ℝ)⁻¹)) |>.intervalIntegral_slope_bound hab (by simp)
          using 2
        simp [g]
      _ = ENNReal.ofReal (f b - f a) := by grind
  have hG'₀ : liminf (fun (n : ℕ) ↦ ∫⁻ (x : ℝ) in Icc a b, ‖G (n : ℝ)⁻¹ x‖ₑ) atTop ≠ ⊤ :=
    lt_of_le_of_lt hG' ENNReal.ofReal_lt_top |>.ne_top
  have integrable_f_deriv := integrable_of_tendsto_atTop_aestronglyMeasurable_liminf_ne_top
    hGf hG hG'₀
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr integrable_f_deriv, ?_⟩
  rw [MeasureTheory.ae_restrict_iff' (by simp)] at hGf
  rw [← uIcc_of_le hab] at hGf hG hG'
  have ebound := lintegral_bound_of_tendsto_atTop_aestronglyMeasurable
    ((MeasureTheory.ae_restrict_iff' (by measurability) |>.mpr hGf)) hG
  grw [hG'] at ebound
  have : f a ≤ f b := hf (by simp [hab]) (by simp [hab]) hab
  rw [uIcc_of_le (by linarith), mem_Icc]
  constructor
  · apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' (by simp)]
    filter_upwards [h₁, h₂] with x _ _ _
    rw [hfg (by grind)]
    exact hg.deriv_nonneg
  · rw [uIcc_of_le hab,
        ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm integrable_f_deriv,
        ENNReal.ofReal_le_ofReal_iff (by linarith),
        integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab] at ebound
    convert ebound using 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [h₂] with x _ _
    rw [hfg (by grind [uIoc])]
    exact abs_eq_self.mpr hg.deriv_nonneg |>.symm

/-- If `f` is monotone on `a..b`, then `f'` is interval integrable on `a..b`. -/
theorem MonotoneOn.intervalIntegrable_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : MonotoneOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b :=
  hf.intervalIntegrable_deriv_intervalIntegral_bound.left

/-- If `f` is monotone on `a..b`, then the integral of `f'` on `a..b` is in between `0` and
`f b - f a`. -/
theorem MonotoneOn.intervalIntegral_bound {f : ℝ → ℝ} {a b : ℝ}
    (hf : MonotoneOn f (uIcc a b)) :
    ∫ x in a..b, deriv f x ∈ uIcc 0 (f b - f a) :=
  hf.intervalIntegrable_deriv_intervalIntegral_bound.right

/-- If `f` has bounded variation on `uIcc a b`, then `f'` is interval integrable on `a..b`. -/
theorem BoundedVariationOn.intervalIntegrable_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedVariationOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have h₂ : ∀ᵐ x, x ≠ max a b := by simp [ae_iff, measure_singleton]
  apply (hp.intervalIntegrable_deriv.sub hq.intervalIntegrable_deriv).congr
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by simp [uIoc])]
  filter_upwards [hp.ae_differentiableWithinAt_of_mem, hq.ae_differentiableWithinAt_of_mem, h₂]
    with x hx₁ hx₂ hx₃ hx₄
  have hx₅ : x ∈ uIcc a b := Ioc_subset_Icc_self hx₄
  rw [uIoc, mem_Ioc] at hx₄
  replace hx₁ := (hx₁ hx₅).differentiableAt (Icc_mem_nhds (by grind) (by grind)) |>.hasDerivAt
  replace hx₂ := (hx₂ hx₅).differentiableAt (Icc_mem_nhds (by grind) (by grind)) |>.hasDerivAt
  exact (hx₁.sub hx₂).deriv.symm

/-- If `f` is absolute continuous on `uIcc a b`, then `f'` is interval integrable on `a..b`. -/
theorem AbsolutelyContinuousOnInterval.intervalIntegrable_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b :=
  hf.boundedVariationOn.intervalIntegrable_deriv
