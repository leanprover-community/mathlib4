/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# `f'` is interval integrable for certain classes of functions `f`

This file proves that:
* `MonotoneOn.deriv_intervalIntegrable` - If `f` is monotone on `a..b`, then `f'` is interval
integrable on `a..b`.
* `LocallyBoundedVariationOn.deriv_intervalIntegrable` - If `f` has bounded variation on `a..b`,
then `f'` is interval integrable on `a..b`.
* `AbsolutelyContinuousOnInterval.ae_differentiableAt` - If `f` is absolutely continuous on `a..b`,
then `f'` exists a.e. on `a..b`.
* `AbsolutelyContinuousOnInterval.deriv_intervalIntegrable` - If `f` is absolutely continuous on
`a..b`, then `f'` is interval integrable on `a..b`.

## Tags
interval integrable, monotone, bounded variation, absolutely continuous
-/

open MeasureTheory Set Filter Function

open scoped Topology ENNReal Interval NNReal


/-- If `f` is monotone, then `f'` is interval integrable on `a..b` for any `a` and `b`. -/
theorem MonotoneOn.deriv_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ} (hf : MonotoneOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  wlog hab : a ≤ b generalizing a b
  · exact @this b a (uIcc_comm a b ▸ hf) (by linarith) |>.symm
  rw [uIcc_of_le hab] at hf
  let g (x : ℝ) : ℝ := if x <= a then f a else if x < b then f x else f b
  have hg : Monotone g := by
    intro x y hxy
    dsimp only [g]
    split_ifs <;> try linarith
    all_goals apply hf
    all_goals grind
  have h₂ : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  have hfg : EqOn f g (Ioo a b) := by grind [EqOn]
  replace hfg := hfg.deriv isOpen_Ioo
  have hg_shift (z a₀ b₀ : ℝ) : IntervalIntegrable (fun x ↦ g (x + z)) volume a₀ b₀ := by
      convert hg.intervalIntegrable (a := a₀ + z) (b := b₀ + z) |>.comp_add_right z <;> abel
  let G (c x : ℝ) := slope g x (x + c)
  have G_nonneg (c x : ℝ) (hc : 0 ≤ c) : 0 ≤ G c x := by
    simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul, G]
    exact mul_nonneg (inv_nonneg.mpr hc) (by linarith [hg (show x ≤ x + c by linarith)])
  have G_integrable (c : ℝ) : LocallyIntegrable (G c) volume := by
    simp only [G, slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
    exact (hg.covariant_of_const' c).locallyIntegrable.sub (hg.locallyIntegrable) |>.smul (c := c⁻¹)
  have G_lim : ∀ᵐ (x : ℝ), Filter.Tendsto (fun (n : ℕ) ↦ G (n : ℝ)⁻¹ x) Filter.atTop
      (𝓝 (deriv g x)) := by
    filter_upwards [hg.ae_differentiableAt] with x hx₁ using hx₁.hasDerivAt.tendsto_slope.comp <|
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by convert tendsto_const_nhds.add tendsto_inverse_atTop_nhds_zero_nat; simp)
      (by simp [eventually_ne_atTop 0])
  have G_liminf : ∀ᵐ (x : ℝ),
      Filter.liminf (fun (n : ℕ) ↦ ‖G (n : ℝ)⁻¹ x‖ₑ) Filter.atTop = ‖deriv g x‖ₑ:= by
    filter_upwards [G_lim] with x hx using hx.enorm.liminf_eq
  have G_fatou := MeasureTheory.lintegral_liminf_le₀'
    (fun n ↦ G_integrable (n : ℝ)⁻¹ |>.aestronglyMeasurable |>.aemeasurable |>.enorm) (Ioc a b)
  have G_bound {n : ℕ} (hn : n ≠ 0) :
      n * (∫ (x : ℝ) in a..b, g (x + (n : ℝ)⁻¹) - g x) ≤ g b - g a := by
    have n_inv_mul : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (by norm_cast)
    rw [intervalIntegral.integral_sub (hg_shift _ _ _) hg.intervalIntegrable,
        intervalIntegral.integral_comp_add_right,
        intervalIntegral.integral_interval_sub_interval_comm',
        intervalIntegral.integral_congr (g := fun _ ↦ g b),
        intervalIntegral.integral_const]
    · simp only [add_sub_cancel_left, smul_eq_mul, mul_sub, ← mul_assoc, n_inv_mul]
      have : g a = ↑n * ∫ (x : ℝ) in a..a + (↑n)⁻¹, g a := by simp [← mul_assoc, n_inv_mul]
      rw [this]
      gcongr
      · simp
      · exact intervalIntegral.integral_mono_on (by simp) (by simp) hg.intervalIntegrable
          (fun x hx ↦ hg (mem_Icc.mp hx).left)
    · simp only [EqOn, le_add_iff_nonneg_right, inv_nonneg, Nat.cast_nonneg, uIcc_of_le, mem_Icc,
          and_imp]
      grind
    all_goals exact hg.intervalIntegrable
  have f_fatou : ∫⁻ x in Ioc a b, ‖deriv f x‖ₑ ≤ ENNReal.ofReal (f b - f a) := by
    calc
      _ = ∫⁻ x in (Ioc a b), ‖deriv g x‖ₑ := by
        apply MeasureTheory.setLIntegral_congr_fun_ae (by simp)
        filter_upwards [h₂] with x hxb hx
        rw [hfg (by grind)]
      _ ≤ liminf (fun (n : ℕ) ↦ ∫⁻ (x : ℝ) in Ioc a b, ‖G (n : ℝ)⁻¹ x‖ₑ) atTop := by
        convert G_fatou using 1
        apply MeasureTheory.setLIntegral_congr_fun_ae (by simp)
        filter_upwards [G_liminf] with x hx _
        rw [hx]
      _ = liminf (fun (n : ℕ) ↦ ENNReal.ofReal (∫ (x : ℝ) in Ioc a b, (G (n : ℝ)⁻¹) x)) atTop := by
        apply Filter.liminf_congr
        filter_upwards with n
        rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm]
        · congr with y
          apply abs_eq_self.mpr
          apply G_nonneg; simp
        · exact (G_integrable (n : ℝ)⁻¹).integrableOn_isCompact (k := Icc a b)
              (hk := isCompact_Icc) |>.mono_set (by grind)
      _ ≤ ENNReal.ofReal (g b - g a) := by
        refine Filter.liminf_le_of_frequently_le' (Filter.Eventually.frequently ?_)
        simp only [Filter.Eventually, mem_atTop_sets, mem_setOf_eq]
        refine ⟨1, fun n hn ↦ ENNReal.ofReal_le_ofReal ?_⟩
        simp [← intervalIntegral.integral_of_le hab, slope,
          intervalIntegral.integral_const_mul, G, G_bound (show n ≠ 0 by omega)]
      _ = ENNReal.ofReal (f b - f a) := by grind
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  constructor
  · suffices AEStronglyMeasurable (deriv g) (volume.restrict (Ioc a b)) by
      apply this.congr
      rw [EventuallyEq, ae_restrict_iff' (by simp)]
      filter_upwards [h₂] with x hx₁ hx₂ using hfg.symm (by grind)
    suffices AEStronglyMeasurable (deriv g) from this.restrict
    apply aestronglyMeasurable_of_tendsto_ae (lim := G_lim)
    exact fun n ↦ (G_integrable (n : ℝ)⁻¹).aestronglyMeasurable
  · grw [HasFiniteIntegral, f_fatou]
    exact ENNReal.ofReal_lt_top

/-- If `f` has locally bounded variation on `uIcc a b`, then `f'` is interval integrable on
`a..b`. -/
theorem LocallyBoundedVariationOn.deriv_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ}
  (hf : LocallyBoundedVariationOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.exists_monotoneOn_sub_monotoneOn
  have h₂ : ∀ᵐ x, x ≠ max a b := by simp [ae_iff, measure_singleton]
  apply (hp.deriv_intervalIntegrable.sub hq.deriv_intervalIntegrable).congr
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by simp [uIoc])]
  filter_upwards [hp.ae_differentiableWithinAt_of_mem, hq.ae_differentiableWithinAt_of_mem, h₂]
    with x hx₁ hx₂ hx₃ hx₄
  have hx₅ : x ∈ uIcc a b := Ioc_subset_Icc_self hx₄
  rw [uIoc, mem_Ioc] at hx₄
  replace hx₁ := (hx₁ hx₅).differentiableAt (Icc_mem_nhds (by grind) (by grind)) |>.hasDerivAt
  replace hx₂ := (hx₂ hx₅).differentiableAt (Icc_mem_nhds (by grind) (by grind)) |>.hasDerivAt
  exact (hx₁.sub hx₂).deriv.symm

/-- If `f` is absolute continuous on `uIcc a b`, then `f'` exists a.e. on `uIcc a b`. -/
theorem AbsolutelyContinuousOnInterval.ae_differentiableAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ (x : ℝ), x ∈ uIcc a b → DifferentiableAt ℝ f x := by
  have := hf.boundedVariationOn.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem
  have h₁ : ∀ᵐ x, x ≠ min a b := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ max a b := by simp [ae_iff, measure_singleton]
  filter_upwards [this, h₁, h₂] with x hx₁ hx₂ hx₃ hx₄
  rw [uIcc, mem_Icc] at hx₄
  exact (hx₁ hx₄).differentiableAt (Icc_mem_nhds (by grind) (by grind))

/-- If `f` is absolute continuous on `uIcc a b`, then `f'` is interval integrable on `a..b`. -/
theorem AbsolutelyContinuousOnInterval.deriv_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ}
  (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b :=
  hf.boundedVariationOn.locallyBoundedVariationOn.deriv_intervalIntegrable
