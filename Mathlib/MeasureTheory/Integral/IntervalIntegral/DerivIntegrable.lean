/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# `f'` is interval integrable for certain classes of functions `f`

This file proves that:
* If `f` is monotone on `a..b`, then `f'` is interval integrable on `a..b`.
* If `f` has bounded variation on `a..b`, then `f'` is interval integrable on `a..b`.
* If `f` is absolutely continuous on `a..b`, then `f'` exists a.e. on `a..b` and is interval
integrable on `a..b`.

## Tags
interval integrable, monotone, bounded variation, absolutely continuous
-/

open MeasureTheory Set Filter Function

open scoped Topology ENNReal Interval NNReal

/-- If `f z` tends to `y` as `z` tends to `x`, then `f (x + (n : ℝ)⁻¹)` tends to `y` as `n` tends
to infinity. -/
theorem Filter.Tendsto.inverse_atTop {f : ℝ → ℝ} {x y : ℝ}
    (h : Filter.Tendsto f (𝓝[≠] x) (𝓝 y)) :
    Filter.Tendsto (fun n : ℕ ↦ f (x + (n : ℝ)⁻¹)) Filter.atTop (𝓝 y) := by
  apply Filter.Tendsto.comp h
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · nth_rw 2 [show x = x + 0 by simp]
    apply tendsto_const_nhds.add
    exact tendsto_inverse_atTop_nhds_zero_nat
  · have : ∀ᶠ (n : ℕ) in atTop, n ≠ 0 := by
      simp only [Filter.Eventually, mem_atTop_sets, mem_setOf_eq]
      use 1; intro n hn; omega
    filter_upwards [this] with n hn
    simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, inv_eq_zero]
    norm_cast

/-- If `f` differentiable at `x ∈ uIoo a b` within `uIcc a b`, then `f'` exists at `x`. -/
theorem DifferentiableWithinAt.hasDerivAt_interval {f : ℝ → ℝ} {a b x : ℝ}
    (hf : DifferentiableWithinAt ℝ f (uIcc a b) x) (hx : x ∈ uIoo a b) :
    HasDerivAt f (deriv f x) x := by
  have : uIcc a b ∈ 𝓝 x := by
    suffices uIoo a b ∈ 𝓝 x from Filter.mem_of_superset this Ioo_subset_Icc_self
    rw [uIoo, mem_Ioo] at hx
    apply Ioo_mem_nhds <;> tauto
  have hx1 := hf.hasDerivWithinAt.hasDerivAt this
  rwa [hx1.deriv]

/-- If `f` is monotone on `uIcc a b`, then `f'` is interval integrable on `a..b`. -/
theorem MonotoneOn.deriv_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ} (hf : MonotoneOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  wlog hab : a ≤ b
  · exact @this f b a (uIcc_comm a b ▸ hf) (by linarith) |>.symm
  rw [uIcc_of_le hab] at hf
  let g (x : ℝ) : ℝ := if x <= a then f a else if x < b then f x else f b
  have hg : Monotone g := by
    intro x y hxy
    dsimp only [g]
    split_ifs <;> try linarith
    all_goals apply hf
    any_goals rw [mem_Icc]
    any_goals constructor
    all_goals linarith
  have hgc (c : ℝ) : Monotone (fun x ↦ g (x + c)) := by
    intro x y hxy; beta_reduce; apply hg; linarith
  have h1 : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h2 : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  have hg2 : ∀ᵐ (x : ℝ), HasDerivAt g (deriv g x) x ∧ 0 ≤ deriv g x := by
    filter_upwards [hg.ae_differentiableAt, h1, h2] with x hx1 hx2 hx3
    exact ⟨hx1.hasDerivAt, hg.deriv_nonneg⟩
  have hfg : ∀ x ∈ Ioo a b, deriv f x = deriv g x := by
    intro x hx
    rw [mem_Ioo] at hx
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [show Ioo a b ∈ 𝓝 x by apply Ioo_mem_nhds <;> tauto] with y hy
    simp [g, mem_Ioo.mp hy]
  have hg3 (a0 b0 : ℝ) := hg.intervalIntegrable (μ := volume) (a := a0) (b := b0)
  have hg4 (z a0 b0 : ℝ) : IntervalIntegrable (fun x ↦ g (x + z)) volume a0 b0 := by
      convert hg3 (a0 + z) (b0 + z) |>.comp_add_right z <;> abel
  have hg5 {x : ℝ} (hx : b ≤ x) : g x = g b := by
    simp only [lt_self_iff_false, ↓reduceIte, g]
    split_ifs <;> (congr; try linarith)
  let G (c x : ℝ) := slope g x (x + c)
  have G_nonneg (c x : ℝ) (hc : 0 ≤ c) : 0 ≤ G c x := by
    have : g x ≤ g (x + c) := by apply hg; linarith
    have : 0 ≤ g (x + c) - g x := by linarith
    simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul, ge_iff_le, G]
    exact mul_nonneg (inv_nonneg.mpr hc) this
  have G_integrable (c : ℝ) : LocallyIntegrable (G c) volume := by
    simp only [G, slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul]
    exact (hgc c).locallyIntegrable.sub (hg.locallyIntegrable) |>.smul (c := c⁻¹)
  have G_measurable (n : ℕ) : AEMeasurable (G (n : ℝ)⁻¹) volume := by
    exact G_integrable (n : ℝ)⁻¹ |>.aestronglyMeasurable |>.aemeasurable
  have G_measurable_ab (n : ℕ) : AEMeasurable ((Ioc a b).indicator (G (n : ℝ)⁻¹)) volume := by
    apply (G_measurable n).indicator; simp
  have G_lim : ∀ᵐ (x : ℝ), Filter.Tendsto (fun (n : ℕ) ↦ G (n : ℝ)⁻¹ x) Filter.atTop
      (nhds (deriv g x)) := by
    filter_upwards [hg2] with x ⟨hx1, hx2⟩
    rw [hasDerivAt_iff_tendsto_slope] at hx1
    dsimp only [G]
    exact hx1.inverse_atTop
  have G_liminf' : ∀ᵐ (x : ℝ),
      Filter.liminf (fun (n : ℕ) ↦ ‖G (n : ℝ)⁻¹ x‖ₑ) Filter.atTop =
        ‖deriv g x‖ₑ:= by
    filter_upwards [G_lim] with x hx
    exact hx.enorm.liminf_eq
  have G_liminf'_ab : ∀ᵐ (x : ℝ),
      Filter.liminf (fun (n : ℕ) ↦ ‖(Ioc a b).indicator (G (n : ℝ)⁻¹) x‖ₑ) Filter.atTop =
      ‖((Ioc a b).indicator (deriv g)) x‖ₑ := by
    filter_upwards [G_liminf'] with x hx
    by_cases hx1 : x ∈ Ioc a b <;> simp only [hx1, Set.indicator, ↓reduceIte]
    · exact hx
    · simp
  have G_fatou := MeasureTheory.lintegral_liminf_le' (fun n ↦ ((G_measurable_ab n).enorm))
  have G_bound {n : ℕ} (hn : n ≥ 1) :
      n * (∫ (x : ℝ) in a..b, g (x + (n : ℝ)⁻¹) - g x) ≤ g b - g a := by
    calc
      _ = n * ((∫ (x : ℝ) in a..b, g (x + (↑n)⁻¹)) - ∫ (x : ℝ) in a..b, g x) := by
        rw [intervalIntegral.integral_sub (hg4 _ _ _) (hg3 _ _)]
      _ = n * ((∫ (x : ℝ) in (a + (↑n)⁻¹)..(b + (↑n)⁻¹), g x) - ∫ (x : ℝ) in a..b, g x) := by simp
      _ = n * ((∫ (x : ℝ) in b..(b + (↑n)⁻¹), g x) - ∫ (x : ℝ) in a..(a + (↑n)⁻¹), g x) := by
        rw [intervalIntegral.integral_interval_sub_interval_comm'] <;> exact hg3 _ _
      _ = n * ((∫ (x : ℝ) in b..(b + (↑n)⁻¹), g b) - ∫ (x : ℝ) in a..(a + (↑n)⁻¹), g x) := by
        congr 2
        apply intervalIntegral.integral_congr
        simp only [EqOn, le_add_iff_nonneg_right, inv_nonneg, Nat.cast_nonneg, uIcc_of_le, mem_Icc,
          and_imp]
        exact fun x hx1 _ ↦ hg5 hx1
      _ = n * ((↑n)⁻¹ * g b - ∫ (x : ℝ) in a..(a + (↑n)⁻¹), g x) := by simp
      _ ≤ n * ((↑n)⁻¹ * g b - ∫ (x : ℝ) in a..(a + (↑n)⁻¹), g a) := by
        gcongr
        apply intervalIntegral.integral_mono_on <;> try simp
        · exact hg3 _ _
        · intros; apply hg; assumption
      _ = n * ((↑n)⁻¹ * g b - (↑n)⁻¹ * g a) := by simp
      _ = g b - g a := by
        ring_nf
        rw [show (n : ℝ) * (n : ℝ)⁻¹ = 1 by refine mul_inv_cancel₀ ?_; norm_cast; omega]
        ring
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  constructor
  · suffices AEStronglyMeasurable (deriv g) (volume.restrict (Ioc a b)) by
      apply this.congr
      have h3 : ∀ᵐ x ∂(volume.restrict (Ioc a b)), x ∈ Ioc a b := by
        apply MeasureTheory.ae_restrict_mem; simp
      have h4 : ∀ᵐ x ∂(volume.restrict (Ioc a b)), x ≠ b := by
        rw [MeasureTheory.ae_restrict_iff']
        · filter_upwards [h2] with x hx1 hx2; exact hx1
        · simp
      filter_upwards [h3, h4] with x hx1 hx2
      symm; apply hfg
      rw [← Ioc_diff_right, mem_diff]
      simp [hx1, hx2]
    suffices AEStronglyMeasurable (deriv g) from this.restrict
    apply aestronglyMeasurable_of_tendsto_ae (lim := G_lim)
    intro n; exact (G_integrable (n : ℝ)⁻¹).aestronglyMeasurable
  · unfold HasFiniteIntegral
    calc ∫⁻ x in Ioc a b, ‖deriv f x‖ₑ
      _ = ∫⁻ x, (Ioc a b).indicator (fun t ↦ ‖deriv f t‖ₑ) x := by simp
      _ = ∫⁻ x, (Ioc a b).indicator (fun t ↦ ‖deriv g t‖ₑ) x := by
        apply MeasureTheory.lintegral_congr_ae
        filter_upwards [h2] with x hxb
        by_cases hx : x ∈ Ioc a b <;> simp only [indicator, hx, ↓reduceIte]
        congr 1
        apply hfg
        rw [← Ioc_diff_right, mem_diff]
        simp [hx, hxb]
      _ = ∫⁻ x, ‖(Ioc a b).indicator (deriv g) x‖ₑ := by
        apply MeasureTheory.lintegral_congr
        intro x
        dsimp only [Set.indicator]
        by_cases hx : x ∈ Ioc a b <;> simp [hx]
      _ ≤ liminf (fun (n : ℕ) ↦ ∫⁻ (a_1 : ℝ), ‖(Ioc a b).indicator (G (n : ℝ)⁻¹) a_1‖ₑ) atTop := by
        convert G_fatou using 1
        apply MeasureTheory.lintegral_congr_ae
        filter_upwards [G_liminf'_ab] with x hx
        rw [hx]
      _ = liminf (fun (n : ℕ) ↦ ENNReal.ofReal (∫ (a_1 : ℝ), (Ioc a b).indicator (G (n : ℝ)⁻¹) a_1))
          atTop := by
        apply Filter.liminf_congr
        filter_upwards with n
        rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm]
        · congr with y
          apply abs_eq_self.mpr
          dsimp only [Set.indicator]
          by_cases hy : y ∈ Ioc a b
          · simp only [hy, ↓reduceIte]
            apply G_nonneg; simp
          · simp only [hy, ↓reduceIte]; simp
        · have := (G_integrable (n : ℝ)⁻¹).integrableOn_isCompact (k := Icc a b)
              (hk := isCompact_Icc)
          have := this.indicator (t := Ioc a b) (ht := by simp)
          have := this.integrable_indicator (hs := by simp)
          convert this using 1
          ext x
          by_cases hx : x ∈ Ioc a b <;> simp only [indicator, hx, ↓reduceIte]
          · simp [Ioc_subset_Icc_self hx]
          · simp
      _ = liminf (fun (n : ℕ) ↦ ENNReal.ofReal (∫ a_1 in a..b, (G (n : ℝ)⁻¹) a_1)) atTop := by
        apply Filter.liminf_congr
        filter_upwards with n
        congr 1
        rw [intervalIntegral.integral_of_le hab, integral_indicator]
        simp
      _ ≤ ENNReal.ofReal (g b - g a) := by
        apply Filter.liminf_le_of_frequently_le'
        refine Filter.Eventually.frequently ?_
        simp only [Filter.Eventually, mem_atTop_sets, mem_setOf_eq]
        use 1
        intro n hn
        apply ENNReal.ofReal_le_ofReal
        simp only [slope, add_sub_cancel_left, vsub_eq_sub, smul_eq_mul, inv_inv,
          intervalIntegral.integral_const_mul, G]
        exact G_bound hn
      _ < ∞ := ENNReal.ofReal_lt_top

/-- If `f` has locally bounded variation on `uIcc a b`, then `f'` is interval integrable on
`a..b`. -/
theorem LocallyBoundedVariationOn.deriv_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ}
  (hf : LocallyBoundedVariationOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.exists_monotoneOn_sub_monotoneOn
  have h1 : ∀ᵐ x, x ≠ min a b := by simp [ae_iff, measure_singleton]
  have h2 : ∀ᵐ x, x ≠ max a b := by simp [ae_iff, measure_singleton]
  have hp1 := hp.deriv_intervalIntegrable
  have hq1 := hq.deriv_intervalIntegrable
  have hp2 := hp.ae_differentiableWithinAt_of_mem
  have hq2 := hq.ae_differentiableWithinAt_of_mem
  apply (hp1.sub hq1).congr
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff']
  · filter_upwards [hp2, hq2, h1, h2] with x hx1 hx2 hx3 hx4 hx5
    have hx6 : x ∈ uIcc a b := by rw [uIcc]; rw [uIoc] at hx5; exact Ioc_subset_Icc_self hx5
    have hx7 : x ∈ uIoo a b := by
      rw [uIoo, ← Icc_diff_both, mem_diff, ← uIcc]; simp [hx3, hx4, hx6]
    replace hx1 := (hx1 hx6).hasDerivAt_interval hx7
    replace hx2 := (hx2 hx6).hasDerivAt_interval hx7
    rw [(hx1.sub hx2).deriv]
  · simp [uIoc]

/-- If `f` is absolute continuous on `uIcc a b`, then `f` is a.e. differentiable on `uIcc a b`. -/
theorem AbsolutelyContinuousOnInterval.ae_differentiableWithinAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ (x : ℝ), x ∈ Set.uIcc a b → DifferentiableWithinAt ℝ f (Set.uIcc a b) x :=
  hf.boundedVariationOn.locallyBoundedVariationOn.ae_differentiableWithinAt_of_mem

/-- If `f` is absolute continuous on `uIcc a b`, then `f` exists a.e. on `uIcc a b`. -/
theorem AbsolutelyContinuousOnInterval.ae_hasDerivAt {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ (x : ℝ), x ∈ Set.uIcc a b → HasDerivAt f (deriv f x) x := by
  have h1 : ∀ᵐ x, x ≠ min a b := by simp [ae_iff, measure_singleton]
  have h2 : ∀ᵐ x, x ≠ max a b := by simp [ae_iff, measure_singleton]
  filter_upwards [hf.ae_differentiableWithinAt, h1, h2] with x hx1 hx2 hx3 hx4
  have : x ∈ uIoo a b := by rw [uIoo, ← Icc_diff_both, mem_diff, ← uIcc]; simp [hx2, hx3, hx4]
  exact (hx1 hx4).hasDerivAt_interval this

/-- If `f` is absolute continuous on `uIcc a b`, then `f'` is interval integrable on `a..b`. -/
theorem AbsolutelyContinuousOnInterval.deriv_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ}
  (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b :=
  hf.boundedVariationOn.locallyBoundedVariationOn.deriv_intervalIntegrable
