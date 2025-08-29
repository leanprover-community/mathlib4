/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Lebesgue Differentiation Theorem (Interval Version)

This file proves the interval version of the Lebesgue Differentiation Theorem.
-/

open MeasureTheory Set Filter Function

open scoped Topology ENNReal Interval NNReal

lemma vitaliFamily_cover : ∀ (x : ℝ), ∃ᶠ (r : ℝ) in 𝓝[>] 0,
    (volume) (Metric.closedBall x (3 * r)) ≤
      6 * (volume) (Metric.closedBall x r) := by
  simp_rw [frequently_nhdsWithin_iff, frequently_nhds_iff]
  intro x U hU1 hU2
  obtain ⟨ε, hε1, hε2⟩ := Metric.mem_nhds_iff.mp <| hU2.mem_nhds hU1
  have : ε ≥ 0 := by linarith
  use ε / 2
  constructor
  · apply hε2
    simp only [Metric.mem_ball, dist_zero_right, norm_div, Real.norm_eq_abs, Nat.abs_ofNat]
    rw [abs_eq_self.mpr this]
    linarith
  · simp; constructor <;> try assumption
    rw [show 6 = ENNReal.ofReal 6 by norm_num, ← ENNReal.ofReal_mul] <;> try norm_num
    rw [ENNReal.ofReal_le_ofReal_iff] <;> linarith

/-- The interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → ℝ` is integrable and
`c : ℝ`, then for almost every `x`, the derivative of `∫ (t : ℝ) in c..x, f t` at `x`
is equal to `f x`. -/
theorem Integrable.ae_eq_deriv_integral {f : ℝ → ℝ} (hf : Integrable f volume) (c : ℝ) :
    ∀ᵐ x, HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  simp_rw [hasDerivAt_iff_tendsto]
  have hfL : LocallyIntegrable f (volume) := by
    apply Integrable.locallyIntegrable; assumption
  have hg0 : IntegrableOn f Set.univ volume := by simpa
  have hg1 (x y : ℝ) : IntervalIntegrable f volume x y := by
    unfold IntervalIntegrable; constructor <;> apply IntegrableOn.mono_set hg0 <;> simp
  set vF := Vitali.vitaliFamily volume 6 vitaliFamily_cover
  have LDT := VitaliFamily.ae_tendsto_average_norm_sub vF hfL
  filter_upwards [LDT] with x hx
  simp_rw [Filter.tendsto_def, VitaliFamily.mem_filterAt_iff] at hx
  simp +contextual only [mem_preimage] at hx
  rw [Filter.tendsto_def]
  intro s hs
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε0, hε01, hε02⟩ := hs
  obtain ⟨ε, hε1, hε2⟩ := hx (Metric.ball 0 ε0) (by rw [Metric.mem_nhds_iff]; use ε0)
  have hε3 (ε' : ℝ) (hε'1 : ε' > 0) (hε'1 : ε' < ε) :
      (Icc x (x + ε') ∈ vF.setsAt x ∧ Icc x (x + ε') ⊆ Metric.closedBall x ε) ∧
      (Icc (x - ε') x ∈ vF.setsAt x ∧ Icc (x - ε') x ⊆ Metric.closedBall x ε) := by
    constructor
    all_goals
      constructor
      · simp only [Vitali.vitaliFamily, vF]
        simp only [Real.volume_closedBall, ENNReal.coe_ofNat, mem_setOf_eq, interior_Icc,
          nonempty_Ioo, Real.volume_Icc]
        constructor
        · exact isClosed_Icc
        · constructor; linarith
          use ε'; constructor
          · rw [Real.closedBall_eq_Icc]; gcongr; linarith
          · rw [show 6 = ENNReal.ofReal 6 by norm_num, ← ENNReal.ofReal_mul] <;> try norm_num
            rw [ENNReal.ofReal_le_ofReal_iff] <;> linarith
      · rw [Real.closedBall_eq_Icc]; gcongr; linarith
  rw [Metric.mem_nhds_iff]
  use ε
  constructor; · assumption
  intro y hy
  simp only [Metric.mem_ball, Real.dist_eq] at hy
  simp only [Real.norm_eq_abs, smul_eq_mul, mem_preimage]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := x)]
  · simp only [add_sub_cancel_left]
    by_cases hxy0 : x = y
    · simp only [hxy0, sub_self, abs_zero, inv_zero, intervalIntegral.integral_same, zero_mul,
        mul_zero]
      apply hε02; simpa
    · by_cases hxy : x < y
      · replace hε3 := hε3 (y - x) (by linarith) (lt_of_abs_lt hy) |>.left
        simp only [add_sub_cancel] at hε3
        specialize hε2 (Icc x y) (hε3.left) (hε3.right)
        simp only [average, MeasurableSet.univ, Measure.restrict_apply, univ_inter, Real.volume_Icc,
          Real.norm_eq_abs, MeasureTheory.integral_smul_measure, ENNReal.toReal_inv,
          smul_eq_mul] at hε2
        rw [ENNReal.toReal_ofReal] at hε2 <;> try linarith
        suffices abs (|y - x|⁻¹ * |(∫ (t : ℝ) in x..y, f t) - (y - x) * f x|) ≤
            abs ((y - x)⁻¹ * ∫ (x_1 : ℝ) in Icc x y, |f x_1 - f x|) by
          apply hε02
          simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε2 ⊢
          exact lt_of_le_of_lt this hε2
        have : y - x ≥ 0 := by linarith
        simp only [abs_mul, abs_abs, ge_iff_le]
        gcongr 1
        · rw [abs_eq_self.mpr this]
        · calc
          _ = |(∫ (t : ℝ) in x..y, f t) - ∫ (t : ℝ) in x..y, f x| := by congr; simp
          _ = |∫ (t : ℝ) in x..y, (f t - f x)| := by
            rw [intervalIntegral.integral_sub]; · exact hg1 x y
            simp
          _ = |∫ (t : ℝ) in Ioc x y, (f t - f x)| := by
            rw [intervalIntegral.integral_of_le]; linarith
          _ ≤ ∫ (t : ℝ) in Ioc x y, |f t - f x| := by
            exact MeasureTheory.abs_integral_le_integral_abs
          _ ≤ ∫ (t : ℝ) in Icc x y, |f t - f x| := by
            refine setIntegral_mono_set ?_ ?_ ?_
            · dsimp only [IntegrableOn]
              apply Integrable.abs
              rw [show (fun a ↦ f a - f x) = f - (fun a ↦ f x) by ext a; simp]
              apply Integrable.sub
              · exact hf.integrableOn
              · simp
            · filter_upwards
              simp
            · suffices Ioc x y ⊆ Icc x y by
                filter_upwards
                intro z
                simp only [le_Prop_eq]
                intro hz
                exact this hz
              exact Ioc_subset_Icc_self
          _ = abs (∫ (t : ℝ) in Icc x y, |f t - f x|) := by
            rw [abs_eq_self.mpr]
            refine setIntegral_nonneg ?_ ?_ <;> simp
      · have hxy : y < x := by grind
        replace hy : |x - y| < ε := by
          convert hy using 1
          simp [← Real.dist_eq]; apply dist_comm
        replace hε3 := hε3 (x - y) (by linarith) (lt_of_abs_lt hy) |>.right
        simp only [sub_sub_cancel] at hε3
        specialize hε2 (Icc y x) (hε3.left) (hε3.right)
        simp only [average, MeasurableSet.univ, Measure.restrict_apply, univ_inter, Real.volume_Icc,
          Real.norm_eq_abs, MeasureTheory.integral_smul_measure, ENNReal.toReal_inv,
          smul_eq_mul] at hε2
        rw [ENNReal.toReal_ofReal] at hε2 <;> try linarith
        suffices abs (|y - x|⁻¹ * |(∫ (t : ℝ) in x..y, f t) - (y - x) * f x|) ≤
            abs ((x - y)⁻¹ * ∫ (x_1 : ℝ) in Icc y x, |f x_1 - f x|) by
          apply hε02
          simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε2 ⊢
          exact lt_of_le_of_lt this hε2
        have : y - x ≤ 0 := by linarith
        simp only [abs_mul, abs_abs, ge_iff_le]
        gcongr 1
        · rw [abs_eq_neg_self.mpr this]
          ring_nf; simp
        · calc
          _ = |(∫ (t : ℝ) in x..y, f t) - ∫ (t : ℝ) in x..y, f x| := by congr; simp
          _ = |∫ (t : ℝ) in x..y, (f t - f x)| := by
            rw [intervalIntegral.integral_sub]; · exact hg1 x y
            simp
          _ = |-∫ (t : ℝ) in Ioc y x, (f t - f x)| := by
            rw [intervalIntegral.integral_of_ge]; linarith
          _ = |∫ (t : ℝ) in Ioc y x, -(f t - f x)| := by
            rw [MeasureTheory.integral_neg]
          _ ≤ ∫ (t : ℝ) in Ioc y x, |-(f t - f x)| := by
            exact MeasureTheory.abs_integral_le_integral_abs
          _ = ∫ (t : ℝ) in Ioc y x, |f t - f x| := by
            simp_rw [abs_neg]
          _ ≤ ∫ (t : ℝ) in Icc y x, |f t - f x| := by
            refine setIntegral_mono_set ?_ ?_ ?_
            · dsimp only [IntegrableOn]
              apply Integrable.abs
              rw [show (fun a ↦ f a - f x) = f - (fun a ↦ f x) by ext a; simp]
              apply Integrable.sub
              · exact hf.integrableOn
              · simp
            · filter_upwards
              simp
            · suffices Ioc y x ⊆ Icc y x by
                filter_upwards
                intro z
                simp only [le_Prop_eq]
                intro hz
                exact this hz
              exact Ioc_subset_Icc_self
          _ = abs (∫ (t : ℝ) in Icc y x, |f t - f x|) := by
            rw [abs_eq_self.mpr]
            refine setIntegral_nonneg ?_ ?_ <;> simp
  all_goals apply hg1

/-- The interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → ℝ` is integrable on
`uIoc a b`, and `c ∈ uIoc a b`, then for almost every `x ∈ uIcc a b`, the derivative of
`∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`. -/
theorem IntervalIntegrable.ae_eq_deriv_integral {f : ℝ → ℝ} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    ∀ᵐ x, x ∈ uIcc a b → HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  wlog hab : a ≤ b
  · have S : uIcc a b = uIcc b a := by exact uIcc_comm a b
    simp_rw [S]
    exact @this f b a c hf.symm (S ▸ hc) (by linarith)
  simp_rw [uIcc, show min a b = a by simp [hab], show max a b = b by simp [hab] ] at hc ⊢
  have h1 : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h2 : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  let g (x : ℝ) := if x ∈ Ioc a b then f x else 0
  have hg1 : Integrable g volume := by
    apply MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero (s := Ioc a b)
    · rw [MeasureTheory.integrableOn_congr_fun (g := f)]
      · exact hf.left
      · simp +contextual [g, EqOn]
      · simp
    · simp +contextual [g]
  have hg2 := Integrable.ae_eq_deriv_integral hg1 c
  have hg3 : ∀ x ∈ Ioc a b, f x = g x := by intro x hx; simp only [g, hx, ↓reduceIte]
  have hg4 : ∀ (y z : ℝ), a ≤ y → z ≤ b → ∀ x ∈ Ioc y z, f x = g x := by
    intro y z hy hz x hx
    apply hg3
    suffices Ioc y z ⊆ Ioc a b by exact this hx
    gcongr
  filter_upwards [hg2, h1, h2] with x hx1 hx2 hx3 hx4
  have hx5 : x ∈ Ioo a b := by rw [← Icc_diff_both, mem_diff]; simp [hx2, hx3, hx4]
  have hx6 : x ∈ Ioc a b := by exact mem_Ioc_of_Ioo hx5
  rw [mem_Icc] at hc
  rw [mem_Icc] at hx4
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
