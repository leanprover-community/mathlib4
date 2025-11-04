/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Fundamental theorem of calculus for `C^1` functions

We give versions of the second fundamental theorem of calculus under the strong assumption
that the function is `C^1` on the interval. This is restrictive, but satisfied in many situations.
-/

noncomputable section

open MeasureTheory Set Filter Function Asymptotics

open scoped Topology ENNReal Interval NNReal

variable {ι 𝕜 E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E} {a b : ℝ}

namespace intervalIntegral

variable [CompleteSpace E]

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, deriv f y` equals `f b - f a`. -/
theorem integral_deriv_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b)) (hab : a ≤ b) :
    ∫ x in a..b, deriv f x = f b - f a := by
  rcases hab.eq_or_lt with rfl | h'ab
  · simp
  apply integral_eq_sub_of_hasDerivAt_of_le hab h.continuousOn
  · intro x hx
    apply DifferentiableAt.hasDerivAt
    apply ((h x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt le_rfl).differentiableAt
    exact Icc_mem_nhds hx.1 hx.2
  · have := (h.derivWithin (m := 0) (uniqueDiffOn_Icc h'ab) (by simp)).continuousOn
    apply (this.intervalIntegrable_of_Icc (μ := volume) hab).congr_ae
    simp only [hab, uIoc_of_le]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, derivWithin f (Icc a b) y` equals `f b - f a`. -/
theorem integral_derivWithin_Icc_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b)) (hab : a ≤ b) :
    ∫ x in a..b, derivWithin f (Icc a b) x = f b - f a := by
  rw [← integral_deriv_of_contDiffOn_Icc h hab]
  rw [integral_of_le hab, integral_of_le hab]
  apply MeasureTheory.integral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, deriv f y` equals `f b - f a`. -/
theorem integral_deriv_of_contDiffOn_uIcc (h : ContDiffOn ℝ 1 f (uIcc a b)) :
    ∫ x in a..b, deriv f x = f b - f a := by
  rcases le_or_gt a b with hab | hab
  · simp only [uIcc_of_le hab] at h
    exact integral_deriv_of_contDiffOn_Icc h hab
  · simp only [uIcc_of_ge hab.le] at h
    rw [integral_symm, integral_deriv_of_contDiffOn_Icc h hab.le]
    abel

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is `C^1` on `[a, b]`,
then `∫ y in a..b, derivWithin f (uIcc a b) y` equals `f b - f a`. -/
theorem integral_derivWithin_uIcc_of_contDiffOn_uIcc (h : ContDiffOn ℝ 1 f (uIcc a b)) :
    ∫ x in a..b, derivWithin f (uIcc a b) x = f b - f a := by
  rcases le_or_gt a b with hab | hab
  · simp only [uIcc_of_le hab] at h ⊢
    exact integral_derivWithin_Icc_of_contDiffOn_Icc h hab
  · simp only [uIcc_of_ge hab.le] at h ⊢
    rw [integral_symm, integral_derivWithin_Icc_of_contDiffOn_Icc h hab.le]
    abel

end intervalIntegral

open intervalIntegral

theorem enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b))
    (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ x in Icc a b, ‖deriv f x‖ₑ := by
  /- We want to write `f b - f a = ∫ x in Icc a b, deriv f x` and use the inequality between
  norm of integral and integral of norm. There is a small difficulty that this formula is not
  true when `E` is not complete, so we need to go first to the completion, and argue there. -/
  let g := UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ) (E := E)
  have : ‖(g ∘ f) b - (g ∘ f) a‖ₑ = ‖f b - f a‖ₑ := by
    rw [← edist_eq_enorm_sub, Function.comp_def, g.isometry.edist_eq, edist_eq_enorm_sub]
  rw [← this, ← integral_deriv_of_contDiffOn_Icc (g.contDiff.comp_contDiffOn h) hab,
    integral_of_le hab, restrict_Ioc_eq_restrict_Icc]
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [fderiv_comp_deriv]; rotate_left
  · exact (g.contDiff.differentiable le_rfl).differentiableAt
  · exact ((h x ⟨hx.1.le, hx.2.le⟩).contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt le_rfl
  have : fderiv ℝ g (f x) = g.toContinuousLinearMap := g.toContinuousLinearMap.fderiv
  simp [this]

theorem enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b))
    (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ x in Icc a b, ‖derivWithin f (Icc a b) x‖ₑ := by
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc h hab).trans_eq
  apply lintegral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
