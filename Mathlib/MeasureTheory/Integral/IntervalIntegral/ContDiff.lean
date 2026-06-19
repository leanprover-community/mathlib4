/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Fundamental theorem of calculus for `C^1` functions

We give versions of the second fundamental theorem of calculus under the strong assumption
that the function is `C^1` on the interval. This is restrictive, but satisfied in many situations.
-/

public section

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
    apply ((h x ⟨hx.1.le, hx.2.le⟩).differentiableWithinAt one_ne_zero).differentiableAt
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

/-- Auxiliary form of `enorm_sub_le_lintegral_deriv_of_contDiffOn_Ioo` for a complete codomain,
where the second fundamental theorem of calculus is available. -/
private theorem enorm_sub_le_lintegral_deriv_aux [CompleteSpace E]
    (hcont : ContinuousOn f (Icc a b)) (hdiff : ContDiffOn ℝ 1 f (Ioo a b)) (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ t in Ioc a b, ‖deriv f t‖ₑ := by
  have hderiv_cont : ContinuousOn (deriv f) (Ioo a b) :=
    (hdiff.continuousOn_derivWithin isOpen_Ioo.uniqueDiffOn le_rfl).congr
      fun t ht => (derivWithin_of_isOpen isOpen_Ioo ht).symm
  by_cases hint : IntegrableOn (deriv f) (Ioc a b) volume
  · -- The fundamental theorem of calculus writes `f b - f a` as an integral.
    have hftc : f b - f a = ∫ t in a..b, deriv f t :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
        (fun t ht => ((hdiff.differentiableOn one_ne_zero).differentiableAt
          (isOpen_Ioo.mem_nhds ht)).hasDerivAt)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hint)).symm
    rw [hftc, intervalIntegral.integral_of_le hab]
    exact enorm_integral_le_lintegral_enorm _
  · -- Otherwise `deriv f` has infinite enorm integral, so the right-hand side is `⊤`.
    rw [show ∫⁻ t in Ioc a b, ‖deriv f t‖ₑ = ⊤ by
      by_contra h
      refine hint ⟨?_, hasFiniteIntegral_iff_enorm.mpr (lt_top_iff_ne_top.2 h)⟩
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
      exact hderiv_cont.aestronglyMeasurable measurableSet_Ioo]
    exact le_top

open UniformSpace in
/-- **The second fundamental theorem of calculus, as an extended-norm bound.** If `f : ℝ → E` is
continuous on `[a, b]` and continuously differentiable on the open interval `(a, b)`, then the
extended norm of `f b - f a` is bounded by the lower Lebesgue integral of the extended norm of its
derivative. No integrability hypothesis is required: when the derivative is not integrable the
right-hand side is `⊤`. Unlike `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc`, differentiability
at the endpoints is not assumed. -/
theorem enorm_sub_le_lintegral_deriv_of_contDiffOn_Ioo
    (hcont : ContinuousOn f (Icc a b)) (hdiff : ContDiffOn ℝ 1 f (Ioo a b)) (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ t in Ioc a b, ‖deriv f t‖ₑ := by
  -- Compose with the isometric inclusion `ι : E →ₗᵢ Completion E`, apply the complete-space lemma,
  -- then transfer back: `ι` preserves norms and derivatives.
  set ι : E →ₗᵢ[ℝ] Completion E := Completion.toComplₗᵢ
  have key := enorm_sub_le_lintegral_deriv_aux (ι.continuous.comp_continuousOn hcont)
    (hdiff.continuousLinearMap_comp ι.toContinuousLinearMap) hab
  simp only [Function.comp_def, ← map_sub, ι.enorm_map] at key
  refine key.trans (le_of_eq (lintegral_congr_ae ?_))
  have hae : ∀ᵐ t ∂volume.restrict (Ioc a b), t ∈ Ioo a b := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume))]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hae] with t ht
  have hfx : DifferentiableAt ℝ f t :=
    (hdiff.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds ht)
  have hg : HasDerivAt (fun y => ι (f y)) (ι (deriv f t)) t :=
    ι.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hfx.hasDerivAt
  rw [hg.deriv, ι.enorm_map]

theorem enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b))
    (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ x in Icc a b, ‖deriv f x‖ₑ := by
  rw [← restrict_Ioc_eq_restrict_Icc]
  exact enorm_sub_le_lintegral_deriv_of_contDiffOn_Ioo h.continuousOn
    (h.mono Ioo_subset_Icc_self) hab

theorem enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc (h : ContDiffOn ℝ 1 f (Icc a b))
    (hab : a ≤ b) :
    ‖f b - f a‖ₑ ≤ ∫⁻ x in Icc a b, ‖derivWithin f (Icc a b) x‖ₑ := by
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc h hab).trans_eq
  apply lintegral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
