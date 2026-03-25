/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/

module

public import Mathlib

/-!
# Stieltjes Transform of a Borel Measure
-/

@[expose] public section

variable {𝕜 A : Type*}

open MeasureTheory Measure spectrum

open scoped NNReal Topology Ring

-- theorem integrable_resolvent [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra ℝ A]
--     [CompleteSpace A] {μ : Measure ℝ} [IsFiniteMeasure μ] {a : A}
--     (ha : a ∉ algebraMap ℝ A '' μ.support) :
--     Integrable (resolvent a) μ := by
--   refine ⟨by sorry, ?_⟩
--   apply HasFiniteIntegral.of_bounded

-- theorem complex_resolvent_def (z : ℂ) :
--     resolvent (R := ℝ) z = fun x : ℝ ↦ (x - z)⁻¹ := by
--   ext x
--   simp [resolvent, Ring.inverse_eq_inv']

-- @[fun_prop]
-- theorem continuous_complex_resolvent {z : ℂ} (hz : z.im ≠ 0) :
--     Continuous (resolvent (R := ℝ) z) := by
--   rw [complex_resolvent_def]
--   have h (x : ℝ) : x - z ≠ 0 := by
--     intro h
--     absurd hz
--     simpa using congrArg im h
--   fun_prop (disch := exact h)

-- theorem hasDerivAt_complex_resolvent {z : ℂ} (x : ℝ) (hx : x ∈ resolventSet ℝ z) :
--     HasDerivAt (resolvent (R := ℝ) · x) (resolvent z x ^ 2) z := by
--   apply hasDerivAt_resolvent' hx

-- theorem complex_resolvent_bound {z : ℂ} (x : ℝ) (hx : x ∈ resolventSet ℝ z) :
--     ‖resolvent z x‖ ≤ |z.im|⁻¹ := by
--   have h : x - z ≠ 0 := by
--     intro h
--     absurd hz
--     simpa using congrArg im h
--   rw [complex_resolvent_def, norm_inv, inv_le_inv₀ (by positivity [h]) (by positivity)]
--   convert abs_im_le_norm (x - z) using 1
--   simp

-- @[fun_prop]
-- theorem complex_resolvent_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ} (hz : z.im ≠ 0) :
--     Integrable (resolvent z) μ := by
--   refine ⟨by fun_prop (disch := exact hz), ?_⟩
--   apply HasFiniteIntegral.of_bounded
--   · filter_upwards with x
--     apply complex_resolvent_bound hz

noncomputable def stieltjesTransform (μ : Measure ℝ) (z : ℂ) :=
  ∫ x, resolvent z x ∂μ

@[simp]
lemma stieltjesTransform_zero_measure : stieltjesTransform 0 = 0 := by
  ext
  simp [stieltjesTransform]

lemma stieltjesTransform_def (μ : Measure ℝ) (z : ℂ) :
    stieltjesTransform μ z = ∫ x, (x - z)⁻¹ ∂μ := by
  simp [stieltjesTransform, resolvent]

@[simp]
lemma stieltjesTransform_dirac (x : ℝ) (z : ℂ) : stieltjesTransform (.dirac x) z = (x - z)⁻¹ := by
  simp [stieltjesTransform_def]

theorem stieltjesTransform_zero_of_not_integrable {μ : Measure ℝ} (z : ℂ)
    (hμ : ¬ Integrable (fun x : ℝ ↦ (x - z)⁻¹) μ) : stieltjesTransform μ z = 0 := by
  simp [stieltjesTransform_def, integral_undef hμ]

theorem conj_stieltjesTransform (μ : Measure ℝ) (z : ℂ) :
    conj (stieltjesTransform μ z) = stieltjesTransform μ (conj z) := by
  simp [stieltjesTransform_def, ← integral_conj]

theorem stieltjesTransform_bound (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ} (hz : z.im ≠ 0) :
    ‖stieltjesTransform μ z‖ ≤ μ.real .univ * |z.im|⁻¹ := by
  grw [stieltjesTransform, norm_integral_le_integral_norm,
    integral_mono (g := fun _ ↦ |z.im|⁻¹) (by fun_prop (disch := exact hz)) (by fun_prop)
      (fun _ ↦ complex_resolvent_bound hz _)]
  simp

theorem hasDerivAt_stieltjesTransform (μ : Measure ℝ) [IsFiniteMeasure μ] (z : ℂ) (hz : z.im ≠ 0) :
    HasDerivAt (stieltjesTransform μ) (∫ x, resolvent z x ^ 2 ∂μ) z := by
  unfold stieltjesTransform
  conv => enter [2, 2, x]; change (fun z x ↦ resolvent z x ^ 2) z x
  let s := ball z (|z.im| / 2)
  have hs_z : s ∈ nhds z := IsOpen.mem_nhds isOpen_ball (by simp [s, hz])
  have hs_im {w : ℂ} (hw : w ∈ s) : w.im ≠ 0 := by
    intro h
    have hw' : ‖w - z‖ < |z.im| / 2 := by simpa [s, dist_eq] using hw
    grw [← abs_im_le_norm, sub_im, h, zero_sub, abs_neg] at hw'
    grind
  have resolvent_meas : ∀ᶠ w in nhds z, AEStronglyMeasurable (resolvent w) μ := by
    filter_upwards [hs_z] with _ hw
    exact (continuous_complex_resolvent (hs_im hw)).aestronglyMeasurable
  let resolvent' : ℂ → ℝ → ℂ := (fun z x ↦ (resolvent z x) ^ 2)
  have resolvent'_meas :  AEStronglyMeasurable (resolvent' z) μ := by
    unfold resolvent'
    exact Continuous.aestronglyMeasurable (by fun_prop (disch := exact hz))
  have resolvent'_bound : ∀ᵐ x ∂μ, ∀ w ∈ s, ‖resolvent' w x‖ ≤ (|z.im| / 2)⁻¹ ^ 2 := by
    unfold resolvent'
    filter_upwards with x
    intro w hw
    grw [norm_pow, sq_le_sq₀ (by simp) (by positivity),
      complex_resolvent_bound (hs_im hw) x, inv_le_inv₀ (by simp [hs_im hw]) (by simp [hz])]
    have hw' : ‖z - w‖ < |z.im| / 2 := by simpa [s, dist_eq, norm_sub_rev] using hw
    calc
      |z.im| / 2 = |z.im| - |z.im| / 2 := by ring
               _ ≤ |z.im| - |(z - w).im| := by gcongr; grw [abs_im_le_norm, hw']
               _ ≤ |z.im - (z - w).im| := by exact abs_sub_abs_le_abs_sub _ _
               _ = |w.im| := by simp
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ s,
      HasDerivAt (resolvent (R := ℝ) · x) (resolvent' z x) z := by
    unfold resolvent'
    filter_upwards with x
    intro w hw
    exact hasDerivAt_complex_resolvent (hs_im hw) _
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_z resolvent_meas
    (complex_resolvent_integrable μ hz) resolvent'_meas resolvent'_bound
    (integrable_const _) h_diff |>.2

theorem analyticOn_stieltjesTransform (μ : Measure ℝ) [IsFiniteMeasure μ] :
    AnalyticOn ℂ (stieltjesTransform μ) {z | z.im ≠ 0} := by
  rw [analyticOn_iff_differentiableOn (isClosed_eq continuous_im continuous_const).not]
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply HasDerivAt.differentiableAt
  exact hasDerivAt_stieltjesTransform μ z hz

section InversionFormula

noncomputable def stieltjes_measure (μ : Measure ℝ) (ε : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (stieltjesTransform μ (x + I * ε)).im)

end InversionFormula
