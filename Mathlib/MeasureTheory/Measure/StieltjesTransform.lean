/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Stieltjes Transform of a Borel Measure
-/

@[expose] public section

variable {𝕜 A : Type*}

open MeasureTheory Measure Metric Filter spectrum

open scoped NNReal Topology Ring ComplexConjugate

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] [MeasurableSpace A] [BorelSpace A]

@[fun_prop]
theorem measurable_resolvent {a : A} : Measurable (resolvent (R := 𝕜) a) := by
  classical
  have h1 : ContinuousOn (resolvent (R := 𝕜) a) (resolventSet 𝕜 a) :=
    HasDerivAt.continuousOn (fun _ hx ↦ hasDerivAt_resolvent hx)
  have h2 : ContinuousOn (resolvent (R := 𝕜) a) (resolventSet 𝕜 a)ᶜ := by
    rw [continuousOn_iff_continuous_restrict]
    convert continuous_const (y := (0 : A)) with x
    simp
  have h3 : MeasurableSet (resolventSet 𝕜 a) := (isOpen_resolventSet a).measurableSet
  simpa using h1.measurable_piecewise h2 h3

-- maybe we need to assume `NormedDivisonRing` (is this even a generalization then?)
theorem norm_resolvent_le_inv_infDist_support [CompleteSpace 𝕜] [NormOneClass A]
    {μ : Measure 𝕜} [IsFiniteMeasure μ] {a : A} (hz : a ∉ algebraMap 𝕜 A '' μ.support) {x : 𝕜} (hx : x ∈ μ.support) :
    ‖resolvent a x‖ ≤ (infDist a (algebraMap 𝕜 A '' μ.support))⁻¹ := by
  have : 0 < (infDist a (algebraMap 𝕜 A '' μ.support)) := by
    refine (IsClosed.notMem_iff_infDist_pos ?_ ((Set.nonempty_of_mem hx).image _)).mp hz
    refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
    exact (algebraMap_isometry 𝕜 A).isClosedEmbedding
  have : infDist a (algebraMap 𝕜 A '' μ.support) ≤ ‖(algebraMap 𝕜 A) x - a‖ := by
    grw [infDist_le_dist_of_mem (y := (algebraMap 𝕜 A) x), ← dist_eq_norm, dist_comm]
    sorry
  simp [resolvent]
  grw [resolvent, Ring.inverse_eq_inv ((algebraMap 𝕜 A) x - a)]
  -- grw [resolvent, Complex.coe_algebraMap, Ring.inverse_eq_inv', norm_inv,
  -- --   inv_le_inv₀ (by linarith) (by positivity), this]

-- theorem norm_resolvent_le_inv_infDist_support {μ : Measure ℝ} [IsFiniteMeasure μ] {z : ℂ}
--     (hz : z ∉ (↑) '' μ.support) {x : ℝ} (hx : x ∈ μ.support) :
--     ‖resolvent z x‖ ≤ (infDist z ((↑) '' μ.support))⁻¹ := by
--   have : 0 < infDist z (Complex.ofReal '' μ.support) := by
--     refine (IsClosed.notMem_iff_infDist_pos ?_ ((Set.nonempty_of_mem hx).image _)).mp hz
--     refine (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp isClosed_support
--     exact Complex.isometry_ofReal.isClosedEmbedding
--   have : infDist z (Complex.ofReal '' μ.support) ≤ ‖x - z‖ := by
--     grw [infDist_le_dist_of_mem (y := ↑x) (by simp [hx]), ← dist_eq_norm, dist_comm]
--   grw [resolvent, Complex.coe_algebraMap, Ring.inverse_eq_inv', norm_inv,
--     inv_le_inv₀ (by linarith) (by positivity), this]

-- generalize this!
theorem integrable_resolvent (μ : Measure ℝ) [IsFiniteMeasure μ] (z : ℂ)
    (hz : z ∉ (↑) '' μ.support) : Integrable (resolvent z) μ := by
  refine ⟨by fun_prop, ?_⟩
  apply HasFiniteIntegral.of_bounded
  filter_upwards [support_mem_ae] with x hx using norm_resolvent_le_inv_infDist_support hz hx

noncomputable def stieltjesTransform (μ : Measure ℝ) (z : ℂ) :=
  ∫ x, resolvent z x ∂μ

lemma stieltjesTransform_resolvent_def (μ : Measure ℝ) :
    stieltjesTransform μ = fun z ↦ (∫ x, resolvent z x ∂μ) := rfl

lemma stieltjesTransform_resolvent_apply (μ : Measure ℝ) (z : ℂ) :
    stieltjesTransform μ z = ∫ x, resolvent z x ∂μ := rfl

lemma stieltjesTransform_apply (μ : Measure ℝ) (z : ℂ) :
    stieltjesTransform μ z = ∫ x, (x - z)⁻¹ ∂μ := by
  simp [stieltjesTransform_resolvent_def, resolvent]

lemma stieltjesTransform_def (μ : Measure ℝ):
    stieltjesTransform μ = fun z : ℂ ↦ ∫ x, (x - z)⁻¹ ∂μ := by
  ext z
  exact stieltjesTransform_apply μ z

@[simp]
lemma stieltjesTransform_zero_measure : stieltjesTransform 0 = 0 := by
  ext
  simp [stieltjesTransform_def]

@[simp]
lemma stieltjesTransform_dirac (x : ℝ) (z : ℂ) : stieltjesTransform (.dirac x) z = (x - z)⁻¹ := by
  simp [stieltjesTransform_def]

set_option backward.isDefEq.respectTransparency false in
theorem conj_stieltjesTransform (μ : Measure ℝ) (z : ℂ) :
    conj (stieltjesTransform μ z) = stieltjesTransform μ (conj z) := by
  simp [stieltjesTransform_def, ← integral_conj]

-- theorem stieltjesTransform_bound (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ} (hz : z.im ≠ 0) :
--     ‖stieltjesTransform μ z‖ ≤ μ.real .univ * |z.im|⁻¹ := by
--   grw [stieltjesTransform, norm_integral_le_integral_norm,
--     integral_mono (g := fun _ ↦ |z.im|⁻¹) (by fun_prop (disch := exact hz)) (by fun_prop)
--       (fun _ ↦ complex_resolvent_bound hz _)]
--   simp

#check norm_resolvent_le_inv_infDist_support
#check IsClosed.notMem_iff_infDist_pos

theorem hasDerivAt_stieltjesTransform (μ : Measure ℝ) [IsFiniteMeasure μ] (z : ℂ)
    (hz : z ∉ (↑) '' μ.support) :
    HasDerivAt (stieltjesTransform μ) (∫ x, resolvent z x ^ 2 ∂μ) z := by
  rw [stieltjesTransform_resolvent_def]
  have h : 0 < infDist z ((↑) '' μ.support) := by sorry
  let s : Set ℂ := ball z ((infDist z ((↑) '' μ.support)) / 2)
  have hs_z : s ∈ 𝓝 z := ball_mem_nhds _ (by positivity)
  have resolvent_meas : ∀ᶠ w in nhds z, AEStronglyMeasurable (resolvent w) μ := by sorry
  let resolvent' : ℂ → ℝ → ℂ := (fun z x ↦ (resolvent z x) ^ 2)
  have resolvent'_meas :  AEStronglyMeasurable (resolvent' z) μ := by sorry
  have resolvent'_bound : ∀ᵐ x ∂μ, ∀ w ∈ s,
      ‖resolvent' w x‖ ≤ ((infDist z ((↑) '' μ.support)) / 2)⁻¹ ^ 2 := by
    filter_upwards [support_mem_ae] with x hx w hw
    unfold resolvent'
    have h : infDist z ((↑) '' μ.support) / 2 ≤ ‖↑x - w‖ := calc
      infDist z ((↑) '' μ.support) / 2
      _ ≤ infDist z ((↑) '' μ.support) - infDist z ((↑) '' μ.support) / 2 := by grind
      _ ≤ ‖↑x - z‖ - ‖z - w‖ := by
        gcongr
        · grw [infDist_le_dist_of_mem (y := ↑x) (by simp [hx]), dist_comm, dist_eq_norm]
        · apply le_of_lt; simpa [s, ← dist_eq_norm, dist_comm w z] using hw
      _ ≤ ‖↑x - w‖ := by grw [norm_sub_le_norm_add]; grind
    grw [norm_pow, sq_le_sq₀ (by simp) (by positivity), resolvent, Complex.coe_algebraMap,
      Ring.inverse_eq_inv', norm_inv, inv_le_inv₀ (by linarith) (by positivity)]
    exact h
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs_z resolvent_meas ?_ resolvent'_meas resolvent'_bound ?_ ?_ |>.2


    -- exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_z resolvent_meas
  --   (complex_resolvent_integrable μ hz) resolvent'_meas resolvent'_bound
  --   (integrable_const _) h_diff |>.2


  -- unfold stieltjesTransform
  -- conv => enter [2, 2, x]; change (fun z x ↦ resolvent z x ^ 2) z x
  -- let s := ball z (|z.im| / 2)
  -- have hs_z : s ∈ nhds z := IsOpen.mem_nhds isOpen_ball (by simp [s, hz])
  -- have hs_im {w : ℂ} (hw : w ∈ s) : w.im ≠ 0 := by
  --   intro h
  --   have hw' : ‖w - z‖ < |z.im| / 2 := by simpa [s, dist_eq] using hw
  --   grw [← abs_im_le_norm, sub_im, h, zero_sub, abs_neg] at hw'
  --   grind
  -- have resolvent_meas : ∀ᶠ w in nhds z, AEStronglyMeasurable (resolvent w) μ := by
  --   filter_upwards [hs_z] with _ hw
  --   exact (continuous_complex_resolvent (hs_im hw)).aestronglyMeasurable
  -- let resolvent' : ℂ → ℝ → ℂ := (fun z x ↦ (resolvent z x) ^ 2)
  -- have resolvent'_meas :  AEStronglyMeasurable (resolvent' z) μ := by
  --   unfold resolvent'
  --   exact Continuous.aestronglyMeasurable (by fun_prop (disch := exact hz))
  -- have resolvent'_bound : ∀ᵐ x ∂μ, ∀ w ∈ s, ‖resolvent' w x‖ ≤ (|z.im| / 2)⁻¹ ^ 2 := by
  --   unfold resolvent'
  --   filter_upwards with x
  --   intro w hw
  --   grw [norm_pow, sq_le_sq₀ (by simp) (by positivity),
  --     complex_resolvent_bound (hs_im hw) x, inv_le_inv₀ (by simp [hs_im hw]) (by simp [hz])]
  --   have hw' : ‖z - w‖ < |z.im| / 2 := by simpa [s, dist_eq, norm_sub_rev] using hw
  --   calc
  --     |z.im| / 2 = |z.im| - |z.im| / 2 := by ring
  --              _ ≤ |z.im| - |(z - w).im| := by gcongr; grw [abs_im_le_norm, hw']
  --              _ ≤ |z.im - (z - w).im| := by exact abs_sub_abs_le_abs_sub _ _
  --              _ = |w.im| := by simp
  -- have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ s,
  --     HasDerivAt (resolvent (R := ℝ) · x) (resolvent' z x) z := by
  --   unfold resolvent'
  --   filter_upwards with x
  --   intro w hw
  --   exact hasDerivAt_complex_resolvent (hs_im hw) _
  -- exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_z resolvent_meas
  --   (complex_resolvent_integrable μ hz) resolvent'_meas resolvent'_bound
  --   (integrable_const _) h_diff |>.2

-- theorem analyticOn_stieltjesTransform (μ : Measure ℝ) [IsFiniteMeasure μ] :
--     AnalyticOn ℂ (stieltjesTransform μ) {z | z.im ≠ 0} := by
--   rw [analyticOn_iff_differentiableOn (isClosed_eq continuous_im continuous_const).not]
--   intro z hz
--   apply DifferentiableAt.differentiableWithinAt
--   apply HasDerivAt.differentiableAt
--   exact hasDerivAt_stieltjesTransform μ z hz

section InversionFormula

noncomputable def stieltjes_measure (μ : Measure ℝ) (ε : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (stieltjesTransform μ (x + I * ε)).im)

end InversionFormula
