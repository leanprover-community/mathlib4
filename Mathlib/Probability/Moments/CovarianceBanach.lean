/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Covariance in Banach spaces

We define the covariance of a measure in a Banach space, as a continous bilinear form.

## Main definitions

Let `μ` be a finite measure on a Banach space `E` with the Borel σ-algebra, such that
`∫ x, ‖x‖^2 ∂μ < ∞`.

* `covarianceBilin` : covariance of the measure `μ` as a continuous bilinear form
  `(E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ`

## Main statements

* `covarianceBilin_apply` : the covariance of `μ` on `L₁, L₂ : E →L[ℝ] ℝ` is equal to
  `∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ`.

-/


open MeasureTheory ProbabilityTheory Complex NormedSpace
open scoped ENNReal NNReal Real Topology

section Aux

variable {α F : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup F] {f : α → F}

lemma rpow_toReal_eLpNorm {p : ℝ} (hf : MemLp f (ENNReal.ofReal p) μ) (hp : 0 < p) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal ^ p = ∫ x, ‖f x‖ ^ p ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by simp [hp]) (by simp)]
  simp only [one_div]
  have : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by positivity)
  simp_rw [this]
  rw [ENNReal.toReal_rpow, ← ENNReal.rpow_mul, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
  simp_rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  rw [← ofReal_integral_eq_lintegral_ofReal, ENNReal.toReal_ofReal (by positivity)]
  · convert MemLp.integrable_norm_rpow hf (by simp [hp]) (by simp)
    exact this.symm
  · exact ae_of_all _ fun x ↦ by positivity

lemma pow_toReal_eLpNorm {n : ℕ} (hf : MemLp f n μ) (hn : n ≠ 0) :
    (eLpNorm f n μ).toReal ^ n = ∫ x, ‖f x‖ ^ n ∂μ := by
  have h_Lp : MemLp f (ENNReal.ofReal n) μ := by convert hf; simp
  have h := rpow_toReal_eLpNorm h_Lp (by positivity)
  simpa using h

end Aux

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {mE : MeasurableSpace E} {μ : Measure E}

section ToLp

variable [OpensMeasurableSpace E] {p : ℝ≥0∞}

lemma _root_.MeasureTheory.MemLp.continuousLinearMap (h_Lp : MemLp id p μ) (L : E →L[ℝ] ℝ) :
    MemLp L p μ := by
  refine MemLp.mono (g := fun x ↦ ‖L‖ • x) (h_Lp.const_smul _) ?_ ?_
  · exact Measurable.aestronglyMeasurable <| by fun_prop
  refine ae_of_all _ fun x ↦ ?_
  simp only [norm_smul, norm_norm]
  exact L.le_opNorm x

lemma _root_.MeasureTheory.MemLp.integrable_continuousLinearMap
    (h_Lp : MemLp id 1 μ) (L : E →L[ℝ] ℝ) :
    Integrable L μ := by
  rw [← memLp_one_iff_integrable]
  exact h_Lp.continuousLinearMap L

/-- `MemLp.toLp` as a `LinearMap` from the continuous linear maps. -/
def ContinuousLinearMap.toLpₗ (μ : Measure E) (p : ℝ≥0∞) (h_Lp : MemLp id p μ) :
    (E →L[ℝ] ℝ) →ₗ[ℝ] Lp ℝ p μ where
  toFun := fun L ↦ MemLp.toLp L (h_Lp.continuousLinearMap L)
  map_add' u v := by push_cast; rw [MemLp.toLp_add]
  map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl

@[simp]
lemma ContinuousLinearMap.toLpₗ_apply (h_Lp : MemLp id p μ) (L : E →L[ℝ] ℝ) :
    L.toLpₗ μ p h_Lp = MemLp.toLp L (h_Lp.continuousLinearMap L) := rfl

lemma norm_toLpₗ_le (h_Lp : MemLp id p μ) (L : E →L[ℝ] ℝ) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    ‖L.toLpₗ μ p h_Lp‖ ≤ ‖L‖ * (eLpNorm id p μ).toReal := by
  have h0 : 0 < p.toReal := by simp [ENNReal.toReal_pos_iff, pos_iff_ne_zero, hp, hp_top.lt_top]
  suffices ‖L.toLpₗ μ p h_Lp‖
      ≤ (‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ).toReal ^ p.toReal⁻¹ by
    refine this.trans_eq ?_
    simp only [ENNReal.toReal_mul]
    rw [← ENNReal.toReal_rpow, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by positivity), mul_inv_cancel₀ h0.ne', Real.rpow_one, toReal_enorm]
    rw [eLpNorm_eq_lintegral_rpow_enorm (by simp [hp]) hp_top, ENNReal.toReal_rpow]
    simp
  rw [ContinuousLinearMap.toLpₗ_apply, Lp.norm_toLp,
    eLpNorm_eq_lintegral_rpow_enorm (by simp [hp]) hp_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, one_div]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  suffices ∫⁻ x, ‖L x‖ₑ ^ p.toReal ∂μ ≤ ‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    gcongr
    rwa [ENNReal.ofReal_toReal]
    refine ENNReal.mul_ne_top (by simp) ?_
    have h := h_Lp.eLpNorm_ne_top
    rw [eLpNorm_eq_lintegral_rpow_enorm (by simp [hp]) hp_top] at h
    simpa [h0] using h
  calc ∫⁻ x, ‖L x‖ₑ ^ p.toReal ∂μ
  _ ≤ ∫⁻ x, ‖L‖ₑ ^ p.toReal * ‖x‖ₑ ^ p.toReal ∂μ := by
    refine lintegral_mono fun x ↦ ?_
    rw [← ENNReal.mul_rpow_of_nonneg]
    swap; · positivity
    gcongr
    simp_rw [← ofReal_norm]
    rw [← ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact L.le_opNorm x
  _ = ‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ := by rw [lintegral_const_mul]; fun_prop

/-- `MemLp.toLp` as a `ContinuousLinearMap` from the continuous linear forms. -/
def ContinuousLinearMap.toLp (μ : Measure E) (p : ℝ≥0∞) [Fact (1 ≤ p)] (h_Lp : MemLp id p μ)
    (hp : p ≠ ∞) :
    (E →L[ℝ] ℝ) →L[ℝ] Lp ℝ p μ where
  toLinearMap := ContinuousLinearMap.toLpₗ μ p h_Lp
  cont := by
    refine LinearMap.continuous_of_locally_bounded _ fun s hs ↦ ?_
    rw [image_isVonNBounded_iff]
    simp_rw [isVonNBounded_iff'] at hs
    obtain ⟨r, hxr⟩ := hs
    refine ⟨r * (eLpNorm id p μ).toReal, fun L hLs ↦ ?_⟩
    specialize hxr L hLs
    have hp_ne : p ≠ 0 := by
      have : 1 ≤ p := Fact.out
      positivity
    refine (norm_toLpₗ_le h_Lp L hp_ne hp).trans ?_
    gcongr

@[simp]
lemma ContinuousLinearMap.toLp_apply (L : E →L[ℝ] ℝ)
    [Fact (1 ≤ p)] (h_Lp : MemLp id p μ) (hp : p ≠ ∞) :
    L.toLp μ p h_Lp hp = MemLp.toLp L (h_Lp.continuousLinearMap L) := rfl

end ToLp

section Covariance

section Centered

variable [OpensMeasurableSpace E]

/-- Continuous bilinear form with value `∫ x, L₁ x * L₂ x ∂μ` on `(L₁, L₂)`.
This is the covariance only if `μ` is centered. -/
noncomputable
def centeredCovariance (μ : Measure E) (h : MemLp id 2 μ) :
    (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (ContinuousLinearMap.toLp μ 2 h (by simp)) (ContinuousLinearMap.toLp μ 2 h (by simp))

lemma centeredCovariance_apply (h : MemLp id 2 μ) (L₁ L₂ : E →L[ℝ] ℝ) :
    centeredCovariance μ h L₁ L₂ = ∫ x, L₁ x * L₂ x ∂μ := by
  simp only [centeredCovariance, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.toLp_apply, L2.inner_def,
    RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (h.continuousLinearMap L₁),
    MemLp.coeFn_toLp (h.continuousLinearMap L₂)] with x hxL₁ hxL₂
  rw [hxL₁, hxL₂, mul_comm]

lemma norm_centeredCovariance_le (h : MemLp id 2 μ) (L₁ L₂ : E →L[ℝ] ℝ) :
    ‖centeredCovariance μ h L₁ L₂‖ ≤ ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := by
  calc ‖centeredCovariance μ h L₁ L₂‖
  _ = ‖∫ x, L₁ x * L₂ x ∂μ‖ := by rw [centeredCovariance_apply]
  _ ≤ ∫ x, ‖L₁ x‖ * ‖L₂ x‖ ∂μ := (norm_integral_le_integral_norm _).trans (by simp)
  _ ≤ ∫ x, ‖L₁‖ * ‖x‖ * ‖L₂‖ * ‖x‖ ∂μ := by
    refine integral_mono_ae ?_ ?_ (ae_of_all _ fun x ↦ ?_)
    · simp_rw [← norm_mul]
      exact (MemLp.integrable_mul (h.continuousLinearMap L₁) (h.continuousLinearMap L₂)).norm
    · simp_rw [mul_assoc]
      refine Integrable.const_mul ?_ _
      simp_rw [← mul_assoc, mul_comm _ (‖L₂‖), mul_assoc, ← pow_two]
      refine Integrable.const_mul ?_ _
      exact h.integrable_norm_pow (by simp)
    · simp only
      rw [mul_assoc]
      gcongr
      · exact ContinuousLinearMap.le_opNorm L₁ x
      · exact ContinuousLinearMap.le_opNorm L₂ x
  _ = ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := by
    rw [← integral_const_mul]
    congr with x
    ring

lemma norm_centeredCovariance_le' (h : MemLp id 2 μ) (L₁ L₂ : E →L[ℝ] ℝ) :
    ‖centeredCovariance μ h L₁ L₂‖ ≤ ‖L₁‖ * ‖L₂‖ * (eLpNorm id 2 μ).toReal ^ 2 := by
  calc ‖centeredCovariance μ h L₁ L₂‖
  _ ≤ ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := norm_centeredCovariance_le _ _ _
  _ = ‖L₁‖ * ‖L₂‖ * (eLpNorm id 2 μ).toReal ^ 2 := by
    congr
    have h := pow_toReal_eLpNorm h (by simp)
    simpa only [ENNReal.ofReal_ofNat, Real.rpow_two, id_eq] using h.symm

end Centered

variable [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- Continuous bilinear form with value `∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ` on `(L₁, L₂)`. -/
noncomputable
def covarianceBilin (μ : Measure E) [IsFiniteMeasure μ] (h : MemLp id 2 μ) :
    (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  centeredCovariance (μ.map (fun x ↦ x - ∫ x, x ∂μ)) <| by
    rw [memLp_map_measure_iff]
    · exact h.sub (memLp_const _)
    · exact Measurable.aestronglyMeasurable <| by fun_prop
    · fun_prop

lemma covarianceBilin_apply [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L₁ L₂ : E →L[ℝ] ℝ) :
    covarianceBilin μ h L₁ L₂ = ∫ x, (L₁ x - ∫ x, L₁ x ∂μ) * (L₂ x - ∫ x, L₂ x ∂μ) ∂μ := by
  rw [covarianceBilin, centeredCovariance_apply, integral_map]
  · simp [← ContinuousLinearMap.integral_comm_of_memLp_id (h.mono_exponent (by simp))]
  · fun_prop
  · exact Measurable.aestronglyMeasurable <| by fun_prop

end Covariance

end ProbabilityTheory
