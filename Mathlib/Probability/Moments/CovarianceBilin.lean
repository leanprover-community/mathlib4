/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Probability.Variance

/-!
# Covariance in Banach spaces

We define the covariance of a finite measure in a separable Banach space `E`,
as a continous bilinear form on `Dual ℝ E`.

## Main definitions

Let `μ` be a finite measure on a normed space `E` with the Borel σ-algebra. We then define

* `Dual.toLp`: the function `MemLp.toLp` as a continuous linear map from
  `Dual 𝕜 E` (for `RCLike 𝕜`) into the space `Lp 𝕜 p μ` for finite `p ≥ 1`.
  This needs a hypothesis `MemLp id p μ`.
* `covarianceBilin` : covariance of a measure `μ` with `∫ x, ‖x‖^2 ∂μ < ∞` on a separable Banach
  space, as a continuous bilinear form `Dual ℝ E →L[ℝ] Dual ℝ E →L[ℝ] ℝ`.
  If the second moment of `μ` is not finite, we set `covarianceBilin μ = 0`.

## Main statements

* `covarianceBilin_apply` : the covariance of `μ` on `L₁, L₂ : Dual ℝ E` is equal to
  `∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ`.
* `covarianceBilin_same_eq_variance`: `covarianceBilin μ L L = Var[L; μ]`.

## Implementation notes

The hypothesis that `μ` has a second moment is written as `MemLp id 2 μ` in the code.

-/


open MeasureTheory ProbabilityTheory Complex NormedSpace
open scoped ENNReal NNReal Real Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] {mE : MeasurableSpace E} {μ : Measure E} {p : ℝ≥0∞}

section ToLp

section LinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

/-- `MemLp.toLp` as a `LinearMap` from the dual. -/
noncomputable
def ContinuousLinearMap.toLpₗ (μ : Measure E) (p : ℝ≥0∞) (h_Lp : MemLp id p μ) :
    Dual 𝕜 E →ₗ[𝕜] Lp 𝕜 p μ where
  toFun := fun L ↦ MemLp.toLp L (h_Lp.continuousLinearMap_comp L)
  map_add' u v := by push_cast; rw [MemLp.toLp_add]
  map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl

@[simp]
lemma ContinuousLinearMap.toLpₗ_apply (h_Lp : MemLp id p μ) (L : Dual 𝕜 E) :
    L.toLpₗ μ p h_Lp = MemLp.toLp L (h_Lp.continuousLinearMap_comp L) := rfl

lemma norm_toLpₗ_le [OpensMeasurableSpace E]
    (h_Lp : MemLp id p μ) (L : Dual 𝕜 E) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
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

end LinearMap

section ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [OpensMeasurableSpace E]

/-- `MemLp.toLp` as a continuous linear map from `Dual 𝕜 E` to `Lp 𝕜 p μ`. -/
noncomputable
def _root_.NormedSpace.Dual.toLp (μ : Measure E) (p : ℝ≥0∞) [Fact (1 ≤ p)] (h_Lp : MemLp id p μ)
    (hp : p ≠ ∞) :
    Dual 𝕜 E →L[𝕜] Lp 𝕜 p μ where
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
lemma Dual.toLp_apply [Fact (1 ≤ p)] (h_Lp : MemLp id p μ) (hp : p ≠ ∞) (L : Dual 𝕜 E) :
    L.toLp μ p h_Lp hp = MemLp.toLp L (h_Lp.continuousLinearMap_comp L) := rfl

end ContinuousLinearMap

end ToLp

section Centered

variable [NormedSpace ℝ E] [OpensMeasurableSpace E]

/-- Continuous bilinear form with value `∫ x, L₁ x * L₂ x ∂μ` on `(L₁, L₂)`.
This is equal to the covariance only if `μ` is centered. -/
noncomputable
def centeredCovarianceBilin (μ : Measure E) (h : MemLp id 2 μ) :
    Dual ℝ E →L[ℝ] Dual ℝ E →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (Dual.toLp μ 2 h (by simp)) (Dual.toLp μ 2 h (by simp))

lemma centeredCovarianceBilin_apply (h : MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    centeredCovarianceBilin μ h L₁ L₂ = ∫ x, L₁ x * L₂ x ∂μ := by
  simp only [centeredCovarianceBilin, ContinuousLinearMap.bilinearComp_apply,
    Dual.toLp_apply, L2.inner_def, RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (h.continuousLinearMap_comp L₁),
    MemLp.coeFn_toLp (h.continuousLinearMap_comp L₂)] with x hxL₁ hxL₂
  simp only [id_eq] at hxL₁ hxL₂
  rw [hxL₁, hxL₂, mul_comm]

lemma norm_centeredCovarianceBilin_le (h : MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    ‖centeredCovarianceBilin μ h L₁ L₂‖ ≤ ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := by
  calc ‖centeredCovarianceBilin μ h L₁ L₂‖
  _ = ‖∫ x, L₁ x * L₂ x ∂μ‖ := by rw [centeredCovarianceBilin_apply]
  _ ≤ ∫ x, ‖L₁ x‖ * ‖L₂ x‖ ∂μ := (norm_integral_le_integral_norm _).trans (by simp)
  _ ≤ ∫ x, ‖L₁‖ * ‖x‖ * ‖L₂‖ * ‖x‖ ∂μ := by
    refine integral_mono_ae ?_ ?_ (ae_of_all _ fun x ↦ ?_)
    · simp_rw [← norm_mul]
      exact (MemLp.integrable_mul (h.continuousLinearMap_comp L₁)
        (h.continuousLinearMap_comp L₂)).norm
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

end Centered

section Covariance

variable [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] [IsFiniteMeasure μ]

open Classical in
/-- Continuous bilinear form with value `∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ` on `(L₁, L₂)`
if `MemLp id 2 μ`. If not, we set it to zero. -/
noncomputable
def covarianceBilin (μ : Measure E) [IsFiniteMeasure μ] :
    Dual ℝ E →L[ℝ] Dual ℝ E →L[ℝ] ℝ :=
  if h : MemLp id 2 μ then
    centeredCovarianceBilin (μ.map (fun x ↦ x - ∫ x, x ∂μ))
      ((memLp_map_measure_iff (by fun_prop) (by fun_prop)).mpr <| h.sub (memLp_const _))
  else 0

lemma covarianceBilin_of_memLp (h : MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = centeredCovarianceBilin (μ.map (fun x ↦ x - ∫ x, x ∂μ))
      ((memLp_map_measure_iff (by fun_prop) (by fun_prop)).mpr <| h.sub (memLp_const _)) L₁ L₂ := by
  rw [covarianceBilin, dif_pos h]

lemma covarianceBilin_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = 0 := by
  simp [covarianceBilin, dif_neg h]

variable [CompleteSpace E]

lemma covarianceBilin_apply (h : MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = ∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ := by
  rw [covarianceBilin_of_memLp h, centeredCovarianceBilin_apply,
    integral_map (by fun_prop) (by fun_prop)]
  have hL (L : Dual ℝ E) : μ[L] = L (∫ x, x ∂μ) := L.integral_comp_comm (h.integrable (by simp))
  simp [← hL]

lemma covarianceBilin_same_eq_variance (h : MemLp id 2 μ) (L : Dual ℝ E) :
    covarianceBilin μ L L = Var[L; μ] := by
  rw [covarianceBilin_apply h, variance_eq_integral (by fun_prop)]
  simp_rw [pow_two]

end Covariance

end ProbabilityTheory
