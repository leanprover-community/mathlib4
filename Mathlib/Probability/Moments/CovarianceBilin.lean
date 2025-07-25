/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.Probability.Moments.Covariance

/-!
# Covariance in Banach spaces

We define the covariance of a finite measure in a Banach space `E`,
as a continuous bilinear form on `Dual ℝ E`.

## Main definitions

Let `μ` be a finite measure on a normed space `E` with the Borel σ-algebra. We then define

* `Dual.toLp`: the function `MemLp.toLp` as a continuous linear map from `Dual 𝕜 E` (for `RCLike 𝕜`)
  into the space `Lp 𝕜 p μ` for `p ≥ 1`. This needs a hypothesis `MemLp id p μ` (we set it to the
  junk value 0 if that's not the case).
* `covarianceBilin` : covariance of a measure `μ` with `∫ x, ‖x‖^2 ∂μ < ∞` on a Banach space,
  as a continuous bilinear form `Dual ℝ E →L[ℝ] Dual ℝ E →L[ℝ] ℝ`.
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

variable {E : Type*} [NormedAddCommGroup E] {mE : MeasurableSpace E} {μ : Measure E} {p : ℝ≥0∞}

namespace NormedSpace.Dual

section LinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

open Classical in
/-- Linear map from the dual to `Lp` equal to `MemLp.toLp` if `MemLp id p μ` and to 0 otherwise. -/
noncomputable
def toLpₗ (μ : Measure E) (p : ℝ≥0∞) :
    Dual 𝕜 E →ₗ[𝕜] Lp 𝕜 p μ :=
  if h_Lp : MemLp id p μ then
  { toFun := fun L ↦ MemLp.toLp L (h_Lp.continuousLinearMap_comp L)
    map_add' u v := by push_cast; rw [MemLp.toLp_add]
    map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl }
  else 0

@[simp]
lemma toLpₗ_apply (h_Lp : MemLp id p μ) (L : Dual 𝕜 E) :
    L.toLpₗ μ p = MemLp.toLp L (h_Lp.continuousLinearMap_comp L) := by
  simp [toLpₗ, dif_pos h_Lp]

@[simp]
lemma toLpₗ_of_not_memLp (h_Lp : ¬ MemLp id p μ) (L : Dual 𝕜 E) :
    L.toLpₗ μ p = 0 := by
  simp [toLpₗ, dif_neg h_Lp]

lemma norm_toLpₗ_le [OpensMeasurableSpace E] (L : Dual 𝕜 E) :
    ‖L.toLpₗ μ p‖ ≤ ‖L‖ * (eLpNorm id p μ).toReal := by
  by_cases h_Lp : MemLp id p μ
  swap
  · simp only [h_Lp, not_false_eq_true, toLpₗ_of_not_memLp, Lp.norm_zero]
    positivity
  by_cases hp : p = 0
  · simp only [h_Lp, toLpₗ_apply, Lp.norm_toLp]
    simp [hp]
  by_cases hp_top : p = ∞
  · simp only [hp_top, Dual.toLpₗ_apply h_Lp, Lp.norm_toLp, eLpNorm_exponent_top] at h_Lp ⊢
    simp only [eLpNormEssSup, id_eq]
    suffices (essSup (fun x ↦ ‖L x‖ₑ) μ).toReal ≤ (essSup (fun x ↦ ‖L‖ₑ *‖x‖ₑ) μ).toReal by
      rwa [ENNReal.essSup_const_mul, ENNReal.toReal_mul, toReal_enorm] at this
    gcongr
    · rw [ENNReal.essSup_const_mul]
      exact ENNReal.mul_ne_top (by simp) h_Lp.eLpNorm_ne_top
    · exact essSup_mono_ae <| ae_of_all _ L.le_opNorm_enorm
  have h0 : 0 < p.toReal := by simp [ENNReal.toReal_pos_iff, pos_iff_ne_zero, hp, Ne.lt_top hp_top]
  suffices ‖L.toLpₗ μ p‖
      ≤ (‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ).toReal ^ p.toReal⁻¹ by
    refine this.trans_eq ?_
    simp only [ENNReal.toReal_mul]
    rw [← ENNReal.toReal_rpow, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by positivity), mul_inv_cancel₀ h0.ne', Real.rpow_one, toReal_enorm]
    rw [eLpNorm_eq_lintegral_rpow_enorm (by simp [hp]) hp_top, ENNReal.toReal_rpow]
    simp
  rw [Dual.toLpₗ_apply h_Lp, Lp.norm_toLp, eLpNorm_eq_lintegral_rpow_enorm (by simp [hp]) hp_top]
  simp only [one_div]
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
    exact L.le_opNorm_enorm x
  _ = ‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ := by rw [lintegral_const_mul]; fun_prop

end LinearMap

section ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [OpensMeasurableSpace E]

/-- Continuous linear map from the dual to `Lp` equal to `MemLp.toLp` if `MemLp id p μ`
and to 0 otherwise. -/
noncomputable
def toLp (μ : Measure E) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Dual 𝕜 E →L[𝕜] Lp 𝕜 p μ where
  toLinearMap := Dual.toLpₗ μ p
  cont := by
    refine LinearMap.continuous_of_locally_bounded _ fun s hs ↦ ?_
    rw [image_isVonNBounded_iff]
    simp_rw [isVonNBounded_iff'] at hs
    obtain ⟨r, hxr⟩ := hs
    refine ⟨r * (eLpNorm id p μ).toReal, fun L hLs ↦ ?_⟩
    specialize hxr L hLs
    refine (Dual.norm_toLpₗ_le L).trans ?_
    gcongr

@[simp]
lemma toLp_apply [Fact (1 ≤ p)] (h_Lp : MemLp id p μ) (L : Dual 𝕜 E) :
    L.toLp μ p = MemLp.toLp L (h_Lp.continuousLinearMap_comp L) := by
  simp [toLp, h_Lp]

@[simp]
lemma toLp_of_not_memLp [Fact (1 ≤ p)] (h_Lp : ¬ MemLp id p μ) (L : Dual 𝕜 E) :
    L.toLp μ p = 0 := by
  simp [toLp, h_Lp]

end ContinuousLinearMap

end NormedSpace.Dual

namespace ProbabilityTheory

section Centered

variable [NormedSpace ℝ E] [OpensMeasurableSpace E]

/-- Continuous bilinear form with value `∫ x, L₁ x * L₂ x ∂μ` on `(L₁, L₂)`.
This is equal to the covariance only if `μ` is centered. -/
noncomputable
def uncenteredCovarianceBilin (μ : Measure E) : Dual ℝ E →L[ℝ] Dual ℝ E →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (Dual.toLp μ 2) (Dual.toLp μ 2)

lemma uncenteredCovarianceBilin_apply (h : MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    uncenteredCovarianceBilin μ L₁ L₂ = ∫ x, L₁ x * L₂ x ∂μ := by
  simp only [uncenteredCovarianceBilin, ContinuousLinearMap.bilinearComp_apply,
    Dual.toLp_apply h, L2.inner_def, RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (h.continuousLinearMap_comp L₁),
    MemLp.coeFn_toLp (h.continuousLinearMap_comp L₂)] with x hxL₁ hxL₂
  simp only [id_eq] at hxL₁ hxL₂
  rw [hxL₁, hxL₂, mul_comm]

lemma uncenteredCovarianceBilin_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    uncenteredCovarianceBilin μ L₁ L₂ = 0 := by
  simp [uncenteredCovarianceBilin, Dual.toLp_of_not_memLp h]

lemma uncenteredCovarianceBilin_zero : uncenteredCovarianceBilin (0 : Measure E) = 0 := by
  ext
  have : Subsingleton (Lp ℝ 2 (0 : Measure E)) := ⟨fun x y ↦ Lp.ext_iff.2 rfl⟩
  simp [uncenteredCovarianceBilin, Subsingleton.eq_zero (Dual.toLp 0 2)]

lemma norm_uncenteredCovarianceBilin_le (L₁ L₂ : Dual ℝ E) :
    ‖uncenteredCovarianceBilin μ L₁ L₂‖ ≤ ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := by
  by_cases h : MemLp id 2 μ
  swap; · simp only [uncenteredCovarianceBilin_of_not_memLp h, norm_zero]; positivity
  calc ‖uncenteredCovarianceBilin μ L₁ L₂‖
  _ = ‖∫ x, L₁ x * L₂ x ∂μ‖ := by rw [uncenteredCovarianceBilin_apply h]
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

variable [NormedSpace ℝ E] [BorelSpace E] [IsFiniteMeasure μ]

open Classical in
/-- Continuous bilinear form with value `∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ` on `(L₁, L₂)`
if `MemLp id 2 μ`. If not, we set it to zero. -/
noncomputable
def covarianceBilin (μ : Measure E) : Dual ℝ E →L[ℝ] Dual ℝ E →L[ℝ] ℝ :=
  uncenteredCovarianceBilin (μ.map (fun x ↦ x - ∫ x, x ∂μ))

@[simp]
lemma covarianceBilin_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = 0 := by
  rw [covarianceBilin, uncenteredCovarianceBilin_of_not_memLp]
  rw [(measurableEmbedding_subRight _).memLp_map_measure_iff]
  refine fun h_Lp ↦ h ?_
  have : (id : E → E) = fun x ↦ x - ∫ x, x ∂μ + ∫ x, x ∂μ := by ext; simp
  rw [this]
  exact h_Lp.add (memLp_const _)

@[simp]
lemma covarianceBilin_zero : covarianceBilin (0 : Measure E) = 0 := by
  rw [covarianceBilin, Measure.map_zero, uncenteredCovarianceBilin_zero]

lemma covarianceBilin_comm (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = covarianceBilin μ L₂ L₁ := by
  by_cases h : MemLp id 2 μ
  · have h' : MemLp id 2 (Measure.map (fun x ↦ x - ∫ (x : E), x ∂μ) μ) :=
      (measurableEmbedding_subRight _).memLp_map_measure_iff.mpr <| h.sub (memLp_const _)
    simp_rw [covarianceBilin, uncenteredCovarianceBilin_apply h', mul_comm (L₁ _)]
  · simp [h]

variable [CompleteSpace E]

lemma covarianceBilin_apply (h : MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = ∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ := by
  rw [covarianceBilin, uncenteredCovarianceBilin_apply,
    integral_map (by fun_prop) (by fun_prop)]
  · have hL (L : Dual ℝ E) : μ[L] = L (∫ x, x ∂μ) := L.integral_comp_comm (h.integrable (by simp))
    simp [← hL]
  · exact (measurableEmbedding_subRight _).memLp_map_measure_iff.mpr <| h.sub (memLp_const _)

lemma covarianceBilin_apply' (h : MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = ∫ x, L₁ (x - μ[id]) * L₂ (x - μ[id]) ∂μ := by
  rw [covarianceBilin_apply h]
  have hL (L : Dual ℝ E) : μ[L] = L (∫ x, x ∂μ) := L.integral_comp_comm (h.integrable (by simp))
  simp [← hL]

lemma covarianceBilin_eq_covariance (h : MemLp id 2 μ) (L₁ L₂ : Dual ℝ E) :
    covarianceBilin μ L₁ L₂ = cov[L₁, L₂; μ] := by
  rw [covarianceBilin_apply h, covariance]

lemma covarianceBilin_self_eq_variance (h : MemLp id 2 μ) (L : Dual ℝ E) :
    covarianceBilin μ L L = Var[L; μ] := by
  rw [covarianceBilin_eq_covariance h, covariance_self (by fun_prop)]

@[deprecated (since := "2025-07-16")] alias covarianceBilin_same_eq_variance :=
  covarianceBilin_self_eq_variance

end Covariance

end ProbabilityTheory
