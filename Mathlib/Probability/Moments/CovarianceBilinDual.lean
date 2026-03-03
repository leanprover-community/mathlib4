/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.LocallyConvex.ContinuousOfBounded
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Probability.Moments.Variance

/-!
# Covariance in Banach spaces

We define the covariance of a finite measure in a Banach space `E`,
as a continuous bilinear form on `Dual ℝ E`.

## Main definitions

Let `μ` be a finite measure on a normed space `E` with the Borel σ-algebra. We then define

* `Dual.toLp`: the function `MemLp.toLp` as a continuous linear map from `Dual 𝕜 E` (for `RCLike 𝕜`)
  into the space `Lp 𝕜 p μ` for `p ≥ 1`. This needs a hypothesis `MemLp id p μ` (we set it to the
  junk value 0 if that's not the case).
* `covarianceBilinDual` : covariance of a measure `μ` with `∫ x, ‖x‖^2 ∂μ < ∞` on a Banach space,
  as a continuous bilinear form `Dual ℝ E →L[ℝ] Dual ℝ E →L[ℝ] ℝ`.
  If the second moment of `μ` is not finite, we set `covarianceBilinDual μ = 0`.

## Main statements

* `covarianceBilinDual_apply` : the covariance of `μ` on `L₁, L₂ : Dual ℝ E` is equal to
  `∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ`.
* `covarianceBilinDual_same_eq_variance`: `covarianceBilinDual μ L L = Var[L; μ]`.

## Implementation notes

The hypothesis that `μ` has a second moment is written as `MemLp id 2 μ` in the code.

-/

@[expose] public section


open MeasureTheory ProbabilityTheory Complex NormedSpace
open scoped ENNReal NNReal Real Topology

variable {E : Type*} [NormedAddCommGroup E] {mE : MeasurableSpace E} {μ : Measure E} {p : ℝ≥0∞}

namespace StrongDual

section LinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]

open Classical in
/-- Linear map from the dual to `Lp` equal to `MemLp.toLp` if `MemLp id p μ` and to 0 otherwise. -/
noncomputable
def toLpₗ (μ : Measure E) (p : ℝ≥0∞) :
    StrongDual 𝕜 E →ₗ[𝕜] Lp 𝕜 p μ :=
  if h_Lp : MemLp id p μ then
  { toFun := fun L ↦ MemLp.toLp L (h_Lp.continuousLinearMap_comp L)
    map_add' u v := by push_cast; rw [MemLp.toLp_add]
    map_smul' c L := by push_cast; rw [MemLp.toLp_const_smul]; rfl }
  else 0

@[simp]
lemma toLpₗ_apply (h_Lp : MemLp id p μ) (L : StrongDual 𝕜 E) :
    L.toLpₗ μ p = MemLp.toLp L (h_Lp.continuousLinearMap_comp L) := by
  simp [toLpₗ, dif_pos h_Lp]

@[simp]
lemma toLpₗ_of_not_memLp (h_Lp : ¬ MemLp id p μ) (L : StrongDual 𝕜 E) :
    L.toLpₗ μ p = 0 := by
  simp [toLpₗ, dif_neg h_Lp]

lemma norm_toLpₗ_le [OpensMeasurableSpace E] (L : StrongDual 𝕜 E) :
    ‖L.toLpₗ μ p‖ ≤ ‖L‖ * (eLpNorm id p μ).toReal := by
  by_cases h_Lp : MemLp id p μ
  swap
  · simp only [h_Lp, not_false_eq_true, toLpₗ_of_not_memLp, Lp.norm_zero]
    positivity
  by_cases hp : p = 0
  · simp only [h_Lp, toLpₗ_apply, Lp.norm_toLp]
    simp [hp]
  by_cases hp_top : p = ∞
  · simp only [hp_top, StrongDual.toLpₗ_apply h_Lp, Lp.norm_toLp, eLpNorm_exponent_top] at h_Lp ⊢
    simp only [eLpNormEssSup, id_eq]
    suffices (essSup (fun x ↦ ‖L x‖ₑ) μ).toReal ≤ (essSup (fun x ↦ ‖L‖ₑ * ‖x‖ₑ) μ).toReal by
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
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) hp_top, ENNReal.toReal_rpow]
    simp
  rw [StrongDual.toLpₗ_apply h_Lp, Lp.norm_toLp,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) hp_top]
  simp only [one_div]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  suffices ∫⁻ x, ‖L x‖ₑ ^ p.toReal ∂μ ≤ ‖L‖ₑ ^ p.toReal * ∫⁻ x, ‖x‖ₑ ^ p.toReal ∂μ by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    gcongr
    rwa [ENNReal.ofReal_toReal]
    refine ENNReal.mul_ne_top (by simp) ?_
    have h := h_Lp.eLpNorm_ne_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp]) hp_top] at h
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
    StrongDual 𝕜 E →L[𝕜] Lp 𝕜 p μ where
  toLinearMap := StrongDual.toLpₗ μ p
  cont := by
    refine LinearMap.continuous_of_locally_bounded _ fun s hs ↦ ?_
    rw [image_isVonNBounded_iff]
    simp_rw [isVonNBounded_iff'] at hs
    obtain ⟨r, hxr⟩ := hs
    refine ⟨r * (eLpNorm id p μ).toReal, fun L hLs ↦ ?_⟩
    specialize hxr L hLs
    refine (StrongDual.norm_toLpₗ_le L).trans ?_
    gcongr

@[simp]
lemma toLp_apply [Fact (1 ≤ p)] (h_Lp : MemLp id p μ) (L : StrongDual 𝕜 E) :
    L.toLp μ p = MemLp.toLp L (h_Lp.continuousLinearMap_comp L) := by
  simp [toLp, h_Lp]

@[simp]
lemma toLp_of_not_memLp [Fact (1 ≤ p)] (h_Lp : ¬ MemLp id p μ) (L : StrongDual 𝕜 E) :
    L.toLp μ p = 0 := by
  simp [toLp, h_Lp]

end ContinuousLinearMap

end StrongDual

namespace ProbabilityTheory

section Centered

variable [NormedSpace ℝ E] [OpensMeasurableSpace E]

/-- Continuous bilinear form with value `∫ x, L₁ x * L₂ x ∂μ` on `(L₁, L₂)`.
This is equal to the covariance only if `μ` is centered. -/
noncomputable
def uncenteredCovarianceBilinDual (μ : Measure E) : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (StrongDual.toLp μ 2) (StrongDual.toLp μ 2)

@[deprecated (since := "2025-10-10")] alias uncenteredCovarianceBilin :=
  uncenteredCovarianceBilinDual

set_option backward.isDefEq.respectTransparency false in
lemma uncenteredCovarianceBilinDual_apply (h : MemLp id 2 μ) (L₁ L₂ : StrongDual ℝ E) :
    uncenteredCovarianceBilinDual μ L₁ L₂ = ∫ x, L₁ x * L₂ x ∂μ := by
  simp only [uncenteredCovarianceBilinDual, ContinuousLinearMap.bilinearComp_apply,
    StrongDual.toLp_apply h, L2.inner_def, RCLike.inner_apply, conj_trivial]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (h.continuousLinearMap_comp L₁),
    MemLp.coeFn_toLp (h.continuousLinearMap_comp L₂)] with x hxL₁ hxL₂
  simp only [id_eq] at hxL₁ hxL₂
  rw [hxL₁, hxL₂, mul_comm]

@[deprecated (since := "2025-10-10")] alias uncenteredCovarianceBilin_apply :=
  uncenteredCovarianceBilinDual_apply

lemma uncenteredCovarianceBilinDual_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual ℝ E) :
    uncenteredCovarianceBilinDual μ L₁ L₂ = 0 := by
  simp [uncenteredCovarianceBilinDual, StrongDual.toLp_of_not_memLp h]

@[deprecated (since := "2025-10-10")] alias uncenteredCovarianceBilin_of_not_memLp :=
  uncenteredCovarianceBilinDual_of_not_memLp

@[simp]
lemma uncenteredCovarianceBilinDual_zero : uncenteredCovarianceBilinDual (0 : Measure E) = 0 := by
  ext
  have : Subsingleton (Lp ℝ 2 (0 : Measure E)) := ⟨fun x y ↦ Lp.ext_iff.2 rfl⟩
  simp [uncenteredCovarianceBilinDual, Subsingleton.eq_zero (StrongDual.toLp 0 2)]

@[deprecated (since := "2025-10-10")] alias uncenteredCovarianceBilin_zero :=
  uncenteredCovarianceBilinDual_zero

lemma norm_uncenteredCovarianceBilinDual_le (L₁ L₂ : StrongDual ℝ E) :
    ‖uncenteredCovarianceBilinDual μ L₁ L₂‖ ≤ ‖L₁‖ * ‖L₂‖ * ∫ x, ‖x‖ ^ 2 ∂μ := by
  by_cases h : MemLp id 2 μ
  swap; · simp only [uncenteredCovarianceBilinDual_of_not_memLp h, norm_zero]; positivity
  calc ‖uncenteredCovarianceBilinDual μ L₁ L₂‖
  _ = ‖∫ x, L₁ x * L₂ x ∂μ‖ := by rw [uncenteredCovarianceBilinDual_apply h]
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

@[deprecated (since := "2025-10-10")] alias norm_uncenteredCovarianceBilin_le :=
  norm_uncenteredCovarianceBilinDual_le

end Centered

section Covariance

variable [NormedSpace ℝ E] [BorelSpace E]

open Classical in
/-- Continuous bilinear form with value `∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ` on `(L₁, L₂)`
if `MemLp id 2 μ`. If not, we set it to zero. -/
noncomputable
def covarianceBilinDual (μ : Measure E) : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ :=
  uncenteredCovarianceBilinDual (μ.map (fun x ↦ x - ∫ x, x ∂μ))

omit [BorelSpace E] in
lemma _root_.MeasureTheory.memLp_id_of_self_sub_integral {p : ℝ≥0∞}
    (h_Lp : MemLp (fun x ↦ x - ∫ y, y ∂μ) p μ) : MemLp id p μ := by
  have : (id : E → E) = fun x ↦ x - ∫ x, x ∂μ + ∫ x, x ∂μ := by ext; simp
  rw [this]
  apply h_Lp.add
  set c := ∫ x, x ∂μ
  /- We need to check that the constant `c = ∫ x, x ∂μ` is in `L^p`. Note that we don't assume
  that `μ` is finite, so this requires an argument. If the constant is zero, it's obvious.
  If it's nonzero, this means that `x` is integrable for `μ` (as otherwise the integral would be
  `0` by our choice of junk value), so `‖x‖ ^ (1/p)` is in `L^p`.
  The constant `c` is controlled by `2 ‖x - c‖` close to `0` (say when `‖x‖ ≤ ‖c‖ / 2`)
  and by a multiple of `‖x‖ ^ (1/p)` away from `0`. Those two functions
  are in `L^p` by assumptions, so the constant `c` also is. -/
  by_cases hx : c = 0
  · simp [hx]
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [aestronglyMeasurable_const]
  rcases eq_or_ne p ∞ with rfl | hptop
  · exact memLp_top_const c
  apply (integrable_norm_rpow_iff (by fun_prop) hp0 hptop).1
  have I : Integrable (fun (x : E) ↦ ‖x‖) μ := by
    apply Integrable.norm
    contrapose! hx
    exact integral_undef hx
  have := (h_Lp.integrable_norm_rpow hp0 hptop).const_mul (2 ^ p.toReal)
  apply (((I.const_mul (2 * ‖c‖ ^ (p.toReal - 1))).add this)).mono' (by fun_prop)
  filter_upwards [] with y
  lift p to ℝ≥0 using hptop
  simp only [ENNReal.coe_toReal, Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (by positivity)]
  rcases le_total ‖y‖ (‖c‖ / 2)
  · have : ‖c‖ ≤ ‖y‖ + ‖y - c‖ := Eq.trans_le (by abel_nf) (norm_sub_le y (y - c))
    calc ‖c‖ ^ (p : ℝ)
    _ ≤ (2 * ‖y - c‖) ^ (p : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    _ = 0 + 2 ^ (p : ℝ) * ‖y - c‖ ^ (p : ℝ) := by
      rw [Real.mul_rpow (by simp) (by positivity)]
      ring
    _ ≤ 2 * ‖c‖ ^ (p - 1 : ℝ) * ‖y‖ + 2 ^ (p : ℝ) * ‖y - c‖ ^ (p : ℝ) := by
      gcongr
      positivity
  · calc ‖c‖ ^ (p : ℝ)
    _ = ‖c‖ ^ ((p - 1) + 1 : ℝ) := by abel_nf
    _ = ‖c‖ ^ (p - 1 : ℝ) * ‖c‖ := by rw [Real.rpow_add (by positivity), Real.rpow_one]
    _ ≤ ‖c‖ ^ (p - 1 : ℝ) * (2 * ‖y‖) := by gcongr; linarith
    _ = 2 * ‖c‖ ^ (p - 1 : ℝ) * ‖y‖ + 0 := by ring
    _ ≤ 2 * ‖c‖ ^ (p - 1 : ℝ) * ‖y‖ + 2 ^ (p : ℝ) * ‖y - c‖ ^ (p : ℝ) := by gcongr; positivity

lemma covarianceBilinDual_of_not_memLp' (h : ¬ MemLp (fun x ↦ x - ∫ y, y ∂μ) 2 μ)
    (L₁ L₂ : StrongDual ℝ E) :
    covarianceBilinDual μ L₁ L₂ = 0 := by
  rw [covarianceBilinDual, uncenteredCovarianceBilinDual_of_not_memLp]
  rw [(measurableEmbedding_subRight _).memLp_map_measure_iff]
  exact h

@[simp]
lemma covarianceBilinDual_of_not_memLp (h : ¬ MemLp id 2 μ) (L₁ L₂ : StrongDual ℝ E) :
    covarianceBilinDual μ L₁ L₂ = 0 := by
  apply covarianceBilinDual_of_not_memLp'
  contrapose! h
  exact memLp_id_of_self_sub_integral h

@[simp]
lemma covarianceBilinDual_zero : covarianceBilinDual (0 : Measure E) = 0 := by
  rw [covarianceBilinDual, Measure.map_zero, uncenteredCovarianceBilinDual_zero]

lemma covarianceBilinDual_comm (L₁ L₂ : StrongDual ℝ E) :
    covarianceBilinDual μ L₁ L₂ = covarianceBilinDual μ L₂ L₁ := by
  by_cases h : MemLp (fun x ↦ x - ∫ y, y ∂μ) 2 μ
  · have h' : MemLp id 2 (Measure.map (fun x ↦ x - ∫ (x : E), x ∂μ) μ) :=
      (measurableEmbedding_subRight _).memLp_map_measure_iff.mpr <| h
    simp_rw [covarianceBilinDual, uncenteredCovarianceBilinDual_apply h', mul_comm (L₁ _)]
  · simp [h, covarianceBilinDual_of_not_memLp']

@[simp]
lemma covarianceBilinDual_self_nonneg (L : StrongDual ℝ E) : 0 ≤ covarianceBilinDual μ L L := by
  by_cases h : MemLp id 2 μ
  · simp only [covarianceBilinDual, uncenteredCovarianceBilinDual,
      ContinuousLinearMap.bilinearComp_apply, IsBoundedBilinearMap.toContinuousLinearMap_apply]
    exact real_inner_self_nonneg
  · simp [h]

lemma isPosSemidef_covarianceBilinDual : (covarianceBilinDual μ).toBilinForm.IsPosSemidef where
  eq := covarianceBilinDual_comm
  nonneg := covarianceBilinDual_self_nonneg

variable [CompleteSpace E] [IsFiniteMeasure μ]

lemma covarianceBilinDual_apply (h : MemLp id 2 μ) (L₁ L₂ : StrongDual ℝ E) :
    covarianceBilinDual μ L₁ L₂ = ∫ x, (L₁ x - μ[L₁]) * (L₂ x - μ[L₂]) ∂μ := by
  rw [covarianceBilinDual, uncenteredCovarianceBilinDual_apply,
    integral_map (by fun_prop) (by fun_prop)]
  · have hL (L : StrongDual ℝ E) : μ[L] = L (∫ x, x ∂μ) :=
      L.integral_comp_comm (h.integrable (by simp))
    simp [← hL]
  · exact (measurableEmbedding_subRight _).memLp_map_measure_iff.mpr <| h.sub (memLp_const _)

lemma covarianceBilinDual_apply' (h : MemLp id 2 μ) (L₁ L₂ : StrongDual ℝ E) :
    covarianceBilinDual μ L₁ L₂ = ∫ x, L₁ (x - μ[id]) * L₂ (x - μ[id]) ∂μ := by
  rw [covarianceBilinDual_apply h]
  have hL (L : StrongDual ℝ E) : μ[L] = L (∫ x, x ∂μ) :=
    L.integral_comp_comm (h.integrable (by simp))
  simp [← hL]

lemma covarianceBilinDual_eq_covariance (h : MemLp id 2 μ) (L₁ L₂ : StrongDual ℝ E) :
    covarianceBilinDual μ L₁ L₂ = cov[L₁, L₂; μ] := by
  rw [covarianceBilinDual_apply h, covariance]

lemma covarianceBilinDual_self_eq_variance (h : MemLp id 2 μ) (L : StrongDual ℝ E) :
    covarianceBilinDual μ L L = Var[L; μ] := by
  rw [covarianceBilinDual_eq_covariance h, covariance_self (by fun_prop)]

end Covariance

end ProbabilityTheory
