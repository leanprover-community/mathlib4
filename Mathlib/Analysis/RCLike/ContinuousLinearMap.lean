/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Analysis.RCLike.Real
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Continuous linear maps between `RCLike K` and `ℝ`

This file realizes the real and imaginary parts as continuous linear maps, as well as the
`ℝ → K` coercion as a linear isometry. It also realizes conjugation as an `ℝ`-linear isometry
equivalence from `K` to itself.

These are not included in earlier files to avoid importing material involving the operator norm.
-/

open scoped ComplexConjugate
namespace RCLike

variable {K : Type*} [RCLike K]

lemma lipschitzWith_re : LipschitzWith 1 (re (K := K)) := by
  simpa using AddMonoidHomClass.lipschitz_of_bound reLm 1
    fun _ ↦ (by simpa using norm_re_le_norm _)

lemma lipschitzWith_im : LipschitzWith 1 (im (K := K)) := by
  simpa using AddMonoidHomClass.lipschitz_of_bound imLm 1
    fun _ ↦ (by simpa using norm_im_le_norm _)

@[continuity, fun_prop]
theorem continuous_re : Continuous (re : K → ℝ) :=
  lipschitzWith_re.continuous

@[continuity, fun_prop]
theorem continuous_im : Continuous (im : K → ℝ) :=
  lipschitzWith_im.continuous

/-- The real part in an `RCLike` field, as a continuous linear map. -/
noncomputable def reCLM : StrongDual ℝ K where
  __ := reLm

@[simp, rclike_simps, norm_cast]
theorem reCLM_coe : ((reCLM : StrongDual ℝ K) : K →ₗ[ℝ] ℝ) = reLm :=
  rfl

@[simp, rclike_simps]
theorem reCLM_apply : ((reCLM : StrongDual ℝ K) : K → ℝ) = re :=
  rfl

/-- The imaginary part in an `RCLike` field, as a continuous linear map. -/
noncomputable def imCLM : StrongDual ℝ K where
  __ := imLm

@[simp, rclike_simps, norm_cast]
theorem imCLM_coe : ((imCLM : StrongDual ℝ K) : K →ₗ[ℝ] ℝ) = imLm :=
  rfl

@[simp, rclike_simps]
theorem imCLM_apply : ((imCLM : StrongDual ℝ K) : K → ℝ) = im :=
  rfl

/-- Conjugate as a linear isometry -/
noncomputable def conjLIE : K ≃ₗᵢ[ℝ] K :=
  ⟨conjAe.toLinearEquiv, norm_conj⟩

@[simp, rclike_simps]
theorem conjLIE_apply : (conjLIE : K → K) = conj :=
  rfl

/-- Conjugate as a continuous linear equivalence -/
noncomputable def conjCLE : K ≃L[ℝ] K :=
  @conjLIE K _

@[simp, rclike_simps]
theorem conjCLE_coe : (@conjCLE K _).toLinearEquiv = conjAe.toLinearEquiv :=
  rfl

@[simp, rclike_simps]
theorem conjCLE_apply : (conjCLE : K → K) = conj :=
  rfl

instance (priority := 100) : ContinuousStar K :=
  ⟨conjLIE.continuous⟩

@[continuity, fun_prop]
theorem continuous_conj : Continuous (conj : K → K) :=
  continuous_star

/-- The ℝ → K coercion, as a linear isometry -/
noncomputable def ofRealLI : ℝ →ₗᵢ[ℝ] K where
  toLinearMap := ofRealAm.toLinearMap
  norm_map' := norm_ofReal

@[simp, rclike_simps]
theorem ofRealLI_apply : (ofRealLI : ℝ → K) = ofReal :=
  rfl

/-- The `ℝ → K` coercion, as a continuous linear map -/
noncomputable def ofRealCLM : ℝ →L[ℝ] K :=
  ofRealLI.toContinuousLinearMap

@[simp, rclike_simps]
theorem ofRealCLM_coe : (@ofRealCLM K _ : ℝ →ₗ[ℝ] K) = ofRealAm.toLinearMap :=
  rfl

@[simp, rclike_simps]
theorem ofRealCLM_apply : (ofRealCLM : ℝ → K) = ofReal :=
  rfl

@[continuity, fun_prop]
theorem continuous_ofReal : Continuous (ofReal : ℝ → K) :=
  ofRealLI.continuous

@[continuity]
theorem continuous_normSq : Continuous (normSq : K → ℝ) :=
  (continuous_re.mul continuous_re).add (continuous_im.mul continuous_im)

theorem lipschitzWith_ofReal : LipschitzWith 1 (ofReal : ℝ → K) :=
  ofRealLI.lipschitz

/-- The natural `ℝ`-linear isometry equivalence between `𝕜` satisfying `RCLike 𝕜` and `ℝ` when
`RCLike.I = 0`. -/
@[simps]
noncomputable def realLinearIsometryEquiv (h : I = (0 : K)) : K ≃ₗᵢ[ℝ] ℝ where
  map_smul' := smul_re
  norm_map' z := by rw [← re_add_im z]; simp [- re_add_im, h]
  __ := realRingEquiv h

end RCLike
