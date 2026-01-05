/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.Laplacian

/-! # Fourier multiplier on Schwartz functions and tempered distributions -/

@[expose] public noncomputable section

variable {ι 𝕜 E F F₁ F₂ : Type*}

namespace SchwartzMap

open scoped SchwartzMap

variable [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

variable [CompleteSpace F]

@[fun_prop]
theorem Complex.hasTemperateGrowth_ofReal : Complex.ofReal.HasTemperateGrowth :=
  (Complex.ofRealCLM).hasTemperateGrowth

@[fun_prop]
theorem RCLike.hasTemperateGrowth_ofReal : (RCLike.ofReal (K := 𝕜)).HasTemperateGrowth :=
  (RCLike.ofRealCLM (K := 𝕜)).hasTemperateGrowth

variable (F) in
def fourierMultiplierCLM (g : E → 𝕜) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  (fourierTransformCLE 𝕜).symm.toContinuousLinearMap ∘L (smulLeftCLM F g) ∘L
    fourierTransformCLM 𝕜

theorem fourierMultiplierCLM_apply (g : E → 𝕜) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f)) := by
  rfl

variable (𝕜) in
theorem fourierMultiplierCLM_ofReal {g : E → ℝ} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F (fun x ↦ RCLike.ofReal (K := 𝕜) (g x)) f =
    fourierMultiplierCLM F g f := by
  simp_rw [fourierMultiplierCLM_apply]
  congr 1
  ext x
  rw [smulLeftCLM_apply_apply (by fun_prop), smulLeftCLM_apply_apply (by fun_prop),
    algebraMap_smul]

@[simp]
theorem fourierMultiplierCLM_const_apply (f : 𝓢(E, F)) (c : 𝕜) :
    fourierMultiplierCLM F (fun _ ↦ c) f = c • f := by
  ext
  simp [fourierMultiplierCLM_apply]

theorem fourierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E → 𝕜}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g₁ (fourierMultiplierCLM F g₂ f) =
    fourierMultiplierCLM F (g₁ * g₂) f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]

variable (F) in
theorem fourierMultiplierCLM_sum {g : ι → E → 𝕜} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) :
    fourierMultiplierCLM F (fun x ↦ ∑ i ∈ s, g i x) = ∑ i ∈ s, fourierMultiplierCLM F (g i) := by
  ext1 f
  simpa [fourierMultiplierCLM_apply, smulLeftCLM_sum hg] using map_sum _ _ _

open LineDeriv Laplacian Real

theorem lineDeriv_eq_fourierMultiplierCLM (m : E) (f : 𝓢(E, F)) :
    ∂_{m} f = (2 * π * Complex.I) • fourierMultiplierCLM F (inner ℝ · m) f := by
  rw [fourierMultiplierCLM_apply, ← FourierTransform.fourierInv_smul, ← fourier_lineDerivOp_eq,
    FourierTransform.fourierInv_fourier_eq]

@[fun_prop]
theorem inner_hasTemperateGrowth_left (c : E) : (inner ℝ · c).HasTemperateGrowth :=
  ((innerSL ℝ).flip c).hasTemperateGrowth

theorem laplacian_eq_fourierMultiplierCLM (f : 𝓢(E, F)) :
    Δ f = -(2 * π) ^ 2 • fourierMultiplierCLM F (‖·‖ ^ 2) f := by
  let ι := Fin (Module.finrank ℝ E)
  let b := stdOrthonormalBasis ℝ E
  have : ∀ i (hi : i ∈ Finset.univ), (inner ℝ · (b i) ^ 2).HasTemperateGrowth := by
    fun_prop
  simp_rw [laplacian_eq_sum b, ← b.sum_sq_inner_left, fourierMultiplierCLM_sum F this,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, Finset.smul_sum]
  congr 1
  ext i x
  simp_rw [smul_apply, lineDeriv_eq_fourierMultiplierCLM]
  rw [← fourierMultiplierCLM_ofReal ℂ (by fun_prop)]
  simp_rw [map_smul, smul_apply, smul_smul]
  congr 1
  · ring_nf
    simp
  rw [fourierMultiplierCLM_ofReal ℂ (by fun_prop)]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr 3
  ext y
  simp [pow_two]

end SchwartzMap

namespace TemperedDistribution

open scoped SchwartzMap

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

variable (F) in
def fourierMultiplierCLM (g : E → ℂ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierTransformInvCLM E F ∘L (smulLeftCLM F g) ∘L fourierTransformCLM E F

theorem fourierMultiplierCLM_apply (g : E → ℂ) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f)) := by
  rfl

@[simp]
theorem fourierMultiplierCLM_apply_apply (g : E → ℂ) (f : 𝓢'(E, F)) (u : 𝓢(E, ℂ)) :
    fourierMultiplierCLM F g f u = f (𝓕 (SchwartzMap.smulLeftCLM ℂ g (𝓕⁻ u))) := by
  rfl

@[simp]
theorem fourierMultiplierCLM_const_apply (f : 𝓢'(E, F)) (c : ℂ) :
    fourierMultiplierCLM F (fun _ ↦ c) f = c • f := by
  ext
  simp

theorem fourierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E → ℂ}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F g₂ (fourierMultiplierCLM F g₁ f) =
    fourierMultiplierCLM F (g₁ * g₂) f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]

variable [CompleteSpace F]

theorem fourierMultiplierCLM_toTemperedDistributionCLM_eq (f : 𝓢(E, F)) (g : E → ℂ)
    (hg : g.HasTemperateGrowth) :
    fourierMultiplierCLM F g (f : 𝓢'(E, F)) = SchwartzMap.fourierMultiplierCLM F g f := by
  ext u
  simp [SchwartzMap.integral_fourier_smul_eq, SchwartzMap.fourierMultiplierCLM_apply g f,
    ← SchwartzMap.integral_fourierInv_smul_eq, hg, smul_smul, mul_comm]

open LineDeriv Laplacian Real

variable [CompleteSpace E]

theorem lineDeriv_eq_fourierMultiplierCLM (m : E) (f : 𝓢'(E, F)) :
    ∂_{m} f = (2 * π * Complex.I) • fourierMultiplierCLM F (inner ℝ · m) f := by
  rw [fourierMultiplierCLM_apply, ← FourierTransform.fourierInv_smul, ← fourier_lineDerivOp_eq,
    FourierTransform.fourierInv_fourier_eq]
  ext u
  simp [SchwartzMap.lineDeriv_eq_fourierMultiplierCLM m u]
  congr 2
  rw [← SchwartzMap.fourierMultiplierCLM_ofReal ℂ (by fun_prop)]
  simp [SchwartzMap.fourierMultiplierCLM_apply]


  rw [SchwartzMap.lineDeriv_eq_fourierMultiplierCLM m u]
  sorry


end TemperedDistribution
