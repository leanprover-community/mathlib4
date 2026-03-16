/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-! # Fourier multiplier on Schwartz functions and tempered distributions

We define a Fourier multiplier as continuous linear maps on Schwartz functions and tempered
distributions. The multiplier function is throughout assumed to have temperate growth.

## Main definitions
* `SchwartzMap.fourierMultiplierCLM`: Fourier multiplier on Schwartz functions
* `TemperedDistribution.fourierMultiplierCLM`: Fourier multiplier on tempered distribution

## Main statements
* `SchwartzMap.lineDeriv_eq_fourierMultiplierCLM`: the directional derivative is equal to the
  Fourier multiplier with `inner ℝ . m`.
* `SchwartzMap.laplacian_eq_fourierMultiplierCLM`: the Laplacian is equal to the Fourier multiplier
  with `‖·‖`.
* `TemperedDistribution.lineDeriv_eq_fourierMultiplierCLM`: the distributional directional
  derivative is equal to the Fourier multiplier with `inner ℝ . m`.
* `TemperedDistribution.laplacian_eq_fourierMultiplierCLM`: the distributional Laplacian is equal to
  the Fourier multiplier with `‖·‖`.

-/

@[expose] public noncomputable section

variable {ι 𝕜 E F F₁ F₂ : Type*}

namespace SchwartzMap

/-! ## Schwartz functions -/

open scoped SchwartzMap

variable [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

variable (F) in
/-- Fourier multiplier on Schwartz functions. -/
def fourierMultiplierCLM (g : E → 𝕜) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  fourierInvCLM 𝕜 𝓢(E, F) ∘L (smulLeftCLM F g) ∘L fourierCLM 𝕜 𝓢(E, F)

theorem fourierMultiplierCLM_apply (g : E → 𝕜) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (𝕜) in
theorem fourierMultiplierCLM_ofReal {g : E → ℝ} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F (fun x ↦ RCLike.ofReal (K := 𝕜) (g x)) f =
    fourierMultiplierCLM F g f := by
  simp_rw [fourierMultiplierCLM_apply]
  congr 1
  exact smulLeftCLM_ofReal 𝕜 hg (𝓕 f)

theorem fourierMultiplierCLM_smul {g : E → 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜) :
    fourierMultiplierCLM F (c • g) = c • fourierMultiplierCLM F g := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smul hg]

variable (F) in
theorem fourierMultiplierCLM_sum {g : ι → E → 𝕜} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) :
    fourierMultiplierCLM F (∑ i ∈ s, g i ·) = ∑ i ∈ s, fourierMultiplierCLM F (g i) := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_sum hg]

variable [CompleteSpace F]

@[simp]
theorem fourierMultiplierCLM_const (c : 𝕜) :
    fourierMultiplierCLM F (fun (_ : E) ↦ c) = c • ContinuousLinearMap.id _ _ := by
  ext f x
  simp [fourierMultiplierCLM_apply]

theorem fourierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E → 𝕜}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g₁ (fourierMultiplierCLM F g₂ f) =
    fourierMultiplierCLM F (g₁ * g₂) f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]

theorem fourierMultiplierCLM_compL_fourierMultiplierCLM {g₁ g₂ : E → 𝕜}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F g₁ ∘L fourierMultiplierCLM F g₂ =
    fourierMultiplierCLM F (g₁ * g₂) := by
  ext1 f
  simp [fourierMultiplierCLM_fourierMultiplierCLM_apply hg₁ hg₂]

open LineDeriv Real

set_option backward.isDefEq.respectTransparency false in
theorem lineDeriv_eq_fourierMultiplierCLM (m : E) (f : 𝓢(E, F)) :
    ∂_{m} f = (2 * π * Complex.I) • fourierMultiplierCLM F (inner ℝ · m) f := by
  rw [fourierMultiplierCLM_apply, ← FourierTransform.fourierInv_smul, ← fourier_lineDerivOp_eq,
    FourierTransform.fourierInv_fourier_eq]

open Laplacian

set_option backward.isDefEq.respectTransparency false in
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
  · rw [fourierMultiplierCLM_ofReal ℂ (by fun_prop),
      fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
    simp [sq, Pi.mul_def]

end SchwartzMap

namespace TemperedDistribution

/-! ## Tempered distributions -/

open scoped SchwartzMap

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform

variable (F) in
/-- Fourier multiplier on tempered distributions. -/
def fourierMultiplierCLM (g : E → ℂ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierInvCLM ℂ 𝓢'(E, F) ∘L (smulLeftCLM F g) ∘L fourierCLM ℂ 𝓢'(E, F)

theorem fourierMultiplierCLM_apply (g : E → ℂ) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F g f = 𝓕⁻ (smulLeftCLM F g (𝓕 f)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem fourierMultiplierCLM_apply_apply (g : E → ℂ) (f : 𝓢'(E, F)) (u : 𝓢(E, ℂ)) :
    fourierMultiplierCLM F g f u = f (𝓕 (SchwartzMap.smulLeftCLM ℂ g (𝓕⁻ u))) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem fourierMultiplierCLM_const (c : ℂ) :
    fourierMultiplierCLM F (fun (_ : E) ↦ c) = c • ContinuousLinearMap.id _ _ := by
  ext
  simp

theorem fourierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E → ℂ}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F g₂ (fourierMultiplierCLM F g₁ f) =
    fourierMultiplierCLM F (g₁ * g₂) f := by
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smulLeftCLM_apply hg₁ hg₂]

theorem fourierMultiplierCLM_compL_fourierMultiplierCLM {g₁ g₂ : E → ℂ}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) :
    fourierMultiplierCLM F g₂ ∘L fourierMultiplierCLM F g₁ =
    fourierMultiplierCLM F (g₁ * g₂) := by
  ext1 f
  simp [fourierMultiplierCLM_fourierMultiplierCLM_apply hg₁ hg₂]

theorem fourierMultiplierCLM_smul {g : E → ℂ} (hg : g.HasTemperateGrowth) (c : ℂ) :
    fourierMultiplierCLM F (c • g) = c • fourierMultiplierCLM F g := by
  ext1 f
  simp [fourierMultiplierCLM_apply, smulLeftCLM_smul hg]

set_option backward.isDefEq.respectTransparency false in
variable (F) in
theorem fourierMultiplierCLM_sum {g : ι → E → ℂ} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) :
    fourierMultiplierCLM F (∑ i ∈ s, g i ·) = ∑ i ∈ s, fourierMultiplierCLM F (g i) := by
  ext f u
  simp [SchwartzMap.smulLeftCLM_sum hg]

section embedding

variable [CompleteSpace F]

set_option backward.isDefEq.respectTransparency false in
theorem fourierMultiplierCLM_toTemperedDistributionCLM_eq {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g (f : 𝓢'(E, F)) = SchwartzMap.fourierMultiplierCLM F g f := by
  ext u
  simp [SchwartzMap.integral_fourier_smul_eq, SchwartzMap.fourierMultiplierCLM_apply g f,
    ← SchwartzMap.integral_fourierInv_smul_eq, hg, smul_smul, mul_comm]

end embedding

open LineDeriv Real

theorem lineDeriv_eq_fourierMultiplierCLM (m : E) (f : 𝓢'(E, F)) :
    ∂_{m} f = (2 * π * Complex.I) • fourierMultiplierCLM F (inner ℝ · m) f := by
  rw [fourierMultiplierCLM_apply, ← FourierTransform.fourierInv_smul, ← fourier_lineDerivOp_eq,
    FourierTransform.fourierInv_fourier_eq]

open Laplacian

set_option backward.isDefEq.respectTransparency false in
theorem laplacian_eq_fourierMultiplierCLM (f : 𝓢'(E, F)) :
    Δ f = -(2 * π) ^ 2 • fourierMultiplierCLM F (fun x ↦ Complex.ofReal (‖x‖ ^ 2)) f := by
  let ι := Fin (Module.finrank ℝ E)
  let b := stdOrthonormalBasis ℝ E
  have : ∀ i (hi : i ∈ Finset.univ),
      (fun x ↦ Complex.ofReal (inner ℝ x (b i)) ^ 2).HasTemperateGrowth := by
    fun_prop
  simp_rw [laplacian_eq_sum b, ← b.sum_sq_inner_left, Complex.ofReal_sum, Complex.ofReal_pow,
    fourierMultiplierCLM_sum F this, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    Finset.smul_sum]
  congr 1
  ext i x
  simp_rw [lineDeriv_eq_fourierMultiplierCLM, map_smul, smul_smul]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop),
    ← Complex.coe_smul (-(2 * π) ^ 2)]
  congr 4
  · ring_nf
    simp
  · simp [sq, Pi.mul_def]

end TemperedDistribution
