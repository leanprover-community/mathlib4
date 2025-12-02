/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.FourierSchwartz
public import Mathlib.Analysis.LocallyConvex.PointwiseConvergence

/-!
# TemperedDistribution

## Main definitions

* `TemperedDistribution 𝕜 E F V`: The space `𝓢(E, F) →L[𝕜] V` equipped with the pointwise
convergence topology.
* `MeasureTheory.Measure.toTemperedDistribution`: Every measure of temperate growth is a tempered
distribution.
* `TemperedDistribution.fourierTransformCLM`: The Fourier transform on tempered distributions.

## Notation
* `𝓢'(𝕜, E, F, V)`: The space of tempered distributions `TemperedDistribution 𝕜 E F V` localized
in `SchwartzSpace`
* `𝓢'(E, V)`: A shorthand for `𝓢'(ℂ, E, ℂ, V)`, the most common use-case.
-/

@[expose] public section

noncomputable section

open SchwartzMap ContinuousLinearMap
open MeasureTheory MeasureTheory.Measure

open scoped Nat NNReal ContDiff

variable {α 𝕜 𝕜' H D E F G V W R : Type*}

variable [RCLike 𝕜] [NormedAddCommGroup D] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedAddCommGroup H] [NormedAddCommGroup V] [NormedAddCommGroup W]

section definition

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable (𝕜 E F V)

/-- A tempered distribution is a continuous linear map from the Schwartz to -/
abbrev TemperedDistribution := 𝓢(E, F) →Lₚₜ[𝕜] V

scoped[SchwartzMap] notation "𝓢'(" 𝕜 ", " E ", " F ", " V ")" => TemperedDistribution 𝕜 E F V

scoped[SchwartzMap] notation "𝓢'(" E ", " V ")" => TemperedDistribution ℂ E ℂ V

end definition

namespace TemperedDistribution

section Embeddings

section measure

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 V] [NormedSpace 𝕜 F]
variable [MeasurableSpace E] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
variable [BorelSpace E] [SecondCountableTopology E]

variable (𝕜 F μ) in
def MeasureTheory.Measure.toTemperedDistribution : 𝓢'(𝕜, E, F, F) :=
  toPointwiseConvergenceCLM _ _ _ _ (integralCLM 𝕜 μ)

variable (𝕜) in
@[simp]
theorem MeasureTheory.Measure.toTemperedDistribution_apply (g : 𝓢(E, F)) :
    Measure.toTemperedDistribution 𝕜 F μ g = ∫ (x : E), g x ∂μ := by
  rfl

end measure

end Embeddings

section fourier

open FourierTransform

variable
  [NormedSpace ℂ E]
  [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedSpace 𝕜 V]

variable (𝕜 H E V) in
def fourierTransformCLM : 𝓢'(𝕜, H, E, V) →L[𝕜] 𝓢'(𝕜, H, E, V) :=
  PointwiseConvergenceCLM.precomp V (SchwartzMap.fourierTransformCLM 𝕜)

instance instFourierTransform : FourierTransform 𝓢'(𝕜, H, E, V) 𝓢'(𝕜, H, E, V) where
  fourier := fourierTransformCLM 𝕜 H E V

@[simp]
theorem fourierTransformCLM_apply (f : 𝓢'(𝕜, H, E, V)) :
    fourierTransformCLM 𝕜 H E V f = 𝓕 f := rfl

@[simp]
theorem fourierTransform_apply (f : 𝓢'(𝕜, H, E, V)) (g : 𝓢(H, E)) : 𝓕 f g = f (𝓕 g) := rfl

variable [CompleteSpace E]

variable (𝕜 H E V) in
def fourierTransformInvCLM : 𝓢'(𝕜, H, E, V) →L[𝕜] 𝓢'(𝕜, H, E, V) :=
  PointwiseConvergenceCLM.precomp V (SchwartzMap.fourierTransformCLE 𝕜).symm.toContinuousLinearMap

instance instFourierTransformInv : FourierTransformInv 𝓢'(𝕜, H, E, V) 𝓢'(𝕜, H, E, V) where
  fourierInv := fourierTransformInvCLM 𝕜 H E V

@[simp]
theorem fourierTransformInvCLM_apply (f : 𝓢'(𝕜, H, E, V)) :
    fourierTransformInvCLM 𝕜 H E V f = 𝓕⁻ f := rfl

@[simp]
theorem fourierTransformInv_apply (f : 𝓢'(𝕜, H, E, V)) (g : 𝓢(H, E)) : 𝓕⁻ f g = f (𝓕⁻ g) := rfl

instance instFourierPair : FourierPair 𝓢'(𝕜, H, E, V) 𝓢'(𝕜, H, E, V) where
  fourierInv_fourier_eq f := by ext; simp

instance instFourierPairInv : FourierInvPair 𝓢'(𝕜, H, E, V) 𝓢'(𝕜, H, E, V) where
  fourier_fourierInv_eq f := by ext; simp

end fourier

end TemperedDistribution
