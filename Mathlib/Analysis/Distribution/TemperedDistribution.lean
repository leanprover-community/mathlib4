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

* `TemperedDistribution E F`: The space `𝓢(E, ℂ) →L[ℂ] F` equipped with the pointwise
convergence topology.
* `MeasureTheory.Measure.toTemperedDistribution`: Every measure of temperate growth is a tempered
distribution.
* `TemperedDistribution.fourierTransformCLM`: The Fourier transform on tempered distributions.

## Notation
* `𝓢'(E, F)`: The space of tempered distributions `TemperedDistribution E F` scoped in
`SchwartzMap`
-/

@[expose] public noncomputable section

noncomputable section

open SchwartzMap ContinuousLinearMap

open scoped Nat NNReal ContDiff

variable {E F : Type*}

section definition

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℂ F]

variable (E F) in
/-- The space of tempered distribution is the space of continuous linear maps from the Schwartz to
a normed space, equipped with the topology of pointwise convergence. -/
abbrev TemperedDistribution := 𝓢(E, ℂ) →Lₚₜ[ℂ] F
/- Since mathlib is missing quite a few results that show that continuity of linear maps and
convergence of sequences can be checked for strong duals of Fréchet-Montel spaces pointwise, we
use the pointwise topology for now and not the strong topology. The pointwise topology is
conventially used in PDE texts, but has the downside that it is not barrelled, hence the uniform
boundedness principle does not hold. -/

@[inherit_doc]
scoped[SchwartzMap] notation "𝓢'(" E ", " F ")" => TemperedDistribution E F

end definition

/-! ### Embeddings into tempered distributions -/

section Embeddings

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℂ F]

namespace MeasureTheory.Measure

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]

/-- Every temperate growth measure defines a tempered distribution. -/
def toTemperedDistribution : 𝓢'(E, ℂ) :=
  toPointwiseConvergenceCLM _ _ _ _ (integralCLM ℂ μ)

@[simp]
theorem toTemperedDistribution_apply (g : 𝓢(E, ℂ)) :
    μ.toTemperedDistribution g = ∫ (x : E), g x ∂μ := by
  rfl

end MeasureTheory.Measure

end Embeddings

namespace TemperedDistribution

/-! ### Fourier transform -/

section Fourier

open FourierTransform

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [NormedSpace ℂ F]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable (E F) in
/-- The Fourier transform on tempered distributions as a continuous linear map. -/
def fourierTransformCLM : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.fourierTransformCLM ℂ)

instance instFourierTransform : FourierTransform 𝓢'(E, F) 𝓢'(E, F) where
  fourier := fourierTransformCLM E F

@[simp]
theorem fourierTransformCLM_apply (f : 𝓢'(E, F)) :
  fourierTransformCLM E F f = 𝓕 f := rfl

@[simp]
theorem fourierTransform_apply (f : 𝓢'(E, F)) (g : 𝓢(E, ℂ)) : 𝓕 f g = f (𝓕 g) := rfl

variable (E F) in
/-- The inverse Fourier transform on tempered distributions as a continuous linear map. -/
def fourierTransformInvCLM : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.fourierTransformCLE ℂ).symm.toContinuousLinearMap

instance instFourierTransformInv : FourierTransformInv 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv := fourierTransformInvCLM E F

@[simp]
theorem fourierTransformInvCLM_apply (f : 𝓢'(E, F)) :
    fourierTransformInvCLM E F f = 𝓕⁻ f := rfl

@[simp]
theorem fourierTransformInv_apply (f : 𝓢'(E, F)) (g : 𝓢(E, ℂ)) : 𝓕⁻ f g = f (𝓕⁻ g) := rfl

instance instFourierPair : FourierPair 𝓢'(E, F) 𝓢'(E, F) where
  fourierInv_fourier_eq f := by ext; simp

instance instFourierPairInv : FourierInvPair 𝓢'(E, F) 𝓢'(E, F) where
  fourier_fourierInv_eq f := by ext; simp

end Fourier

end TemperedDistribution
