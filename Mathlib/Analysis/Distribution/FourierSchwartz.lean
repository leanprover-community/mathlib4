/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Fourier transform on Schwartz functions

This file will construct the Fourier transform as a continuous linear map acting on Schwartz
functions.

For now, it only contains the fact that the Fourier transform of a Schwartz function is
differentiable, with an explicit derivative given by a Fourier transform. See
`SchwartzMap.hasFDerivAt_fourier`.
-/

open Real Complex TopologicalSpace SchwartzMap MeasureTheory MeasureTheory.Measure VectorFourier

noncomputable section

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (L : D →L[ℝ] E →L[ℝ] ℝ)

/-- Multiplication by a linear map on Schwartz space: for `f : D → V` a Schwartz function and `L` a
bilinear map from `D × E` to `ℝ`, we define a new Schwartz function on `D` taking values in the
space of linear maps from `E` to `V`, given by
`(VectorFourier.fourierSMulRightSchwartz L f) (v) = -(2 * π * I) • L (v, ⬝) • f v`.
The point of this definition is that the derivative of the Fourier transform of `f` is the
Fourier transform of `VectorFourier.fourierSMulRightSchwartz L f`. -/
def VectorFourier.fourierSMulRightSchwartz : 𝓢(D, V) →L[ℝ] 𝓢(D, E →L[ℝ] V) :=
  -(2 * π * I) • (bilinLeftCLM (ContinuousLinearMap.smulRightL ℝ E V).flip L.hasTemperateGrowth)

@[simp]
lemma VectorFourier.fourierSMulRightSchwartz_apply (f : 𝓢(D, V)) (d : D) :
    VectorFourier.fourierSMulRightSchwartz L f d = -(2 * π * I) • (L d).smulRight (f d) := rfl

/-- The Fourier transform of a Schwartz map `f` has a Fréchet derivative (everywhere in its domain)
and its derivative is the Fourier transform of the Schwartz map `mul_L_schwartz L f`. -/
theorem SchwartzMap.hasFDerivAt_fourierIntegral [MeasurableSpace D] [BorelSpace D]
    {μ : Measure D} [SecondCountableTopology D] [HasTemperateGrowth μ] (f : 𝓢(D, V)) (w : E) :
    HasFDerivAt (fourierIntegral fourierChar μ L.toLinearMap₂ f)
      (fourierIntegral fourierChar μ L.toLinearMap₂ (fourierSMulRightSchwartz L f) w) w :=
  VectorFourier.hasFDerivAt_fourierIntegral L f.integrable
    (by simpa using f.integrable_pow_mul μ 1) w
