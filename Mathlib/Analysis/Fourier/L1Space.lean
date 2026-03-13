/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public noncomputable section

section FourierTransform

variable {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

open SchwartzMap MeasureTheory FourierTransform ComplexInnerProductSpace

open scoped ZeroAtInfty Filter Topology BoundedContinuousFunction

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable [CompleteSpace E]

variable (V E) in
/-- The Fourier transform on `L1` as a linear isometry equivalence. -/
def Lp.fourierTransformZeroAtInftyCLM : (Lp (α := V) E 1) →L[ℂ] C₀(V, E) :=
  (toZeroAtInftyCLM ℂ V E ∘L (fourierCLM ℂ 𝓢(V, E))).toLinearMap.extendOfNorm
    (toLpCLM ℂ (E := V) E 1)

@[simp]
theorem Lp.fourierTransformZeroAtInftyCLM_toLp_apply (f : 𝓢(V, E)) (x : V) :
    Lp.fourierTransformZeroAtInftyCLM V E (f.toLp 1) x = 𝓕 f x := by
  calc
    _ = ((fourierTransformZeroAtInftyCLM V E) (toLpCLM ℂ (E := V) E 1 volume f)) x := by simp
    _ = (toZeroAtInftyCLM ℂ V E ∘L (fourierCLM ℂ 𝓢(V, E))) f x := by
      congr 1
      apply LinearMap.extendOfNorm_eq
      · apply SchwartzMap.denseRange_toLpCLM
        norm_num
      use 1
      simpa using norm_fourier_toBoundedContinuousFunction_le_toLp_one
    _ = 𝓕 f x := by simp

theorem Lp.fourierTransformZeroAtInftyCLM_toBCF (f : Lp (α := V) E 1) :
    (Lp.fourierTransformZeroAtInftyCLM V E f).toBCF = Real.Lp.fourierTransform f := by
  apply (denseRange_toLpCLM (by norm_num)).induction_on
    (p := fun f ↦ (Lp.fourierTransformZeroAtInftyCLM V E f).toBCF = Real.Lp.fourierTransform f) f
    (isClosed_eq (by fun_prop) (Real.Lp.fourierTransformCLM V E).cont)
  intro f
  ext x
  simpa using Real.fourier_congr_ae (coeFn_toLp f 1 volume).symm x

theorem Lp.fourierTransformZeroAtInftyCLM_apply_apply (f : Lp (α := V) E 1) (x : V) :
    Lp.fourierTransformZeroAtInftyCLM V E f x = 𝓕 (f : V → E) x := by
  rw [← ZeroAtInftyContinuousMap.toBCF_apply, Lp.fourierTransformZeroAtInftyCLM_toBCF]
  simp

theorem riemann_lebesgue (f : V → E) (hf : MemLp f 1) :
    Filter.Tendsto (𝓕 f) (Filter.cocompact V) (𝓝 0) := by
  rw [← Real.fourierTransform_toLp hf, ← Lp.fourierTransformZeroAtInftyCLM_toBCF]
  apply zero_at_infty ((Lp.fourierTransformZeroAtInftyCLM V E) (hf.toLp f))

variable (V E) in
/-- The inverse Fourier transform on `L1` as a linear isometry equivalence. -/
def Lp.fourierTransformInvZeroAtInftyCLM : (Lp (α := V) E 1) →L[ℂ] C₀(V, E) :=
  (toZeroAtInftyCLM ℂ V E ∘L (fourierInvCLM ℂ 𝓢(V, E))).toLinearMap.extendOfNorm
    (toLpCLM ℂ (E := V) E 1)
