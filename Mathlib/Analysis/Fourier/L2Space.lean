/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.InnerProductSpace.Extend
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.Distribution.DenseLp
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!

# The Fourier transform on L^2

-/

variable
  {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup V]
  [MeasurableSpace V] [BorelSpace V]

open SchwartzMap MeasureTheory

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable (f : 𝓢(V, E)) (g : Lp (α := V) E 2 volume)

variable (V E) in
noncomputable
def Lp.fourierTransformLI : (Lp (α := V) E 2) ≃ₗᵢ[ℂ] (Lp (α := V) E 2) :=
  (SchwartzMap.fourierTransformCLE ℂ (V := V) (E := E)).toLinearEquiv.extendOfIsometry
    (SchwartzMap.toLpCLM ℂ (E := V) E 2) (SchwartzMap.toLpCLM ℂ (E := V) E 2)
    (LinearMap.ker_eq_bot_of_injective (injective_toLp _ _)) (by
        apply SchwartzMap.denseRange_toLpCLM
        exact Ne.symm ENNReal.top_ne_ofNat)
    (by apply norm_fourierTransform_toL2_eq)
    (LinearMap.ker_eq_bot_of_injective (injective_toLp _ _)) (by
        apply SchwartzMap.denseRange_toLpCLM
        exact Ne.symm ENNReal.top_ne_ofNat)
    (by
      intro f
      convert (norm_fourierTransform_toL2_eq f.fourierTransformInv).symm
      simp)

noncomputable
def Lp.fourierTransform (f : Lp (α := V) E 2) : Lp (α := V) E 2 := fourierTransformLI V E f

@[simp]
theorem toLp_fourierTransform_eq (f : 𝓢(V, E)) :
    Lp.fourierTransform (f.toLp 2) = f.fourierTransform.toLp 2 := by
  apply LinearMap.extendOfNorm_eq (LinearMap.ker_eq_bot_of_injective (injective_toLp _ _))
  · apply SchwartzMap.denseRange_toLpCLM
    exact Ne.symm ENNReal.top_ne_ofNat
  use 1
  intro f
  rw [one_mul]
  exact (norm_fourierTransform_toL2_eq f).le

@[simp]
theorem toLp_fourierTransform_symm_eq (f : 𝓢(V, E)) :
    (Lp.fourierTransformLI V E).symm (f.toLp 2) = f.fourierTransformInv.toLp 2 := by
  apply LinearMap.extendOfNorm_eq (LinearMap.ker_eq_bot_of_injective (injective_toLp _ _))
  · apply SchwartzMap.denseRange_toLpCLM
    exact Ne.symm ENNReal.top_ne_ofNat
  use 1
  intro f
  rw [one_mul]
  convert (norm_fourierTransform_toL2_eq f.fourierTransformInv).symm.le
  simp



variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Fourier transform on `L^2` coincides with the Fourier transform on `𝓢'`. -/
theorem foo (f : Lp (α := V) E 2) :
    TemperedDistribution.fourierTransform (Lp.toTemperedDistribution ℂ F f) =
      (Lp.toTemperedDistribution ℂ F (Lp.fourierTransform f)) := by
  set p := fun f : Lp (α := V) E 2 ↦
    TemperedDistribution.fourierTransform (Lp.toTemperedDistribution ℂ F f) =
      (Lp.toTemperedDistribution ℂ F (Lp.fourierTransform f))
  apply DenseRange.induction_on (p := p)
    ( SchwartzMap.denseRange_toLpCLM (F := E) (E := V) (μ := volume) (p := 2)
      (Ne.symm ENNReal.top_ne_ofNat)) f
  · apply isClosed_eq
    · exact ((TemperedDistribution.fourierTransformCLM ℂ V _ F) ∘L
        (Lp.toTemperedDistributionCLM ℂ E F volume 2)).cont
    · exact (Lp.toTemperedDistributionCLM ℂ E F volume 2).cont.comp
        (Lp.fourierTransformLI V E).continuous
  intro f
  unfold p
  simp [TemperedDistribution.fourierTransformCLM_toTemperedDistributionCLM_eq]
