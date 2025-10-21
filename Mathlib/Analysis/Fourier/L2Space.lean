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

section FourierTransform

variable
  {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

open SchwartzMap MeasureTheory FourierTransform

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

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
      convert (norm_fourierTransform_toL2_eq (𝓕⁻ f)).symm
      simp)

noncomputable
instance Lp.instFourierTransform : FourierTransform (Lp (α := V) E 2) (Lp (α := V) E 2) where
  fourierTransform := fourierTransformLI V E

noncomputable
instance Lp.instFourierTransformInv : FourierTransformInv (Lp (α := V) E 2) (Lp (α := V) E 2) where
  fourierTransformInv := (fourierTransformLI V E).symm

noncomputable
instance instFourierPair : FourierPair (Lp (α := V) E 2) (Lp (α := V) E 2) where
  inv_fourier := (Lp.fourierTransformLI V E).symm_apply_apply

noncomputable
instance instFourierPairInv : FourierPairInv (Lp (α := V) E 2) (Lp (α := V) E 2) where
  fourier_inv := (Lp.fourierTransformLI V E).apply_symm_apply

@[simp]
theorem toLp_fourierTransform_eq (f : 𝓢(V, E)) : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2 := by
  apply LinearMap.extendOfNorm_eq (LinearMap.ker_eq_bot_of_injective (injective_toLp _ _))
  · apply SchwartzMap.denseRange_toLpCLM
    exact Ne.symm ENNReal.top_ne_ofNat
  use 1
  intro f
  rw [one_mul]
  exact (norm_fourierTransform_toL2_eq f).le

@[simp]
theorem toLp_fourierTransformInv_eq (f : 𝓢(V, E)) : 𝓕⁻ (f.toLp 2) = (𝓕⁻ f).toLp 2 := by
  apply LinearMap.extendOfNorm_eq (LinearMap.ker_eq_bot_of_injective (injective_toLp _ _))
  · apply SchwartzMap.denseRange_toLpCLM
    exact Ne.symm ENNReal.top_ne_ofNat
  use 1
  intro f
  rw [one_mul]
  convert (norm_fourierTransform_toL2_eq (𝓕⁻ f)).symm.le
  simp


end FourierTransform


variable {E F V : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

open SchwartzMap MeasureTheory FourierTransform

variable (V) in
/-- The Fourier transform on `L^2` coincides with the Fourier transform on `𝓢'`. -/
theorem toTemperedDistribution_fourierTransform_eq (f : Lp (α := E) F 2) :
    𝓕 (f : 𝓢'(ℂ, E, F →L[ℂ] V, V)) = (𝓕 f : Lp (α := E) F 2) := by
  set p := fun f : Lp (α := E) F 2 ↦
    𝓕 (Lp.toTemperedDistribution ℂ V f) =
      (Lp.toTemperedDistribution ℂ V (𝓕 f))
  apply DenseRange.induction_on (p := p)
    ( SchwartzMap.denseRange_toLpCLM (F := F) (E := E) (μ := volume) (p := 2)
      (Ne.symm ENNReal.top_ne_ofNat)) f
  · apply isClosed_eq
    · exact ((TemperedDistribution.fourierTransformCLM ℂ E _ V) ∘L
        (Lp.toTemperedDistributionCLM ℂ F V volume 2)).cont
    · exact (Lp.toTemperedDistributionCLM ℂ F V volume 2).cont.comp
        (Lp.fourierTransformLI E F).continuous
  intro f
  unfold p
  simp [TemperedDistribution.fourierTransformCLM_toTemperedDistributionCLM_eq]

variable (V) in
theorem toTemperedDistribution_fourierTransformInv_eq (f : Lp (α := E) F 2) :
    𝓕⁻ (f : 𝓢'(ℂ, E, F →L[ℂ] V, V)) = (𝓕⁻ f : Lp (α := E) F 2) := by
  have := toTemperedDistribution_fourierTransform_eq V (𝓕⁻ f)
  apply_fun 𝓕⁻ at this
  simp only [FourierPair.inv_fourier, FourierPairInv.fourier_inv] at this
  exact this.symm
