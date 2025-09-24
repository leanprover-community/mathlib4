/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.InnerProductSpace.Extend
import Mathlib.Analysis.Distribution.FourierSchwartz

/-!

# The Fourier transform on L^2

-/

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

open SchwartzMap MeasureTheory

variable (f : 𝓢(V, E)) (g : MeasureTheory.Lp (α := V) E 2)

noncomputable
def fourierTransform : (MeasureTheory.Lp (α := V) E 2) ≃ₗᵢ[ℂ] (MeasureTheory.Lp (α := V) E 2) :=
  (SchwartzMap.fourierTransformCLE ℂ (V := V) (E := E)).toLinearEquiv.extendOfIsometry
    (SchwartzMap.toLpCLM ℂ (E := V) E 2) (SchwartzMap.toLpCLM ℂ (E := V) E 2)
    (LinearMap.ker_eq_bot_of_injective (injective_toLp _ _)) sorry
    (by apply norm_fourierTransform_toL2_eq)
    (LinearMap.ker_eq_bot_of_injective (injective_toLp _ _)) sorry
    (by
      intro f
      convert (norm_fourierTransform_toL2_eq f.fourierTransformInv).symm
      simp)

@[simp]
theorem toLp_fourierTransform_eq (f : 𝓢(V, E)) :
    fourierTransform (f.toLp 2) = f.fourierTransform.toLp 2 := by
  apply LinearMap.extendOfNorm_eq (LinearMap.ker_eq_bot_of_injective (injective_toLp _ _))
  · sorry
  use 1
  intro f
  rw [one_mul]
  exact (norm_fourierTransform_toL2_eq f).le

@[simp]
theorem toLp_fourierTransform_symm_eq (f : 𝓢(V, E)) :
    fourierTransform.symm (f.toLp 2) = f.fourierTransformInv.toLp 2 := by
  apply LinearMap.extendOfNorm_eq (LinearMap.ker_eq_bot_of_injective (injective_toLp _ _))
  · sorry
  use 1
  intro f
  rw [one_mul]
  convert (norm_fourierTransform_toL2_eq f.fourierTransformInv).symm.le
  simp
