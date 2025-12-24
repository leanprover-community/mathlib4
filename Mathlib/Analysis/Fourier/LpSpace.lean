/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.FourierSchwartz
public import Mathlib.Analysis.Normed.Operator.Extend

/-!

# The Fourier transform on $L^p$

In this file we define the Fourier transform on $L^2$ as a linear isometry equivalence.

## Main definitions

* `Lp.fourierTransformₗᵢ`: The Fourier transform on $L^2$ as a linear isometry equivalence.

## Main statements

* `SchwartzMap.toLp_fourierTransform_eq`: The Fourier transform on `𝓢(E, F)` agrees with the Fourier
  transform on $L^2$.

-/

@[expose] public section

noncomputable section

section FourierTransform

variable {E F : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open SchwartzMap MeasureTheory FourierTransform ComplexInnerProductSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace MeasureTheory.Lp

variable (E F) in
/-- The Fourier transform on `L2` as a linear isometry equivalence. -/
def fourierTransformₗᵢ : (Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2) :=
  (fourierTransformCLE ℂ (V := E) (E := F)).toLinearEquiv.extendOfIsometry
    (toLpCLM ℂ (E := E) F 2 volume) (toLpCLM ℂ (E := E) F 2 volume)
    -- Not explicitly stating the measure as being the volume causes time-outs in the proofs below
    (denseRange_toLpCLM ENNReal.ofNat_ne_top) (denseRange_toLpCLM ENNReal.ofNat_ne_top)
    norm_fourier_toL2_eq

instance instFourierTransform : FourierTransform (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier := fourierTransformₗᵢ E F

instance instFourierTransformInv : FourierTransformInv (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv := (fourierTransformₗᵢ E F).symm

instance instFourierPair : FourierPair (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv_fourier_eq := (Lp.fourierTransformₗᵢ E F).symm_apply_apply

instance instFourierPairInv : FourierInvPair (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier_fourierInv_eq := (Lp.fourierTransformₗᵢ E F).apply_symm_apply

/-- Plancherel's theorem for `L2` functions. -/
@[simp]
theorem norm_fourier_eq (f : Lp (α := E) F 2) : ‖𝓕 f‖ = ‖f‖ :=
  (Lp.fourierTransformₗᵢ E F).norm_map f

@[simp]
theorem inner_fourier_eq (f g : Lp (α := E) F 2) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ :=
  (Lp.fourierTransformₗᵢ E F).inner_map_map f g

end MeasureTheory.Lp

@[simp]
theorem SchwartzMap.toLp_fourierTransform_eq (f : 𝓢(E, F)) : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2 := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  exact (norm_fourier_toL2_eq f).le

@[simp]
theorem SchwartzMap.toLp_fourierTransformInv_eq (f : 𝓢(E, F)) : 𝓕⁻ (f.toLp 2) = (𝓕⁻ f).toLp 2 := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  convert (norm_fourier_toL2_eq (𝓕⁻ f)).symm.le
  simp

end FourierTransform
