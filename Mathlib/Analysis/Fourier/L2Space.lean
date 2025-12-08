/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.FourierSchwartz
public import Mathlib.Analysis.Normed.Operator.Extend

/-!

# The Fourier transform on L^2

In this file we define the Fourier transform on `L2` as a linear isometry equivalence.

## Main definitions

* `Lp.fourierTransformLI`: The Fourier transform on `L2` as a linear isometry equivalence.

## Main statements

* `SchwartzMap.toLp_fourierTransform_eq`: The Fourier transform on `𝓢(E, F)` agrees with the Fourier
transform on `L2`.

-/

@[expose] public section

noncomputable section

section FourierTransform

variable
  {E F : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open SchwartzMap MeasureTheory FourierTransform ComplexInnerProductSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable (E F) in
/-- The Fourier transform on `L2` as a linear isometry equivalence. -/
def Lp.fourierTransformLI : (Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2) :=
  (SchwartzMap.fourierTransformCLE ℂ (V := E) (E := F)).toLinearEquiv.extendOfIsometry
    (SchwartzMap.toLpCLM ℂ (E := E) F 2) (SchwartzMap.toLpCLM ℂ (E := E) F 2)
    (by apply SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top)
    (by apply SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top)
    (by apply norm_fourier_toL2_eq) -- omitting `by apply` causes time-outs

instance Lp.instFourierTransform : FourierTransform (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier := fourierTransformLI E F

instance Lp.instFourierTransformInv : FourierTransformInv (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv := (fourierTransformLI E F).symm

instance Lp.instFourierPair : FourierPair (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv_fourier_eq := (Lp.fourierTransformLI E F).symm_apply_apply

instance Lp.instFourierPairInv : FourierInvPair (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier_fourierInv_eq := (Lp.fourierTransformLI E F).apply_symm_apply

/-- Plancherel's theorem for `L^2` functions. -/
@[simp]
theorem Lp.norm_fourier_eq (f : Lp (α := E) F 2) : ‖𝓕 f‖ = ‖f‖ :=
  (Lp.fourierTransformLI E F).norm_map f

@[simp]
theorem Lp.inner_fourier_eq (f g : Lp (α := E) F 2) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ :=
  (Lp.fourierTransformLI E F).inner_map_map f g

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
