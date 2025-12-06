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

* `SchwartzMap.toLp_fourierTransform_eq`: The Fourier transform on `𝓢(V, E)` agrees with the Fourier
transform on `L2`.

-/

@[expose] public section

noncomputable section

section FourierTransform

variable
  {V E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

open SchwartzMap MeasureTheory FourierTransform ComplexInnerProductSpace

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable (V E) in
/-- The Fourier transform on `L2` as a linear isometry equivalence. -/
def Lp.fourierTransformLI : (Lp (α := V) E 2) ≃ₗᵢ[ℂ] (Lp (α := V) E 2) :=
  (SchwartzMap.fourierTransformCLE ℂ (V := V) (E := E)).toLinearEquiv.extendOfIsometry
    (SchwartzMap.toLpCLM ℂ (E := V) E 2) (SchwartzMap.toLpCLM ℂ (E := V) E 2)
    (by apply SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top)
    (by apply SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top)
    (by apply norm_fourier_toL2_eq) -- omitting `by apply` causes time-outs

instance Lp.instFourierTransform : FourierTransform (Lp (α := V) E 2) (Lp (α := V) E 2) where
  fourier := fourierTransformLI V E

instance Lp.instFourierTransformInv : FourierTransformInv (Lp (α := V) E 2) (Lp (α := V) E 2) where
  fourierInv := (fourierTransformLI V E).symm

instance Lp.instFourierPair : FourierPair (Lp (α := V) E 2) (Lp (α := V) E 2) where
  fourierInv_fourier_eq := (Lp.fourierTransformLI V E).symm_apply_apply

instance Lp.instFourierPairInv : FourierInvPair (Lp (α := V) E 2) (Lp (α := V) E 2) where
  fourier_fourierInv_eq := (Lp.fourierTransformLI V E).apply_symm_apply

/-- Plancherel's theorem for `L^2` functions. -/
@[simp]
theorem Lp.norm_fourier_eq (f : Lp (α := V) E 2) : ‖𝓕 f‖ = ‖f‖ :=
  (Lp.fourierTransformLI V E).norm_map f

@[simp]
theorem Lp.inner_fourier_eq (f g : Lp (α := V) E 2) : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ :=
  (Lp.fourierTransformLI V E).inner_map_map f g

@[simp]
theorem SchwartzMap.toLp_fourierTransform_eq (f : 𝓢(V, E)) : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2 := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  exact (norm_fourier_toL2_eq f).le

@[simp]
theorem SchwartzMap.toLp_fourierTransformInv_eq (f : 𝓢(V, E)) : 𝓕⁻ (f.toLp 2) = (𝓕⁻ f).toLp 2 := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  convert (norm_fourier_toL2_eq (𝓕⁻ f)).symm.le
  simp

end FourierTransform
