/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!

# The Fourier transform on $L^p$

In this file we define the Fourier transform on $L^2$ as a linear isometry equivalence.

## Main definitions

* `MeasureTheory.Lp.fourierTransformₗᵢ`: The Fourier transform on $L^2$ as a linear isometry
  equivalence.
* `MeasureTheory.Lp.fourierTransformZeroAtInftyCLM`: The Fourier transform from $L^2$ to $C_0$ as a
  continuous linear map.

## Main statements

* `SchwartzMap.toLp_fourier_eq`: The Fourier transform on `𝓢(E, F)` agrees with the Fourier
  transform on $L^2$.
* `MeasureTheory.Lp.fourier_toTemperedDistribution_eq`: The Fourier transform on $L^2$ agrees with
  the Fourier transform on `𝓢'(E, F)`.

-/

@[expose] public section

noncomputable section

variable {E F : Type*}

section L2Space

variable
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

open SchwartzMap MeasureTheory FourierTransform

open scoped ComplexInnerProductSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace MeasureTheory.Lp

variable (E F) in
/-- The Fourier transform on `L2` as a linear isometry equivalence. -/
@[wikidata Q6520159]
def fourierTransformₗᵢ : (Lp (α := E) F 2) ≃ₗᵢ[ℂ] (Lp (α := E) F 2) :=
  (fourierEquiv ℂ 𝓢(E, F)).extendOfIsometry
    (toLpCLM ℂ (E := E) F 2 volume) (toLpCLM ℂ (E := E) F 2 volume)
    -- Not explicitly stating the measure as being the volume causes time-outs in the proofs below
    (denseRange_toLpCLM ENNReal.ofNat_ne_top) (denseRange_toLpCLM ENNReal.ofNat_ne_top)
    norm_fourier_toL2_eq

instance instFourierTransform : FourierTransform (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier := fourierTransformₗᵢ E F

instance instFourierAdd : FourierAdd (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier_add := (fourierTransformₗᵢ E F).map_add

instance instFourierSMul : FourierSMul ℂ (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourier_smul := (fourierTransformₗᵢ E F).map_smul

instance instContinuousFourier : ContinuousFourier (Lp (α := E) F 2) (Lp (α := E) F 2) where
  continuous_fourier := (fourierTransformₗᵢ E F).continuous

instance instFourierTransformInv : FourierTransformInv (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv := (fourierTransformₗᵢ E F).symm

instance instFourierInvAdd : FourierInvAdd (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv_add := (fourierTransformₗᵢ E F).symm.map_add

instance instFourierInvSMul : FourierInvSMul ℂ (Lp (α := E) F 2) (Lp (α := E) F 2) where
  fourierInv_smul := (fourierTransformₗᵢ E F).symm.map_smul

instance instContinuousFourierInv : ContinuousFourierInv (Lp (α := E) F 2) (Lp (α := E) F 2) where
  continuous_fourierInv := (fourierTransformₗᵢ E F).symm.continuous

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
theorem SchwartzMap.toLp_fourier_eq (f : 𝓢(E, F)) : 𝓕 (f.toLp 2) = (𝓕 f).toLp 2 := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  exact (norm_fourier_toL2_eq f).le

@[simp]
theorem SchwartzMap.toLp_fourierInv_eq (f : 𝓢(E, F)) : 𝓕⁻ (f.toLp 2) = (𝓕⁻ f).toLp 2 := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  use 1
  intro f
  rw [one_mul]
  convert! (norm_fourier_toL2_eq (𝓕⁻ f)).symm.le
  simp

namespace MeasureTheory.Lp

/-- The `𝓢'`-Fourier transform and the `L2`-Fourier transform coincide on `L2`. -/
theorem fourier_toTemperedDistribution_eq (f : Lp (α := E) F 2) :
    𝓕 (f : 𝓢'(E, F)) = (𝓕 f : Lp (α := E) F 2) := by
  set p := fun f : Lp (α := E) F 2 ↦ 𝓕 (f : 𝓢'(E, F)) = (𝓕 f : Lp (α := E) F 2)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (fourierCLM ℂ 𝓢'(E, F) ∘L toTemperedDistributionCLM F volume 2).continuous
    · exact (toTemperedDistributionCLM F volume 2 ∘L fourierCLM ℂ (Lp (α := E) F 2)).continuous
  intro f
  simp [p, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]

/-- The `𝓢'`-inverse Fourier transform and the `L2`-inverse Fourier transform coincide on `L2`. -/
theorem fourierInv_toTemperedDistribution_eq (f : Lp (α := E) F 2) :
    𝓕⁻ (f : 𝓢'(E, F)) = (𝓕⁻ f : Lp (α := E) F 2) := calc
  _ = 𝓕⁻ (Lp.toTemperedDistribution (𝓕 (𝓕⁻ f))) := by
    congr; exact (fourier_fourierInv_eq f).symm
  _ = 𝓕⁻ (𝓕 (Lp.toTemperedDistribution (𝓕⁻ f))) := by
    rw [fourier_toTemperedDistribution_eq]
  _ = _ := fourierInv_fourier_eq _

end MeasureTheory.Lp

end L2Space

section L1Space

namespace MeasureTheory.Lp

open SchwartzMap MeasureTheory FourierTransform

open scoped ZeroAtInfty

variable
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable (E F) in
/-- The Fourier transform from `L1` to `C₀` as a continuous linear map.

This is the bundled version of the Riemann-Lebesgue lemma. -/
def fourierTransformZeroAtInftyCLM : (Lp (α := E) F 1) →L[ℂ] C₀(E, F) :=
  (toZeroAtInftyCLM ℂ E F ∘L (fourierCLM ℂ 𝓢(E, F))).toLinearMap.extendOfNorm
    (toLpCLM ℂ (E := E) F 1)

@[simp]
theorem fourierTransformZeroAtInftyCLM_toLp_apply (f : 𝓢(E, F)) (x : E) :
    fourierTransformZeroAtInftyCLM E F (f.toLp 1) x = 𝓕 f x := by
  calc
    _ = ((fourierTransformZeroAtInftyCLM E F) (toLpCLM ℂ (E := E) F 1 volume f)) x := by simp
    _ = (toZeroAtInftyCLM ℂ E F ∘L (fourierCLM ℂ 𝓢(E, F))) f x := by
      congr 1
      apply LinearMap.extendOfNorm_eq
      · apply SchwartzMap.denseRange_toLpCLM
        norm_num
      use 1
      simpa using norm_fourier_toBoundedContinuousFunction_le_toLp_one
    _ = 𝓕 f x := by simp

@[simp]
theorem fourierTransformZeroAtInftyCLM_toBCF (f : Lp (α := E) F 1) :
    (fourierTransformZeroAtInftyCLM E F f).toBCF = Real.Lp.fourierTransform f := by
  apply (denseRange_toLpCLM (by norm_num)).induction_on
    (p := fun f ↦ (Lp.fourierTransformZeroAtInftyCLM E F f).toBCF = Real.Lp.fourierTransform f) f
    (isClosed_eq (by fun_prop) (Real.Lp.fourierTransformCLM E F).cont)
  intro f
  ext x
  simpa using Real.fourier_congr_ae (coeFn_toLp f 1 volume).symm x

theorem fourierTransformZeroAtInftyCLM_apply_apply (f : Lp (α := E) F 1) (x : E) :
    Lp.fourierTransformZeroAtInftyCLM E F f x = 𝓕 (f : E → F) x := by
  simp [← ZeroAtInftyContinuousMap.toBCF_apply]

end MeasureTheory.Lp

end L1Space
