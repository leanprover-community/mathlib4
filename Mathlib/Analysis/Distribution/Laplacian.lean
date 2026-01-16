/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-! # The Laplacian on Schwartz functions

We define the Laplacian on Schwartz functions.

## Main definitions

* `LineDeriv.laplacianCLM`: The abstract definition of a Laplacian as a sum over the second
  derivatives.
* `SchwartzMap.instLaplacian`: The Laplacian for `𝓢(E, F)` as an instance of the notation type-class
  `Laplacian`.

## Main statements
* `SchwartzMap.laplacian_eq_sum`: The Laplacian is equal to the sum of second derivatives in any
  orthonormal basis.
* `SchwartzMap.integral_bilinear_laplacian_right_eq_left`: Integration by parts for the Laplacian.

## Implementation notes
The abstract definition `LineDeriv.laplacianCLM` does not provide an instance of `Laplacian` because
the type-class system is not able to infer the inner product space `E`. In order to avoid duplicated
definitions, we do not define `LineDeriv.laplacian` and subsequently every concrete instance of
`LineDeriv` has to provide an instance for `Laplacian` and a proof that
`LineDeriv.laplacianCLM _ _ _ f = Δ f`, for example see `SchwartzMap.laplacianCLM_eq'` and
`SchwartzMap.laplacian_eq_sum'` below.

We also note that since `LineDeriv` merely notation and not tied to `fderiv`, it is not possible to
prove the independence of the basis in the definition of the Laplacian in the abstract setting.
In the case of sufficiently smooth functions, this follows from an equality of `lineDerivOp` and
`fderiv`, see for example `SchwartzMap.coe_laplacian_eq_sum`, and in the case of distributions, this
follows from duality. Therefore, when implementing `Laplacian` using `LineDeriv.laplacianCLM`, you
should prove a version of `SchwartzMap.laplacian_eq_sum`.

-/

@[expose] public noncomputable section

variable {ι ι' 𝕜 R E F F₁ F₂ F₃ V₁ V₂ V₃ : Type*}

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F]

namespace SchwartzMap

/-! ## Laplacian on `𝓢(E, F)` -/

variable [NormedSpace ℝ F]

open Laplacian LineDeriv

instance instLaplacian : Laplacian 𝓢(E, F) 𝓢(E, F) where
  laplacian := laplacianCLM ℝ E 𝓢(E, F)

theorem laplacianCLM_eq' (f : 𝓢(E, F)) : laplacianCLM ℝ E 𝓢(E, F) f = Δ f := rfl

theorem laplacian_eq_sum [Fintype ι] (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, F)) :
    Δ f = ∑ i, ∂_{b i} (∂_{b i} f) :=
  LineDeriv.laplacianCLM_eq_sum b f

variable (𝕜) in
@[simp]
theorem laplacianCLM_eq [RCLike 𝕜] [NormedSpace 𝕜 F] (f : 𝓢(E, F)) :
    laplacianCLM 𝕜 E 𝓢(E, F) f = Δ f := by
  simp [laplacianCLM, laplacian_eq_sum (stdOrthonormalBasis ℝ E)]

theorem laplacian_apply (f : 𝓢(E, F)) (x : E) : Δ f x = Δ (f : E → F) x := by
  rw [laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (stdOrthonormalBasis ℝ E), sum_apply]
  congr 1
  ext i
  rw [← iteratedLineDerivOp_eq_iteratedFDeriv]
  rfl

open MeasureTheory

/-! ### Integration by parts -/

variable
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  [MeasurableSpace E] {μ : Measure E} [BorelSpace E] [μ.IsAddHaarMeasure]

/-- Integration by parts of Schwartz functions for the Laplacian.

Version for a general bilinear map. -/
theorem integral_bilinear_laplacian_right_eq_left (f : 𝓢(E, F₁)) (g : 𝓢(E, F₂))
    (L : F₁ →L[ℝ] F₂ →L[ℝ] F₃) :
    ∫ x, L (f x) (Δ g x) ∂μ = ∫ x, L (Δ f x) (g x) ∂μ := by
  simp_rw [laplacian_eq_sum (stdOrthonormalBasis ℝ E), sum_apply, map_sum,
    ContinuousLinearMap.coe_sum', Finset.sum_apply]
  rw [MeasureTheory.integral_finset_sum, MeasureTheory.integral_finset_sum]
  · simp [integral_bilinear_lineDerivOp_right_eq_neg_left]
  · exact fun _ _ ↦ (pairing L (∂_{_} <| ∂_{_} f) g).integrable
  · exact fun _ _ ↦ (pairing L f (∂_{_} <| ∂_{_} g)).integrable

variable [NormedRing 𝕜] [NormedSpace ℝ 𝕜] [IsScalarTower ℝ 𝕜 𝕜] [SMulCommClass ℝ 𝕜 𝕜] in
/-- Integration by parts of Schwartz functions for the Laplacian.

Version for multiplication of scalar-valued Schwartz functions. -/
theorem integral_mul_laplacian_right_eq_left (f : 𝓢(E, 𝕜)) (g : 𝓢(E, 𝕜)) :
    ∫ x, f x * Δ g x ∂μ = ∫ x, Δ f x * g x ∂μ :=
  integral_bilinear_laplacian_right_eq_left f g (ContinuousLinearMap.mul ℝ 𝕜)

variable [RCLike 𝕜] [NormedSpace 𝕜 F]

/-- Integration by parts of Schwartz functions for the Laplacian.

Version for scalar multiplication. -/
theorem integral_smul_laplacian_right_eq_left (f : 𝓢(E, 𝕜)) (g : 𝓢(E, F)) :
    ∫ x, f x • Δ g x ∂μ = ∫ x, Δ f x • g x ∂μ :=
  integral_bilinear_laplacian_right_eq_left f g (ContinuousLinearMap.lsmul ℝ 𝕜)

variable [NormedSpace 𝕜 F₁] [NormedSpace 𝕜 F₂]

/-- Integration by parts of Schwartz functions for the Laplacian.

Version for a Schwartz function with values in continuous linear maps. -/
theorem integral_clm_comp_laplacian_right_eq_left (f : 𝓢(E, F₁ →L[𝕜] F₂)) (g : 𝓢(E, F₁)) :
    ∫ x, f x (Δ g x) ∂μ = ∫ x, Δ f x (g x) ∂μ :=
  integral_bilinear_laplacian_right_eq_left f g
    ((ContinuousLinearMap.id 𝕜 (F₁ →L[𝕜] F₂)).bilinearRestrictScalars ℝ)

end SchwartzMap
