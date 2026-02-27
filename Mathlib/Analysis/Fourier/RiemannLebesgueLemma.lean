/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.Fourier.L1Space

/-!
# The Riemann-Lebesgue Lemma

In this file we prove the Riemann-Lebesgue lemma, for functions on finite-dimensional real vector
spaces `V`: if `f` is a function on `V` (valued in a complete normed space `E`), then the
Fourier transform of `f`, viewed as a function on the dual space of `V`, tends to 0 along the
cocompact filter. Here the Fourier transform is defined by

`fun w : StrongDual ℝ V ↦ ∫ (v : V), exp (↑(2 * π * w v) * I) • f v`.

This is true for arbitrary functions, but is only interesting for `L¹` functions (if `f` is not
integrable then the integral is zero for all `w`). This is proved first for continuous
compactly-supported functions on inner-product spaces; then we pass to arbitrary functions using the
density of continuous compactly-supported functions in `L¹` space. Finally we generalise from
inner-product spaces to arbitrary finite-dimensional spaces, by choosing a continuous linear
equivalence to an inner-product space.

## Main results

- `tendsto_integral_exp_inner_smul_cocompact` : for `V` a finite-dimensional real inner product
  space and `f : V → E`, the function `fun w : V ↦ ∫ v : V, exp (2 * π * ⟪w, v⟫ * I) • f v`
  tends to 0 along `cocompact V`.
- `tendsto_integral_exp_smul_cocompact` : for `V` a finite-dimensional real vector space (endowed
  with its unique Hausdorff topological vector space structure), and `W` the dual of `V`, the
  function `fun w : W ↦ ∫ v : V, exp (2 * π * w v * I) • f v` tends to along `cocompact W`.
- `Real.tendsto_integral_exp_smul_cocompact`: special case of functions on `ℝ`.
- `Real.zero_at_infty_fourierIntegral` and `Real.zero_at_infty_vector_fourierIntegral`:
  reformulations explicitly using the Fourier integral.
-/

public section

noncomputable section

open MeasureTheory Filter Complex Set Module

open scoped Filter Topology Real ENNReal FourierTransform RealInnerProductSpace NNReal

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

section InnerProductSpace

variable [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

variable (f)

/-- Riemann-Lebesgue lemma for functions on a real inner-product space: the integral
`∫ v, exp (-2 * π * ⟪w, v⟫ * I) • f v` tends to 0 as `w → ∞`. -/
theorem tendsto_integral_exp_inner_smul_cocompact :
    Tendsto (𝓕 f) (cocompact V) (𝓝 0) := by
  by_cases h : CompleteSpace E ∧ Integrable f; swap
  · convert tendsto_const_nhds (x := (0 : E)) with w
    simp only [Real.fourier_eq, integral, Real.fourierIntegral_convergent_iff, dite_eq_right_iff]
    intro a b
    by_contra
    exact h ⟨a, b⟩
  haveI := h.1
  exact riemann_lebesgue f (memLp_one_iff_integrable.mpr h.2)

/-- The Riemann-Lebesgue lemma for functions on `ℝ`. -/
theorem Real.tendsto_integral_exp_smul_cocompact (f : ℝ → E) :
    Tendsto (fun w : ℝ => ∫ v : ℝ, 𝐞 (-(v * w)) • f v) (cocompact ℝ) (𝓝 0) := by
  simp_rw [mul_comm]
  exact tendsto_integral_exp_inner_smul_cocompact f

/-- The Riemann-Lebesgue lemma for functions on `ℝ`, formulated via
`Real.instFourierTransform.fourier`. -/
theorem Real.zero_at_infty_fourier (f : ℝ → E) : Tendsto (𝓕 f) (cocompact ℝ) (𝓝 0) :=
  tendsto_integral_exp_inner_smul_cocompact f

@[deprecated (since := "2025-11-16")]
alias Real.zero_at_infty_fourierIntegral := Real.zero_at_infty_fourier

/-- Riemann-Lebesgue lemma for functions on a finite-dimensional inner-product space, formulated
via dual space. **Do not use** -- it is only a stepping stone to
`tendsto_integral_exp_smul_cocompact` where the inner-product-space structure isn't required. -/
theorem tendsto_integral_exp_smul_cocompact_of_inner_product (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (fun w : StrongDual ℝ V => ∫ v, 𝐞 (-w v) • f v ∂μ) (cocompact (StrongDual ℝ V))
    (𝓝 0) := by
  rw [μ.isAddLeftInvariant_eq_smul volume]
  simp_rw [integral_smul_nnreal_measure]
  rw [← (smul_zero _ : Measure.addHaarScalarFactor μ volume • (0 : E) = 0)]
  apply Tendsto.const_smul
  let A := (InnerProductSpace.toDual ℝ V).symm
  have : (fun w : StrongDual ℝ V ↦ ∫ v, 𝐞 (-w v) • f v) =
      (fun w : V ↦ ∫ v, 𝐞 (-⟪v, w⟫) • f v) ∘ A := by
    ext1 w
    congr 1 with v : 1
    rw [← inner_conj_symm, RCLike.conj_to_real, InnerProductSpace.toDual_symm_apply]
  rw [this]
  exact (tendsto_integral_exp_inner_smul_cocompact f).comp
      A.toHomeomorph.toCocompactMap.cocompact_tendsto'

end InnerProductSpace

section NoInnerProduct

variable (f) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] [Module ℝ V] [ContinuousSMul ℝ V] [FiniteDimensional ℝ V]

/-- Riemann-Lebesgue lemma for functions on a finite-dimensional real vector space, formulated via
dual space. -/
theorem tendsto_integral_exp_smul_cocompact (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (fun w : StrongDual ℝ V => ∫ v, 𝐞 (-w v) • f v ∂μ) (cocompact (StrongDual ℝ V))
      (𝓝 0) := by
  -- We have already proved the result for inner-product spaces, formulated in a way which doesn't
  -- refer to the inner product. So we choose an arbitrary inner-product space isomorphic to V
  -- and port the result over from there.
  let V' := EuclideanSpace ℝ (Fin (finrank ℝ V))
  have A : V ≃L[ℝ] V' := toEuclidean
  borelize V'
  -- various equivs derived from A
  let Aₘ : MeasurableEquiv V V' := A.toHomeomorph.toMeasurableEquiv
  -- isomorphism between duals derived from A
  let Adual : StrongDual ℝ V ≃L[ℝ] StrongDual ℝ V' := A.arrowCongrSL (.refl _ _)
  have : (μ.map Aₘ).IsAddHaarMeasure := A.isAddHaarMeasure_map _
  convert (tendsto_integral_exp_smul_cocompact_of_inner_product (f ∘ A.symm) (μ.map Aₘ)).comp
    Adual.toHomeomorph.toCocompactMap.cocompact_tendsto' with w
  suffices ∫ v, 𝐞 (-w v) • f v ∂μ = ∫ (x : V), 𝐞 (-w (A.symm (Aₘ x))) • f (A.symm (Aₘ x)) ∂μ by
    simpa [Function.comp_apply, integral_map_equiv, Adual]
  simp [Aₘ]

/-- The Riemann-Lebesgue lemma, formulated in terms of `VectorFourier.fourierIntegral` (with the
pairing in the definition of `fourierIntegral` taken to be the canonical pairing between `V` and
its dual space). -/
theorem Real.zero_at_infty_vector_fourierIntegral (μ : Measure V) [μ.IsAddHaarMeasure] :
    Tendsto (VectorFourier.fourierIntegral 𝐞 μ (topDualPairing ℝ V).flip f)
      (cocompact (StrongDual ℝ V)) (𝓝 0) :=
  _root_.tendsto_integral_exp_smul_cocompact f μ

end NoInnerProduct
