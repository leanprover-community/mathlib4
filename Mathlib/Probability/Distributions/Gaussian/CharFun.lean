/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Moments.CovarianceBilin

import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Floor
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SetLike
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Facts about Gaussian characteristic function

In this file we prove that Gaussian measures over a Banach space `E` are exactly those measures
`μ` such that there exist `m : E` and `f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ`
positive semidefinite (satisfying `f.toBilinForm.IsPosSemidef`) such that
`charFunDual μ L = exp (L m * I - f L L / 2)`.
We also prove that such `m` and `f` are unique and equal to `∫ x, x ∂μ` and `covarianceBilinDual μ`.

We also specialize these statements in the case of Hilbert spaces, with
`f : E →L[ℝ] E →L[ℝ] ℝ`, `charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)` and
`f = covarianceBilin μ`.

## Main statements

* `isGaussian_iff_gaussian_charFunDual μ`: the measure `μ` is Gaussian if and only if there
  exist `m : E` and `f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ`
  satisfying `f.toBilinForm.IsPosSemidef` and `charFunDual μ L = exp (L m * I - f L L / 2)`.
* `isGaussian_iff_gaussian_charFun μ`: the measure `μ` is Gaussian if and only if there
  exist `m : E` and `f : E →L[ℝ]  E →L[ℝ] ℝ`
  satisfying `f.toBilinForm.IsPosSemidef` and `charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)`.

## Tags

Gaussian measure, characteristic function
-/

public section


open Complex MeasureTheory WithLp ContinuousLinearMap

open scoped Matrix NNReal Real RealInnerProductSpace ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E}

section NormedSpace

variable [NormedSpace ℝ E]

lemma IsGaussian.charFunDual_eq' [IsGaussian μ] (L : StrongDual ℝ E) :
    charFunDual μ L = exp ((L μ[id]) * I - covarianceBilinDual μ L L / 2) := by
  rw [IsGaussian.charFunDual_eq, covarianceBilinDual_self_eq_variance, integral_complex_ofReal,
    L.integral_comp_id_comm']
  · exact IsGaussian.integrable_id
  · exact IsGaussian.memLp_two_id

/-- The measure `μ` is Gaussian if and only if there
exist `m : E` and `f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ`
satisfying `f.toBilinForm.IsPosSemidef` and `charFunDual μ L = exp (L m * I - f L L / 2)`. -/
lemma isGaussian_iff_gaussian_charFunDual [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∃ (m : E) (f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ),
      f.toBilinForm.IsPosSemidef ∧ ∀ L, charFunDual μ L = exp (L m * I - f L L / 2) := by
  refine ⟨fun h ↦ ⟨μ[id], covarianceBilinDual μ, isPosSemidef_covarianceBilinDual,
    h.charFunDual_eq'⟩,
    fun ⟨m, f, hf, h⟩ ↦ isGaussian_of_map_eq_gaussianReal fun L ↦ ⟨L m, (f L L).toNNReal, ?_⟩⟩
  apply Measure.ext_of_charFun
  ext t
  simp_rw [charFun_map_eq_charFunDual_smul, h, charFun_gaussianReal,
    smul_apply, map_smul, smul_apply, smul_eq_mul]
  norm_cast
  congrm exp (_ - ofReal ?_)
  rw [Real.coe_toNNReal]
  · ring
  exact hf.nonneg L

lemma gaussian_charFunDual_congr [IsFiniteMeasure μ] {m : E}
    {f : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ}
    (hf : f.toBilinForm.IsPosSemidef) (h : ∀ L, charFunDual μ L = exp (L m * I - f L L / 2)) :
    m = ∫ x, x ∂μ ∧ f = covarianceBilinDual μ := by
  have h' := isGaussian_iff_gaussian_charFunDual.2 ⟨m, f, hf, h⟩
  simp_rw [h'.charFunDual_eq', Complex.exp_eq_exp_iff_exists_int] at h
  choose n hn using h
  have h L : (n L : ℂ) = (L (∫ x, id x ∂μ) * I - covarianceBilinDual μ L L / 2 -
      L m * I + f L L / 2) / (2 * π * I) := by
    rw [hn L]
    field_simp
    ring
  have : Continuous n := by
    rw [← Complex.isometry_intCast.comp_continuous_iff]
    change Continuous (fun L ↦ (n L : ℂ))
    simp_rw [h]
    fun_prop
  have := (IsLocallyConstant.iff_continuous n).2 this |>.eq_const
  have this L : n L = 0 := by
    rw [this 0, ← Int.cast_inj (α := ℂ)]
    simp [h]
  simp only [id_eq, this, Int.cast_zero, zero_mul, add_zero, Complex.ext_iff, sub_re, mul_re,
    ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, div_ofNat_re, zero_sub, neg_inj,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj', sub_im, mul_im, div_ofNat_im,
    zero_div, sub_zero] at hn
  constructor
  · rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
    simp [hn]
  · rw [← toBilinForm_inj]
    apply LinearMap.BilinForm.ext_of_isSymm hf.isSymm isPosSemidef_covarianceBilinDual.isSymm
    intro x
    simp [covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id, (hn x).1.symm]

/-- Two Gaussian measures are equal if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_covarianceBilinDual {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilinDual μ = covarianceBilinDual ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [IsGaussian.charFunDual_eq', hm, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. -/
protected lemma IsGaussian.ext_iff_covarianceBilinDual {ν : Measure E} [IsGaussian μ]
    [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilinDual μ = covarianceBilinDual ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext_covarianceBilinDual h.1 h.2

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E]

lemma IsGaussian.charFun_eq' [IsGaussian μ] (t : E) :
    charFun μ t = exp (⟪t, μ[id]⟫ * I - covarianceBilin μ t t / 2) := by
  rw [IsGaussian.charFun_eq, covarianceBilin_self, integral_complex_ofReal,
    integral_inner]
  · rfl
  · exact IsGaussian.integrable_id
  · exact IsGaussian.memLp_two_id

/-- The measure `μ` is Gaussian if and only if there
exist `m : E` and `f : E →L[ℝ]  E →L[ℝ] ℝ`
satisfying `f.toBilinForm.IsPosSemidef` and `charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)`. -/
lemma isGaussian_iff_gaussian_charFun [IsFiniteMeasure μ] :
    IsGaussian μ ↔
    ∃ (m : E) (f : E →L[ℝ] E →L[ℝ] ℝ),
      f.toBilinForm.IsPosSemidef ∧ ∀ t, charFun μ t = exp (⟪t, m⟫ * I - f t t / 2) := by
  rw [isGaussian_iff_gaussian_charFunDual]
  refine ⟨fun ⟨m, f, hf, h⟩ ↦ ⟨m,
    f.bilinearComp (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap
      (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap,
    ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, ?_⟩,
    fun ⟨m, f, hf, h⟩ ↦ ⟨m,
      f.bilinearComp (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
        (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap,
    ⟨⟨fun x y ↦ ?_⟩, ⟨fun x ↦ ?_⟩⟩, ?_⟩⟩
  any_goals simpa using hf.eq ..
  any_goals simpa using hf.nonneg _
  · simp [charFun_eq_charFunDual_toDualMap, h, -InnerProductSpace.toContinuousLinearMap_toDualMap]
  · simp [← charFun_toDual_symm_eq_charFunDual, h]

/-- If the characteristic function of `μ` takes the form of a gaussian characteristic function,
then the parameters have to be the expectation and the covariance bilinear form. -/
lemma gaussian_charFun_congr [IsFiniteMeasure μ] (m : E) (f : E →L[ℝ] E →L[ℝ] ℝ)
    (hf : f.toBilinForm.IsPosSemidef) (h : ∀ t, charFun μ t = exp (⟪t, m⟫ * I - f t t / 2)) :
    m = ∫ x, x ∂μ ∧ f = covarianceBilin μ := by
  let g : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ :=
    f.bilinearComp (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
      (InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap
  have : ∀ L : StrongDual ℝ E, charFunDual μ L = exp (L m * I - g L L / 2) := by
    simp [← charFun_toDual_symm_eq_charFunDual, h, g]
  have hg : g.toBilinForm.IsPosSemidef :=
    ⟨⟨fun x y ↦ by simpa [g] using hf.eq ..⟩, ⟨fun x ↦ by simpa [g] using hf.nonneg _⟩⟩
  have := gaussian_charFunDual_congr hg this
  refine ⟨this.1, ?_⟩
  ext
  simp [covarianceBilin, ← this.2, g, ← InnerProductSpace.toDual_apply_eq_toDualMap_apply,
    -InnerProductSpace.toContinuousLinearMap_toDualMap]

/-- Two Gaussian measures are equal if they have same mean and same covariance. This is
`IsGaussian.ext_covarianceBilinDual` specialized to Hilbert spaces. -/
protected lemma IsGaussian.ext {ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hm : μ[id] = ν[id]) (hv : covarianceBilin μ = covarianceBilin ν) : μ = ν := by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [IsGaussian.charFun_eq', hm, hv]

/-- Two Gaussian measures are equal if and only if they have same mean and same covariance. This is
`IsGaussian.ext_iff_covarianceBilinDual` specialized to Hilbert spaces. -/
protected lemma IsGaussian.ext_iff {ν : Measure E} [IsGaussian μ] [IsGaussian ν] :
    μ = ν ↔ μ[id] = ν[id] ∧ covarianceBilin μ = covarianceBilin ν where
  mp h := by simp [h]
  mpr h := IsGaussian.ext h.1 h.2

end InnerProductSpace

end ProbabilityTheory
