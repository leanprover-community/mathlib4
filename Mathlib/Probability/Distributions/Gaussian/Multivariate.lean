/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Moments.CovarianceBilin

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# Multivariate Gaussian distributions

In this file we define the standard Gaussian distribution over a Euclidean space and multivariate
Gaussian distributions over `EuclideanSpace ℝ ι`.

## Main definitions

* `stdGaussian E`: Standard Gaussian distribution on a finite-dimensional real inner product space
  `E`. This is the random vector whose coordinates in an orthonormal basis are independent standard
  Gaussian.
* `multivariateGaussian μ S`: The multivariate Gaussian distribution on `EuclideanSpace ℝ ι`
  with mean `μ` and covariance matrix `S`, when `S` is a positive semidefinite matrix.

## TODO

- Generalize `multivariateGaussian μ S` when `S` is a symmetric trace class operator over a
  Hilbert space.

## Tags

multivariate Gaussian distribution

-/

@[expose] public section


open MeasureTheory Matrix WithLp Module Complex
open scoped RealInnerProductSpace MatrixOrder

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

section stdGaussian

/-! ### Standard Gaussian measure over a Euclidean space -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]

variable (E) in
/-- Standard Gaussian distribution on a finite-dimensional real inner product space `E`.
This is the random vector whose coordinates in an orthonormal basis are independent standard
Gaussian.

The definition uses `stdOrthonormalBasis ℝ E` but does not actually depend on the
basis, see `stdGaussian_eq_map_pi_orthonormalBasis`. -/
noncomputable
def stdGaussian : Measure E :=
  (Measure.pi (fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 1)).map
    (fun x ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i)

variable [BorelSpace E]

instance isProbabilityMeasure_stdGaussian : IsProbabilityMeasure (stdGaussian E) :=
  Measure.isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

@[simp]
lemma integral_id_stdGaussian : ∫ x, x ∂(stdGaussian E) = 0 := by
  rw [stdGaussian, integral_map _ (by fun_prop), integral_finset_sum]
  · simp [integral_smul_const, integral_eval]
  · exact fun i _ ↦ Integrable.smul_const (integrable_eval IsGaussian.integrable_id) _
  · exact (Finset.measurable_sum _ (by fun_prop)).aemeasurable

lemma variance_dual_stdGaussian (L : StrongDual ℝ E) :
    Var[L; stdGaussian E] = ‖L‖ ^ 2 := by
  rw [stdGaussian, variance_map L.continuous.aemeasurable (Measurable.aemeasurable (by fun_prop))]
  have : L ∘ (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ ∑ i, x i • stdOrthonormalBasis ℝ E i) =
      ∑ i, (fun x : Fin (Module.finrank ℝ E) → ℝ ↦ L (stdOrthonormalBasis ℝ E i) * x i) := by
    ext x; simp [mul_comm]
  rw [this, variance_sum_pi]
  · change ∑ i, Var[fun x ↦ _ * (id x); gaussianReal 0 1] = _
    simp_rw [variance_const_mul, variance_id_gaussianReal, (stdOrthonormalBasis ℝ E).norm_dual]
    simp
  · exact fun i ↦ IsGaussian.memLp_two_id.const_mul _

set_option backward.isDefEq.respectTransparency false in
lemma charFun_stdGaussian (t : E) :
    charFun (stdGaussian E) t = exp (- ‖t‖ ^ 2 / 2) := by
  rw [charFun_apply, stdGaussian, integral_map (Measurable.aemeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop))]
  simp_rw [sum_inner, ofReal_sum, Finset.sum_mul, exp_sum,
    integral_fintype_prod_eq_prod (f := fun i x ↦ exp (⟪x • stdOrthonormalBasis ℝ E i, t⟫ * I)),
    real_inner_smul_left, mul_comm _ (⟪_, _⟫), ofReal_mul, ← charFun_apply_real,
    charFun_gaussianReal]
  simp only [ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, ofReal_one, one_mul,
    zero_sub]
  simp_rw [← exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, ← ofReal_pow,
    ← ofReal_sum, (stdOrthonormalBasis ℝ E).sum_sq_inner_right, neg_div]

set_option backward.isDefEq.respectTransparency false in
instance isGaussian_stdGaussian : IsGaussian (stdGaussian E) := by
  refine isGaussian_iff_gaussian_charFun.2 ⟨0, innerSL ℝ,
    LinearMap.BilinForm.isPosSemidef_iff.2 isPosSemidef_inner, ?_⟩
  simp [charFun_stdGaussian, neg_div, innerSL_apply_apply ℝ]

@[simp]
lemma integral_strongDual_stdGaussian (L : StrongDual ℝ E) : (stdGaussian E)[L] = 0 := by
  rw [L.integral_comp_id_comm IsGaussian.integrable_id, integral_id_stdGaussian, map_zero]

lemma charFunDual_stdGaussian (L : StrongDual ℝ E) :
    charFunDual (stdGaussian E) L = exp (- ‖L‖ ^ 2 / 2) := by
  simp [IsGaussian.charFunDual_eq, integral_complex_ofReal, variance_dual_stdGaussian, neg_div]

set_option backward.isDefEq.respectTransparency false in
lemma covarianceBilin_stdGaussian :
    covarianceBilin (stdGaussian E) = innerSL ℝ := by
  refine gaussian_charFun_congr 0 _ ?_ ?_ |>.2.symm
  · exact LinearMap.BilinForm.isPosSemidef_iff.2 isPosSemidef_inner
  · simp [charFun_stdGaussian, neg_div, innerSL_apply_apply ℝ]

lemma stdGaussian_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] (f : E ≃ₗᵢ[ℝ] F) :
    haveI := f.finiteDimensional; (stdGaussian E).map f = stdGaussian F := by
  have := f.finiteDimensional
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [show ⇑f = f.toLinearIsometry.toContinuousLinearMap from rfl, charFunDual_map,
    charFunDual_stdGaussian, L.opNorm_comp_linearIsometryEquiv]

lemma map_pi_eq_stdGaussian :
    (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace ℝ ι) := by
  apply Measure.ext_of_charFun (E := EuclideanSpace ℝ ι)
  ext t
  simp_rw [charFun_stdGaussian, charFun_pi, charFun_gaussianReal, ← exp_sum, ← ofReal_pow,
    EuclideanSpace.real_norm_sq_eq]
  simp [Finset.sum_div, neg_div]

/-- The definition of `stdGaussian` does not depend on the basis. -/
lemma stdGaussian_eq_map_pi_orthonormalBasis (b : OrthonormalBasis ι ℝ E) :
    stdGaussian E = (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map (fun x ↦ ∑ i, x i • b i) := by
  have : (fun (x : ι → ℝ) ↦ ∑ i, x i • b i) =
      ⇑((EuclideanSpace.basisFun ι ℝ).equiv b (Equiv.refl ι)) ∘ (toLp 2) := by
    simp_rw [← b.equiv_apply_euclideanSpace]
    rfl
  rw [this, ← Measure.map_map, map_pi_eq_stdGaussian, stdGaussian_map]
  all_goals fun_prop

end stdGaussian

section multivariateGaussian

/-! ### Multivariate Gaussian measures over `ℝⁿ` -/

variable [DecidableEq ι]

/-- Multivariate Gaussian measure on `EuclideanSpace ℝ ι` with mean `μ` and covariance
matrix `S`. This only makes sense when `S` is positive semidefinite,
as then `CFC.sqrt S * CFC.sqrt S = S`. Otherwise `CFC.sqrt S = 0`, and
`multivariateGaussian μ S = Measure.dirac μ` (see `multivariateGaussian_of_not_posSemidef`). -/
noncomputable
def multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  (stdGaussian (EuclideanSpace ℝ ι)).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)

lemma multivariateGaussian_of_not_posSemidef (μ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    (hS : ¬ S.PosSemidef) : multivariateGaussian μ S = .dirac μ := by
  rw [multivariateGaussian, CFC.sqrt, cfcₙ_apply_of_not_predicate]
  · simp
  change ¬ (S - 0).PosSemidef
  simpa

@[simp]
lemma multivariateGaussian_zero_one :
    multivariateGaussian 0 (1 : Matrix ι ι ℝ) = stdGaussian (EuclideanSpace ℝ ι) := by
  simp [multivariateGaussian]

variable {μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}

instance isGaussian_multivariateGaussian : IsGaussian (multivariateGaussian μ S) := by
  have h : (fun x ↦ μ + (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x) =
    (fun x ↦ μ + x) ∘ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))) := rfl
  simp only [multivariateGaussian]
  rw [h, ← Measure.map_map (measurable_const_add μ) (by fun_prop)]
  infer_instance

@[simp]
lemma integral_id_multivariateGaussian : ∫ x, x ∂(multivariateGaussian μ S) = μ := by
  rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop),
    integral_add (integrable_const _), integral_const]
  · simp [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id]
  · exact IsGaussian.integrable_id.comp_measurable (by fun_prop)

lemma integral_id_multivariateGaussian' : (multivariateGaussian μ S)[id] = μ := by simp

set_option backward.isDefEq.respectTransparency false in
lemma covarianceBilin_multivariateGaussian (hS : S.PosSemidef) (x y : EuclideanSpace ℝ ι) :
    covarianceBilin (multivariateGaussian μ S) x y = x ⬝ᵥ S *ᵥ y := by
  have h : (fun x ↦ μ + x) ∘ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))) =
    (fun x ↦ μ + (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x) := rfl
  simp only [multivariateGaussian]
  rw [← h, ← Measure.map_map (measurable_const_add μ) (by fun_prop), covarianceBilin_map_const_add,
    covarianceBilin_map, covarianceBilin_stdGaussian, innerSL_apply_apply,
    ContinuousLinearMap.adjoint_inner_left, IsSelfAdjoint.adjoint_eq,
    ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      CFC.sqrt_mul_sqrt_self _ hS.nonneg, inner_toEuclideanCLM]
  · exact (CFC.sqrt_nonneg S).isSelfAdjoint.map _
  · exact IsGaussian.memLp_two_id

set_option backward.isDefEq.respectTransparency false in
lemma covariance_eval_multivariateGaussian (hS : S.PosSemidef) (i j : ι) :
    cov[fun x ↦ x i, fun x ↦ x j; multivariateGaussian μ S] = S i j := by
  have (i : ι) : (fun x : EuclideanSpace ℝ ι ↦ x i) =
      fun x ↦ ⟪EuclideanSpace.basisFun ι ℝ i, x⟫ := by ext; simp [PiLp.inner_apply]
  rw [this, this, ← covarianceBilin_apply_eq_cov, covarianceBilin_multivariateGaussian hS]
  · simp
  · exact IsGaussian.memLp_two_id

lemma variance_eval_multivariateGaussian (hS : S.PosSemidef) (i : ι) :
    Var[fun x ↦ x i; multivariateGaussian μ S] = S i i := by
  rw [← covariance_self, covariance_eval_multivariateGaussian hS]
  exact Measurable.aemeasurable <| by fun_prop

lemma measurePreserving_eval_multivariateGaussian (hS : S.PosSemidef) {i : ι} :
    MeasurePreserving (fun x ↦ x i) (multivariateGaussian μ S)
      (gaussianReal (μ i) (S i i).toNNReal) where
  measurable := by fun_prop
  map_eq := by
    rw [← EuclideanSpace.coe_proj, IsGaussian.map_eq_gaussianReal,
      ContinuousLinearMap.integral_comp_id_comm]
    · simp [variance_eval_multivariateGaussian hS]
    exact IsGaussian.integrable_id

lemma charFun_multivariateGaussian (hS : S.PosSemidef) (x : EuclideanSpace ℝ ι) :
    charFun (multivariateGaussian μ S) x =
      exp (⟪x, μ⟫ * I - x ⬝ᵥ S *ᵥ x / 2) := by
  simp [IsGaussian.charFun_eq', covarianceBilin_multivariateGaussian hS]

set_option backward.isDefEq.respectTransparency false in
/-- If one restricts a multivariate Gaussian measure indexed by a finite set `I` to
coordinates indexed by `J ⊆ I`, one obtains the multivariate Gaussian measure whose
covariance matrix is given by the corresponding submatrix. -/
lemma measurePreserving_restrict₂_multivariateGaussian {ι : Type*} [DecidableEq ι] {I J : Finset ι}
    {μ : EuclideanSpace ℝ I} {S : Matrix I I ℝ} (hS : S.PosSemidef) (hJI : J ⊆ I) :
    MeasurePreserving (EuclideanSpace.restrict₂ hJI) (multivariateGaussian μ S)
      (multivariateGaussian (μ.restrict₂ hJI)
        (S.submatrix (fun i : J ↦ ⟨i.1, hJI i.2⟩) (fun i : J ↦ ⟨i.1, hJI i.2⟩))) where
  measurable := by fun_prop
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun J ℝ).toBasis fun i j ↦ ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covariance_map]
    · have (i : J) : (fun u ↦ ⟪(EuclideanSpace.basisFun J ℝ).toBasis i, u⟫) ∘
          EuclideanSpace.restrict₂ hJI = fun u ↦ u ⟨i.1, hJI i.2⟩ := by ext; simp [PiLp.inner_apply]
      simp_rw [this, covariance_eval_multivariateGaussian hS,
        covarianceBilin_multivariateGaussian (hS.submatrix _)]
      simp
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

end multivariateGaussian

end ProbabilityTheory
