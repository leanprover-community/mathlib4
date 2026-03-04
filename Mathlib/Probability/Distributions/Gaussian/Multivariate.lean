/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Probability.Moments.Variance
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Analysis.Matrix.Order
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Multivariate Gaussian distributions

## Main definitions

## Main statements

-/

open WithLp ENNReal

lemma PiLp.coe_proj (p : ENNReal) {ι : Type*} (𝕜 : Type*) {E : ι → Type*} [Semiring 𝕜]
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] {i : ι} :
    ⇑(proj p (𝕜 := 𝕜) E i) = fun x ↦ x i := rfl

lemma EuclideanSpace.coe_proj {ι : Type*} (𝕜 : Type*) [RCLike 𝕜] {i : ι} :
    ⇑(@proj ι 𝕜 _ i) = fun x ↦ x i := rfl

@[simp]
lemma EuclideanSpace.proj_apply {ι 𝕜 : Type*} [RCLike 𝕜] {i : ι} (x : EuclideanSpace 𝕜 ι) :
    proj i x = x i := rfl

lemma ContinuousLinearMap.coe_proj' (R : Type*) {ι : Type*} [Semiring R] {φ : ι → Type*}
    [∀ i, TopologicalSpace (φ i)] [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)] (i : ι) :
    ⇑(ContinuousLinearMap.proj (R := R) (φ := φ) i) = fun x ↦ x i := rfl

lemma EuclideanSpace.coe_equiv_symm {ι 𝕜 : Type*} [RCLike 𝕜] :
    ⇑(EuclideanSpace.equiv ι 𝕜).symm = toLp 2 := rfl

@[expose] public section

open MeasureTheory Matrix WithLp Module
open scoped RealInnerProductSpace MatrixOrder

section InnerProductSpace

open scoped InnerProductSpace

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

theorem OrthonormalBasis.norm_sq_eq_sum_sq_inner_right (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪b i, x⟫_ℝ ^ 2 := by
  simp [← b.sum_sq_norm_inner_right]

theorem OrthonormalBasis.norm_sq_eq_sum_sq_inner_left (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪x, b i⟫_ℝ ^ 2 := by
  simp_rw [b.norm_sq_eq_sum_sq_inner_right, real_inner_comm]

theorem EuclideanSpace.real_norm_sq_eq (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  simp [PiLp.norm_sq_eq_of_L2]

theorem OrthonormalBasis.norm_dual (b : OrthonormalBasis ι ℝ E) (L : StrongDual ℝ E) :
    ‖L‖ ^ 2 = ∑ i, L (b i) ^ 2 := by
  have := Module.Basis.finiteDimensional_of_finite b.toBasis
  simp_rw [← (InnerProductSpace.toDual ℝ E).symm.norm_map, b.norm_sq_eq_sum_sq_inner_left,
    InnerProductSpace.toDual_symm_apply]

@[simp]
lemma LinearIsometryEquiv.coe_coe_eq_coe {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] (f : E ≃ₗᵢ[𝕜] F) :
    ⇑f.toLinearIsometry.toContinuousLinearMap = ⇑f := rfl

end InnerProductSpace

-- section mkContinuous₂

-- namespace LinearMap

-- variable {E F G 𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
--   [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
--   [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T2Space E]
--   [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
--   [Module 𝕜 F] [ContinuousSMul 𝕜 F] [T2Space F]
--   [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
--   [Module 𝕜 G] [ContinuousSMul 𝕜 G]
--   [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (f : E →ₗ[𝕜] F →ₗ[𝕜] G)

-- /-- Given a bilinear map whose codomains are finite dimensional, outputs the continuous
-- version. -/
-- def mkContinuous₂OfFiniteDimensional : E →L[𝕜] F →L[𝕜] G :=
--   letI g x : F →L[𝕜] G := (f x).toContinuousLinearMap
--   letI h : E →ₗ[𝕜] F →L[𝕜] G :=
--     { toFun := g
--       map_add' x y := by ext z; simp [g]
--       map_smul' m x := by ext y; simp [g] }
--   h.toContinuousLinearMap

-- @[simp]
-- lemma mkContinuous₂OfFiniteDimensional_apply (x : E) (y : F) :
--     f.mkContinuous₂OfFiniteDimensional x y = f x y := rfl

-- end LinearMap

-- end mkContinuous₂

-- namespace ContinuousLinearMap



-- variable {𝕜 E n : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace E] [AddCommGroup E]
--   [IsTopologicalAddGroup E] [Module 𝕜 E] [CompleteSpace 𝕜] [ContinuousSMul 𝕜 E] [T2Space E]

-- variable [Fintype n] [DecidableEq n]

-- variable (M : Matrix n n 𝕜) (b : Basis n 𝕜 E) (f : E →L[𝕜] E →L[𝕜] 𝕜)

-- noncomputable
-- def ofMatrix : E →L[𝕜] E →L[𝕜] 𝕜 :=
--   haveI : FiniteDimensional 𝕜 E := Module.Basis.finiteDimensional_of_finite b
--   LinearMap.mkContinuous₂OfFiniteDimensional (M.toBilin b)

-- lemma ofMatrix_apply' (x y : E) : ofMatrix M b x y = M.toBilin b x y := rfl

-- open scoped Matrix in
-- lemma ofMatrix_apply (x y : E) :
--     ofMatrix M b x y = b.repr x ⬝ᵥ M *ᵥ b.repr y := by
--   simp [ofMatrix_apply', Matrix.toBilin_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

-- lemma ofMatrix_basis (i j : n) : ofMatrix M b (b i) (b j) = M i j := by
--   simp [ofMatrix_apply, Finsupp.single_eq_pi_single]

-- lemma ofMatrix_orthonormalBasis {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
--     [InnerProductSpace 𝕜 E] (M : Matrix n n 𝕜) (b : OrthonormalBasis n 𝕜 E) (i j : n) :
--     ofMatrix M b.toBasis (b i) (b j) = M i j := by
--   rw [← b.coe_toBasis, ofMatrix_basis]

-- set_option backward.isDefEq.respectTransparency false in
-- lemma toMatrix_ofMatrix : ofMatrix (f.toBilinForm.toMatrix b) b = f := by
--   ext x y
--   rw [ofMatrix_apply, ← f.toBilinForm.apply_eq_dotProduct_toMatrix_mulVec b, toBilinForm_apply]

-- lemma ofMatrix_toMatrix : (ofMatrix M b).toBilinForm.toMatrix b = M := by
--   ext i j
--   rw [LinearMap.BilinForm.toMatrix_apply, toBilinForm_apply, ofMatrix_basis]

-- end ContinuousLinearMap

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] in
lemma isSymm_inner : LinearMap.IsSymm (innerₗ E) where
  eq x y := by simp only [innerₗ_apply_apply, RingHom.id_apply]; rw [real_inner_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] in
lemma isNonneg_inner : LinearMap.IsNonneg (innerₗ E) where
  nonneg x := by simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] in
lemma isPosSemidef_inner : LinearMap.IsPosSemidef (innerₗ E) where
  isSymm := isSymm_inner
  isNonneg := isNonneg_inner

variable (E) in
/-- Standard Gaussian distribution on `E`. -/
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
  rotate_left
  · refine fun i _ ↦ Integrable.smul_const ?_ _
    convert integrable_comp_eval (i := i) (f := id) ?_
    · infer_instance
    · exact IsGaussian.integrable_id
  · exact (Finset.measurable_sum _ (by fun_prop)).aemeasurable
  rw [integral_finset_sum]
  swap
  · refine fun i _ ↦ Integrable.smul_const ?_ _
    convert integrable_comp_eval (i := i) (f := id) ?_
    · infer_instance
    · exact IsGaussian.integrable_id
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have : (∫ (a : Fin (Module.finrank ℝ E) → ℝ), a i ∂Measure.pi fun x ↦ gaussianReal 0 1)
      = ∫ x, x ∂gaussianReal 0 1 := by
    convert integral_comp_eval (i := i) aestronglyMeasurable_id
    all_goals infer_instance
  simp [integral_smul_const, this]

@[simp]
lemma integral_strongDual_stdGaussian (L : StrongDual ℝ E) : (stdGaussian E)[L] = 0 := by
  rw [L.integral_comp_id_comm, integral_id_stdGaussian, map_zero]
  rw [stdGaussian, integrable_map_measure aestronglyMeasurable_id, Function.id_comp]
  · exact integrable_finset_sum _ fun i _ ↦ Integrable.smul_const
      (integrable_comp_eval (f := id) IsGaussian.integrable_id) _
  · exact Measurable.aemeasurable (by fun_prop)

lemma variance_dual_stdGaussian (L : StrongDual ℝ E) : Var[L; stdGaussian E] = ‖L‖ ^ 2 := by
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
lemma charFun_stdGaussian (t : E) : charFun (stdGaussian E) t = Complex.exp (- ‖t‖ ^ 2 / 2) := by
  rw [charFun_apply, stdGaussian, integral_map (Measurable.aemeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop))]
  simp_rw [sum_inner, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum,
    integral_fintype_prod_eq_prod
      (f := fun i x ↦ Complex.exp (⟪x • stdOrthonormalBasis ℝ E i, t⟫ * Complex.I)),
    real_inner_smul_left, mul_comm _ (⟪_, _⟫), Complex.ofReal_mul, ← charFun_apply_real,
    charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one, one_mul,
    zero_sub]
  simp_rw [← Complex.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_div, ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, ← (stdOrthonormalBasis ℝ E).norm_sq_eq_sum_sq_inner_right, neg_div]

set_option backward.isDefEq.respectTransparency false in
instance isGaussian_stdGaussian : IsGaussian (stdGaussian E) := by
  refine isGaussian_iff_gaussian_charFun.2 ⟨0, innerSL ℝ, ?_, ?_⟩
  · rw [LinearMap.BilinForm.isPosSemidef_iff]
    exact isPosSemidef_inner
  · simp only [charFun_stdGaussian, neg_div, inner_zero_right, Complex.ofReal_zero, zero_mul,
      zero_sub]
    congr!
    rw [innerSL_apply_apply]
    simp

set_option backward.isDefEq.respectTransparency false in
lemma charFunDual_stdGaussian (L : StrongDual ℝ E) :
    charFunDual (stdGaussian E) L = Complex.exp (- ‖L‖ ^ 2 / 2) := by
  rw [IsGaussian.charFunDual_eq, integral_complex_ofReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]
  simp [neg_div]

set_option backward.isDefEq.respectTransparency false in
lemma covarianceBilin_stdGaussian :
    covarianceBilin (stdGaussian E) = innerSL ℝ := by
  refine gaussian_charFun_congr 0 _ ?_ (fun t ↦ ?_) |>.2.symm
  · rw [LinearMap.BilinForm.isPosSemidef_iff]
    exact isPosSemidef_inner
  · simp only [charFun_stdGaussian, neg_div, inner_zero_right, Complex.ofReal_zero, zero_mul,
      zero_sub]
    congr!
    rw [innerSL_apply_apply]
    simp

lemma stdGaussian_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] (f : E ≃ₗᵢ[ℝ] F) :
    haveI := f.finiteDimensional; (stdGaussian E).map f = stdGaussian F := by
  have := f.finiteDimensional
  apply Measure.ext_of_charFunDual
  ext L
  simp_rw [← f.coe_coe_eq_coe, charFunDual_map, charFunDual_stdGaussian,
    L.opNorm_comp_linearIsometryEquiv]

lemma pi_eq_stdGaussian {n : Type*} [Fintype n] :
    (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace ℝ n) := by
  apply Measure.ext_of_charFun (E := EuclideanSpace ℝ n)
  ext t
  simp_rw [charFun_stdGaussian, charFun_pi, charFun_gaussianReal, ← Complex.exp_sum,
    ← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq]
  simp [Finset.sum_div, neg_div]

lemma stdGaussian_eq_pi_map_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    stdGaussian E = (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map
      (fun x ↦ ∑ i, x i • b i) := by
  have : (fun (x : ι → ℝ) ↦ ∑ i, x i • b i) =
      ⇑((EuclideanSpace.basisFun ι ℝ).equiv b (Equiv.refl ι)) ∘ (toLp 2) := by
    simp_rw [← b.equiv_apply_euclideanSpace]
    rfl
  rw [this, ← Measure.map_map, pi_eq_stdGaussian, stdGaussian_map]
  all_goals fun_prop

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
/-- Multivariate Gaussian measure on `EuclideanSpace ℝ ι` with mean `μ` and covariance
matrix `S`. -/
noncomputable
def multivariateGaussian (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  (stdGaussian (EuclideanSpace ℝ ι)).map (fun x ↦ μ + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma multivariateGaussian_zero_one :
    multivariateGaussian 0 (1 : Matrix ι ι ℝ) = stdGaussian (EuclideanSpace ℝ ι) := by
  simp [multivariateGaussian]

variable {μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} {hS : S.PosSemidef}

set_option backward.isDefEq.respectTransparency false in
instance isGaussian_multivariateGaussian : IsGaussian (multivariateGaussian μ S) := by
  have h : (fun x ↦ μ + x) ∘ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))) =
    (fun x ↦ μ + (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x) := rfl
  simp only [multivariateGaussian]
  rw [← h, ← Measure.map_map (measurable_const_add μ) (by measurability)]
  infer_instance

@[simp]
lemma integral_id_multivariateGaussian : ∫ x, x ∂(multivariateGaussian μ S) = μ := by
  rw [multivariateGaussian, integral_map (by fun_prop) (by fun_prop),
    integral_add (integrable_const _), integral_const]
  · simp [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id]
  · exact IsGaussian.integrable_id.comp_measurable (by fun_prop)

set_option backward.isDefEq.respectTransparency false in
lemma inner_toEuclideanCLM (x y : EuclideanSpace ℝ ι) :
    ⟪x, toEuclideanCLM (𝕜 := ℝ) S y⟫
      = (EuclideanSpace.basisFun ι ℝ).toBasis.repr x ⬝ᵥ S
        *ᵥ (EuclideanSpace.basisFun ι ℝ).toBasis.repr y := by
  simp only [toEuclideanCLM, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearEquiv.invFun_eq_symm, LinearMap.coe_toContinuousLinearMap_symm, StarAlgEquiv.trans_apply,
    LinearMap.toMatrixOrthonormal_symm_apply, LinearMap.toMatrix_symm, StarAlgEquiv.coe_mk,
    StarRingEquiv.coe_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk, LinearMap.coe_toContinuousLinearMap',
    toLin_apply, mulVec_eq_sum, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply,
    smul_eq_mul, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    ofLp_sum, ofLp_smul, EuclideanSpace.ofLp_single, RCLike.inner_apply, conj_trivial, dotProduct]
  congr with i
  rw [mul_comm (x.ofLp i)]
  simp [Pi.single_apply]

set_option backward.isDefEq.respectTransparency false in
lemma covarianceBilin_multivariateGaussian (hS : S.PosSemidef) :
    covarianceBilin (multivariateGaussian μ S)
      = (S.toBilin (EuclideanSpace.basisFun ι ℝ).toBasis).toCLM₂ := by
  have h : (fun x ↦ μ + x) ∘ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))) =
    (fun x ↦ μ + (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x) := rfl
  simp only [multivariateGaussian]
  rw [← h, ← Measure.map_map (measurable_const_add μ) (by fun_prop), covarianceBilin_map_const_add]
  ext x y
  rw [covarianceBilin_map, covarianceBilin_stdGaussian, innerSL_apply_apply, LinearMap.toCLM₂_apply,
    ContinuousLinearMap.adjoint_inner_left, IsSelfAdjoint.adjoint_eq]
  · rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      CFC.sqrt_mul_sqrt_self _ hS.nonneg, inner_toEuclideanCLM]
    simp [Matrix.toBilin_apply, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  · exact (CFC.sqrt_nonneg S).isSelfAdjoint.map _
  · exact IsGaussian.memLp_two_id

set_option backward.isDefEq.respectTransparency false in
lemma covariance_eval_multivariateGaussian (hS : S.PosSemidef) (i j : ι) :
    cov[fun x ↦ x i, fun x ↦ x j; multivariateGaussian μ S] = S i j := by
  have (i : ι) : (fun x : EuclideanSpace ℝ ι ↦ x i) =
      fun x ↦ ⟪EuclideanSpace.basisFun ι ℝ i, x⟫ := by ext; simp [PiLp.inner_apply]
  rw [this, this, ← covarianceBilin_apply_eq_cov, covarianceBilin_multivariateGaussian hS,
    LinearMap.toCLM₂_apply, ← OrthonormalBasis.coe_toBasis, Matrix.toBilin_apply_basis]
  exact IsGaussian.memLp_two_id

lemma variance_eval_multivariateGaussian (hS : S.PosSemidef) (i : ι) :
    Var[fun x ↦ x i; multivariateGaussian μ S] = S i i := by
  rw [← covariance_self, covariance_eval_multivariateGaussian hS]
  exact Measurable.aemeasurable <| by fun_prop

lemma hasLaw_eval_multivariateGaussian (hS : S.PosSemidef) {i : ι} :
    HasLaw (fun x ↦ x i) (gaussianReal (μ i) (S i i).toNNReal) (multivariateGaussian μ S) where
  aemeasurable := Measurable.aemeasurable (by fun_prop)
  map_eq := by
    rw [← EuclideanSpace.coe_proj ℝ, IsGaussian.map_eq_gaussianReal,
      ContinuousLinearMap.integral_comp_id_comm, integral_id_multivariateGaussian,
      EuclideanSpace.proj_apply, EuclideanSpace.coe_proj, variance_eval_multivariateGaussian hS]
    exact IsGaussian.integrable_id

lemma charFun_multivariateGaussian (hS : S.PosSemidef) (x : EuclideanSpace ℝ ι) :
    charFun (multivariateGaussian μ S) x =
      Complex.exp (⟪x, μ⟫ * Complex.I - x ⬝ᵥ S *ᵥ x / 2) := by
  rw [IsGaussian.charFun_eq']
  congr
  · exact integral_id_multivariateGaussian
  · rw [covarianceBilin_multivariateGaussian hS, LinearMap.toCLM₂_apply]
    simp [toBilin_apply, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- `Finset.restrict₂` as a continuous linear map. -/
def _root_.Finset.restrict₂CLM {ι : Type*} (R : Type*) {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)]
    {I J : Finset ι} (hIJ : I ⊆ J) :
    (Π i : J, M i) →L[R] Π i : I, M i where
  toFun := Finset.restrict₂ hIJ
  map_add' x y := by ext; simp
  map_smul' m x := by ext; simp
  cont := by fun_prop

lemma _root_.Finset.coe_restrict₂CLM {ι R : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)] {I J : Finset ι}
    (hIJ : I ⊆ J) :
    ⇑(Finset.restrict₂CLM (R := R) (M := M) hIJ) = Finset.restrict₂ hIJ := rfl

@[simp]
lemma _root_.Finset.restrict₂CLM_apply {ι R : Type*} {M : ι → Type*} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, TopologicalSpace (M i)] {I J : Finset ι}
    (hIJ : I ⊆ J) (x : Π i : J, M i) (i : I) :
    Finset.restrict₂CLM (R := R) hIJ x i = x ⟨i.1, hIJ i.2⟩ := rfl

/-- The restriction from `EuclideanSpace 𝕜 J` to `EuclideanSpace κ I` when `I ⊆ J`. -/
noncomputable
def _root_.EuclideanSpace.restrict₂ {ι 𝕜 : Type*} [RCLike 𝕜] {I J : Finset ι} (hIJ : I ⊆ J) :
    EuclideanSpace 𝕜 J →L[𝕜] EuclideanSpace 𝕜 I :=
  (EuclideanSpace.equiv I 𝕜).symm.toContinuousLinearMap ∘L
    (Finset.restrict₂CLM 𝕜 (M := fun _ ↦ 𝕜) hIJ) ∘L
      (EuclideanSpace.equiv J 𝕜).toContinuousLinearMap

-- lemma _root_.EuclideanSpace.coe_restrict₂
--     {ι 𝕜 : Type*} [RCLike 𝕜] {I J : Finset ι} (hIJ : I ⊆ J) :
--     ⇑(@EuclideanSpace.restrict₂ ι 𝕜 _ I J hIJ) = EuclideanSpace.restrict₂ hIJ := rfl

@[simp]
lemma _root_.EuclideanSpace.restrict₂_apply {ι 𝕜 : Type*} [RCLike 𝕜] {I J : Finset ι}
    (hIJ : I ⊆ J) (x : EuclideanSpace 𝕜 J) (i : I) :
    EuclideanSpace.restrict₂ hIJ x i = x ⟨i.1, hIJ i.2⟩ := rfl

variable {ι : Type*} [DecidableEq ι] {I J : Finset ι}

variable {μ : EuclideanSpace ℝ I} {S : Matrix I I ℝ} {hS : S.PosSemidef}

set_option backward.isDefEq.respectTransparency false in
lemma measurePreserving_restrict_multivariateGaussian (hS : S.PosSemidef) (hJI : J ⊆ I) :
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
    apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun J ℝ).toBasis
    intro i j
    simp_rw [ContinuousLinearMap.toBilinForm_apply]
    rw [covarianceBilin_apply_eq_cov, covariance_map]
    · have (i : J) : (fun u ↦ ⟪(EuclideanSpace.basisFun J ℝ).toBasis i, u⟫) ∘
          EuclideanSpace.restrict₂ hJI = fun u ↦ u ⟨i.1, hJI i.2⟩ := by ext; simp [PiLp.inner_apply]
      simp_rw [this, covariance_eval_multivariateGaussian hS,
        covarianceBilin_multivariateGaussian (hS.submatrix _),
        LinearMap.toCLM₂_apply, Matrix.toBilin_apply_basis, S.submatrix_apply]
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

set_option backward.isDefEq.respectTransparency false in
open scoped ComplexOrder in
lemma _root_.Matrix.PosSemidef.sqrt_one {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜] [DecidableEq n] :
    CFC.sqrt (1 : Matrix n n 𝕜) = 1 := by simp

end ProbabilityTheory
