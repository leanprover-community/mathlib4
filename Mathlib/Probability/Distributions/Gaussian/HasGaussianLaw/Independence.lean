/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Independence of Gaussian random variables

In this file we define a predicate `HasGaussianLaw X P`, which states that under the probability
measure `P`, the random variable `X` has a Gaussian distribution, i.e. `IsGaussian (P.map X)`.

## Main definition

* `HasGaussianLaw X P`: The random variable `X` has a Gaussian distribution under the measure `P`.

## Tags

Gaussian random variable
-/

open MeasureTheory WithLp Complex Finset
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section Diagonal

namespace ContinuousLinearMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {L : (i : ι) → StrongDual ℝ (E i) →L[ℝ] StrongDual ℝ (E i) →L[ℝ] ℝ}

/-- Given `L i : (E i)' × (E i)' → ℝ` a family of continuous bilinear forms,
`diagonalStrongDual L` is a continuous bilinear form is the continuous bilinear form over
`(Π i, E i)'` which maps `(x, y) : (Π i, E i)' × (Π i, E i)'` to
`∑ i, L i (fun a ↦ x aᵢ) (fun a ↦ y aᵢ)`. -/
noncomputable
def diagonalStrongDual (L : (i : ι) → StrongDual ℝ (E i) →L[ℝ] StrongDual ℝ (E i) →L[ℝ] ℝ) :
    StrongDual ℝ (Π i, E i) →L[ℝ] StrongDual ℝ (Π i, E i) →L[ℝ] ℝ :=
  letI g : LinearMap.BilinForm ℝ (StrongDual ℝ (Π i, E i)) := LinearMap.mk₂ ℝ
    (fun x y ↦ ∑ i, L i (x ∘L (single ℝ E i)) (y ∘L (single ℝ E i)))
    (fun x y z ↦ by simp [Finset.sum_add_distrib])
    (fun c m n ↦ by simp [Finset.mul_sum])
    (fun x y z ↦ by simp [Finset.sum_add_distrib])
    (fun c m n ↦ by simp [Finset.mul_sum])
  LinearMap.mkContinuous₂ g (∑ i, ‖L i‖) <| by
    intro x y
    simp only [LinearMap.mk₂_apply, g]
    grw [norm_sum_le, Finset.sum_mul, Finset.sum_mul]
    gcongr with i _
    grw [le_opNorm₂, opNorm_comp_le, opNorm_comp_le, norm_single_le_one]
    simp

lemma diagonalStrongDual_apply (x y : StrongDual ℝ (Π i, E i)) :
    diagonalStrongDual L x y = ∑ i, L i (x ∘L (.single ℝ E i)) (y ∘L (.single ℝ E i)) := rfl

lemma toBilinForm_diagonalStrongDual_apply (x y : StrongDual ℝ (Π i, E i)) :
    (diagonalStrongDual L).toBilinForm x y =
    ∑ i, (L i).toBilinForm (x ∘L (.single ℝ E i)) (y ∘L (.single ℝ E i)) := rfl

lemma isPosSemidef_diagonalStrongDual (hL : ∀ i, (L i).toBilinForm.IsPosSemidef) :
    (diagonalStrongDual L).toBilinForm.IsPosSemidef where
  eq x y := by
    simp_rw [toBilinForm_diagonalStrongDual_apply, fun i ↦ (hL i).eq]
  nonneg x := by
    rw [toBilinForm_diagonalStrongDual_apply]
    exact Finset.sum_nonneg fun i _ ↦ (hL i).nonneg _

end ContinuousLinearMap

end Diagonal

public section

namespace ProbabilityTheory

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]

section NormedSpace

variable [∀ i, NormedSpace ℝ (E i)] {X : Π i, Ω → (E i)}

open ContinuousLinearMap in
lemma iIndepFun.hasGaussianLaw (h : ∀ i, HasGaussianLaw (X i) P) (hX : iIndepFun X P) :
    HasGaussianLaw (fun ω ↦ (X · ω)) P where
  isGaussian_map := by
    have := hX.isProbabilityMeasure
    have _ i := (h i).isGaussian_map
    rw [isGaussian_iff_gaussian_charFunDual]
    classical
    refine ⟨fun i ↦ ∫ ω, X i ω ∂P, .diagonalStrongDual (fun i ↦ covarianceBilinDual (P.map (X i))),
      isPosSemidef_diagonalStrongDual (fun i ↦ isPosSemidef_covarianceBilinDual), fun L ↦ ?_⟩
    rw [(iIndepFun_iff_charFunDual_pi (by fun_prop)).1 hX]
    simp only [← LinearMap.sum_single_apply E (fun i ↦ ∫ ω, X i ω ∂P), map_sum, ofReal_sum,
      sum_mul, diagonalStrongDual_apply, sum_div, ← sum_sub_distrib, exp_sum]
    congr with i
    rw [(h i).charFunDual_map_eq, integral_complex_ofReal, Function.comp_def, integral_comp_comm,
      covarianceBilinDual_self_eq_variance, variance_map]
    · simp [Function.comp_def]
    any_goals fun_prop
    · exact IsGaussian.memLp_two_id
    · exact (h i).integrable

open ContinuousLinearMap in
lemma HasGaussianLaw.iIndepFun_of_cov (h : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h' : ∀ i j, i ≠ j → ∀ (L₁ : StrongDual ℝ (E i)) (L₂ : StrongDual ℝ (E j)),
      cov[L₁ ∘ (X i), L₂ ∘ (X j); P] = 0) :
    iIndepFun X P := by
  simp_rw [Function.comp_def] at h'
  have := h.isProbabilityMeasure
  classical
  rw [iIndepFun_iff_charFunDual_pi fun i ↦ h.aemeasurable.eval i]
  intro L
  have this ω : L (X · ω) = ∑ i, (L ∘L (single ℝ E i)) (X i ω) := by
    simp [← map_sum, LinearMap.sum_single_apply]
  simp_rw [h.charFunDual_map_eq_fun, fun i ↦ (h.eval i).charFunDual_map_eq_fun, ← Complex.exp_sum,
    sum_sub_distrib, ← sum_mul, this]
  congr
  · simp_rw [Complex.ofReal_sum]
    rw [integral_finset_sum _ fun i _ ↦ ((h.eval i).map_fun _).integrable.ofReal]
  · rw [variance_fun_sum fun i ↦ ((h.eval i).map_fun _).memLp_two]
    simp only [← sum_div, ← ofReal_sum, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_left_inj', ofReal_inj]
    congr with i
    rw [sum_eq_single_of_mem i (by grind) (fun j _ hij ↦ h' i j hij.symm _ _),
      covariance_self ((h.eval i).map_fun _).aemeasurable]

open ContinuousLinearMap in
lemma HasGaussianLaw.indepFun_of_cov {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F]
    {X : Ω → E} {Y : Ω → F} (h : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h' : ∀ (L₁ : StrongDual ℝ E) (L₂ : StrongDual ℝ F), cov[L₁ ∘ X, L₂ ∘ Y; P] = 0) :
    IndepFun X Y P := by
  have := h.isProbabilityMeasure
  have := h.fst
  have := h.snd
  rw [indepFun_iff_charFunDual_prod h.fst.aemeasurable h.snd.aemeasurable]
  intro L
  have : L ∘ (fun ω ↦ (X ω, Y ω)) = (L ∘L (.inl ℝ E F)) ∘ X + (L ∘L (.inr ℝ E F)) ∘ Y := by
    ext; simp only [Function.comp_apply, ← comp_inl_add_comp_inr, Pi.add_apply]
  rw [h.charFunDual_map_eq, h.fst.charFunDual_map_eq, h.snd.charFunDual_map_eq, ← exp_add,
    sub_add_sub_comm, ← add_mul, integral_complex_ofReal, integral_complex_ofReal,
    integral_complex_ofReal, ← ofReal_add, ← integral_add, ← add_div, ← ofReal_add, this,
    variance_add, h', mul_zero, add_zero]
  · congr
  · exact (h.fst.map _).memLp_two
  · exact (h.snd.map _).memLp_two
  · exact (h.fst.map _).integrable
  · exact (h.snd.map _).integrable

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.iIndepFun_of_cov' {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : Π i, Ω → (E i)} (h : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h' : ∀ i j, i ≠ j → ∀ (x : E i) (y : E j),
      cov[fun ω ↦ ⟪x, X i ω⟫, fun ω ↦ ⟪y, X j ω⟫; P] = 0) :
    iIndepFun X P :=
  h.iIndepFun_of_cov fun i j hij _ _ ↦ by
    simpa [← InnerProductSpace.inner_toDual_symm_eq_self] using h' i j hij ..

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.indepFun_of_cov' {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F]
    {X : Ω → E} {Y : Ω → F} (h : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h' : ∀ x y, cov[fun ω ↦ ⟪x, X ω⟫, fun ω ↦ ⟪y, Y ω⟫; P] = 0) :
    IndepFun X Y P :=
  h.indepFun_of_cov fun _ _ ↦ by simpa [← InnerProductSpace.inner_toDual_symm_eq_self] using h' ..

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.iIndepFun_of_cov'' {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {X : (i : ι) → κ i → Ω → ℝ} (h : HasGaussianLaw (fun ω i j ↦ X i j ω) P)
    (h' : ∀ i j, i ≠ j → ∀ k l, cov[X i k, X j l; P] = 0) :
    iIndepFun (fun i ω j ↦ X i j ω) P := by
  have := h.isProbabilityMeasure
  have : (fun i ω j ↦ X i j ω) = fun i ↦ (ofLp ∘ (toLp 2 ∘ fun ω j ↦ X i j ω)) := by
    ext; simp
  rw [this]
  refine iIndepFun.comp (HasGaussianLaw.iIndepFun_of_cov' ?_ fun i j hij x y ↦ ?_) _
    (by fun_prop)
  · let L : ((i : ι) → κ i → ℝ) →L[ℝ] ((i : ι) → PiLp 2 (fun j : κ i ↦ ℝ)) :=
      { toFun x i := toLp 2 (x i)
        map_add' x y := by ext; simp
        map_smul' m x := by ext; simp
        cont := by fun_prop }
    exact h.map L
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x, ← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right, h' i j hij k l, mul_zero, mul_zero]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun j ↦ ((h.eval i).eval j).memLp_two.const_mul _
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun i ↦ ((h.eval j).eval i).memLp_two.const_mul _

open RealInnerProductSpace in
lemma HasGaussianLaw.iIndepFun_of_covariance_eq_zero {X : ι → Ω → ℝ}
    (h1 : HasGaussianLaw (fun ω ↦ (X · ω)) P) (h2 : ∀ i j : ι, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P := by
  refine h1.iIndepFun_of_cov fun i j hij L₁ L₂ ↦ ?_
  simp [← InnerProductSpace.inner_toDual_symm_eq_self, Function.comp_def,
    covariance_mul_const_right, covariance_mul_const_left, h2, hij]

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.indepFun_of_cov'' {κ : Type*} [Fintype κ]
    {X : ι → Ω → ℝ} {Y : κ → Ω → ℝ} (h : HasGaussianLaw (fun ω ↦ (fun i ↦ X i ω, fun j ↦ Y j ω)) P)
    (h' : ∀ i j, cov[X i, Y j; P] = 0) :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P := by
  have := h.isProbabilityMeasure
  have _ i := h.fst.eval i
  have _ j := h.snd.eval j
  have hX : (fun ω i ↦ X i ω) = (ofLp ∘ (toLp 2 ∘ fun ω i ↦ X i ω)) := by
    ext; simp
  have hY : (fun ω j ↦ Y j ω) = (ofLp ∘ (toLp 2 ∘ fun ω j ↦ Y j ω)) := by
    ext; simp
  rw [hX, hY]
  refine IndepFun.comp (HasGaussianLaw.indepFun_of_cov' ?_ fun x y ↦ ?_) (by fun_prop) (by fun_prop)
  · have : (fun ω ↦ ((toLp 2 ∘ fun ω i ↦ X i ω) ω, (toLp 2 ∘ fun ω j ↦ Y j ω) ω)) =
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm.toContinuousLinearMap.prodMap
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm.toContinuousLinearMap) ∘
          (fun ω ↦ (fun i ↦ X i ω, fun j ↦ Y j ω)) := by
      ext; all_goals simp
    rw [this]
    exact h.map _
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x, ← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right, h', mul_zero, mul_zero]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
    EuclideanSpace.basisFun_inner]
    exact fun i ↦ (h.fst.eval i).memLp_two.const_mul _
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun j ↦ (h.snd.eval j).memLp_two.const_mul _

lemma HasGaussianLaw.indepFun_of_covariance_eq_zero {X Y : Ω → ℝ}
    (h1 : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) (h2 : cov[X, Y; P] = 0) :
    IndepFun X Y P := by
  refine h1.indepFun_of_cov fun L₁ L₂ ↦ ?_
  simp [← InnerProductSpace.inner_toDual_symm_eq_self, Function.comp_def,
    covariance_mul_const_right, covariance_mul_const_left, h2]

variable {X Y : Ω → ℝ} {μX μY : ℝ} {vX vY : ℝ≥0}

lemma IndepFun.hasLaw_sub_of_gaussian
    (hX : HasLaw X (gaussianReal μX vX) P) (hY : HasLaw Y (gaussianReal μY vY) P)
    (h1 : IndepFun X (Y - X) P) (h2 : vX ≤ vY) :
    HasLaw (Y - X) (gaussianReal (μY - μX) (vY - vX)) P where
  map_eq := by
    have : IsProbabilityMeasure P := hX.hasGaussianLaw.isProbabilityMeasure
    refine Measure.ext_of_charFun <| funext fun t ↦ ?_
    apply mul_left_cancel₀ (a := charFun (P.map X) t)
    · rw [hX.map_eq, charFun_gaussianReal]
      exact Complex.exp_ne_zero _
    · rw [← Pi.mul_apply, ← h1.charFun_map_add_eq_mul, add_sub_cancel, hY.map_eq, hX.map_eq,
        charFun_gaussianReal, charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add,
        NNReal.coe_sub h2, Complex.ofReal_sub]
      · congr
        field_simp
        push_cast
        ring
      all_goals fun_prop

lemma IndepFun.hasLaw_gaussianReal_of_add
    (hX : HasLaw X (gaussianReal μX vX) P) (hY : HasLaw (X + Y) (gaussianReal μY vY) P)
    (h : IndepFun X Y P) :
    HasLaw Y (gaussianReal (μY - μX) (vY - vX)) P := by
  have h' := h
  rw [show Y = X + Y - X by simp] at h' ⊢
  apply h'.hasLaw_sub_of_gaussian hX hY
  rw [← @Real.toNNReal_coe vY, ← @variance_id_gaussianReal μY vY, ← hY.variance_eq,
    h.variance_add, hX.variance_eq, variance_id_gaussianReal, Real.toNNReal_add,
    Real.toNNReal_coe]
  any_goals simp
  · exact variance_nonneg _ _
  · exact hX.hasGaussianLaw.memLp_two
  · convert hY.hasGaussianLaw.memLp_two.sub hX.hasGaussianLaw.memLp_two
    simp

lemma HasGaussianLaw.map_eq_gaussianReal {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasGaussianLaw X P) :
    P.map X = gaussianReal P[X] Var[X; P].toNNReal := by
  rw [hX.isGaussian_map.eq_gaussianReal, integral_map, variance_map]
  · rfl
  all_goals fun_prop

lemma HasGaussianLaw.charFun_map_real {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} (hX : HasGaussianLaw X P) (t : ℝ) :
    charFun (P.map X) t = exp (t * P[X] * I - t ^ 2 * Var[X; P] / 2) := by
  rw [hX.map_eq_gaussianReal, charFun_gaussianReal]
  simp [variance_nonneg, integral_complex_ofReal, mul_comm]

lemma IndepFun.hasGaussianLaw_of_add_real
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw (X + Y) P) (h : IndepFun X Y P) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    have h1 : HasLaw X (gaussianReal _ _) P := ⟨hX.aemeasurable, hX.map_eq_gaussianReal⟩
    have h2 : HasLaw (X + Y) (gaussianReal _ _) P := ⟨hY.aemeasurable, hY.map_eq_gaussianReal⟩
    have := h.hasLaw_gaussianReal_of_add h1 h2
    exact this.hasGaussianLaw.isGaussian_map

lemma IndepFun.hasGaussianLaw_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {X Y : Ω → E} (hX : HasGaussianLaw X P)
    (hY : HasGaussianLaw Y P) (h : IndepFun X (Y - X) P) :
    HasGaussianLaw (Y - X) P where
  isGaussian_map := by
    refine ⟨fun L ↦ ?_⟩
    conv => enter [2, 1, 2, x]; change id (L x)
    rw [← integral_map, ← variance_id_map]
    · refine @IsGaussian.eq_gaussianReal _ ?_
      rw [AEMeasurable.map_map_of_aemeasurable]
      · refine @HasGaussianLaw.isGaussian_map (self := ?_)
        apply IndepFun.hasGaussianLaw_of_add_real (X := L ∘ X)
        · exact hX.map L
        · rw [← map_comp_add, add_sub_cancel]
          exact hY.map L
        · exact h.comp L.measurable L.measurable
      · fun_prop
      · exact hY.aemeasurable.sub hX.aemeasurable
    all_goals fun_prop

end ProbabilityTheory
