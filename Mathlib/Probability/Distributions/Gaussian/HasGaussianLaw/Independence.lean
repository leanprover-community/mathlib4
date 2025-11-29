/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
public import Mathlib.Probability.HasLaw

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
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

open MeasureTheory WithLp Complex Finset ContinuousLinearMap
open scoped ENNReal NNReal RealInnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section Diagonal

namespace ContinuousLinearMap

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {L : (i : ι) → StrongDual ℝ (E i) →L[ℝ] StrongDual ℝ (E i) →L[ℝ] ℝ}

/-- Given `L i : (E i)' × (E i)' → ℝ` a family of continuous bilinear forms,
`diagonalStrongDualPi L` is a continuous bilinear form is the continuous bilinear form over
`(Π i, E i)'` which maps `(x, y) : (Π i, E i)' × (Π i, E i)'` to
`∑ i, L i (fun a ↦ x aᵢ) (fun a ↦ y aᵢ)`.

This is an implementation detail used in `iIndepFun.hasGaussianLaw`. -/
noncomputable
def diagonalStrongDualPi (L : (i : ι) → StrongDual ℝ (E i) →L[ℝ] StrongDual ℝ (E i) →L[ℝ] ℝ) :
    StrongDual ℝ (Π i, E i) →L[ℝ] StrongDual ℝ (Π i, E i) →L[ℝ] ℝ :=
  letI g : LinearMap.BilinForm ℝ (StrongDual ℝ (Π i, E i)) := LinearMap.mk₂ ℝ
    (fun x y ↦ ∑ i, L i (x ∘L (single ℝ E i)) (y ∘L (single ℝ E i)))
    (fun x y z ↦ by simp [sum_add_distrib])
    (fun c m n ↦ by simp [mul_sum])
    (fun x y z ↦ by simp [sum_add_distrib])
    (fun c m n ↦ by simp [mul_sum])
  LinearMap.mkContinuous₂ g (∑ i, ‖L i‖) <| by
    intro x y
    simp only [LinearMap.mk₂_apply, g]
    grw [norm_sum_le, sum_mul, sum_mul]
    gcongr with i _
    grw [le_opNorm₂, opNorm_comp_le, opNorm_comp_le, norm_single_le_one]
    simp

lemma diagonalStrongDualPi_apply (x y : StrongDual ℝ (Π i, E i)) :
    diagonalStrongDualPi L x y = ∑ i, L i (x ∘L (.single ℝ E i)) (y ∘L (.single ℝ E i)) := rfl

lemma toBilinForm_diagonalStrongDualPi_apply (x y : StrongDual ℝ (Π i, E i)) :
    (diagonalStrongDualPi L).toBilinForm x y =
    ∑ i, (L i).toBilinForm (x ∘L (.single ℝ E i)) (y ∘L (.single ℝ E i)) := rfl

lemma isPosSemidef_diagonalStrongDualPi (hL : ∀ i, (L i).toBilinForm.IsPosSemidef) :
    (diagonalStrongDualPi L).toBilinForm.IsPosSemidef where
  eq x y := by
    simp_rw [toBilinForm_diagonalStrongDualPi_apply, fun i ↦ (hL i).eq]
  nonneg x := by
    rw [toBilinForm_diagonalStrongDualPi_apply]
    exact sum_nonneg fun i _ ↦ (hL i).nonneg _

end Pi

section Prod

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {L₁ : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ}
  {L₂ : StrongDual ℝ F →L[ℝ] StrongDual ℝ F →L[ℝ] ℝ}

/-- Given `L₁ : E' × E' → ℝ` and `L₂ : F' × F' → ℝ` two continuous bilinear forms,
`diagonalStrongDualProd L` is a continuous bilinear form is the continuous bilinear form over
`(Π i, E i)'` which maps `(x, y) : (Π i, E i)' × (Π i, E i)'` to
`∑ i, L i (fun a ↦ x aᵢ) (fun a ↦ y aᵢ)`.

This is an implementation detail used in `IndepFun.hasGaussianLaw`. -/
noncomputable
def diagonalStrongDualProd
    (L₁ : StrongDual ℝ E →L[ℝ] StrongDual ℝ E →L[ℝ] ℝ)
    (L₂ : StrongDual ℝ F →L[ℝ] StrongDual ℝ F →L[ℝ] ℝ) :
    StrongDual ℝ (E × F) →L[ℝ] StrongDual ℝ (E × F) →L[ℝ] ℝ :=
  letI g : LinearMap.BilinForm ℝ (StrongDual ℝ (E × F)) := LinearMap.mk₂ ℝ
    (fun x y ↦ L₁ (x ∘L (inl ℝ E F)) (y ∘L (inl ℝ E F)) + L₂ (x ∘L (inr ℝ E F)) (y ∘L (inr ℝ E F)))
    (fun x y z ↦ by simp [add_add_add_comm])
    (fun c m n ↦ by simp [mul_add])
    (fun x y z ↦ by simp [add_add_add_comm])
    (fun c m n ↦ by simp [mul_add])
  LinearMap.mkContinuous₂ g (‖L₁‖ + ‖L₂‖) <| by
    intro x y
    simp only [LinearMap.mk₂_apply, g]
    grw [norm_add_le, add_mul, add_mul]
    gcongr
    · grw [le_opNorm₂, opNorm_comp_le, opNorm_comp_le, norm_inl_le_one]
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
    exact sum_nonneg fun i _ ↦ (hL i).nonneg _

end Pi

end ContinuousLinearMap

end Diagonal

public section

namespace ProbabilityTheory

section iIndepFun

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]

section NormedSpace

variable [∀ i, NormedSpace ℝ (E i)] {X : Π i, Ω → (E i)}

/-- Independent Gaussian random variables are jointly Gaussian. -/
lemma iIndepFun.hasGaussianLaw (h : ∀ i, HasGaussianLaw (X i) P) (hX : iIndepFun X P) :
    HasGaussianLaw (fun ω ↦ (X · ω)) P where
  isGaussian_map := by
    have := hX.isProbabilityMeasure
    have _ i := (h i).isGaussian_map
    rw [isGaussian_iff_gaussian_charFunDual]
    classical
    refine ⟨fun i ↦ ∫ x, x ∂P.map (X i),
      .diagonalStrongDual (fun i ↦ covarianceBilinDual (P.map (X i))),
      isPosSemidef_diagonalStrongDual (fun _ ↦ isPosSemidef_covarianceBilinDual), fun L ↦ ?_⟩
    rw [(iIndepFun_iff_charFunDual_pi (by fun_prop)).1 hX]
    simp only [← LinearMap.sum_single_apply E (fun i ↦ ∫ x, x ∂P.map (X i)), map_sum, ofReal_sum,
      sum_mul, diagonalStrongDual_apply, sum_div, ← sum_sub_distrib, exp_sum]
    congr with i
    rw [(h i).isGaussian_map.charFunDual_eq, integral_complex_ofReal, integral_comp_id_comm,
      covarianceBilinDual_self_eq_variance]
    · rfl
    · exact IsGaussian.memLp_two_id
    · exact (h i).isGaussian_map.integrable_id

/-- If $(X_i)_{i \in \iota}$ are jointly Gaussian, then they are independent if they are
uncorrelated. -/
lemma HasGaussianLaw.iIndepFun_of_covariance_strongDual (hX : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h : ∀ i j, i ≠ j → ∀ (L₁ : StrongDual ℝ (E i)) (L₂ : StrongDual ℝ (E j)),
      cov[L₁ ∘ (X i), L₂ ∘ (X j); P] = 0) :
    iIndepFun X P := by
  simp_rw [Function.comp_def] at h
  have := hX.isProbabilityMeasure
  classical
  rw [iIndepFun_iff_charFunDual_pi fun i ↦ hX.aemeasurable.eval i]
  intro L
  have this ω : L (X · ω) = ∑ i, (L ∘L (single ℝ E i)) (X i ω) := by
    simp [← map_sum, LinearMap.sum_single_apply]
  simp_rw [hX.charFunDual_map_eq_fun, fun i ↦ (hX.eval i).charFunDual_map_eq_fun, ← Complex.exp_sum,
    sum_sub_distrib, ← sum_mul, this]
  congr
  · simp_rw [← Complex.ofReal_sum]
    rw [integral_finset_sum _ fun i _ ↦ ((hX.eval i).map_fun _).integrable.ofReal]
  · rw [variance_fun_sum fun i ↦ ((hX.eval i).map_fun _).memLp_two]
    simp only [← sum_div, ← ofReal_sum, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_left_inj', ofReal_inj]
    congr with i
    rw [sum_eq_single_of_mem i (by grind) (fun j _ hij ↦ h i j hij.symm _ _),
      covariance_self ((hX.eval i).map_fun _).aemeasurable]

end NormedSpace

section InnerProductSpace

variable [∀ i, InnerProductSpace ℝ (E i)]

/-- If $(X_i)_{i \in \iota}$ are jointly Gaussian, then they are independent if they are
uncorrelated. -/
lemma HasGaussianLaw.iIndepFun_of_covariance_inner
    {X : Π i, Ω → (E i)} (hX : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h : ∀ i j, i ≠ j → ∀ (x : E i) (y : E j),
      cov[fun ω ↦ ⟪x, X i ω⟫, fun ω ↦ ⟪y, X j ω⟫; P] = 0) :
    iIndepFun X P :=
  hX.iIndepFun_of_covariance_strongDual fun i j hij _ _ ↦ by
    simpa [← InnerProductSpace.inner_toDual_symm_eq_self] using h i j hij ..

end InnerProductSpace

section Real

/-- If $((X_{i,j})_{j \in \kappa_i})_{i \in \iota}$ are jointly Gaussian, then they are independent
if for all $i_1 \ne i_2 \in \iota$ and for all $j_1 \in \kappa_{i_1}, j_2 \in \kappa_{i_2}$,
$\mathrm{Cov}(X_{i_1, j_1}, X_{i_2, j_2}) = 0$. -/
lemma HasGaussianLaw.iIndepFun_of_covariance_eval {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {X : (i : ι) → κ i → Ω → ℝ} (h : HasGaussianLaw (fun ω i j ↦ X i j ω) P)
    (h' : ∀ i j, i ≠ j → ∀ k l, cov[X i k, X j l; P] = 0) :
    iIndepFun (fun i ω j ↦ X i j ω) P := by
  have := h.isProbabilityMeasure
  have : (fun i ω j ↦ X i j ω) = fun i ↦ (ofLp ∘ (toLp 2 ∘ fun ω j ↦ X i j ω)) := by ext; simp
  rw [this]
  refine iIndepFun.comp (HasGaussianLaw.iIndepFun_of_covariance_inner ?_ fun i j hij x y ↦ ?_) _
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
    refine sum_eq_zero fun k _ ↦ sum_eq_zero fun l _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right, h' i j hij k l, mul_zero, mul_zero]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun j ↦ ((h.eval i).eval j).memLp_two.const_mul _
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun i ↦ ((h.eval j).eval i).memLp_two.const_mul _

/-- If $(X_i)_{i \in \iota}$ are jointly Gaussian, then they are independent if for all $i \ne j$,
\mathrm{Cov}(X_i, X_j) = 0$. -/
lemma HasGaussianLaw.iIndepFun_of_covariance {X : ι → Ω → ℝ}
    (h1 : HasGaussianLaw (fun ω ↦ (X · ω)) P) (h2 : ∀ i j : ι, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P := by
  refine h1.iIndepFun_of_covariance_strongDual fun i j hij L₁ L₂ ↦ ?_
  simp [← InnerProductSpace.inner_toDual_symm_eq_self, Function.comp_def,
    covariance_mul_const_right, covariance_mul_const_left, h2, hij]

end Real

end iIndepFun

section IndepFun

variable {E F : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [MeasurableSpace F]
    [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- If $(X, Y)$ is Gaussian, then $X$ and $Y$ are independent if they are uncorrelated. -/
lemma HasGaussianLaw.indepFun_of_covariance_strongDual [NormedSpace ℝ E] [NormedSpace ℝ F]
    {X : Ω → E} {Y : Ω → F} (h : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h' : ∀ (L₁ : StrongDual ℝ E) (L₂ : StrongDual ℝ F), cov[L₁ ∘ X, L₂ ∘ Y; P] = 0) :
    IndepFun X Y P := by
  have := h.isProbabilityMeasure
  rw [indepFun_iff_charFunDual_prod h.fst.aemeasurable h.snd.aemeasurable]
  intro L
  have : L ∘ (fun ω ↦ (X ω, Y ω)) = (L ∘L (.inl ℝ E F)) ∘ X + (L ∘L (.inr ℝ E F)) ∘ Y := by
    ext; simp [- coe_comp', ← comp_inl_add_comp_inr]
  rw [h.charFunDual_map_eq, h.fst.charFunDual_map_eq, h.snd.charFunDual_map_eq, ← exp_add,
    sub_add_sub_comm, ← add_mul, ← ofReal_add, ← integral_add, ← add_div, ← ofReal_add, this,
    variance_add, h', mul_zero, add_zero]
  · rfl
  · exact (h.fst.map _).memLp_two
  · exact (h.snd.map _).memLp_two
  · exact (h.fst.map _).integrable
  · exact (h.snd.map _).integrable

/-- If $(X, Y)$ is Gaussian, then $X$ and $Y$ are independent if they are uncorrelated. -/
lemma HasGaussianLaw.indepFun_of_covariance_inner [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    {X : Ω → E} {Y : Ω → F} (h : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h' : ∀ x y, cov[fun ω ↦ ⟪x, X ω⟫, fun ω ↦ ⟪y, Y ω⟫; P] = 0) :
    IndepFun X Y P :=
  h.indepFun_of_covariance_strongDual fun _ _ ↦ by
    simpa [← InnerProductSpace.inner_toDual_symm_eq_self] using h' ..

/-- If $((X_i)_{i \in \iota}, (Y_j)_{j \in \kappa})$ is Gaussian, then $(X_i)_{i \in \iota}$ and
$(Y_j)_{j \in \kappa}$ are independent if for all $i \in \iota, j \in \kappa$,
$\mathrm{Cov}(X_i, Y_j) = 0$. -/
lemma HasGaussianLaw.indepFun_of_covariance_eval {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : ι → Ω → ℝ} {Y : κ → Ω → ℝ} (h : HasGaussianLaw (fun ω ↦ (fun i ↦ X i ω, fun j ↦ Y j ω)) P)
    (h' : ∀ i j, cov[X i, Y j; P] = 0) :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P := by
  have := h.isProbabilityMeasure
  have hX : (fun ω i ↦ X i ω) = (ofLp ∘ (toLp 2 ∘ fun ω i ↦ X i ω)) := by ext; simp
  have hY : (fun ω j ↦ Y j ω) = (ofLp ∘ (toLp 2 ∘ fun ω j ↦ Y j ω)) := by ext; simp
  rw [hX, hY]
  refine IndepFun.comp (HasGaussianLaw.indepFun_of_covariance_inner ?_ fun x y ↦ ?_)
    (by fun_prop) (by fun_prop)
  · have : (fun ω ↦ ((toLp 2 ∘ fun ω i ↦ X i ω) ω, (toLp 2 ∘ fun ω j ↦ Y j ω) ω)) =
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm.toContinuousLinearMap.prodMap
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm.toContinuousLinearMap) ∘
          (fun ω ↦ (fun i ↦ X i ω, fun j ↦ Y j ω)) := by ext <;> simp
    rw [this]
    exact h.map _
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x, ← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine sum_eq_zero fun k _ ↦ sum_eq_zero fun l _ ↦ ?_
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
  refine h1.indepFun_of_covariance_strongDual fun L₁ L₂ ↦ ?_
  simp [← InnerProductSpace.inner_toDual_symm_eq_self, Function.comp_def,
    covariance_mul_const_right, covariance_mul_const_left, h2]

end IndepFun

section AddSub

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

lemma iIndepFun.hasGaussianLaw_sum [CompleteSpace E] {ι : Type*} [Fintype ι] {X : ι → Ω → E}
    (hX1 : ∀ i, HasGaussianLaw (X i) P) (hX2 : iIndepFun X P) :
    HasGaussianLaw (∑ i, X i) P :=
  (hX2.hasGaussianLaw hX1).sum

lemma iIndepFun.hasGaussianLaw_add [CompleteSpace E] {X Y : Ω → E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (X + Y) P :=
  (h.hasGaussianLaw hX1).sum

/-- If `X` and `Y` are two Gaussian random variables such that `X` and `Y - X` are independent,
then `Y - X` is Gaussian. -/
lemma IndepFun.hasGaussianLaw_sub_of_sub {X Y : Ω → E} (hX : HasGaussianLaw X P)
    (hY : HasGaussianLaw Y P) (h : IndepFun X (Y - X) P) :
    HasGaussianLaw (Y - X) P := by
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  rw [hasGaussianLaw_iff_charFunDual_map_eq (by fun_prop)]
  intro L
  apply mul_left_cancel₀ (a := charFunDual (P.map X) L)
  · simp [hX.charFunDual_map_eq]
  rw [← Pi.mul_apply, ← h.charFunDual_map_add_eq_mul, add_sub_cancel, hX.charFunDual_map_eq,
    ← exp_add, sub_add_sub_comm, ← add_mul, ← ofReal_add, ← integral_add, ← add_div, ← ofReal_add,
    ← IndepFun.variance_add, hY.charFunDual_map_eq]
  · congr with ω <;> simp
  any_goals fun_prop
  · exact (hX.map L).memLp_two
  · rw [map_comp_sub]
    exact (hY.map L).memLp_two.sub (hX.map L).memLp_two
  · exact h.comp (by fun_prop) (by fun_prop)
  · exact (hX.map L).integrable
  · rw [map_comp_sub]
    exact (hY.map L).integrable.sub (hX.map L).integrable

end AddSub

end ProbabilityTheory
