/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
public import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Independence of Gaussian random variables

In this file we prove some results linking Gaussian random variables and independence. It is
a well known fact that if `(X, Y)` is Gaussian, then `X` and `Y` are independent if their covariance
is zero. We prove many versions of this theorem in different settings: in Banach spaces,
Hilbert spaces, and for families of real random variables.

We also prove that independent Gaussian random variables are jointly Gaussian.

## Main statements

* `iIndepFun.hasGaussianLaw`: Independent Gaussian random variables are jointly Gaussian,
  indexed version.
* `IndepFun.hasGaussianLaw`: Independent Gaussian random variables are jointly Gaussian,
  product version.
* `HasGaussianLaw.iIndepFun_of_covariance_eq_zero`: If $(X_i)_{i \in \iota}$ are jointly Gaussian,
  then they are independent if for all $i \ne j$, \mathrm{Cov}(X_i, X_j) = 0$.
* `HasGaussianLaw.indepFun_of_covariance_eq_zero`: If $(X, Y)$ is Gaussian,
  then $X$ and $Y$ are independent if $\mathrm{Cov}(X, Y) = 0$.

## Tags

Gaussian random variable
-/

open MeasureTheory WithLp Complex Finset ContinuousLinearMap InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}


section Diagonal

namespace ContinuousLinearMap

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  {L : (i : ι) → StrongDual ℝ (E i) →L[ℝ] StrongDual ℝ (E i) →L[ℝ] ℝ}

/-- Given `L i : (E i)' × (E i)' → ℝ` a family of continuous bilinear forms,
`diagonalStrongDualPi L` is the continuous bilinear form over `(Π i, E i)'`
which maps `(x, y) : (Π i, E i)' × (Π i, E i)'` to
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
`diagonalStrongDualProd L₁ L₂` is the continuous bilinear form over `(E × F)'`
which maps `(x, y) : (E × F)' × (E × F)'` to
`L₁ (fun (a, b) ↦ x a) (fun (a, b) ↦ y a) + L₂ (fun (a, b) ↦ x b) (fun (a, b) ↦ y b)`.

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
    · grw [le_opNorm₂, opNorm_comp_le, opNorm_comp_le, norm_inr_le_one]
      simp

lemma diagonalStrongDualProd_apply (x y : StrongDual ℝ (E × F)) :
    diagonalStrongDualProd L₁ L₂ x y =
    L₁ (x ∘L (inl ℝ E F)) (y ∘L (inl ℝ E F)) + L₂ (x ∘L (inr ℝ E F)) (y ∘L (inr ℝ E F)) := rfl

lemma toBilinForm_diagonalStrongDualProd_apply (x y : StrongDual ℝ (E × F)) :
    (diagonalStrongDualProd L₁ L₂).toBilinForm x y =
    L₁.toBilinForm (x ∘L (inl ℝ E F)) (y ∘L (inl ℝ E F)) +
    L₂.toBilinForm (x ∘L (inr ℝ E F)) (y ∘L (inr ℝ E F)) := rfl

lemma isPosSemidef_diagonalStrongDualProd
    (h₁ : L₁.toBilinForm.IsPosSemidef) (h₂ : L₂.toBilinForm.IsPosSemidef) :
    (diagonalStrongDualProd L₁ L₂).toBilinForm.IsPosSemidef where
  eq x y := by
    simp_rw [toBilinForm_diagonalStrongDualProd_apply, h₁.eq, h₂.eq]
  nonneg x := by
    rw [toBilinForm_diagonalStrongDualProd_apply]
    exact add_nonneg (h₁.nonneg _) (h₂.nonneg _)

end Prod

end ContinuousLinearMap

end Diagonal


public section

namespace ProbabilityTheory

section iIndepFun

variable {ι : Type*} [Finite ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]

section NormedSpace

variable [∀ i, NormedSpace ℝ (E i)] {X : Π i, Ω → (E i)}

/-- Independent Gaussian random variables are jointly Gaussian. -/
lemma iIndepFun.hasGaussianLaw (hX1 : ∀ i, HasGaussianLaw (X i) P) (hX2 : iIndepFun X P) :
    HasGaussianLaw (fun ω ↦ (X · ω)) P where
  isGaussian_map := by
    have := hX2.isProbabilityMeasure
    let := Fintype.ofFinite ι
    rw [isGaussian_iff_gaussian_charFunDual]
    classical
    refine ⟨fun i ↦ ∫ x, x ∂P.map (X i),
      .diagonalStrongDualPi (fun i ↦ covarianceBilinDual (P.map (X i))),
      isPosSemidef_diagonalStrongDualPi (fun _ ↦ isPosSemidef_covarianceBilinDual), fun L ↦ ?_⟩
    rw [(iIndepFun_iff_charFunDual_pi (by fun_prop)).1 hX2]
    simp only [← LinearMap.sum_single_apply E (fun i ↦ ∫ x, x ∂P.map (X i)), map_sum, ofReal_sum,
      sum_mul, diagonalStrongDualPi_apply, sum_div, ← sum_sub_distrib, exp_sum]
    congr with i
    rw [(hX1 i).isGaussian_map.charFunDual_eq, integral_complex_ofReal, integral_comp_id_comm,
      covarianceBilinDual_self_eq_variance]
    · rfl
    · exact (hX1 i).isGaussian_map.memLp_two_id
    · exact (hX1 i).isGaussian_map.integrable_id

/-- If $(X_i)_{i \in \iota}$ are jointly Gaussian and uncorrelated, then they are independent. -/
lemma HasGaussianLaw.iIndepFun_of_covariance_strongDual (hX : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h : ∀ i j, i ≠ j → ∀ (L₁ : StrongDual ℝ (E i)) (L₂ : StrongDual ℝ (E j)),
      cov[L₁ ∘ (X i), L₂ ∘ (X j); P] = 0) :
    iIndepFun X P := by
  simp_rw [Function.comp_def] at h
  have := hX.isProbabilityMeasure
  classical
  let := Fintype.ofFinite ι
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

/-- If $(X_i)_{i \in \iota}$ are jointly Gaussian and uncorrelated, then they are independent. -/
lemma HasGaussianLaw.iIndepFun_of_covariance_inner
    {X : Π i, Ω → (E i)} (hX : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h : ∀ i j, i ≠ j → ∀ (x : E i) (y : E j),
      cov[fun ω ↦ ⟪x, X i ω⟫, fun ω ↦ ⟪y, X j ω⟫; P] = 0) :
    iIndepFun X P :=
  hX.iIndepFun_of_covariance_strongDual fun i j hij L₁ L₂ ↦ by
    simpa using h i j hij ((toDual ℝ (E i)).symm L₁) ((toDual ℝ (E j)).symm L₂)

end InnerProductSpace

section Real

/-- If $((X_{i,j})_{j \in \kappa_i})_{i \in \iota}$ are jointly Gaussian, then they are independent
if for all $i_1 \ne i_2 \in \iota$ and for all $j_1 \in \kappa_{i_1}, j_2 \in \kappa_{i_2}$,
$\mathrm{Cov}(X_{i_1, j_1}, X_{i_2, j_2}) = 0$. -/
lemma HasGaussianLaw.iIndepFun_of_covariance_eval {κ : ι → Type*} [∀ i, Finite (κ i)]
    {X : (i : ι) → κ i → Ω → ℝ} (hX : HasGaussianLaw (fun ω i j ↦ X i j ω) P)
    (h : ∀ i j, i ≠ j → ∀ k l, cov[X i k, X j l; P] = 0) :
    iIndepFun (fun i ω j ↦ X i j ω) P := by
  have := hX.isProbabilityMeasure
  have : (fun i ω j ↦ X i j ω) = fun i ↦ (ofLp ∘ (toLp 2 ∘ fun ω j ↦ X i j ω)) := by ext; simp
  rw [this]
  let (i : ι) := Fintype.ofFinite (κ i)
  let := Fintype.ofFinite ι
  refine (HasGaussianLaw.iIndepFun_of_covariance_inner ?_ fun i j hij x y ↦ ?_).comp _ (by fun_prop)
  · exact hX.map_equiv (.piCongrRight (fun _ ↦ (PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm))
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x, ← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine sum_eq_zero fun k _ ↦ sum_eq_zero fun l _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right, h i j hij k l, mul_zero, mul_zero]
  · simpa using fun j ↦ ((hX.eval i).eval j).memLp_two.const_mul _
  · simpa using fun i ↦ ((hX.eval j).eval i).memLp_two.const_mul _

/-- If $(X_i)_{i \in \iota}$ are jointly Gaussian, then they are independent if for all $i \ne j$,
\mathrm{Cov}(X_i, X_j) = 0$. -/
lemma HasGaussianLaw.iIndepFun_of_covariance_eq_zero {X : ι → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (h : ∀ i j : ι, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P :=
  hX.iIndepFun_of_covariance_strongDual fun i j hij L₁ L₂ ↦ by
    simp [Function.comp_def, ← toDual_symm_apply, covariance_mul_const_right,
      covariance_mul_const_left, h, hij]

end Real

end iIndepFun

section IndepFun

variable {E F : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [MeasurableSpace F]
    [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- Independent Gaussian random variables are jointly Gaussian. -/
lemma IndepFun.hasGaussianLaw [NormedSpace ℝ E] [NormedSpace ℝ F] {X : Ω → E} {Y : Ω → F}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (hXY : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P where
  isGaussian_map := by
    have := hX.isProbabilityMeasure
    rw [isGaussian_iff_gaussian_charFunDual]
    classical
    refine ⟨(∫ x, x ∂P.map X, ∫ y, y ∂P.map Y),
      .diagonalStrongDualProd (covarianceBilinDual (P.map X)) (covarianceBilinDual (P.map Y)),
      isPosSemidef_diagonalStrongDualProd isPosSemidef_covarianceBilinDual
        isPosSemidef_covarianceBilinDual, fun L ↦ ?_⟩
    rw [(indepFun_iff_charFunDual_prod (by fun_prop) (by fun_prop)).1 hXY]
    have : (∫ x, x ∂Measure.map X P, ∫ y, y ∂Measure.map Y P) =
        ContinuousLinearMap.inl ℝ E F (∫ x, x ∂Measure.map X P) +
        ContinuousLinearMap.inr ℝ E F (∫ y, y ∂Measure.map Y P) := by simp
    simp only [this, map_add, ofReal_add, add_mul, diagonalStrongDualProd_apply, add_div,
      add_sub_add_comm, exp_add]
    congr
    · rw [hX.isGaussian_map.charFunDual_eq, integral_complex_ofReal, integral_comp_id_comm,
        covarianceBilinDual_self_eq_variance]
      · rfl
      · exact hX.isGaussian_map.memLp_two_id
      · exact hX.isGaussian_map.integrable_id
    · rw [hY.isGaussian_map.charFunDual_eq, integral_complex_ofReal, integral_comp_id_comm,
        covarianceBilinDual_self_eq_variance]
      · rfl
      · exact hY.isGaussian_map.memLp_two_id
      · exact hY.isGaussian_map.integrable_id

/-- If $(X, Y)$ is Gaussian, then $X$ and $Y$ are independent if they are uncorrelated. -/
lemma HasGaussianLaw.indepFun_of_covariance_strongDual [NormedSpace ℝ E] [NormedSpace ℝ F]
    {X : Ω → E} {Y : Ω → F} (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h : ∀ (L₁ : StrongDual ℝ E) (L₂ : StrongDual ℝ F), cov[L₁ ∘ X, L₂ ∘ Y; P] = 0) :
    IndepFun X Y P := by
  have := hXY.isProbabilityMeasure
  rw [indepFun_iff_charFunDual_prod hXY.fst.aemeasurable hXY.snd.aemeasurable]
  intro L
  have : L ∘ (fun ω ↦ (X ω, Y ω)) = (L ∘L (.inl ℝ E F)) ∘ X + (L ∘L (.inr ℝ E F)) ∘ Y := by
    ext; simp [- coe_comp', ← comp_inl_add_comp_inr]
  rw [hXY.charFunDual_map_eq, hXY.fst.charFunDual_map_eq, hXY.snd.charFunDual_map_eq, ← exp_add,
    sub_add_sub_comm, ← add_mul, ← ofReal_add, ← integral_add, ← add_div, ← ofReal_add, this,
    variance_add, h, mul_zero, add_zero]
  · rfl
  · exact (hXY.fst.map _).memLp_two
  · exact (hXY.snd.map _).memLp_two
  · exact (hXY.fst.map _).integrable
  · exact (hXY.snd.map _).integrable

/-- If $(X, Y)$ is Gaussian, then $X$ and $Y$ are independent if they are uncorrelated. -/
lemma HasGaussianLaw.indepFun_of_covariance_inner [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    {X : Ω → E} {Y : Ω → F} (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h : ∀ x y, cov[fun ω ↦ ⟪x, X ω⟫, fun ω ↦ ⟪y, Y ω⟫; P] = 0) :
    IndepFun X Y P :=
  hXY.indepFun_of_covariance_strongDual fun L₁ L₂ ↦ by
    simpa using h ((toDual ℝ E).symm L₁) ((toDual ℝ F).symm L₂)

/-- If $((X_i)_{i \in \iota}, (Y_j)_{j \in \kappa})$ is Gaussian, then $(X_i)_{i \in \iota}$ and
$(Y_j)_{j \in \kappa}$ are independent if for all $i \in \iota, j \in \kappa$,
$\mathrm{Cov}(X_i, Y_j) = 0$. -/
lemma HasGaussianLaw.indepFun_of_covariance_eval {ι κ : Type*} [Finite ι] [Finite κ]
    {X : ι → Ω → ℝ} {Y : κ → Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω ↦ (fun i ↦ X i ω, fun j ↦ Y j ω)) P)
    (h : ∀ i j, cov[X i, Y j; P] = 0) :
    IndepFun (fun ω i ↦ X i ω) (fun ω j ↦ Y j ω) P := by
  have := hXY.isProbabilityMeasure
  have hX : (fun ω i ↦ X i ω) = (ofLp ∘ (toLp 2 ∘ fun ω i ↦ X i ω)) := by ext; simp
  have hY : (fun ω j ↦ Y j ω) = (ofLp ∘ (toLp 2 ∘ fun ω j ↦ Y j ω)) := by ext; simp
  rw [hX, hY]
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  refine IndepFun.comp (HasGaussianLaw.indepFun_of_covariance_inner ?_ fun x y ↦ ?_)
    (by fun_prop) (by fun_prop)
  · exact hXY.map_equiv (.prodCongr (PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ ↦ ℝ)).symm)
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x, ← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine sum_eq_zero fun k _ ↦ sum_eq_zero fun l _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right, h, mul_zero, mul_zero]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
    EuclideanSpace.basisFun_inner]
    exact fun i ↦ (hXY.fst.eval i).memLp_two.const_mul _
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun j ↦ (hXY.snd.eval j).memLp_two.const_mul _

/-- If $(X, Y)$ is Gaussian, then $X$ and $Y$ are independent if $\mathrm{Cov}(X, Y) = 0$. -/
lemma HasGaussianLaw.indepFun_of_covariance_eq_zero {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) (h : cov[X, Y; P] = 0) :
    IndepFun X Y P :=
  hXY.indepFun_of_covariance_strongDual fun L₁ L₂ ↦ by
    simp [Function.comp_def, ← toDual_symm_apply, covariance_mul_const_right,
      covariance_mul_const_left, h]

end IndepFun

section AddSub

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

lemma iIndepFun.hasGaussianLaw_sum [CompleteSpace E] {ι : Type*} [Fintype ι] {X : ι → Ω → E}
    (hX1 : ∀ i, HasGaussianLaw (X i) P) (hX2 : iIndepFun X P) :
    HasGaussianLaw (∑ i, X i) P :=
  (hX2.hasGaussianLaw hX1).sum

lemma iIndepFun.hasGaussianLaw_fun_sum [CompleteSpace E] {ι : Type*} [Fintype ι] {X : ι → Ω → E}
    (hX1 : ∀ i, HasGaussianLaw (X i) P) (hX2 : iIndepFun X P) :
    HasGaussianLaw (fun ω ↦ ∑ i, X i ω) P :=
    (hX2.hasGaussianLaw hX1).fun_sum

lemma iIndepFun.hasGaussianLaw_add [CompleteSpace E] {X Y : Ω → E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (X + Y) P :=
  (h.hasGaussianLaw hX hY).add

lemma iIndepFun.hasGaussianLaw_fun_add [CompleteSpace E] {X Y : Ω → E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (fun ω ↦ X ω + Y ω) P :=
  (h.hasGaussianLaw hX hY).add

lemma iIndepFun.hasGaussianLaw_sub [CompleteSpace E] {X Y : Ω → E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (X - Y) P :=
  (h.hasGaussianLaw hX hY).sub

lemma iIndepFun.hasGaussianLaw_fun_sub [CompleteSpace E] {X Y : Ω → E}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P) (h : X ⟂ᵢ[P] Y) :
    HasGaussianLaw (fun ω ↦ X ω - Y ω) P :=
  (h.hasGaussianLaw hX hY).sub

/-- If `X` and `Y` are two Gaussian random variables such that `X` and `Y - X` are independent,
then `Y - X` is Gaussian.

This lemma is useful to prove that a process with independent increments and whose marginals
are Gaussian has Gaussian increments. -/
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
