/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Gaussian random variables

In this file we define a predicate `HasGaussianLaw X P`, which states that under the probability
measure `P`, the random variable `X` has a Gaussian distribution, i.e. `IsGaussian (P.map X)`.

## Main definition

* `HasGaussianLaw X P`: The random variable `X` has a Gaussian distribution under the measure `P`.

## Tags

Gaussian random variable
-/

public section


open MeasureTheory WithLp Complex
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι E F : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → E}

section Basic

variable [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [mE : MeasurableSpace E]

/-- The predicate `HasGaussianLaw X P` means that under the measure `P`,
`X` has a Gaussian distribution. -/
structure HasGaussianLaw (X : Ω → E) (P : Measure Ω) : Prop where
  protected isGaussian_map : IsGaussian (P.map X)

lemma HasGaussianLaw.congr {Y : Ω → E} (hX : HasGaussianLaw X P) (h : ∀ᵐ ω ∂P, X ω = Y ω) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    rw [← Measure.map_congr h]
    exact hX.isGaussian_map

lemma IsGaussian.hasGaussianLaw [IsGaussian (P.map X)] : HasGaussianLaw X P where
  isGaussian_map := inferInstance

variable {mE} in
lemma IsGaussian.hasGaussianLaw_id {μ : Measure E} [IsGaussian μ] : HasGaussianLaw id μ where
  isGaussian_map := by rwa [Measure.map_id]

@[fun_prop, measurability]
lemma HasGaussianLaw.aemeasurable (hX : HasGaussianLaw X P) : AEMeasurable X P := by
  by_contra! h
  have := hX.isGaussian_map
  rw [Measure.map_of_not_aemeasurable h] at this
  exact this.toIsProbabilityMeasure.ne_zero _ rfl

lemma HasGaussianLaw.isProbabilityMeasure (hX : HasGaussianLaw X P) : IsProbabilityMeasure P where
  measure_univ := by
    have := hX.isGaussian_map
    rw [← Set.preimage_univ (f := X), ← Measure.map_apply_of_aemeasurable hX.aemeasurable .univ,
      measure_univ]

variable {mE} in
lemma HasLaw.hasGaussianLaw {μ : Measure E} (hX : HasLaw X μ P) [IsGaussian μ] :
    HasGaussianLaw X P where
  isGaussian_map := by rwa [hX.map_eq]

end Basic

namespace HasGaussianLaw

variable
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  (L : E →L[ℝ] F)

/-- A Gaussian random variable has moments of all orders. -/
lemma memLp [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P)
    {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp X p P := by
  rw [← Function.id_comp X, ← memLp_map_measure_iff]
  · exact hX.isGaussian_map.memLp_id _ p hp
  · exact aestronglyMeasurable_id
  · exact hX.aemeasurable

lemma memLp_two [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P) :
    MemLp X 2 P := hX.memLp (by norm_num)

lemma integrable [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P) :
    Integrable X P :=
  memLp_one_iff_integrable.1 <| hX.memLp (by norm_num)

lemma map (hX : HasGaussianLaw X P) : HasGaussianLaw (L ∘ X) P where
  isGaussian_map := by
    have := hX.isGaussian_map
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · infer_instance
    all_goals fun_prop (disch := assumption)

lemma map_fun (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω ↦ L (X ω)) P :=
  hX.map L

variable (L : E ≃L[ℝ] F)

lemma map_equiv (hX : HasGaussianLaw X P) : HasGaussianLaw (L ∘ X) P :=
  hX.map L.toContinuousLinearMap

lemma map_equiv_fun (hX : HasGaussianLaw X P) :
    HasGaussianLaw (fun ω ↦ L (X ω)) P := hX.map_equiv L

section SpecificMaps

lemma smul (c : ℝ) (hX : HasGaussianLaw X P) : HasGaussianLaw (c • X) P :=
  hX.map (.lsmul ℝ ℝ c)

lemma fun_smul (c : ℝ) (hX : HasGaussianLaw X P) :
    HasGaussianLaw (fun ω ↦ c • (X ω)) P :=
  hX.smul c

lemma neg (hX : HasGaussianLaw X P) : HasGaussianLaw (-X) P := by
  have : -X = (-1 : ℝ) • X := by simp
  rw [this]
  exact hX.smul _

lemma fun_neg (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω ↦ -(X ω)) P :=
  hX.neg

section Prod

variable [SecondCountableTopologyEither E F] {Y : Ω → F}

lemma toLp_prodMk (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ toLp p (X ω, Y ω)) P := by
  simp_rw [← WithLp.prodContinuousLinearEquiv_symm_apply p ℝ]
  exact hXY.map_equiv _

lemma fst (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw X P := by
  have : X = (ContinuousLinearMap.fst ℝ E F) ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  exact hXY.map _

lemma snd (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw Y P := by
  have : Y = (ContinuousLinearMap.snd ℝ E F) ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  exact hXY.map _

variable [SecondCountableTopology E] {Y : Ω → E}

lemma add (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (X + Y) P := by
  have : X + Y = (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) ∘
      (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  exact hXY.map _

lemma fun_add (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ X ω + Y ω) P :=
  hXY.add

lemma sub (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (X - Y) P := by
  have : X - Y = (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E) ∘
      (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  exact hXY.map _

lemma fun_sub (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ X ω - Y ω) P :=
  hXY.sub

end Prod

section Pi

variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}

lemma eval (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (i : ι) :
    HasGaussianLaw (X i) P := by
  have : X i = (ContinuousLinearMap.proj (R := ℝ) (φ := E) i) ∘ (fun ω ↦ (X · ω)) := by ext; simp
  rw [this]
  exact hX.map _

lemma prodMk (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (i j : ι) :
    HasGaussianLaw (fun ω ↦ (X i ω, X j ω)) P := by
  have : (fun ω ↦ (X i ω, X j ω)) =
      ((ContinuousLinearMap.proj (R := ℝ) (φ := E) i).prod
      (ContinuousLinearMap.proj (R := ℝ) (φ := E) j)) ∘ (fun ω ↦ (X · ω)) := by ext <;> simp
  rw [this]
  exact hX.map _

lemma toLp_pi (p : ℝ≥0∞) [Fact (1 ≤ p)] (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) :
    HasGaussianLaw (fun ω ↦ toLp p (X · ω)) P := by
  simp_rw [← PiLp.continuousLinearEquiv_symm_apply p ℝ]
  exact hX.map_equiv _

end Pi

end SpecificMaps

end HasGaussianLaw

section Independence

variable {ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

open ContinuousLinearMap in
lemma iIndepFun.hasGaussianLaw {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : Π i, Ω → (E i)} (h : ∀ i, HasGaussianLaw (X i) P) (hX : iIndepFun X P) :
    HasGaussianLaw (fun ω ↦ (X · ω)) P where
  isGaussian_map := by
    have := hX.isProbabilityMeasure
    obtain hι | hι := isEmpty_or_nonempty ι
    · have : P.map (fun ω ↦ fun x ↦ X x ω) = .dirac hι.elim := by
        ext s -
        apply Subsingleton.set_cases (p := fun s ↦ Measure.map _ _ s = _)
        · simp
        simp only [measure_univ]
        exact @measure_univ _ _ _ (Measure.isProbabilityMeasure_map (by fun_prop))
      rw [this]
      infer_instance
    classical
    rw [isGaussian_iff_gaussian_charFunDual]
    refine ⟨fun i ↦ ∫ ω, X i ω ∂P, .diagonalStrongDual (fun i ↦ covarianceBilinDual (P.map (X i))),
      ContinuousBilinForm.isPosSemidef_diagonalStrongDual
        (fun i ↦ isPosSemidef_covarianceBilinDual), fun L ↦ ?_⟩
    rw [(iIndepFun_iff_charFunDual_pi _).1 hX]
    · simp only [← sum_single_apply E (fun i ↦ ∫ ω, X i ω ∂P), map_sum, ofReal_sum, sum_mul,
      ContinuousBilinForm.diagonalStrongDual_apply, sum_div, ← sum_sub_distrib, exp_sum]
      congr with i
      rw [IsGaussian.charFunDual_eq, integral_complex_ofReal,
        ContinuousLinearMap.integral_comp_id_comm, covarianceBilinDual_self_eq_variance,
        integral_map]
      · simp
      · exact HasGaussianLaw.aemeasurable
      · exact aestronglyMeasurable_id
      · exact IsGaussian.memLp_two_id
      · exact IsGaussian.integrable_id
    · exact fun i ↦ HasGaussianLaw.aemeasurable

open ContinuousLinearMap in
lemma HasGaussianLaw.iIndepFun_of_cov {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : Π i, Ω → (E i)} (h : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h' : ∀ i j, i ≠ j → ∀ (L₁ : StrongDual ℝ (E i)) (L₂ : StrongDual ℝ (E j)),
      cov[L₁ ∘ (X i), L₂ ∘ (X j); P] = 0) :
    iIndepFun X P := by
  have := h.isProbabilityMeasure
  classical
  rw [iIndepFun_iff_charFunDual_pi]
  swap; · exact fun _ ↦ HasGaussianLaw.aemeasurable
  intro L
  simp_rw [IsGaussian.charFunDual_eq, ← Complex.exp_sum, sum_sub_distrib, ← sum_mul]
  congr
  · have this ω : L (X · ω) = ∑ i, L (single ℝ E i (X i ω)) := by
      simp [← map_sum, sum_single_apply]
    rw [integral_map h.aemeasurable (by fun_prop)]
    simp_rw [this, Complex.ofReal_sum]
    rw [integral_finset_sum _ fun _ _ ↦ HasGaussianLaw.integrable.ofReal]
    congr with i
    rw [integral_map HasGaussianLaw.aemeasurable (by fun_prop)]
    rfl
  · have this : L ∘ (fun ω i ↦ X i ω) = ∑ i, (L ∘L (single ℝ E i)) ∘ (X i) := by
      ext ω
      simp [← map_sum, sum_single_apply]
    rw [variance_map (by fun_prop) HasGaussianLaw.aemeasurable, this,
      variance_sum fun _ ↦ HasGaussianLaw.memLp_two]
    simp only [← sum_div, ← ofReal_sum, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_left_inj', ofReal_inj]
    congr with i
    rw [sum_eq_single_of_mem i (by grind) (fun j _ hij ↦ h' i j hij.symm _ _)]
    rw [variance_map HasGaussianLaw.aemeasurable (by fun_prop),
      covariance_self HasGaussianLaw.aemeasurable]

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
  rw [indepFun_iff_charFunDual_prod]
  any_goals fun_prop
  intro L
  have : L ∘ (fun ω ↦ (X ω, Y ω)) = (L ∘L (.inl ℝ E F)) ∘ X + (L ∘L (.inr ℝ E F)) ∘ Y := by
    ext; simp only [Function.comp_apply, ← comp_inl_add_comp_inr, Pi.add_apply]
  rw [IsGaussian.charFunDual_eq, h.fst.isGaussian_map.charFunDual_eq,
    h.snd.isGaussian_map.charFunDual_eq, ← exp_add, sub_add_sub_comm, ← add_mul, integral_map,
    integral_map, integral_map, integral_complex_ofReal, integral_complex_ofReal,
    integral_complex_ofReal, ← ofReal_add, ← integral_add, ← add_div, ← ofReal_add,
    variance_map, variance_map, variance_map, this, variance_add, h', mul_zero, add_zero]
  · congr
  · exact (h.fst.map _).memLp_two
  · exact (h.snd.map _).memLp_two
  any_goals fun_prop
  all_goals exact HasGaussianLaw.integrable

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.iIndepFun_of_cov' {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]
    {X : Π i, Ω → (E i)} (h : HasGaussianLaw (fun ω i ↦ X i ω) P)
    (h' : ∀ i j, i ≠ j → ∀ (x : E i) (y : E j),
      cov[fun ω ↦ ⟪x, X i ω⟫, fun ω ↦ ⟪y, X j ω⟫; P] = 0) :
    iIndepFun X P :=
  h.iIndepFun_of_cov fun i j hij _ _ ↦ by simpa [← inner_toDual_symm_eq_self] using h' i j hij ..

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.indepFun_of_cov' {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [CompleteSpace F] [BorelSpace F] [SecondCountableTopology F]
    {X : Ω → E} {Y : Ω → F} (h : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P)
    (h' : ∀ x y, cov[fun ω ↦ ⟪x, X ω⟫, fun ω ↦ ⟪y, Y ω⟫; P] = 0) :
    IndepFun X Y P :=
  h.indepFun_of_cov fun _ _ ↦ by simpa [← inner_toDual_symm_eq_self] using h' ..

open ContinuousLinearMap RealInnerProductSpace in
lemma HasGaussianLaw.iIndepFun_of_cov'' {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {X : (i : ι) → κ i → Ω → ℝ} (h : HasGaussianLaw (fun ω i j ↦ X i j ω) P)
    (h' : ∀ i j, i ≠ j → ∀ k l, cov[X i k, X j l; P] = 0) :
    iIndepFun (fun i ω j ↦ X i j ω) P := by
  have := h.isProbabilityMeasure
  have _ i j := (h.eval i).eval j
  have : (fun i ω j ↦ X i j ω) = fun i ↦ (ofLp ∘ (toLp 2 ∘ fun ω j ↦ X i j ω)) := by
    ext; simp
  rw [this]
  refine iIndepFun.comp ((?_ : HasGaussianLaw _ _).iIndepFun_of_cov' fun i j hij x y ↦ ?_) _
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
    rw [covariance_mul_left, covariance_mul_right, h' i j hij k l, mul_zero, mul_zero]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun _ ↦ HasGaussianLaw.memLp_two.const_mul _
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun _ ↦ HasGaussianLaw.memLp_two.const_mul _

open RealInnerProductSpace in
lemma HasGaussianLaw.iIndepFun_of_covariance_eq_zero {X : ι → Ω → ℝ}
    [h1 : HasGaussianLaw (fun ω ↦ (X · ω)) P] (h2 : ∀ i j : ι, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P := by
  refine h1.iIndepFun_of_cov fun i j hij L₁ L₂ ↦ ?_
  simp [← inner_toDual_symm_eq_self, Function.comp_def,
    mul_comm _ ((InnerProductSpace.toDual ℝ ℝ).symm _),
    covariance_mul_right, covariance_mul_left, h2, hij]

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
    infer_instance
  rw [← (EuclideanSpace.basisFun _ _).sum_repr x, ← (EuclideanSpace.basisFun _ _).sum_repr y]
  simp_rw [sum_inner, inner_smul_left]
  rw [covariance_fun_sum_fun_sum]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    refine Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ ?_
    rw [covariance_mul_left, covariance_mul_right, h', mul_zero, mul_zero]
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
    EuclideanSpace.basisFun_inner]
    exact fun _ ↦ HasGaussianLaw.memLp_two.const_mul _
  · simp only [EuclideanSpace.basisFun_repr, conj_trivial, Function.comp_apply,
      EuclideanSpace.basisFun_inner]
    exact fun _ ↦ HasGaussianLaw.memLp_two.const_mul _

lemma HasGaussianLaw.indepFun_of_covariance_eq_zero {X Y : Ω → ℝ}
    [h1 : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] (h2 : cov[X, Y; P] = 0) :
    IndepFun X Y P := by
  refine h1.indepFun_of_cov fun L₁ L₂ ↦ ?_
  simp [← inner_toDual_symm_eq_self, Function.comp_def,
    mul_comm _ ((InnerProductSpace.toDual ℝ ℝ).symm _),
    covariance_mul_right, covariance_mul_left, h2]

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
        · infer_instance
        · rw [← map_comp_add, add_sub_cancel]
          infer_instance
        · exact h.comp L.measurable L.measurable
      · fun_prop
      · exact hY.aemeasurable.sub hX.aemeasurable
    all_goals fun_prop

end ProbabilityTheory


end Independence

end ProbabilityTheory
