/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.CovarianceBilinDual

/-!
# Covariance in Hilbert spaces

Given a measure `μ` defined over a Banach space `E`, one can consider the associated covariance
bilinear form which maps `L₁ L₂ : StrongDual ℝ E` to `cov[L₁, L₂; μ]`. This is called
`covarianceBilinDual μ` and is defined in the `CovarianceBilinDual` file.

In the special case where `E` is a Hilbert space, each `L : StrongDual ℝ E` can be represented
as the scalar product against some element of `E`. This motivates the definition of
`covarianceBilin`, which is a continuous bilinear form mapping `x y : E` to
`cov[⟪x, ·⟫, ⟪y, ·⟫; μ]`.

## Main definitions

* `covarianceBilin μ`: the continuous bilinear form over `E` representing the covariance of a
  measure over `E`.
* `covarianceOperator μ`: the bounded operator over `E` such that
  `⟪covarianceOperator μ x, y⟫ = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ ∂μ`.

## Tags

covariance, Hilbert space, bilinear form
-/

@[expose] public section

open MeasureTheory InnerProductSpace NormedSpace WithLp EuclideanSpace
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Covariance of a measure on an inner product space, as a continuous bilinear form. -/
noncomputable
def covarianceBilin (μ : Measure E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (covarianceBilinDual μ)
    (toDualMap ℝ E).toContinuousLinearMap (toDualMap ℝ E).toContinuousLinearMap

@[simp]
lemma covarianceBilin_zero : covarianceBilin (0 : Measure E) = 0 := by
  rw [covarianceBilin]
  simp

lemma covarianceBilin_eq_covarianceBilinDual (x y : E) :
    covarianceBilin μ x y = covarianceBilinDual μ (toDualMap ℝ E x) (toDualMap ℝ E y) := rfl

@[simp]
lemma covarianceBilin_of_not_memLp (h : ¬MemLp id 2 μ) :
    covarianceBilin μ = 0 := by
  ext
  simp [covarianceBilin_eq_covarianceBilinDual, h]

lemma covarianceBilin_apply [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E) :
    covarianceBilin μ x y = ∫ z, ⟪x, z - μ[id]⟫ * ⟪y, z - μ[id]⟫ ∂μ := by
  simp [covarianceBilin, covarianceBilinDual_apply' h]

lemma covarianceBilin_comm (x y : E) :
    covarianceBilin μ x y = covarianceBilin μ y x := by
  rw [covarianceBilin_eq_covarianceBilinDual, covarianceBilinDual_comm,
    covarianceBilin_eq_covarianceBilinDual]

lemma covarianceBilin_self [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x : E) :
    covarianceBilin μ x x = Var[fun u ↦ ⟪x, u⟫; μ] := by
  rw [covarianceBilin_eq_covarianceBilinDual, covarianceBilinDual_self_eq_variance h]
  rfl

lemma covarianceBilin_apply_eq_cov [CompleteSpace E] [IsFiniteMeasure μ]
    (h : MemLp id 2 μ) (x y : E) :
    covarianceBilin μ x y = cov[fun u ↦ ⟪x, u⟫, fun u ↦ ⟪y, u⟫; μ] := by
  rw [covarianceBilin_eq_covarianceBilinDual, covarianceBilinDual_eq_covariance h]
  rfl

lemma covarianceBilin_real {μ : Measure ℝ} [IsFiniteMeasure μ] (x y : ℝ) :
    covarianceBilin μ x y = x * y * Var[id; μ] := by
  by_cases h : MemLp id 2 μ
  · simp only [covarianceBilin_apply_eq_cov h, RCLike.inner_apply, conj_trivial, mul_comm]
    rw [covariance_const_mul_left, covariance_const_mul_right, ← mul_assoc,
      covariance_self aemeasurable_id', Function.id_def]
  · simp [h, variance_of_not_memLp, aestronglyMeasurable_id]

lemma covarianceBilin_real_self {μ : Measure ℝ} [IsFiniteMeasure μ] (x : ℝ) :
    covarianceBilin μ x x = x ^ 2 * Var[id; μ] := by
  rw [covarianceBilin_real, pow_two]

@[simp]
lemma covarianceBilin_self_nonneg (x : E) :
    0 ≤ covarianceBilin μ x x := by
  simp [covarianceBilin]

lemma isPosSemidef_covarianceBilin :
    (covarianceBilin μ).toBilinForm.IsPosSemidef where
  eq := covarianceBilin_comm
  nonneg := covarianceBilin_self_nonneg

lemma covarianceBilin_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [CompleteSpace F]
    [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (L : E →L[ℝ] F) (u v : F) :
    covarianceBilin (μ.map L) u v = covarianceBilin μ (L.adjoint u) (L.adjoint v) := by
  rw [covarianceBilin_apply, covarianceBilin_apply h]
  · simp_rw [id, L.integral_id_map (h.integrable (by simp))]
    rw [integral_map]
    · simp_rw [← map_sub, ← L.adjoint_inner_left]
    all_goals fun_prop
  · exact memLp_map_measure_iff (by fun_prop) (by fun_prop) |>.2 (L.comp_memLp' h)

lemma covarianceBilin_map_const_add [CompleteSpace E] [IsProbabilityMeasure μ] (c : E) :
    covarianceBilin (μ.map (fun x ↦ c + x)) = covarianceBilin μ := by
  by_cases h : MemLp id 2 μ
  · ext x y
    have h_Lp : MemLp id 2 (μ.map (fun x ↦ c + x)) :=
      (measurableEmbedding_addLeft _).memLp_map_measure_iff.mpr <| (memLp_const c).add h
    rw [covarianceBilin_apply h_Lp,
      covarianceBilin_apply h, integral_map (by fun_prop) (by fun_prop)]
    congr with z
    rw [integral_map (by fun_prop) h_Lp.1]
    simp only [id_eq]
    rw [integral_add (integrable_const _)]
    · simp
    · exact h.integrable (by simp)
  · ext
    rw [covarianceBilin_of_not_memLp, covarianceBilin_of_not_memLp h]
    rw [(measurableEmbedding_addLeft _).memLp_map_measure_iff.not]
    contrapose h
    convert! (memLp_const (-c)).add h
    ext; simp

lemma covarianceBilin_apply_basisFun {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) (i j : ι) :
    covarianceBilin (μ.map (fun ω ↦ toLp 2 (X · ω)))
      (basisFun ι ℝ i) (basisFun ι ℝ j) = cov[X i, X j; μ] := by
  have (i : ι) := (hX i).aemeasurable
  rw [covarianceBilin_apply_eq_cov, covariance_map]
  · simp [basisFun_inner]; rfl
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 (MemLp.of_eval_piLp hX)

lemma covarianceBilin_apply_basisFun_self {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) (i : ι) :
    covarianceBilin (μ.map (fun ω ↦ toLp 2 (X · ω)))
      (basisFun ι ℝ i) (basisFun ι ℝ i) = Var[X i; μ] := by
  rw [covarianceBilin_apply_basisFun hX, covariance_self]
  have (i : ι) := (hX i).aemeasurable
  fun_prop

lemma covarianceBilin_apply_pi {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (x y : EuclideanSpace ℝ ι) :
    covarianceBilin (μ.map (fun ω ↦ toLp 2 (X · ω))) x y =
      ∑ i, ∑ j, x i * y j * cov[X i, X j; μ] := by
  have (i : ι) := (hX i).aemeasurable
  nth_rw 1 [covarianceBilin_apply_eq_cov, covariance_map_fun, ← (basisFun ι ℝ).sum_repr' x,
    ← (basisFun ι ℝ).sum_repr' y]
  · simp_rw [sum_inner, real_inner_smul_left, basisFun_inner]
    rw [covariance_fun_sum_fun_sum]
    · refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [covariance_const_mul_left, covariance_const_mul_right]
      ring
    all_goals exact fun i ↦ (hX i).const_mul _
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 (MemLp.of_eval_piLp hX)

section covarianceOperator

variable [CompleteSpace E]

/-- The covariance operator of the measure `μ`. This is the bounded operator `F : E →L[ℝ] E`
associated to the continuous bilinear form `B : E →L[ℝ] E →L[ℝ] ℝ` such that
`B x y = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ ∂μ` (see `covarianceOperator_inner`). Namely we have
`B x y = ⟪F x, y⟫`.

Note that the bilinear form `B` is the _uncentered_ covariance bilinear form associated to the
measure `µ`, which is not to be confused with the covariance bilinear form defined earlier in this
file as `covarianceBilin μ`. -/
noncomputable def covarianceOperator (μ : Measure E) : E →L[ℝ] E :=
  continuousLinearMapOfBilin <| ContinuousLinearMap.bilinearComp (uncenteredCovarianceBilinDual μ)
    (toDualMap ℝ E).toContinuousLinearMap (toDualMap ℝ E).toContinuousLinearMap

@[simp]
lemma covarianceOperator_zero : covarianceOperator (0 : Measure E) = 0 := by
  simp [covarianceOperator]

@[simp]
lemma covarianceOperator_of_not_memLp (hμ : ¬MemLp id 2 μ) :
    covarianceOperator μ = 0 := by
  ext x
  refine (unique_continuousLinearMapOfBilin _ fun y ↦ ?_).symm
  simp [hμ, uncenteredCovarianceBilinDual_of_not_memLp]

lemma covarianceOperator_inner (hμ : MemLp id 2 μ) (x y : E) :
    ⟪covarianceOperator μ x, y⟫ = ∫ z, ⟪x, z⟫ * ⟪y, z⟫ ∂μ := by
  simp [covarianceOperator, uncenteredCovarianceBilinDual_apply hμ]

lemma covarianceOperator_apply (hμ : MemLp id 2 μ) (x : E) :
    covarianceOperator μ x = ∫ y, ⟪x, y⟫ • y ∂μ := by
  refine (unique_continuousLinearMapOfBilin _ fun y ↦ ?_).symm
  rw [real_inner_comm, ← integral_inner]
  · simp_rw [inner_smul_right, ← continuousLinearMapOfBilin_apply, ← covarianceOperator_inner hμ]
    rfl
  exact memLp_one_iff_integrable.1 <| hμ.smul (hμ.const_inner x)

lemma isPositive_covarianceOperator : (covarianceOperator μ).toLinearMap.IsPositive := by
  by_cases hμ : MemLp id 2 μ
  swap; · simp [hμ]
  refine ⟨fun x y ↦ ?_, fun x ↦ ?_⟩
  · simp_rw [ContinuousLinearMap.coe_coe, real_inner_comm _ x, covarianceOperator_inner hμ,
      mul_comm]
  · simp only [ContinuousLinearMap.coe_coe, covarianceOperator_inner hμ, ← pow_two,
      RCLike.re_to_real]
    positivity

end covarianceOperator

end ProbabilityTheory
