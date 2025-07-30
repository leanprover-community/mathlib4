/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Eval.WithLp
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Covariance matrix

-/

open MeasureTheory InnerProductSpace NormedSpace WithLp
open scoped ENNReal NNReal Matrix

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- Covariance of a measure on an inner product space, as a continuous bilinear form. -/
noncomputable
def covInnerBilin (μ : Measure E) : ContinuousBilinForm ℝ E :=
  ContinuousLinearMap.bilinearComp (covarianceBilin μ)
    (toDualMap ℝ E).toContinuousLinearMap (toDualMap ℝ E).toContinuousLinearMap

@[simp]
lemma covInnerBilin_zero : covInnerBilin (0 : Measure E) = 0 := by
  rw [covInnerBilin]
  simp

lemma covInnerBilin_eq_covarianceBilin (x y : E) :
    covInnerBilin μ x y = covarianceBilin μ (toDualMap ℝ E x) (toDualMap ℝ E y) := rfl

@[simp]
lemma covInnerBilin_of_not_memLp [IsFiniteMeasure μ] (h : ¬MemLp id 2 μ) :
    covInnerBilin μ = 0 := by
  ext
  simp [covInnerBilin_eq_covarianceBilin, h]

lemma covInnerBilin_apply [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E) :
    covInnerBilin μ x y = ∫ z, ⟪x, z - μ[id]⟫_ℝ * ⟪y, z - μ[id]⟫_ℝ ∂μ := by
  simp_rw [covInnerBilin, ContinuousLinearMap.bilinearComp_apply, covarianceBilin_apply' h]
  simp only [LinearIsometry.coe_toContinuousLinearMap, id_eq, toDualMap_apply]

lemma covInnerBilin_comm [IsFiniteMeasure μ] (x y : E) :
    covInnerBilin μ x y = covInnerBilin μ y x := by
  rw [covInnerBilin_eq_covarianceBilin, covarianceBilin_comm, covInnerBilin_eq_covarianceBilin]

lemma covInnerBilin_self [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x : E) :
    covInnerBilin μ x x = Var[fun u ↦ ⟪x, u⟫_ℝ; μ] := by
  rw [covInnerBilin_eq_covarianceBilin, covarianceBilin_self_eq_variance h]
  congr

lemma covInnerBilin_apply_eq [CompleteSpace E] [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : E) :
    covInnerBilin μ x y = cov[fun u ↦ ⟪x, u⟫_ℝ, fun u ↦ ⟪y, u⟫_ℝ ; μ] := by
  rw [covInnerBilin_eq_covarianceBilin, covarianceBilin_eq_covariance h]
  congr

lemma covInnerBilin_real {μ : Measure ℝ} [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x y : ℝ) :
    covInnerBilin μ x y = x * y * Var[id; μ] := by
  simp only [covInnerBilin_apply_eq h, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [covariance_mul_left, covariance_mul_right, ← mul_assoc, covariance_self]
  · rfl
  exact aemeasurable_id

lemma covInnerBilin_real_self {μ : Measure ℝ} [IsFiniteMeasure μ] (h : MemLp id 2 μ) (x : ℝ) :
    covInnerBilin μ x x = x ^ 2 * Var[id; μ] := by
  rw [covInnerBilin_real h, pow_two]

@[simp]
lemma covInnerBilin_self_nonneg [CompleteSpace E] [IsFiniteMeasure μ] (x : E) :
    0 ≤ covInnerBilin μ x x := by
  simp [covInnerBilin]

lemma isPosSemidef_covInnerBilin [CompleteSpace E] [IsFiniteMeasure μ] :
    (covInnerBilin μ).IsPosSemidef where
  eq := covInnerBilin_comm
  nonneg := covInnerBilin_self_nonneg

lemma covInnerBilin_map_const_add [CompleteSpace E] [IsProbabilityMeasure μ] (c : E) :
    covInnerBilin (μ.map (fun x ↦ c + x)) = covInnerBilin μ := by
  by_cases h : MemLp id 2 μ
  · ext x y
    have h_Lp : MemLp id 2 (μ.map (fun x ↦ c + x)) :=
      (measurableEmbedding_addLeft _).memLp_map_measure_iff.mpr <| (memLp_const c).add h
    rw [covInnerBilin_apply h_Lp, covInnerBilin_apply h, integral_map (by fun_prop) (by fun_prop)]
    congr with z
    rw [integral_map (by fun_prop) h_Lp.1]
    simp only [id_eq]
    rw [integral_add (integrable_const _)]
    · simp
    · exact h.integrable (by simp)
  · ext
    rw [covInnerBilin_of_not_memLp, covInnerBilin_of_not_memLp h]
    rw [(measurableEmbedding_addLeft _).memLp_map_measure_iff.not]
    contrapose! h
    convert (memLp_const (-c)).add h
    ext; simp

lemma covInnerBilin_apply_basisFun {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) (i j : ι) :
    covInnerBilin (μ.map (fun ω ↦ toLp 2 (X · ω)))
      (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j) = cov[X i, X j; μ] := by
  have (i : ι) := (hX i).aemeasurable
  rw [covInnerBilin_apply_eq, covariance_map]
  · simp only [EuclideanSpace.basisFun_inner]; rfl
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 (MemLp.of_eval_piLp hX)

lemma covInnerBilin_apply_basisFun_self {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ) (i : ι) :
    covInnerBilin (μ.map (fun ω ↦ toLp 2 (X · ω)))
      (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i) = Var[X i; μ] := by
  rw [covInnerBilin_apply_basisFun hX, covariance_self]
  have (i : ι) := (hX i).aemeasurable
  fun_prop

lemma covInnerBilin_apply_pi {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (x y : EuclideanSpace ℝ ι) :
    covInnerBilin (μ.map (fun ω ↦ toLp 2 (X · ω))) x y =
      ∑ i, ∑ j, x i * y j * cov[X i, X j; μ] := by
  have (i : ι) := (hX i).aemeasurable
  nth_rw 1 [covInnerBilin_apply_eq, covariance_map_fun, ← (EuclideanSpace.basisFun ι ℝ).sum_repr' x,
    ← (EuclideanSpace.basisFun ι ℝ).sum_repr' y]
  · simp_rw [sum_inner, real_inner_smul_left, EuclideanSpace.basisFun_inner, PiLp.toLp_apply]
    rw [covariance_fun_sum_fun_sum]
    · refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [covariance_mul_left, covariance_mul_right]
      ring
    all_goals exact fun i ↦ (hX i).const_mul _
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 (MemLp.of_eval_piLp hX)

end ProbabilityTheory
