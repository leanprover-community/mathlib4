/-
Copyright (c) 2026 Ivo Malinowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivo Malinowski
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Cramèr-Wold Theorem

We prove the Cramèr-Wold theorem: convergence in distribution of a sequence of
random variables in a finite-dimensional real inner product space is equivalent
to convergence in distribution of all their 1-dimensional scalar projections.
-/

open Mathlib MeasureTheory ProbabilityTheory Topology Filter Vector Complex
open BoundedContinuousFunction Finset RealInnerProductSpace ProbabilityMeasure Measurable

open scoped NNReal Topology

public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {Ω : Type*} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω}
  {Ω' : Type*} [MeasurableSpace Ω'] {Q : ProbabilityMeasure Ω'}
  {X : Ω' → E} {Xn : ℕ → Ω → E}

-- 1. Basic measurability lemmas updated for E
lemma measurable_dotProduct {n : ℕ} (hX : Measurable (Xn n)) (t : E) :
  Measurable (fun ω : Ω => ⟪(Xn n) ω, t⟫) :=
  Measurable.inner_const hX

lemma aemeasurable_dotProduct {n : ℕ} {μ : Measure Ω} (hX : Measurable (Xn n)) (t : E) :
  AEMeasurable (fun ω : Ω => ⟪(Xn n) ω, t⟫) μ :=
  (measurable_dotProduct hX t).aemeasurable

lemma measurable_dotProduct' (hX : Measurable X) (t : E) :
  Measurable (fun ω : Ω' => ⟪X ω, t⟫) :=
  Measurable.inner_const hX

lemma aemeasurable_dotProduct' {μ : Measure Ω'} (hX : Measurable X) (t : E) :
  AEMeasurable (fun ω : Ω' => ⟪X ω, t⟫) μ :=
  (measurable_dotProduct' hX t).aemeasurable

-- 2. The core argument: 1D weak convergence implies charFun convergence
lemma charFun_tendsto_if_inner_tendsto (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n))
  (hconv : ∀ t : E, Tendsto (fun n : ℕ => P.map (aemeasurable_dotProduct (hXn n) t))
    atTop (𝓝 (Q.map (aemeasurable_dotProduct' hX t)))) :
  ∀ t : E, Tendsto (fun n ↦ charFun (P.map (hXn n).aemeasurable) t)
    atTop (𝓝 (charFun (Q.map hX.aemeasurable) t)) := by
  intro t
  let f : ℝ →ᵇ ℂ := innerProbChar (1 : ℝ)
  have h_weak := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp (hconv t) f
  have h_eq_Pn (n : ℕ) : ∫ y, f y ∂(P.map (aemeasurable_dotProduct (hXn n) t)) =
    charFun (P.map (hXn n).aemeasurable) t := by
    simp_rw [f, charFun_eq_integral_innerProbChar]
    simp only [toMeasure_map]
    rw [MeasureTheory.integral_map (aemeasurable_dotProduct (hXn n) t)
      (innerProbChar (1 : ℝ)).continuous.stronglyMeasurable.aestronglyMeasurable]
    rw [MeasureTheory.integral_map (hXn n).aemeasurable
      (innerProbChar t).continuous.stronglyMeasurable.aestronglyMeasurable]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    simp only [innerProbChar_apply, real_inner_comm]
    rw [real_inner_comm]
    have H : ⟪t, Xn n ω⟫ • (1 : ℝ) = ⟪t, Xn n ω⟫ := by simp
    conv_lhs => rw [← H]
    rw [inner_smul_right]
    simp
  have h_eq_Q : ∫ y, f y ∂(Q.map (aemeasurable_dotProduct' hX t)) =
    charFun (Q.map hX.aemeasurable) t := by
    simp_rw [f, charFun_eq_integral_innerProbChar]
    simp only [toMeasure_map]
    rw [MeasureTheory.integral_map (aemeasurable_dotProduct' hX t)
      (innerProbChar (1 : ℝ)).continuous.stronglyMeasurable.aestronglyMeasurable]
    rw [MeasureTheory.integral_map hX.aemeasurable
      (innerProbChar t).continuous.stronglyMeasurable.aestronglyMeasurable]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    simp only [innerProbChar_apply, real_inner_comm]
    rw [real_inner_comm]
    have H : ⟪t, X ω⟫ • (1 : ℝ) = ⟪t, X ω⟫ := by simp
    conv_lhs => rw [← H]
    rw [inner_smul_right]
    simp
  convert h_weak using 1
  · ext n
    rw [← h_eq_Pn n]
    rfl
  · rw [← h_eq_Q]
    rfl

-- 3. The final Cramèr-Wold theorem using Lévy Convergence
theorem cramerWold (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n)) :
  (∀ t : E, Tendsto (fun n : ℕ => P.map (aemeasurable_dotProduct (hXn n) t))
  atTop (𝓝 (Q.map (aemeasurable_dotProduct' hX t)))) →
  (Tendsto (fun n : ℕ => P.map (hXn n).aemeasurable) atTop (𝓝 (Q.map hX.aemeasurable))) := by
  intro h
  -- Now we just use `ProbabilityMeasure.tendsto_iff_tendsto_charFun` directly!
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  exact charFun_tendsto_if_inner_tendsto hX hXn h

end
