/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrals with a measure derived from probability mass functions.

This file connects `PMF` with `integral`. The main result is that the integral (i.e. the expected
value) with regard to a measure derived from a `PMF` is a sum weighted by the `PMF`.

It also provides the expected value for specific probability mass functions.
-/

public section

namespace PMF

open MeasureTheory NNReal ENNReal TopologicalSpace

section General

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

theorem lintegral_eq_tsum (p : PMF α) (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂(p.toMeasure) = ∑' a, p a * f a := calc
  _ = ∫⁻ (a : α) in p.support, f a ∂p.toMeasure := by rw [p.restrict_toMeasure_support]
  _ = ∑' (a : p.support), f a * p.toMeasure {↑a} := lintegral_countable _ p.support_countable
  _ = ∑' (a : p.support), p a * f a := by
    simp_rw [p.toMeasure_apply_singleton _ (measurableSet_singleton _), mul_comm]
  _ = ∑' a, p a * f a := tsum_subtype_eq_of_support_subset (Function.support_mul_subset_left p f)

theorem lintegral_eq_sum [Fintype α] (p : PMF α) (f : α → ℝ≥0∞) :
    ∫⁻ a, f a ∂(p.toMeasure) = ∑ a, (p a) * f a := by
  rw [p.lintegral_eq_tsum, tsum_fintype]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_eq_tsum (p : PMF α) (f : α → E) (hf : Integrable f p.toMeasure) :
    ∫ a, f a ∂(p.toMeasure) = ∑' a, (p a).toReal • f a := calc
  _ = ∫ a in p.support, f a ∂(p.toMeasure) := by rw [restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p.toMeasure {a.val}).toReal • f a := by
    apply integral_countable f p.support_countable
    rwa [IntegrableOn, restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p a).toReal • f a := by
    congr with x; congr 2
    apply PMF.toMeasure_apply_singleton p x (MeasurableSet.singleton _)
  _ = ∑' a, (p a).toReal • f a :=
    tsum_subtype_eq_of_support_subset <| calc
      (fun a ↦ (p a).toReal • f a).support ⊆ (fun a ↦ (p a).toReal).support :=
        Function.support_smul_subset_left _ _
      _ ⊆ support p := fun x h1 h2 => h1 (by simp [h2])

theorem integral_eq_sum [Fintype α] (p : PMF α) (f : α → E) :
    ∫ a, f a ∂(p.toMeasure) = ∑ a, (p a).toReal • f a := by
  rw [p.integral_eq_tsum _ .of_finite, tsum_fintype]

end General

theorem bernoulli_expectation {p : ℝ≥0} (h : p ≤ 1) :
    ∫ b, cond b 1 0 ∂((bernoulli p h).toMeasure) = p.toReal := by simp [integral_eq_sum]

end PMF
