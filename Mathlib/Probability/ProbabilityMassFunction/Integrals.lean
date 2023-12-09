/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Bochner

/-!
# Integrals with a measure derived from probability mass functions.

This files connects `Pmf` with `integral`. The main result is that the integral (i.e. the expected
value) with regard to a measure derived from a `Pmf` is a sum weighted by the `Pmf`.

It also provides the expected value for specific probability mass functions.
-/

namespace Pmf

open MeasureTheory BigOperators ENNReal TopologicalSpace

section General

variable {α : Type _} [MeasurableSpace α] [MeasurableSingletonClass α]
variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_eq_tsum (p : Pmf α) (f : α → E) (hf : Integrable f p.toMeasure) :
    ∫ a, f a ∂(p.toMeasure) = ∑' a, (p a).toReal • f a := calc
  _ = ∫ a in p.support, f a ∂(p.toMeasure) := by rw [restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p.toMeasure {a.val}).toReal • f a := by
    apply integral_countable f p.support_countable
    rwa [restrict_toMeasure_support p]
  _ = ∑' (a : support p), (p a).toReal • f a := by
    congr with x; congr
    apply Pmf.toMeasure_apply_singleton p x (MeasurableSet.singleton _)
  _ = ∑' a, (p a).toReal • f a :=
    tsum_subtype_eq_of_support_subset $ by calc
      (fun a ↦ (p a).toReal • f a).support ⊆ (fun a ↦ (p a).toReal).support :=
        Function.support_smul_subset_left _ _
      _ ⊆ support p := fun x h1 h2 => h1 (by simp [h2])

theorem integral_eq_sum [Fintype α] (p : Pmf α) (f : α → E) :
    ∫ a, f a ∂(p.toMeasure) = ∑ a, (p a).toReal • f a := by
  rw [integral_fintype _ (integrable_of_fintype _ f)]
  congr with x; congr
  exact Pmf.toMeasure_apply_singleton p x (MeasurableSet.singleton _)

end General

theorem bernoulli_expectation {p : ℝ≥0∞} (h : p ≤ 1) :
    ∫ b, cond b 1 0 ∂((bernoulli p h).toMeasure) = p.toReal := by simp [integral_eq_sum]
