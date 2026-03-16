/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Probability.Notation

/-!
# Distributions on two values

This file proves a few lemmas about random variables that take at most two values.
-/

public section

open scoped ProbabilityTheory

namespace MeasureTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}

/-- If an `AEMeasurable` function is ae equal to `0` or `1`, then its integral is equal to the
measure of the set where it equals `1`. -/
lemma integral_of_ae_eq_zero_or_one (hXmeas : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    μ[X] = μ.real {ω | X ω = 1} := by
  refine (integral_map (f := id) hXmeas <| by fun_prop).symm.trans ?_
  rw [(Measure.ae_eq_or_eq_iff_map_eq_dirac_add_dirac hXmeas zero_ne_one).1 hX]
  by_cases h : μ {ω | X ω = 1} = ⊤
  · simp [h, Measure.real, Set.preimage, integral_undef, Integrable, HasFiniteIntegral]
  rw [integral_add_measure ⟨by fun_prop, by simp [HasFiniteIntegral]⟩ <|
    .smul_measure (by simp [integrable_dirac]) h]
  simp [Measure.real, Set.preimage]

/-- If a random variable is ae equal to `0` or `1`, then one minus its expectation is equal to the
probability that it equals `0`. -/
lemma one_sub_integral_of_ae_eq_zero_or_one [IsProbabilityMeasure μ] (hXmeas : AEMeasurable X μ)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) : 1 - μ[X] = μ.real {ω | X ω = 0} := by
  calc
    _ = μ[1 - X] := by
      rw [integral_sub' _ <| .of_bound hXmeas.aestronglyMeasurable 1 ?_]
      · simp
      · exact integrable_const _
      · filter_upwards [hX]
        rintro ω (hω | hω) <;> simp [hω]
    _ = μ.real {ω | 1 - X ω = 1} :=
      integral_of_ae_eq_zero_or_one (aemeasurable_const (b := 1).sub hXmeas)
        (by simpa [sub_eq_zero, or_comm, eq_comm (a := (1 : ℝ))] using hX)
    _ = μ.real {ω | X ω = 0} := by simp

end MeasureTheory
