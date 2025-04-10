/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Analysis.Fourier.BoundedContinuousFunctionChar
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-!
# Characteristic Function of a Finite Measure

This file defines the characteristic function of a finite measure on a topological vector space `V`.

The characteristic function of a finite measure `P` on `V` is the mapping
`W → ℂ, w => ∫ v, e (L v w) ∂P`,
where `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a bilinear map.

A typical example is `V = W = ℝ` and `L v w = v * w`.

The integral is expressed as `∫ v, char he hL w v ∂P`, where `char he hL w` is the
bounded continuous function `fun v ↦ e (L v w)` and `he`, `hL` are continuity hypotheses on `e`
and `L`.

## Main definition

TODO: give a definition of the characteristic function for standard choices of `e` and `L`.

## Main statements

- `ext_of_integral_char_eq`: Assume `e` and `L` are non-trivial. If the integrals of `char`
  with respect to two finite measures `P` and `P'` coincide, then `P = P'`.

-/

open BoundedContinuousFunction

namespace MeasureTheory

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    {e : AddChar ℝ Circle}

section ext

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [PseudoEMetricSpace V] [MeasurableSpace V]
    [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V] {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}

/-- If the integrals of `char` with respect to two finite measures `P` and `P'` coincide, then
`P = P'`. -/
theorem ext_of_integral_char_eq (he : Continuous e) (he' : e ≠ 1)
    (hL' : ∀ v ≠ 0, L v ≠ 0) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {P P' : Measure V} [IsFiniteMeasure P] [IsFiniteMeasure P']
    (h : ∀ w, ∫ v, char he hL w v ∂P = ∫ v, char he hL w v ∂P') :
    P = P' := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
      (separatesPoints_charPoly he he' hL hL')
  intro _ hg
  simp only [mem_charPoly] at hg
  obtain ⟨w, hw⟩ := hg
  rw [hw]
  have hsum (P : Measure V) [IsFiniteMeasure P] :
      ∫ v, ∑ a ∈ w.support, w a * e (L v a) ∂P = ∑ a ∈ w.support, ∫ v, w a * e (L v a) ∂P :=
    integral_finset_sum w.support
      fun a ha => Integrable.const_mul (integrable P (char he hL a)) _
  rw [hsum P, hsum P']
  apply Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_eq_mul, MeasureTheory.integral_mul_left, mul_eq_mul_left_iff]
  exact Or.inl (h i)

end ext

end MeasureTheory
