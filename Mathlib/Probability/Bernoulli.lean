/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Notation

/-!
# Bernoulli random variables

This file computes the expectation, variance, conditional variance of a Bernoulli random variable.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace MeasureTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω} {s : Set Ω}

/-- **Expectation of a Bernoulli random variable**.

If a random variable is ae equal to `0` or `1`, then its expectation is equal to the probability
that it equals `1`. -/
lemma integral_of_ae_eq_zero_or_one [IsFiniteMeasure μ] (hXmeas : AEStronglyMeasurable X μ)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) : μ[X] = (μ {ω | X ω = 1}).toReal := by
  wlog hXmeas : StronglyMeasurable X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEStronglyMeasurable X μ›
    calc
      μ[X]
      _ = μ[Y] := (integral_congr_ae hXY:)
      _ = (μ {ω | Y ω = 1}).toReal := by
        refine this hYmeas.aestronglyMeasurable ?_ hYmeas
        filter_upwards [hX, hXY] with ω hXω hXYω
        simp [hXω, ← hXYω]
      _ = (μ {ω | X ω = 1}).toReal := by
        congr 1
        exact measure_congr <| by filter_upwards [hXY] with ω hω; simp [hω, setOf]
  calc
    _ = ∫ ω in {ω | X ω = 0 ∨ X ω = 1}, X ω ∂μ := integral_eq_setIntegral hX _
    _ = ∫ ω in {ω | X ω = 0}, X ω ∂μ + ∫ ω in {ω | X ω = 1}, X ω ∂μ := by
      rw [Set.setOf_or]
      refine setIntegral_union (by simp +contextual [Set.disjoint_left])
        (hXmeas.measurable <| .singleton 1)
        ((integrableOn_congr_fun ?_ (hXmeas.measurable <| .singleton 0)).1 integrableOn_zero)
        ((integrableOn_congr_fun ?_ (hXmeas.measurable <| .singleton 1)).1
          (integrable_const 1).integrableOn) <;>
        simp [Set.EqOn, eq_comm]
    _ = ∫ ω in {ω | X ω = 0}, 0 ∂μ + ∫ ω in {ω | X ω = 1}, 1 ∂μ := by
      congr 1
      · exact setIntegral_congr_ae (hXmeas.measurable <| .singleton 0) (by simp)
      · exact setIntegral_congr_ae (hXmeas.measurable <| .singleton 1) (by simp)
    _ = _ := by simp [Measure.real]

/-- **Expectation of a Bernoulli random variable**.

If a random variable is ae equal to `0` or `1`, then one minus its expectation is equal to the
probability that it equals `0`. -/
lemma one_sub_integral_of_ae_eq_zero_or_one [IsProbabilityMeasure μ]
    (hXmeas : AEStronglyMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    1 - μ[X] = (μ {ω | X ω = 0}).toReal := by
  calc
    _ = μ[1 - X] := by
      rw [integral_sub' _ <| .of_bound hXmeas 1 ?_]
      · simp
      · exact integrable_const _
      · filter_upwards [hX]
        rintro ω (hω | hω) <;> simp [hω]
    _ = (μ {ω | 1 - X ω = 1}).toReal :=
      integral_of_ae_eq_zero_or_one (aestronglyMeasurable_const (b := 1).sub hXmeas)
        (by simpa [sub_eq_zero, or_comm, eq_comm (a := (1 : ℝ))] using hX)
    _ = (μ {ω | X ω = 0}).toReal := by simp

end MeasureTheory

namespace ProbabilityTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → ℝ}

/-- **Variance of a Bernoulli random variable**.

If a random variable is ae equal to `0` or `1`, then we can compute its variance as the probability
that it's equal to `0` times the conditional probability that it's equal to `1`. -/
lemma variance_of_ae_eq_zero_or_one {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    (hXmeas : AEStronglyMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Var[X; μ] = (μ {ω | X ω = 0}).toReal * (μ {ω | X ω = 1}).toReal := by
  wlog hXmeas : StronglyMeasurable X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEStronglyMeasurable X μ›
    calc
      Var[X; μ]
      _ = Var[Y; μ] := variance_congr hXY
      _ = (μ {ω | Y ω = 0}).toReal * (μ {ω | Y ω = 1}).toReal := by
        refine this hYmeas.aestronglyMeasurable ?_ hYmeas
        filter_upwards [hX, hXY] with ω hXω hXYω
        simp [hXω, ← hXYω]
      _ = (μ {ω | X ω = 0}).toReal * (μ {ω | X ω = 1}).toReal := by
        congr 2 <;> exact measure_congr <| by filter_upwards [hXY] with ω hω; simp [hω, setOf]
  obtain rfl | hμ := eq_zero_or_isProbabilityMeasure μ
  · simp
  calc
    _ = μ[X ^ 2] - μ[X] ^ 2 := variance_eq_sub <| .of_bound hXmeas.aestronglyMeasurable 1 <| by
        filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ = μ[X] - μ[X] ^ 2 := by
      congr! 1
      exact integral_congr_ae <| by filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ = (μ {ω | X ω = 0}).toReal * (μ {ω | X ω = 1}).toReal := by
      rw [sq, ← one_sub_mul, integral_of_ae_eq_zero_or_one hXmeas.aestronglyMeasurable hX]
      congr
      rw [← ENNReal.toReal_one, ← ENNReal.toReal_sub_of_le, ← prob_compl_eq_one_sub]
      · congr 1
        refine measure_congr ?_
        filter_upwards [hX]
        -- FIXME: The following change is due to the measure theory library abusing the defeq
        -- `Set Ω = (Ω → Prop)`
        change ∀ ω _, (_ ≠ _) = (_ = _)
        rintro ω (hω | hω) <;> simp [hω]
      · exact (hXmeas.measurable <| .singleton _)
      · exact prob_le_one
      · simp

/-- **Conditional variance of a Bernoulli random variable**.

If a random variable is ae equal to `0` or `1`, then we can compute its conditional variance as the
conditional probability that it's equal to `0` times the conditional probability that it's equal to
`1`. -/
lemma condVar_of_ae_eq_zero_or_one {m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) {μ : Measure[m₀] Ω}
    [IsFiniteMeasure μ] (hXmeas : AEStronglyMeasurable[m₀] X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Var[X; μ | m] =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
  wlog hXmeas : StronglyMeasurable[m₀] X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEStronglyMeasurable[m₀] X μ›
    calc
      Var[X; μ | m]
      _ =ᵐ[μ] Var[Y; μ | m] := condVar_congr_ae hXY
      _ =ᵐ[μ] μ[Y | m] * μ[1 - Y | m] := by
        refine this hm hYmeas.aestronglyMeasurable ?_ hYmeas
        filter_upwards [hX, hXY] with ω hXω hXYω
        simp [hXω, ← hXYω]
      _ =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
        refine .mul ?_ ?_ <;>
          exact condExp_congr_ae <| by filter_upwards [hXY] with ω hω; simp [hω]
  calc
    _ =ᵐ[μ] μ[X ^ 2 | m] - μ[X | m] ^ 2 :=
      condVar_ae_eq_condExp_sq_sub_sq_condExp hm <| .of_bound hXmeas.aestronglyMeasurable 1 <| by
        filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ =ᵐ[μ] μ[X | m] - μ[X | m] ^ 2 := by
      refine .sub ?_ ae_eq_rfl
      exact condExp_congr_ae <| by filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
      rw [sq, ← one_sub_mul, mul_comm]
      refine .mul ae_eq_rfl ?_
      calc
        1 - μ[X | m]
        _ = μ[1 | m] - μ[X | m] := by simp [Pi.one_def, hm]
        _ =ᵐ[μ] μ[1 - X | m] := by
          refine (condExp_sub (integrable_const _)
            (.of_bound (C := 1) hXmeas.aestronglyMeasurable ?_) _).symm
          filter_upwards [hX]
          rintro ω (hω | hω) <;> simp [hω]

end ProbabilityTheory
