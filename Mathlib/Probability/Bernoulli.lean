/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Probability.CondVar
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Notation

/-!
# Bernoulli random variables

This file computes the expectation, variance, conditional variance of a Bernoulli random variable.

## Main declarations

* `ProbabilityTheory.bernoulli`: Bernoulli measure on `ℝ` with parameter `p`.
* `ProbabilityTheory.IsBernoulli`:
  Predicate for a random variable to be Bernoulli according to *some* parameter.
* `ProbabilityTheory.IsBernoulli.integral_eq`: Computation of the expectation of a Bernoulli r.v.
* `ProbabilityTheory.IsBernoulli.variance_eq`: Computation of the variance of a Bernoulli r.v.
* `ProbabilityTheory.IsBernoulli.condVar_eq`:
  Computation of the conditional variance of a Bernoulli r.v.
-/

open MeasureTheory
open scoped NNReal ProbabilityTheory

namespace MeasureTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω} {s : Set Ω}

/-- If a `AEMeasurable` function is ae equal to `0` or `1`, then its integral is equal to the
measure of the set where it equals `1`. -/
lemma integral_of_ae_eq_zero_or_one (hXmeas : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    μ[X] = (μ {ω | X ω = 1}).toReal := by
  wlog hXmeas : Measurable X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEMeasurable X μ›
    calc
      μ[X]
      _ = μ[Y] := (integral_congr_ae hXY:)
      _ = (μ {ω | Y ω = 1}).toReal := by
        refine this hYmeas.aemeasurable ?_ hYmeas
        filter_upwards [hX, hXY] with ω hXω hXYω
        simp [hXω, ← hXYω]
      _ = (μ {ω | X ω = 1}).toReal := by
        congr 1
        exact measure_congr <| by filter_upwards [hXY] with ω hω; simp [hω, setOf]
  calc
    _ = ∫ ω in {ω | X ω = 0 ∨ X ω = 1}, X ω ∂μ := integral_eq_setIntegral hX _
    _ = ∫ ω in {ω | X ω = 1}, X ω ∂μ :=
      setIntegral_eq_of_subset_of_ae_diff_eq_zero
        (hXmeas <| .union (.singleton 0) <| .singleton 1).nullMeasurableSet
        Set.subset_union_right (by simp [← or_iff_not_imp_right])
    _ = ∫ ω in {ω | X ω = 1}, 1 ∂μ := setIntegral_congr_ae (hXmeas <| .singleton 1) (by simp)
    _ = _ := by simp [Measure.real]

/-- If a random variable is ae equal to `0` or `1`, then one minus its expectation is equal to the
probability that it equals `0`. -/
lemma one_sub_integral_of_ae_eq_zero_or_one [IsProbabilityMeasure μ] (hXmeas : AEMeasurable X μ)
    (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    1 - μ[X] = (μ {ω | X ω = 0}).toReal := by
  calc
    _ = μ[1 - X] := by
      rw [integral_sub' _ <| .of_bound hXmeas.aestronglyMeasurable 1 ?_]
      · simp
      · exact integrable_const _
      · filter_upwards [hX]
        rintro ω (hω | hω) <;> simp [hω]
    _ = (μ {ω | 1 - X ω = 1}).toReal :=
      integral_of_ae_eq_zero_or_one (aemeasurable_const (b := 1).sub hXmeas)
        (by simpa [sub_eq_zero, or_comm, eq_comm (a := (1 : ℝ))] using hX)
    _ = (μ {ω | X ω = 0}).toReal := by simp

end MeasureTheory

namespace ProbabilityTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure ℝ} {P : Measure Ω}

/-- If a random variable is ae equal to `0` or `1`, then its variance is the product of
the probabilities that it's equal to `0` and that it's equal to `1`. -/
lemma variance_of_ae_eq_zero_or_one {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    (hXmeas : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Var[X; μ] = μ.real {ω | X ω = 0} * μ.real {ω | X ω = 1} := by
  wlog hXmeas : Measurable X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEMeasurable X μ›
    calc
      Var[X; μ]
      _ = Var[Y; μ] := variance_congr hXY
      _ = μ.real {ω | Y ω = 0} * μ.real {ω | Y ω = 1} := by
        refine this hYmeas.aemeasurable ?_ hYmeas
        filter_upwards [hX, hXY] with ω hXω hXYω
        simp [hXω, ← hXYω]
      _ = μ.real {ω | X ω = 0} * μ.real {ω | X ω = 1} := by
        congr 1 <;> exact measureReal_congr <| by filter_upwards [hXY] with ω hω; simp [hω, setOf]
  obtain rfl | hμ := eq_zero_or_isProbabilityMeasure μ
  · simp
  calc
    _ = μ[X ^ 2] - μ[X] ^ 2 := variance_eq_sub <| .of_bound hXmeas.aestronglyMeasurable 1 <| by
        filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ = μ[X] - μ[X] ^ 2 := by
      congr! 1
      exact integral_congr_ae <| by filter_upwards [hX]; rintro ω (hω | hω) <;> simp [hω]
    _ = μ.real {ω | X ω = 0} * μ.real {ω | X ω = 1} := by
      rw [sq, ← one_sub_mul, integral_of_ae_eq_zero_or_one hXmeas.aemeasurable hX]
      congr
      rw [← ENNReal.toReal_one, ← ENNReal.toReal_sub_of_le, ← prob_compl_eq_one_sub]
      · congr 1
        refine measure_congr ?_
        filter_upwards [hX]
        -- FIXME: The following change is due to the measure theory library abusing the defeq
        -- `Set Ω = (Ω → Prop)`
        change ∀ ω _, (_ ≠ _) = (_ = _)
        rintro ω (hω | hω) <;> simp [hω]
      · exact hXmeas <| .singleton _
      · exact prob_le_one
      · simp

/-- If a random variable is ae equal to `0` or `1`, then its conditional variance is the product of
the conditional probabilities that it's equal to `0` and that it's equal to `1`. -/
lemma condVar_of_ae_eq_zero_or_one {m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) {μ : Measure[m₀] Ω}
    [IsFiniteMeasure μ] (hXmeas : AEMeasurable[m₀] X μ) (hX : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    Var[X; μ | m] =ᵐ[μ] μ[X | m] * μ[1 - X | m] := by
  wlog hXmeas : Measurable[m₀] X
  · obtain ⟨Y, hYmeas, hXY⟩ := ‹AEMeasurable[m₀] X μ›
    calc
      Var[X; μ | m]
      _ =ᵐ[μ] Var[Y; μ | m] := condVar_congr_ae hXY
      _ =ᵐ[μ] μ[Y | m] * μ[1 - Y | m] := by
        refine this hm hYmeas.aemeasurable ?_ hYmeas
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

/-! ### Predicate for a measure to be Bernoulli -/

/-- The Bernoulli probability distribution with parameter `p`.

`p` is taken to have type `ℝ≥0`, and therefore we need to choose a junk value for `p > 1`.
We decide to make `bernoulli` monotone in `p`, meaning that `bernoulli p = bernoulli 1` for all
`p ≥ 1`. -/
noncomputable def bernoulli (p : ℝ≥0) : Measure ℝ := (1 - p) • .dirac 0 + (1 - (1 - p)) • .dirac 1

/-- A measure is Bernoulli if it is the Bernoulli distribution with some parameter `p`. -/
class IsBernoulli (μ : Measure ℝ) where
  eq_bernoulli (μ) : μ = bernoulli (μ {1}).toNNReal

instance isBernoulli_bernoulli (p : ℝ≥0) : IsBernoulli (bernoulli p) where
  eq_bernoulli := by simp [bernoulli, tsub_tsub_cancel_of_le]

variable [IsBernoulli μ]

instance IsBernoulli.toIsProbabilityMeasure : IsProbabilityMeasure μ where
  measure_univ := by rw [eq_bernoulli μ]; simp [bernoulli, ENNReal.smul_def]

lemma IsBernoulli.map_eq_bernoulli (hX : HasLaw X μ P) :
    P.map X = bernoulli (P (X ⁻¹' {1})).toNNReal := by
  rw [hX.map_eq, eq_bernoulli μ, ← hX.map_eq,
    Measure.map_apply₀ hX.aemeasurable (nullMeasurableSet_singleton _)]

lemma IsBernoulli.ae_eq_zero_or_one (hX : HasLaw X μ P) : ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = 1 := by
  change P (X ⁻¹' {0, 1}ᶜ) = 0
  rw [← Measure.map_apply₀ hX.aemeasurable (by simp), map_eq_bernoulli hX]
  simp [bernoulli]

/-! ### Restatements using the predicate -/

/-- **Expectation of a Bernoulli random variable**.

The expectation of a Bernoulli random variable is equal
to the probability that it's equal to `1`. -/
lemma IsBernoulli.integral_eq (hX : HasLaw X μ P) : P[X] = P.real {ω | X ω = 1} :=
  integral_of_ae_eq_zero_or_one hX.aemeasurable <| ae_eq_zero_or_one hX

/-- **Expectation of a Bernoulli random variable**.

One minus the expectation of a Bernoulli random variable is equal
to the probability that it's equal to `0`. -/
lemma IsBernoulli.one_sub_integral (hX : HasLaw X μ P) : 1 - P[X] = P.real {ω | X ω = 0} :=
  have := hX.isProbabilityMeasure
  one_sub_integral_of_ae_eq_zero_or_one hX.aemeasurable (ae_eq_zero_or_one hX)

/-- **Variance of a Bernoulli random variable**.

The variance of a Bernoulli random variable is the product of the probabilities that it's equal to
`0` and that it's equal to `1`. -/
lemma IsBernoulli.variance_eq (hX : HasLaw X μ P) :
    Var[X; P] = P.real {ω | X ω = 0} * P.real {ω | X ω = 1} :=
  have := hX.isProbabilityMeasure
  variance_of_ae_eq_zero_or_one hX.aemeasurable (ae_eq_zero_or_one hX)

/-- **Conditional variance of a Bernoulli random variable**.

The conditional variance of a Bernoulli random variable is the product of the conditional
probabilities that it's equal to `0` and that it's equal to `1`. -/
lemma IsBernoulli.condVar_eq {m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) {P : Measure[m₀] Ω}
    (hX : HasLaw X μ P) :
    Var[X; P | m] =ᵐ[P] P[X | m] * P[1 - X | m] :=
  have := hX.isProbabilityMeasure
  condVar_of_ae_eq_zero_or_one hm hX.aemeasurable (ae_eq_zero_or_one hX)

end ProbabilityTheory
