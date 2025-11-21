/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Probability.CondVar
public import Mathlib.Probability.Distributions.SetBernoulli
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.HasLaw

import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Probability.Notation

/-!
# Binomial random variables

This file defines the binomial distribution and binomial random variables,
and computes their expectation and variance.

## Main definitions

* `ProbabilityTheory.binomial`:
  Binomial distribution on an arbitrary semiring with parameters `n` and `p`.
* `ProbabilityTheory.IsBinomial`:
  Predicate for a random variable to be binomial with parameters `n` and `p`.

## Main statements

* `ProbabilityTheory.IsBinomial.integral_eq`: Computation of the expectation of a binomial r.v.
* `ProbabilityTheory.IsBinomial.variance_eq`: Computation of the variance of a binomial r.v.
* `ProbabilityTheory.IsBinomial.condVar_eq`:
  Computation of the conditional variance of a binomial r.v.

## Notation

`Bin(n, p)` is the binomial distribution with parameters `n` and `p` in `ℕ`.
`Bin(R, n, p)` is the binomial distribution with parameters `n` and `p` in `R`.
-/

public section

open MeasureTheory
open scoped NNReal ProbabilityTheory unitInterval

namespace MeasureTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω} {s : Set Ω}

/-! ### Preliminary lemmas -/

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
      rw [← probReal_compl_eq_one_sub (by exact hXmeas <| .singleton _)]
      refine measureReal_congr ?_
      filter_upwards [hX]
      -- FIXME: The following change is due to the measure theory library abusing the defeq
      -- `Set Ω = (Ω → Prop)`
      change ∀ ω _, (_ ≠ _) = (_ = _)
      rintro ω (hω | hω) <;> simp [hω]

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

/-! ### Binomial distribution -/

variable {R : Type*} [MeasurableSpace R] [AddMonoidWithOne R] {X : Ω → R} {n : ℕ} {p : I}

/-- The binomial probability distribution with parameter `p`.

For convenience, this distribution is defined over any semiring.
It is meant to be used on `ℕ` and `ℝ` mainly. -/
@[expose]
noncomputable def binomial (n : ℕ) (p : I) : Measure R :=
  setBer(Set.Iio n, p).map (Nat.cast ∘ Set.ncard)

/-- The binomial probability distribution with parameter `p` valued in the semiring `R`. -/
scoped notation3 "Bin(" R' ", " n ", " p ")" => binomial (R := R') n p

/-- The binomial probability distribution with parameter `p`. -/
scoped notation3 "Bin(" n ", " p ")" => Bin(ℕ, n, p)

instance isProbabilityMeasure_binomial : IsProbabilityMeasure Bin(R, n, p) :=
  Measure.isProbabilityMeasure_map <| by fun_prop

@[simp] lemma map_natCast_binomial : Bin(n, p).map Nat.cast = Bin(R, n, p) :=
  -- FIXME: Why can't `fun_prop` deal with the composition itself?
  -- See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/fun_prop.20fails.20Nat.2Ecast.20.E2.88.98.20Set.2Encard.20.3A.20Set.20.E2.84.95.20.E2.86.92.20.E2.84.95.20measurable/
  Measure.map_map (by fun_prop) (.comp (by fun_prop) (by fun_prop))

variable (X n p) in
/-- A random variable is binomial if it is distributed following the binomial distribution. -/
abbrev IsBinomial (P : Measure Ω := by volume_tac) := HasLaw X Bin(R, n, p) P

lemma IsBinomial.id_binomial : IsBinomial id n p Bin(R, n, p) := .id

lemma IsBinomial.natCast_binomial : IsBinomial (Nat.cast : ℕ → R) n p Bin(n, p) where
  map_eq := by simp
  -- FIXME: Why doesn't `fun_prop` apply `Measurable.aemeasurable` itself?
  aemeasurable := by refine Measurable.aemeasurable ?_; fun_prop

lemma IsBinomial.ae_mem_image_natCast_Iic [MeasurableSingletonClass R]
    (hX : IsBinomial X n p P) : ∀ᵐ ω ∂P, X ω ∈ Nat.cast '' Set.Iic n := by
  have : MeasurableSet (Nat.cast (R := R) '' Set.Iic n) :=
    ((Set.finite_Iic _).image _).measurableSet
  rw [hX.ae_iff <| by simpa, binomial, ae_map_iff (by fun_prop) <| by exact this]
  filter_upwards [setBernoulli_ae_subset] with s hs
  exact Set.mem_image_of_mem _ <| by simpa using Set.ncard_le_ncard hs

lemma IsBinomial.ae_le {X : Ω → ℕ} (hX : IsBinomial X n p P) : ∀ᵐ ω ∂P, X ω ≤ n := by
  simpa using hX.ae_mem_image_natCast_Iic

/-! ### Binomial random variables -/

variable {X : Ω → ℝ}

/-- **Expectation of a binomial random variable**.

The expectation of a binomial random variable with parameters `n` and `p` is `pn`. -/
lemma IsBinomial.integral_eq (hX : IsBinomial X n p P) : P[X] = p.val * n := by
  rw [HasLaw.integral_eq hX, binomial, integral_map] <;> sorry

/-- **Variance of a binomial random variable**.

The variance of a binomial random variable with parameters `n` and `p` is `p(1 - p)n`. -/
lemma IsBinomial.variance_eq (hX : HasLaw X μ P) : Var[X; P] = p * (1 - p) * n :=
  sorry

/-- **Conditional variance of a binomial random variable**.

The conditional variance of a binomial random variable is the product of the conditional
probabilities that it's equal to `0` and that it's equal to `1`. -/
lemma IsBinomial.condVar_eq {m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) {P : Measure[m₀] Ω}
    (hX : HasLaw X μ P) :
    Var[X; P | m] =ᵐ[P] P[X | m] * P[1 - X | m] :=
  sorry

end ProbabilityTheory
