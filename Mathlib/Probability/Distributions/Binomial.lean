/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
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
import Mathlib.Probability.Distributions.TwoValued
import Mathlib.Probability.Notation

/-!
# Binomial random variables

This file defines the binomial distribution and binomial random variables,
and computes their expectation and variance.

## Main definitions

* `ProbabilityTheory.binomial`:
  Binomial distribution on an arbitrary semiring with parameters `n` and `p`.

## Notation

`Bin(n, p)` is the binomial distribution with parameters `n` and `p` in `ℕ`.
`Bin(R, n, p)` is the binomial distribution with parameters `n` and `p` in `R`.
-/

public section

open MeasureTheory
open scoped NNReal ProbabilityTheory unitInterval

namespace ProbabilityTheory
variable {R Ω : Type*} [MeasurableSpace R] [AddMonoidWithOne R] {m : MeasurableSpace Ω}
  {P : Measure Ω} {X : Ω → R} {n : ℕ} {p : I}

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

lemma hasLaw_binomial_natCast : HasLaw (Nat.cast : ℕ → R) Bin(R, n, p) Bin(n, p) where
  map_eq := by simp
  -- FIXME: Why doesn't `fun_prop` apply `Measurable.aemeasurable` itself?
  aemeasurable := by refine Measurable.aemeasurable ?_; fun_prop

lemma ae_mem_image_natCast_Iic_of_hasLaw_binomial [MeasurableSingletonClass R]
    (hX : HasLaw X Bin(R, n, p) P) : ∀ᵐ ω ∂P, X ω ∈ Nat.cast '' Set.Iic n := by
  have : MeasurableSet (Nat.cast (R := R) '' Set.Iic n) :=
    ((Set.finite_Iic _).image _).measurableSet
  rw [hX.ae_iff <| by simpa, binomial, ae_map_iff (by fun_prop) <| by exact this]
  filter_upwards [setBernoulli_ae_subset] with s hs
  exact Set.mem_image_of_mem _ <| by simpa using Set.ncard_le_ncard hs

lemma ae_le_of_hasLaw_binomial {X : Ω → ℕ} (hX : HasLaw X Bin(n, p) P) : ∀ᵐ ω ∂P, X ω ≤ n := by
  simpa using ae_mem_image_natCast_Iic_of_hasLaw_binomial hX

/-! ### Binomial random variables -/

variable {X : Ω → ℝ}

/-- **Expectation of a binomial random variable**.

The expectation of a binomial random variable with parameters `n` and `p` is `pn`. -/
proof_wanted integral_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) : P[X] = p.val * n

/-- **Variance of a binomial random variable**.

The variance of a binomial random variable with parameters `n` and `p` is `p(1 - p)n`. -/
proof_wanted variance_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) :
    Var[X; P] = p * (1 - p) * n

/-- **Conditional variance of a binomial random variable**.

The conditional variance of a binomial random variable is the product of the conditional
probabilities that it's equal to `0` and that it's equal to `1`. -/
proof_wanted condVar_of_hasLaw_binomial {m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) {P : Measure[m₀] Ω}
    (hX : HasLaw X Bin(ℝ, n, p) P) :
    Var[X; P | m] =ᵐ[P] P[X | m] * P[1 - X | m]

end ProbabilityTheory
