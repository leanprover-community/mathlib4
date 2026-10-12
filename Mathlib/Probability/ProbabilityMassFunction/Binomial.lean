/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The binomial distribution

This file defines the probability mass function of the binomial distribution.

## Main results

* `binomial_one_eq_bernoulli`: For `n = 1`, it is equal to `PMF.bernoulli`.
-/

@[expose] public section

namespace PMF

/-- The binomial distribution on one coin is the Bernoulli distribution. -/
@[deprecated ProbabilityTheory.binomial_one_eq_bernoulliMeasure +typeChanged
  (since := "2026-05-31")]
theorem binomial_one_eq_bernoulli (p : ℝ≥0) (h : p ≤ 1) :
    binomial p h 1 = (bernoulli p h).map (cond · 1 0) := by
  ext i; fin_cases i <;> simp [binomial_apply, bernoulli_apply]

end PMF
