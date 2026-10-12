/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module -- shake: keep-all

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The binomial distribution

This file defines the probability mass function of the binomial distribution.

## Main results

* `binomial_one_eq_bernoulli`: For `n = 1`, it is equal to `PMF.bernoulli`.
-/

deprecated_module (since := "2026-05-31")

public section

namespace PMF

@[deprecated "type changed" (since := "2026-05-31")]
alias binomial_one_eq_bernoulli := ProbabilityTheory.binomial_one_eq_bernoulliMeasure

end PMF
