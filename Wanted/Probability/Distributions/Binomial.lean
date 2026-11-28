/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Probability.Distributions.Binomial

open MeasureTheory
open scoped ProbabilityTheory unitInterval

namespace ProbabilityTheory
variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {n : ℕ} {p : I} {X : Ω → ℝ}

/-- **Variance of a binomial random variable**.

The variance of a binomial random variable with parameters `n` and `p` is `p(1 - p)n`. -/
proof_wanted variance_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) :
    Var[X; P] = p * (1 - p) * n

end ProbabilityTheory
