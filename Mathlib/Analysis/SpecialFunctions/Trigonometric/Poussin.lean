/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The de la Vallée Poussin trigonometric inequality

The inequality `3 + 4 * cos θ + cos (2 * θ) ≥ 0` is the trigonometric
heart of the classical zero-free region argument for `L`-functions
(the "3-4-1" trick): applied to the real parts of a logarithmic
derivative at `σ`, `σ + it` and `σ + 2it`, it produces a nonnegative
combination whose Euler-product bound forces zeros away from the
line `Re s = 1`. The proof is the identity
`3 + 4 * cos θ + cos (2 * θ) = 2 * (cos θ + 1) ^ 2`.
-/

public section

namespace Real

/-- The de la Vallée Poussin inequality: for every real `θ`,
`0 ≤ 3 + 4 * cos θ + cos (2 * θ)`. In fact the left-hand side equals
`2 * (cos θ + 1) ^ 2`. -/
theorem three_add_four_mul_cos_add_cos_two_mul_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h1 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  rw [h1]
  nlinarith [Real.cos_sq_le_one θ, sq_nonneg (Real.cos θ + 1),
    Real.neg_one_le_cos θ]

end Real
