/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan, Heather Macbeth
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The Motzkin polynomial

The Motzkin polynomial is a well-known counterexample: it is nonnegative everywhere, but not
expressible as a polynomial sum of squares.

This file contains a proof of the first property (nonnegativity).

TODO: prove the second property.
-/

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The **Motzkin polynomial** is nonnegative.
This bivariate polynomial cannot be written as a sum of squares. -/
lemma motzkin_polynomial_nonneg (x y : K) :
    0 ≤ x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h : 0 < (x ^ 2 + y ^ 2) ^ 2 := by positivity
  refine nonneg_of_mul_nonneg_left ?_ h
  have H : 0 ≤ (x ^ 3 * y + x * y ^ 3 - 2 * x * y) ^ 2 * (1 + x ^ 2 + y ^ 2)
    + (x ^ 2 - y ^ 2) ^ 2 := by positivity
  linear_combination H
