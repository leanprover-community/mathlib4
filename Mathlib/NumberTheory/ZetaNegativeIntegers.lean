/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude)
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The value of `ζ` at `-3`

The special value `ζ(-3) = 1 / 120`, from the classical formula
`ζ(-k) = -B'_{k+1} / (k + 1)` for the Bernoulli numbers `B'` (Mathlib's `bernoulli'`,
with `B'_1 = 1 / 2`): here `ζ(-3) = -B'_4 / 4 = -(-1 / 30) / 4 = 1 / 120`.
-/

public section

/-- **The value of the Riemann zeta function at `-3`:** `ζ(-3) = 1 / 120`. -/
theorem riemannZeta_neg_three : riemannZeta (-3 : ℂ) = 1 / 120 := by
  have h := riemannZeta_neg_nat_eq_bernoulli' 3
  push_cast at h
  norm_num [bernoulli'_four] at h
  exact h
