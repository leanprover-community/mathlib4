/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.RingTheory.Int.Basic

/-!
# Squarefree rationals

This file gathers results about squarefreeness and rational numbers.

## Main results

* `Rat.sq_mul_squarefree_unique`: the squarefree integer `d` in such a decomposition is unique.
-/

public section

/-- The squarefree integer `d` in a decomposition `q = r ^ 2 * d` is unique. -/
theorem Rat.sq_mul_squarefree_unique {d₁ d₂ : ℤ} (h₁ : Squarefree d₁) (h₂ : Squarefree d₂)
    (r₁ r₂ : ℚ) (hr₁ : r₁ ≠ 0) (h : r₁ ^ 2 * d₁ = r₂ ^ 2 * d₂) :
    d₁ = d₂ := by
  rw [mul_comm, ← div_eq_iff_mul_eq (pow_ne_zero 2 hr₁), mul_div_right_comm, ← div_pow] at h
  refine Int.eq_of_squarefree_of_isSquare_mul h₁ h₂ ?_
  rw [← Rat.isSquare_intCast_iff, Int.cast_mul, ← h, mul_assoc, ← sq, ← mul_pow]
  exact IsSquare.sq _
