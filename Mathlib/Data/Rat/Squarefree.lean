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

* `Rat.exists_sq_mul_squarefree`: every rational `q` is `r ^ 2 * d` for some rational `r` and
  squarefree integer `d`.
* `Rat.sq_mul_squarefree_unique`: the squarefree integer `d` in such a decomposition is unique.
-/

public section

/-- Every rational is a square times a squarefree integer. -/
theorem Rat.exists_sq_mul_squarefree (q : ℚ) :
    ∃ (d : ℤ) (r : ℚ), Squarefree d ∧ q = r ^ 2 * d := by
  obtain ⟨e, d, hed, hd⟩ := _root_.exists_sq_mul_squarefree (q.num * q.den)
  refine ⟨d, e / q.den, hd, ?_⟩
  rw [div_pow, div_mul_eq_mul_div, ← Int.cast_pow, ← Int.cast_mul, hed, sq,
    Int.cast_mul, Int.cast_natCast, mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr q.den_nz),
    Rat.num_div_den]

/-- The squarefree integer `d` in a decomposition `q = r ^ 2 * d` is unique. -/
theorem Rat.sq_mul_squarefree_unique {d₁ d₂ : ℤ} (h₁ : Squarefree d₁) (h₂ : Squarefree d₂)
    (r₁ r₂ : ℚ) (hr₁ : r₁ ≠ 0) (h : r₁ ^ 2 * d₁ = r₂ ^ 2 * d₂) :
    d₁ = d₂ := by
  rw [mul_comm, ← div_eq_iff_mul_eq (pow_ne_zero 2 hr₁), mul_div_right_comm, ← div_pow] at h
  suffices d₁ = d₂ ∨ d₁ = -d₂ by
    refine this.resolve_right fun h' ↦ ?_
    rw [h', Int.cast_neg, ← neg_one_mul, mul_left_inj' (Int.cast_ne_zero.mpr h₂.ne_zero)] at h
    linarith [sq_nonneg (r₂ / r₁)]
  refine Int.associated_iff.mp <| h₁.associated_of_isSquare_mul h₂ ?_
  rw [← Rat.isSquare_intCast_iff, Int.cast_mul, ← h, mul_assoc, ← sq, ← mul_pow]
  exact IsSquare.sq _
