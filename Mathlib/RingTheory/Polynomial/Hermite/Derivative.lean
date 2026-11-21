/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Derivatives, recurrence, and parity of the Hermite polynomials

`Mathlib/RingTheory/Polynomial/Hermite/Basic.lean` defines the probabilists' Hermite polynomials
by the recursion `hermite (n + 1) = X * hermite n - derivative (hermite n)` and develops their
coefficient API. This file records the classical closed form of their derivatives, and its
consequences:

## Main results

* `Polynomial.derivative_hermite`: the lowering identity `H'ₙ = n • Hₙ₋₁`;
* `Polynomial.iterate_derivative_hermite`: its iterated form
  `derivative^[k] (hermite n) = n.descFactorial k • hermite (n - k)`;
* `Polynomial.hermite_add_two`: the three-term recurrence `Hₙ₊₂ = X * Hₙ₊₁ - (n + 1) • Hₙ`,
  obtained by eliminating the derivative from the defining recursion;
* `Polynomial.hermite_comp_neg_X` and `Polynomial.hermite_aeval_neg`: the parity identity, as a
  polynomial identity and after evaluation in any commutative ring.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)
-/

public section

namespace Polynomial

/-- **Lowering (derivative) identity for the Hermite polynomials.** Differentiating the
`(n + 1)`-st probabilists' Hermite polynomial lowers the index: `H'ₙ₊₁ = (n + 1) • Hₙ`. -/
theorem derivative_hermite_succ (n : ℕ) :
    derivative (hermite (n + 1)) = (n + 1) • hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, one_mul, ih,
      derivative_smul, hermite_succ n]
    ring

/-- The Hermite derivative identity at index `n`: `H'ₙ = n • Hₙ₋₁`. For `n = 0` both sides
vanish, since `H₀ = 1`. -/
theorem derivative_hermite (n : ℕ) :
    derivative (hermite n) = n • hermite (n - 1) := by
  cases n with
  | zero => simp [hermite_zero]
  | succ n => simpa using derivative_hermite_succ n

/-- Iterating the lowering identity: the `k`-th derivative of `Hₙ` is the descending factorial
`n * (n - 1) * ⋯ * (n - k + 1)` times `Hₙ₋ₖ`. For `k > n` the descending factorial is `0` and
both sides vanish. -/
theorem iterate_derivative_hermite (n k : ℕ) :
    derivative^[k] (hermite n) = n.descFactorial k • hermite (n - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_smul, derivative_hermite, smul_smul,
      Nat.descFactorial_succ, Nat.sub_sub, mul_comm]

/-- **Three-term recurrence for the Hermite polynomials.** Eliminating the derivative from the
defining recursion `Polynomial.hermite_succ` gives the classical relation
`Hₙ₊₂ = X * Hₙ₊₁ - (n + 1) • Hₙ`. -/
theorem hermite_add_two (n : ℕ) :
    hermite (n + 2) = X * hermite (n + 1) - (n + 1) • hermite n := by
  rw [hermite_succ (n + 1), derivative_hermite_succ]

/-- The parity identity for the Hermite polynomials, as a polynomial identity. -/
theorem hermite_comp_neg_X (n : ℕ) : (hermite n).comp (-X) = (-1) ^ n * hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := congrArg derivative ih
    rw [derivative_comp, derivative_neg, derivative_X, derivative_mul, derivative_pow] at h
    simp only [derivative_neg, derivative_one, neg_mul, one_mul, zero_mul,
      mul_zero, zero_add, neg_zero] at h
    rw [hermite_succ, sub_comp, mul_comp, X_comp, ih, neg_eq_iff_eq_neg.mp h]
    ring

/-- **Parity of the Hermite polynomials**: `Hₙ(-x) = (-1)ⁿ * Hₙ(x)` in any commutative ring. -/
@[simp]
theorem hermite_aeval_neg {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    aeval (-x) (hermite n) = (-1) ^ n * aeval x (hermite n) := by
  rw [show (-x) = aeval x (-X : ℤ[X]) by simp, ← aeval_comp, hermite_comp_neg_X]
  simp

end Polynomial
