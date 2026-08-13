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

* `Polynomial.derivative_hermite`: the lowering identity `H'ₙ = n • Hₙ₋₁`;
* `Polynomial.iterate_derivative_hermite`: its iterated form
  `derivative^[k] (hermite n) = n.descFactorial k • hermite (n - k)`;
* `Polynomial.hermite_add_two`: the three-term recurrence `Hₙ₊₂ = X * Hₙ₊₁ - (n + 1) • Hₙ`,
  obtained by eliminating the derivative from the defining recursion;
* `Polynomial.hermite_aeval_neg`: the parity `Hₙ(-x) = (-1)ⁿ * Hₙ(x)` in any commutative ring.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)
-/

public section

namespace Polynomial

/-- **Lowering (derivative) identity for the Hermite polynomials.** Differentiating the
`(n + 1)`-st probabilists' Hermite polynomial lowers the index: `H'ₙ₊₁ = (n + 1) • Hₙ`.

This is not a `simp` lemma because its left-hand side is already reduced by the `n`-indexed
form `Polynomial.derivative_hermite`. -/
theorem derivative_hermite_succ (n : ℕ) :
    derivative (hermite (n + 1)) = (n + 1) • hermite n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      derivative (hermite (n + 1 + 1))
          = derivative (X * hermite (n + 1) - derivative (hermite (n + 1))) := by
            rw [hermite_succ]
      _ = hermite (n + 1) + X * ((n + 1) • hermite n) -
            derivative ((n + 1) • hermite n) := by
            simp only [derivative_sub, derivative_mul, derivative_X, one_mul, ih, derivative_smul]
      _ = (n + 1 + 1) • hermite (n + 1) := by
            rw [hermite_succ n]
            simp only [derivative_smul]
            ring_nf

/-- The Hermite derivative identity at index `n`: `H'ₙ = n • Hₙ₋₁`. For `n = 0` both sides
vanish, since `H₀ = 1`. -/
@[simp]
theorem derivative_hermite (n : ℕ) :
    derivative (hermite n) = n • hermite (n - 1) := by
  cases n with
  | zero => simp [hermite_zero]
  | succ n => simpa using derivative_hermite_succ n

/-- Iterating the lowering identity: the `k`-th derivative of `Hₙ` is the descending factorial
`n * (n - 1) * ⋯ * (n - k + 1)` times `Hₙ₋ₖ`. For `k > n` the descending factorial is `0` and
both sides vanish. -/
@[simp]
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

/-- **Parity of the Hermite polynomials**: `Hₙ(-x) = (-1)ⁿ * Hₙ(x)` in any commutative ring.
A coefficient of `hermite n` in degree `k` can be nonzero only when `n + k` is even
(`Polynomial.coeff_hermite_of_odd_add`), so `k` and `n` share parity and `(-x)ᵏ = (-1)ⁿ * xᵏ`
on every surviving monomial. -/
@[simp]
theorem hermite_aeval_neg {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    aeval (-x) (hermite n) = (-1) ^ n * aeval x (hermite n) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hodd : Odd (n + k)
  · rw [coeff_hermite_of_odd_add hodd]; simp
  · rw [Nat.not_odd_iff_even] at hodd
    rw [zsmul_eq_mul, zsmul_eq_mul]
    have hpow : (-x) ^ k = (-1) ^ n * x ^ k := by
      rcases Nat.even_or_odd n with hn | hn
      · rw [Even.neg_pow ((Nat.even_add.mp hodd).mp hn), Even.neg_one_pow hn, one_mul]
      · have hk : Odd k := Nat.not_even_iff_odd.mp fun hke =>
          (Nat.not_even_iff_odd.mpr hn) ((Nat.even_add.mp hodd).mpr hke)
        rw [Odd.neg_pow hk, Odd.neg_one_pow hn]; ring
    rw [hpow]; ring

end Polynomial
