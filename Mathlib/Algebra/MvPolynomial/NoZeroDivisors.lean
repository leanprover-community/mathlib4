/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Multivariate polynomials over `NoZeroDivisors`

Many results about polynomials hold when the coefficient ring has no zero divisors.

This file does not define any new operations, but proves some of these stronger results.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[NoZeroDivisors R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

## TODOs

* Add a `totalDegree_mul_eq` theorem, which states that the total degree of a product of two
nonzero multivariate polynomials is the sum of their total degrees.

-/

@[expose] public section


noncomputable section

open Set Function Finsupp AddMonoidAlgebra

universe u v

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section NoZeroDivisors

variable [CommSemiring R] [NoZeroDivisors R]

variable {p q : MvPolynomial σ R}

section DegreeOf

lemma degreeOf_mul (hp : p ≠ 0) (hq : q ≠ 0) :
    degreeOf n (p * q) = degreeOf n p + degreeOf n q := by
  classical
  simp_rw [degreeOf_eq_natDegree, map_mul]
  rw [Polynomial.natDegree_mul] <;> simpa [← renameEquiv_apply, EmbeddingLike.map_eq_zero_iff]

theorem degreeOf_C_mul (j : σ) (c : R) (hc : c ≠ 0) :
    MvPolynomial.degreeOf j (MvPolynomial.C c * p) = MvPolynomial.degreeOf j p := by
  by_cases hp : p = 0
  · simp [hp]
  rw [degreeOf_mul (C_eq_zero.not.mpr hc) hp, degreeOf_C, zero_add]

end DegreeOf

section Degrees

lemma degrees_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) :
    degrees (p * q) = degrees p + degrees q := by
  classical
  apply Multiset.ext'
  intro s
  simp_rw [Multiset.count_add, ← degreeOf_def, degreeOf_mul hp hq]

end Degrees

end NoZeroDivisors

end MvPolynomial
