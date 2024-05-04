/-
Copyright (c) 2017 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Algebra.MvPolynomial.Variables

#align_import data.mv_polynomial.comm_ring from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

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

This file should be extended to include `=` versions of all the `≤` lemmas about degree-related
definitions.

-/

noncomputable section

open Set Function Finsupp AddMonoidAlgebra

universe u v

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section NoZeroDivisors

variable [CommSemiring R] [NoZeroDivisors R]

variable {p q : MvPolynomial σ R}

section Degrees

lemma degrees_mul' (hp : p ≠ 0) (hq : q ≠ 0) : degrees (p * q) = degrees p + degrees q := by
  sorry

end Degrees

section DegreeOf

lemma degreeOf_mul : degreeOf n (p * q) = degreeOf n p + degreeOf n q := by
  sorry

theorem degreeOf_C_mul (j : σ) (c : F) (hc : c ≠ 0) :
    MvPolynomial.degreeOf j (MvPolynomial.C c * p) = MvPolynomial.degreeOf j p := by sorry

end DegreeOf

section TotalDegree

lemma totalDegree_mul' (hp : p ≠ 0) (hq : q ≠ 0) : totalDegree (p * q) = totalDegree p + totalDegree q := by
  sorry

end TotalDegree

end NoZeroDivisors

end MvPolynomial
