/-
Copyright (c) 2020 Johan Commelin, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.AlgebraTower

#align_import data.mv_polynomial.invertible from "leanprover-community/mathlib"@"f6c030fea3c2809bb489bc8901f307bf6b4bf0c0"

/-!
# Invertible polynomials

This file is a stub containing some basic facts about
invertible elements in the ring of polynomials.
-/


open MvPolynomial

noncomputable instance MvPolynomial.invertibleC (σ : Type*) {R : Type*} [CommSemiring R] (r : R)
    [Invertible r] : Invertible (C r : MvPolynomial σ R) :=
  Invertible.map (C : R →+* MvPolynomial σ R) _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.invertible_C MvPolynomial.invertibleC

/-- A natural number that is invertible when coerced to a commutative semiring `R`
is also invertible when coerced to any polynomial ring with rational coefficients.

Short-cut for typeclass resolution. -/
noncomputable instance MvPolynomial.invertibleCoeNat (σ R : Type*) (p : ℕ) [CommSemiring R]
    [Invertible (p : R)] : Invertible (p : MvPolynomial σ R) :=
  IsScalarTower.invertibleAlgebraCoeNat R _ _
#align mv_polynomial.invertible_coe_nat MvPolynomial.invertibleCoeNat
