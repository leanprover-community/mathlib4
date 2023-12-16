/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Binomial semirings and binomial rings

In this file we introduce binomial semirings and binomial rings, together with related functions
like binomial coefficients.

According to our main reference [elliott2006binomial] (which lists many equivalent conditions), a
binomial ring is a torsion-free commutative ring `R` such that for any `x ∈ R` and any `k ∈ ℕ`, the
product `x(x-1)⋯(x-k+1)` is divisible by `k!`.  The torsion-free condition lets us divide by `k!`
unambiguously, so we get uniquely defined binomial coefficients.

The defining condition doesn't require commutativity, and we get a theory with essentially the same
power by replacing subtraction with addition.  Thus, we consider a semiring `R` in which
multiplication by factorials is injective, and demand that for all `x ∈ R` and any `k ∈ ℕ`,
`x(x+1)⋯(x+(k-1))` is divisible by `k!`.
The quotient is called `multichoose r k`, following the convention given for natural numbers.

## References
* [J. Elliott, *Binomial rings, integer-valued polynomials, and λ-rings*][elliott2006binomial]

-/

universe u

variable {R : Type u}

section BinomialSemiring

/-- A semiring is binomial if multiplication by nonzero natural numbers is injective and ascending
factorials are divisible by the corresponding factorial. -/
class BinomialSemiring (R : Type u) extends Semiring R where
  /-- Multiplication by positive integers is injective -/
  nsmul_injective (n : ℕ) (r s : R) (h : n ≠ 0) : n • r = n • s → r = s
  /-- The multichoose function witnesses the divisibility of ascFactorial r n by n! -/
  multichoose : R → ℕ → R
  /-- ascFactorial r n is divisible by n! (witnessed by multichoose) -/
  factorial_nsmul_multichoose : ∀ (r : R) (n : ℕ),
    n.factorial • multichoose r n = Polynomial.eval r (ascPochhammer R n)

namespace Ring

theorem nsmul_injective [BinomialSemiring R] (n : ℕ) (r s : R) (h : n ≠ 0) :
    n • r = n • s → r = s := BinomialSemiring.nsmul_injective n r s h

theorem eq_of_mul_eq_mul_factorial [BinomialSemiring R] {r s : R} (n : ℕ)
    (h : n.factorial • r = n.factorial • s) : r = s :=
  nsmul_injective n.factorial r s (Nat.factorial_ne_zero n) h

/-- This is a generalization of the combinatorial multichoose function, given by choosing with
replacement. -/
def multichoose [BinomialSemiring R] (r : R) (n : ℕ) : R :=
  BinomialSemiring.multichoose r n

theorem factorial_mul_multichoose_eq_ascPochhammer [BinomialSemiring R] (r : R) (n : ℕ) :
    n.factorial • multichoose r n = Polynomial.eval r (ascPochhammer R n) :=
  BinomialSemiring.factorial_nsmul_multichoose r n

end Ring

end BinomialSemiring
