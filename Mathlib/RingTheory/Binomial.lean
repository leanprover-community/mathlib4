/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Binomial rings

In this file we introduce the binomial property as a mixin, and define the `multichoose`
and `choose` functions generalizing binomial coefficients.

According to our main reference [elliott2006binomial] (which lists many equivalent conditions), a
binomial ring is a torsion-free commutative ring `R` such that for any `x ∈ R` and any `k ∈ ℕ`, the
product `x(x-1)⋯(x-k+1)` is divisible by `k!`. The torsion-free condition lets us divide by `k!`
unambiguously, so we get uniquely defined binomial coefficients.

The defining condition doesn't require commutativity (or associativity), and we get a theory with
essentially the same power by replacing subtraction with addition. Thus, we consider a semiring `R`
in which multiplication by factorials is injective, and demand that the evaluation of the ascending
Pochhammer polynomial `X(X+1)⋯(X+(k-1))` at any element is divisible by `k!`. The quotient is called
`multichoose r k`, following the convention given for natural numbers.

## References

* [J. Elliott, *Binomial rings, integer-valued polynomials, and λ-rings*][elliott2006binomial]

## TODO

* Replace `Nat.multichoose` with `Ring.multichoose`.
* `Int.instBinomialRing`
* `Ring.choose` for binomial rings.
* Generalize to the power-associative case, when power-associativity is implemented.

-/

open Function

/-- A binomial ring is a ring for which ascending Pochhammer evaluations are uniquely divisible by
suitable factorials.  We define this notion for semirings, but retain the ring name.  We introduce
`Ring.multichoose` as the uniquely defined quotient. -/
class BinomialRing (R : Type*) [Semiring R] where
  /-- Multiplication by positive integers is injective -/
  nsmul_right_injective (n : ℕ) (h : n ≠ 0) : Injective (n • · : R → R)
  /-- A multichoose function, giving the quotient of Pochhammer evaluations by factorials. -/
  multichoose : R → ℕ → R
  /-- `ascPochhammer R n` evaluated at any `r` is divisible by n! (witnessed by multichoose) -/
  factorial_nsmul_multichoose (r : R) (n : ℕ) :
    n.factorial • multichoose r n = Polynomial.eval r (ascPochhammer R n)

section Binomial

namespace Ring

variable {R : Type*} [Semiring R] [BinomialRing R]

theorem nsmul_right_injective (n : ℕ) (h : n ≠ 0) :
    Injective (n • · : R → R) := BinomialRing.nsmul_right_injective n h

/-- The multichoose function is the quotient of ascending Pochhammer evaluation by the corresponding
factorial. When applied to natural numbers, `multichoose k n` describes choosing a multiset of `n`
items from a group of `k`, i.e., choosing with replacement. -/
def multichoose (r : R) (n : ℕ) : R := BinomialRing.multichoose r n

@[simp]
theorem multichoose_eq_multichoose (r : R) (n : ℕ) :
    BinomialRing.multichoose r n = multichoose r n := rfl

theorem factorial_nsmul_multichoose_eq_eval_ascPochhammer (r : R) (n : ℕ) :
    n.factorial • multichoose r n = Polynomial.eval r (ascPochhammer R n) :=
  BinomialRing.factorial_nsmul_multichoose r n

instance Nat.instBinomialRing : BinomialRing ℕ where
  nsmul_right_injective n hn r s hrs := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) hrs
  multichoose := Nat.multichoose
  factorial_nsmul_multichoose r n := by
    rw [Nat.multichoose_eq, smul_eq_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
    ascPochhammer_nat_eq_descFactorial]

end Ring

end Binomial
