/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Data.Rat.NNRat
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

section Semiring

variable [Semiring R]

namespace Ring

/-- `ascFactorial`, also known as the rising factorial function, is the product
`r (r+1) ⋯ (r + n - 1)`.  In other words, it recursively evaluates the `n`-th ascending Pochhammer
polynomial at a semiring element `r`.-/
def ascFactorial (r : R) : ℕ → R
  | 0 => 1
  | (k + 1) => (ascFactorial r k) * (r + k)

theorem ascFactorial_zero (r : R) : ascFactorial r 0 = 1 := rfl

theorem ascFactorial_succ (r : R) (k : ℕ) :
    ascFactorial r (k.succ) = (ascFactorial r k) * (r + k) := rfl

theorem ascFactorial_cast (n : ℕ) : ∀ (k : ℕ), ascFactorial (n : R) k = ascFactorial n k
  | 0 => by rw [ascFactorial_zero, ascFactorial_zero, Nat.cast_one]
  | (k + 1) => by
    rw [ascFactorial_succ, ascFactorial_succ, Nat.cast_mul, ascFactorial_cast n k, Nat.cast_add]
    norm_cast

theorem ascFactorial_eq_ascPochhammer_eval (r : R) :
    ∀ (k : ℕ), ascFactorial r k = Polynomial.eval r (ascPochhammer R k)
  | 0 => by rw [ascPochhammer_zero, Polynomial.eval_one, ascFactorial_zero]
  | (k + 1) => by
    rw [ascPochhammer_succ_eval, ← ascFactorial_eq_ascPochhammer_eval r k, ascFactorial_succ]

theorem translate_comm_ascFactorial (r s : R) (k : ℕ) (h : Commute r s) : ∀ (n : ℕ),
    Commute (r + k) (ascFactorial s n)
  | 0 => by
    rw [ascFactorial_zero]
    exact Commute.one_right (r + ↑k)
  | (n + 1) => by
    rw [ascFactorial_succ]
    exact (translate_comm_ascFactorial r s k h n).mul_right (Nat.add_cast_commute_add_cast r s k n h)

theorem ascFactorial_add_right (r : R) (n : ℕ) : ∀ (k : ℕ),
    ascFactorial r (n + k) = ascFactorial r n * ascFactorial (r + n) k
  | 0 => by rw [add_zero, ascFactorial_zero, mul_one]
  | (k + 1) => by
    rw [← add_assoc, ascFactorial_succ, ascFactorial_add_right r n k, ascFactorial_succ, mul_assoc,
    Nat.cast_add, add_assoc]

end Ring

end Semiring

section BinomialSemiring

/-- A semiring is binomial if multiplication by nonzero natural numbers is injective and ascending
factorials are divisible by the corresponding factorial. -/
class BinomialSemiring (R: Type u) extends Semiring R where
  /-- Multiplication by positive integers is injective -/
  inj_smul_pos (n : ℕ) (r s : R) (h: n ≠ 0) : n * r = n * s → r = s
  /-- The multichoose function witnesses the divisibility of ascFactorial r n by n! -/
  multichoose : R → ℕ → R
  /-- ascFactorial r n is divisible by n! (witnessed by multichoose) -/
  factorial_mul_multichoose : ∀ (r : R) (n : ℕ),
    n.factorial * multichoose r n = Ring.ascFactorial r n

namespace Ring

theorem inj_smul_pos [BinomialSemiring R] (n : ℕ) (r s : R) (h: n ≠ 0) :
    n * r = n * s → r = s := BinomialSemiring.inj_smul_pos n r s h

theorem eq_of_mul_eq_mul_factorial [BinomialSemiring R] {r s : R} (n : ℕ)
    (h : n.factorial * r = n.factorial * s) : r = s :=
  inj_smul_pos n.factorial r s (Nat.factorial_ne_zero n) h

/-- This is a generalization of the combinatorial multichoose function, given by choosing with
replacement. -/
def multichoose [BinomialSemiring R] (r : R) (n : ℕ) : R :=
  BinomialSemiring.multichoose r n

theorem factorial_mul_multichoose_eq_ascFactorial [BinomialSemiring R] (r : R) (n : ℕ) :
    n.factorial * multichoose r n = ascFactorial r n :=
  BinomialSemiring.factorial_mul_multichoose r n

end Ring

end BinomialSemiring
