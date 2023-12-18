/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Binomial semirings and binomial rings

In this file we introduce the binomial property as a Prop-valued mixin, and define the `multichoose`
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

-/

open Function

variable {R : Type*}

section Binomial

/-- A `Prop`-valued mixin for multi-binomial coefficients. -/
class Binomial (R : Type*) [Semiring R] : Prop where
  /-- Multiplication by positive integers is injective -/
  nsmul_right_injective (n : ℕ) (h : n ≠ 0) : Injective (n • · : R → R)
  /-- `ascFactorial r n` is divisible by n! -/
  factorial_nsmul_multichoose (r : R) (n : ℕ) : ∃ (s : R),
    n.factorial • s = Polynomial.eval r (ascPochhammer R n)

namespace Ring

theorem nsmul_right_injective [Semiring R] [Binomial R] (n : ℕ) (h : n ≠ 0) :
    Injective (n • · : R → R) := Binomial.nsmul_right_injective n h

/-- This is a generalization of the combinatorial multichoose function, given by choosing with
replacement. -/
noncomputable def multichoose [Semiring R] [Binomial R] (r : R) (n : ℕ) : R :=
  Exists.choose (Binomial.factorial_nsmul_multichoose r n)

theorem factorial_nsmul_multichoose_eq_eval_ascPochhammer [Semiring R] [Binomial R] (r : R)
    (n : ℕ) : n.factorial • multichoose r n = Polynomial.eval r (ascPochhammer R n) :=
  Exists.choose_spec (Binomial.factorial_nsmul_multichoose r n)

instance naturals_binomial : Binomial ℕ := by
  refine Binomial.mk ?nsmul_right_injective ?factorial_nsmul_multichoose
  intro n hn r s hrs
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) hrs
  intro n k
  use Nat.multichoose n k
  rw [Nat.multichoose_eq, smul_eq_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
    ascPochhammer_nat_eq_descFactorial]

end Ring

end Binomial
