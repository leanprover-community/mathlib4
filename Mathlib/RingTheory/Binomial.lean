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

/-- `ascPochEval` directly evaluates the `n`-th ascending Pochhammer polynomial at an element `r`.-/
noncomputable def ascPochEval (r : R) (n : ℕ) : R :=
    Polynomial.eval r (ascPochhammer R n)

theorem ascPochEval_zero (r : R) : ascPochEval r 0 = 1 := by
  unfold ascPochEval
  rw [ascPochhammer_zero R, Polynomial.eval_one]

theorem ascPochEval_succ (r : R) (k : ℕ) :
    ascPochEval r (k.succ) = (ascPochEval r k) * (r + k) := by
  unfold ascPochEval
  rw [ascPochhammer_succ_eval]

theorem ascPochEval_cast (n : ℕ) : ∀ (k : ℕ), ascPochEval (n : R) k = ascPochEval n k
  | 0 => by rw [ascPochEval_zero, ascPochEval_zero, Nat.cast_one]
  | (k + 1) => by
    rw [ascPochEval_succ, ascPochEval_succ, Nat.cast_mul, ascPochEval_cast n k, Nat.cast_add]
    norm_cast

theorem translate_comm_ascPochEval (r s : R) (k : ℕ) (h : Commute r s) : ∀ (n : ℕ),
    Commute (r + k) (ascPochEval s n)
  | 0 => by
    rw [ascPochEval_zero]
    exact Commute.one_right (r + ↑k)
  | (n + 1) => by
    rw [ascPochEval_succ]
    exact (translate_comm_ascPochEval r s k h n).mul_right (Nat.add_cast_commute_add_cast r s k n h)

theorem ascPochEval_add_right (r : R) (n : ℕ) : ∀ (k : ℕ),
    ascPochEval r (n + k) = ascPochEval r n * ascPochEval (r + n) k
  | 0 => by rw [add_zero, ascPochEval_zero, mul_one]
  | (k + 1) => by
    rw [← add_assoc, ascPochEval_succ, ascPochEval_add_right r n k, ascPochEval_succ, mul_assoc,
    Nat.cast_add, add_assoc]

end Ring

end Semiring

section BinomialSemiring

/-- A semiring is binomial if multiplication by nonzero natural numbers is injective and pochhammer
evaluations are divisible by the corresponding factorial. -/
class BinomialSemiring (R: Type u) extends Semiring R where
  /-- Multiplication by positive integers is injective -/
  inj_smul_pos (n : ℕ) (r s : R) (h: n ≠ 0) : n * r = n * s → r = s
  /-- The multichoose function witnesses the divisibility of pochhammer n (evaluated at r) by n! -/
  multichoose : R → ℕ → R
  /-- pochhammer n (evaluated at r) is divisible by n! (witnessed by multichoose) -/
  factorial_mul_multichoose : ∀ (r : R) (n : ℕ), n.factorial * multichoose r n = Ring.ascPochEval r n

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

theorem factorial_mul_multichoose_eq_ascPochEval [BinomialSemiring R] (r : R) (n : ℕ) :
    n.factorial * multichoose r n = ascPochEval r n :=
  BinomialSemiring.factorial_mul_multichoose r n

end Ring

end BinomialSemiring
