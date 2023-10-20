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
def ascPochEval (r : R) : ℕ → R
  | 0 => 1
  | (k + 1) => (ascPochEval r k) * (r + k)

theorem ascPochEval_zero (r : R) : ascPochEval r 0 = 1 := rfl

theorem ascPochEval_succ (r : R) (k : ℕ) :
    ascPochEval r (k.succ) = (ascPochEval r k) * (r + k) := rfl

theorem add_cast_succ (r : R) (k : ℕ) : r + @Nat.cast R Semiring.toNatCast (k + 1) =
    r + (@Nat.cast R Semiring.toNatCast k + 1) := by norm_cast

theorem ascPochEval_succ_left (r : R) : ∀ (k : ℕ),
    ascPochEval r (k.succ) = r * (ascPochEval (r+1) k)
  | 0 => by
    rw[ascPochEval_zero, ascPochEval_succ, ascPochEval_zero]
    simp only [Nat.cast_zero, add_zero, one_mul, mul_one]
  | (k+1) => by
    rw [ascPochEval_succ, ascPochEval_succ_left r k, ascPochEval_succ]
    rw [add_assoc, add_comm 1]
    rw [add_cast_succ, mul_assoc]

theorem ascPochEval_cast (n : ℕ) : ∀ (k : ℕ), ascPochEval (n : R) k = ascPochEval n k
  | 0 => by rw [ascPochEval_zero, ascPochEval_zero, Nat.cast_one]
  | (k + 1) => by
    rw [ascPochEval_succ, ascPochEval_succ, Nat.cast_mul, ascPochEval_cast n k, Nat.cast_add]
    norm_cast

theorem ascPochEval_eq_ascPochhammer_eval (r : R) :
    ∀ (k : ℕ), ascPochEval r k = Polynomial.eval r (ascPochhammer R k)
  | 0 => by rw [ascPochhammer_zero, Polynomial.eval_one, ascPochEval_zero]
  | (k + 1) => by
    rw [ascPochhammer_succ_eval, ← ascPochEval_eq_ascPochhammer_eval r k, ascPochEval_succ]

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
  factorial_mul_multichoose : ∀ (r : R) (n : ℕ),
    n.factorial * multichoose r n = Ring.ascPochEval r n

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

theorem ascPochEval_nat_eq_descFactorial (n : ℕ) : ∀ (k : ℕ),
    ascPochEval n k = Nat.descFactorial (n+k-1) k
  | 0 => by
    rw[add_zero, Nat.descFactorial_zero, ascPochEval_zero]
  | (k+1) => by
    rw[ascPochEval_succ_left, Nat.descFactorial_succ, ascPochEval_nat_eq_descFactorial (n+1) k]
    simp only [ge_iff_le, Nat.succ_add_sub_one, Nat.add_succ_sub_one, add_le_iff_nonpos_left,
      nonpos_iff_eq_zero, add_tsub_cancel_right]

theorem ascPochEval_nat_eq_fact_mul_choose (n : ℕ) : ∀ (k:ℕ),
    ascPochEval n k = k.factorial * Nat.choose (n+k-1) k
| 0 => by rw [Nat.factorial_zero, Nat.add_zero, Nat.choose, ascPochEval_zero, one_mul]
| (k+1) => by
  rw [← Nat.descFactorial_eq_factorial_mul_choose, ascPochEval_succ_left,
    ascPochEval_nat_eq_descFactorial, Nat.descFactorial_succ]
  simp only [ge_iff_le, Nat.add_succ_sub_one, add_le_iff_nonpos_left, add_tsub_cancel_right]
  rw [add_assoc, add_comm 1 k]
  simp only [ge_iff_le, Nat.add_succ_sub_one]

instance naturals_binomial_semiring : BinomialSemiring ℕ := by
  refine BinomialSemiring.mk ?inj_smul_pos ?multichoose ?factorial_mul_multichoose
  intro n r s npos h
  refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero npos) h
  use fun n k => Nat.multichoose n k
  intro n k
  rw [Nat.multichoose_eq, ascPochEval_nat_eq_fact_mul_choose]
  norm_cast

theorem multichoose_eq_nat_multichoose (n k : ℕ) : multichoose n k = Nat.multichoose n k := by
  refine eq_of_mul_eq_mul_factorial k ?_
  rw [factorial_mul_multichoose_eq_ascPochEval, Nat.multichoose_eq,
    ascPochEval_nat_eq_fact_mul_choose n k]
  norm_cast

end Ring

end BinomialSemiring

section descFactorial

variable [Ring R]

namespace Ring

/-- `descFactorial` is a direct generalization of the natural number descending factorial function,
  given by r(r-1) ··· (r-n+1) -/
def descFactorial (r:R) : ℕ → R
  | 0 => 1
  | (n+1) => (r-n) * (descFactorial r n)

theorem descFactorial_zero (r : R) :
    descFactorial r 0 = 1 := rfl

theorem descFactorial_succ (r : R) (n : ℕ) :
    descFactorial r (n+1) = (r - n) * (descFactorial r n) := by rfl

theorem zero_descFactorial_succ [Ring R] : ∀ (k : ℕ), descFactorial (0:R) k.succ = 0
  | 0 => by
    simp [descFactorial_succ]
  | (k+1) => by
    simp [descFactorial_succ]
    cases k with
    | zero => simp
    | succ n =>
      simp [zero_descFactorial_succ n]

theorem ascPochEval_eq_descFactorial (r : R) : ∀ (k : ℕ),
    ascPochEval r k = descFactorial (r+k-1) k
  | 0 => by
    rw [descFactorial_zero, ascPochEval_zero]
  | (k+1) => by
    rw [ascPochEval_succ_left, descFactorial_succ, ascPochEval_eq_descFactorial (r+1) k,
      add_cast_succ]
    have h₁: r + 1 + (k:R) - 1 = r + k := by
      rw [add_sub_right_comm, add_sub_cancel]
    have h₂ : r + (k + 1) - 1 = r + k := by
      refine sub_eq_of_eq_add (add_assoc r (↑k) 1).symm
    rw [h₁, h₂, add_sub_cancel]

end Ring

end descFactorial

/-- A ring is binomial if multiplication by factorials is injective and pochhammer evaluations
  are divisible by the corresponding factorial. -/
class BinomialRing (R: Type u) extends Ring R, BinomialSemiring R

section choose

namespace Ring

/-- The binomial coefficient `choose r n` generalizes the natural number choose function,
  interpreted in terms of choosing without replacement. -/
def choose {R: Type _} [BinomialRing R] (r : R) (n : ℕ): R :=
  multichoose (r-n+1) n

theorem descFactorial_eq_factorial_mul_choose [BinomialRing R] (r : R) (n : ℕ) :
    descFactorial r n = n.factorial * choose r n := by
  unfold choose
  rw [factorial_mul_multichoose_eq_ascPochEval, ascPochEval_eq_descFactorial, sub_add,
    add_sub_assoc, sub_add_cancel]

theorem choose_zero_right [BinomialRing R] (r : R) : choose r 0 = 1 := by
  refine eq_of_mul_eq_mul_factorial 0 ?_
  rw [← descFactorial_eq_factorial_mul_choose, descFactorial_zero, Nat.factorial_zero, Nat.cast_one,
    mul_one]

theorem choose_zero_succ [BinomialRing R] (k : ℕ) : choose (0 : R) (Nat.succ k) = 0 := by
  refine eq_of_mul_eq_mul_factorial (Nat.succ k) ?_
  rw [← descFactorial_eq_factorial_mul_choose, mul_zero, zero_descFactorial_succ]

theorem choose_zero_pos [BinomialRing R] (k : ℕ) (h_pos: 0 < k) : choose (0:R) k = 0 := by
  rw [← Nat.succ_pred_eq_of_pos h_pos, choose_zero_succ]

end Ring

end choose
