/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Polynomial.Smeval

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
class BinomialSemiring (R: Type u) extends Semiring R where
  /-- Multiplication by positive integers is injective -/
  inj_smul_pos (n : ℕ) (r s : R) (h: n ≠ 0) : n • r = n • s → r = s
  /-- The multichoose function witnesses the divisibility of the ascending factorial by n! -/
  multichoose : R → ℕ → R
  /-- the ascending factorial is divisible by n! (witnessed by multichoose) -/
  factorial_smul_multichoose : ∀ (r : R) (n : ℕ),
    n.factorial • multichoose r n = Polynomial.smeval (ascPochhammer ℕ n) r

namespace Ring

theorem inj_smul_pos [BinomialSemiring R] (n : ℕ) (r s : R) (h: n ≠ 0) :
    n • r = n • s → r = s := BinomialSemiring.inj_smul_pos n r s h

theorem eq_of_smul_factorial_eq [BinomialSemiring R] {r s : R} (n : ℕ)
    (h : n.factorial • r = n.factorial • s) : r = s :=
  inj_smul_pos n.factorial r s (Nat.factorial_ne_zero n) h

/-- This is a generalization of the combinatorial multichoose function, given by choosing with
replacement. -/
def multichoose [BinomialSemiring R] (r : R) (n : ℕ) : R :=
  BinomialSemiring.multichoose r n

theorem factorial_smul_multichoose_eq_ascPochhammer [BinomialSemiring R] (r : R) (n : ℕ) :
    n.factorial • multichoose r n = Polynomial.smeval (ascPochhammer ℕ n) r :=
  BinomialSemiring.factorial_smul_multichoose r n

theorem ascPochhammer_smeval_eq_eval [Semiring R] (r : R) (k : ℕ) :
    Polynomial.smeval (ascPochhammer ℕ k) r = Polynomial.eval r (ascPochhammer R k) := by
  induction k with
  | zero =>
    rw [ascPochhammer_zero, ascPochhammer_zero, Polynomial.eval_one, Polynomial.smeval_one,
      nsmul_eq_mul, pow_zero, mul_one, Nat.cast_one]
  | succ n ih =>
    rw [ascPochhammer_succ_right, ascPochhammer_succ_right, Polynomial.smeval_mul r, ih,
      mul_add (ascPochhammer R n), Polynomial.smeval_add, Polynomial.smeval_X r, pow_one,
      ← Polynomial.C_eq_nat_cast, Polynomial.smeval_C, pow_zero, nsmul_one, Nat.cast_id,
      Polynomial.eval_add, Polynomial.eval_mul_X, ← Nat.cast_comm, Polynomial.eval_nat_cast_mul,
      mul_add, Nat.cast_comm]

instance naturals_binomial_semiring : BinomialSemiring ℕ := by
  refine BinomialSemiring.mk ?inj_smul_pos ?multichoose ?factorial_mul_multichoose
  intro n r s npos h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero npos) h
  use fun n k => Nat.multichoose n k
  intro n k
  rw [Nat.multichoose_eq, smul_eq_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
    Polynomial.smeval_eq_eval, ascPochhammer_nat_eq_descFactorial]

theorem multichoose_eq_nat_multichoose (n k : ℕ) : multichoose n k = Nat.multichoose n k := by
  refine eq_of_smul_factorial_eq k ?_
  rw [factorial_smul_multichoose_eq_ascPochhammer, Nat.multichoose_eq, ascPochhammer_smeval_eq_eval,
    ascPochhammer_nat_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose, smul_eq_mul]

end Ring

end BinomialSemiring

/-- A ring is binomial if multiplication by factorials is injective and ascending factorials
  are divisible by the corresponding factorial. -/
class BinomialRing (R: Type u) extends Ring R, BinomialSemiring R

/-- This is multichoose for integers, but only for the purpose of proving the instance. -/
def mcAux : ℤ → ℕ → ℤ
  | (n : ℕ) => fun k => ((Nat.multichoose n k):ℤ)
  | Int.negSucc n => fun k => (-1)^k * Nat.choose n.succ k

instance integers_binomial_ring : BinomialRing ℤ := by
  refine BinomialRing.mk ?_ ?_ ?_
  intro _ _ _ hn hmul
  exact nat_mul_inj' hmul hn
  use mcAux
  intro r k
  cases r with
  | ofNat n => {
    have h₁ : mcAux (Int.ofNat n) k = ((Nat.multichoose n k):ℤ) := rfl
    rw [h₁, nsmul_eq_mul, Int.ofNat_mul_out, ← Ring.multichoose_eq_nat_multichoose,
    ← Nat.nsmul_eq_mul, Ring.factorial_smul_multichoose_eq_ascPochhammer]
    simp only [Ring.ascPochhammer_smeval_eq_eval, ascPochhammer_eval_cast, Int.ofNat_eq_coe]
  }
  | negSucc n => {
    have h₂ : mcAux (Int.negSucc n) k = (-1)^k * Nat.choose n.succ k := rfl
    rw [h₂, nsmul_eq_mul, mul_comm, mul_assoc, ← Nat.cast_mul, mul_comm _ (k.factorial),
      ← Nat.descFactorial_eq_factorial_mul_choose, ← descPochhammer_int_eq_descFactorial,
      Ring.ascPochhammer_smeval_eq_eval, ← Int.neg_ofNat_succ,
      ascPochhammer_eval_neg_eq_descPochhammer]
  }

section choose

namespace Ring

variable [BinomialRing R]

theorem ascPochhammer_smeval_nat_int (r : R) :
    ∀(n : ℕ), Polynomial.smeval (ascPochhammer ℤ n) r = Polynomial.smeval (ascPochhammer ℕ n) r
  | 0 => by
    simp only [ascPochhammer_zero, Polynomial.smeval_one]
  | n + 1 => by
    simp only [ascPochhammer_succ_right, Polynomial.smeval_mul]
    rw [ascPochhammer_smeval_nat_int r n]
    simp only [Polynomial.smeval_add, Polynomial.smeval_X, ← Polynomial.C_eq_nat_cast,
      Polynomial.smeval_C]
    norm_cast

/-- The binomial coefficient `choose r n` generalizes the natural number choose function,
  interpreted in terms of choosing without replacement. -/
def choose {R: Type _} [BinomialRing R] (r : R) (n : ℕ): R :=
  multichoose (r-n+1) n

theorem descPochhammer_eq_factorial_mul_choose (r : R) (n : ℕ) :
    Polynomial.smeval (descPochhammer ℤ n) r = n.factorial • choose r n := by
  unfold choose
  rw [factorial_smul_multichoose_eq_ascPochhammer, descPochhammer_eq_ascPochhammer,
    Polynomial.smeval_comp r, add_comm_sub, Polynomial.smeval_add, Polynomial.smeval_X, pow_one]
  have h : Polynomial.smeval (1 - n : Polynomial ℤ) r = 1 - n := by
    rw [← Polynomial.C_eq_nat_cast, ← Polynomial.C_1, ← Polynomial.C_sub, Polynomial.smeval_C]
    simp only [pow_zero, zsmul_eq_mul, Int.cast_sub, Int.cast_one, Int.cast_ofNat, mul_one]
  rw [h, ascPochhammer_smeval_nat_int, add_comm_sub]

theorem choose_zero_right (r : R) : choose r 0 = 1 := by
  refine eq_of_smul_factorial_eq 0 ?_
  rw [← descPochhammer_eq_factorial_mul_choose, Nat.factorial_zero,
    descPochhammer_zero, Polynomial.smeval_one, pow_zero]

theorem choose_zero_succ (k : ℕ) : choose (0 : R) (Nat.succ k) = 0 := by
  refine eq_of_smul_factorial_eq (Nat.succ k) ?_
  rw [← descPochhammer_eq_factorial_mul_choose, smul_zero, descPochhammer_succ_left, mul_comm,
    Polynomial.smeval_mul_X (0 : R), mul_zero]

theorem choose_zero_pos (k : ℕ) (h_pos: 0 < k) : choose (0 : R) k = 0 := by
  rw [← Nat.succ_pred_eq_of_pos h_pos, choose_zero_succ]

theorem choose_zero_ite (k : ℕ) : choose (0 : R) k = if k = 0 then 1 else 0 := by
  rw [eq_ite_iff]
  by_cases hk: k = 0
  constructor
  rw [hk, choose_zero_right, ← Prod.mk.inj_iff]
  right
  constructor
  exact hk
  rw [← @Nat.le_zero, Nat.not_le] at hk
  rw [choose_zero_pos k hk]

end Ring

end choose
