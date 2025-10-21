/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Polynomial.Smeval
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.NNRat.Order
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Binomial rings

In this file we introduce the binomial property as a mixin, and define the `multichoose`
and `choose` functions generalizing binomial coefficients.

According to our main reference [elliott2006binomial] (which lists many equivalent conditions), a
binomial ring is a torsion-free commutative ring `R` such that for any `x ∈ R` and any `k ∈ ℕ`, the
product `x(x-1)⋯(x-k+1)` is divisible by `k!`. The torsion-free condition lets us divide by `k!`
unambiguously, so we get uniquely defined binomial coefficients.

The defining condition doesn't require commutativity or associativity, and we get a theory with
essentially the same power by replacing subtraction with addition. Thus, we consider any additive
commutative monoid with a notion of natural number exponents in which multiplication by positive
integers is injective, and demand that the evaluation of the ascending Pochhammer polynomial
`X(X+1)⋯(X+(k-1))` at any element is divisible by `k!`. The quotient is called `multichoose r k`,
because for `r` a natural number, it is the number of multisets of cardinality `k` taken from a type
of cardinality `n`.

## Definitions

* `BinomialRing`: a mixin class specifying a suitable `multichoose` function.
* `Ring.multichoose`: the quotient of an ascending Pochhammer evaluation by a factorial.
* `Ring.choose`: the quotient of a descending Pochhammer evaluation by a factorial.

## Results

* Basic results with choose and multichoose, e.g., `choose_zero_right`
* Relations between choose and multichoose, negated input.
* Fundamental recursion: `choose_succ_succ`
* Chu-Vandermonde identity: `add_choose_eq`
* Pochhammer API

## References

* [J. Elliott, *Binomial rings, integer-valued polynomials, and λ-rings*][elliott2006binomial]

## TODO

Further results in Elliot's paper:
* A CommRing is binomial if and only if it admits a λ-ring structure with trivial Adams operations.
* The free commutative binomial ring on a set `X` is the ring of integer-valued polynomials in the
  variables `X`.  (also, noncommutative version?)
* Given a commutative binomial ring `A` and an `A`-algebra `B` that is complete with respect to an
  ideal `I`, formal exponentiation induces an `A`-module structure on the multiplicative subgroup
  `1 + I`.

-/

open Function Polynomial

/-- A binomial ring is a ring for which ascending Pochhammer evaluations are uniquely divisible by
suitable factorials. We define this notion as a mixin for additive commutative monoids with natural
number powers, but retain the ring name. We introduce `Ring.multichoose` as the uniquely defined
quotient. -/
class BinomialRing (R : Type*) [AddCommMonoid R] [Pow R ℕ] where
  -- This base class has been demoted to a field, to avoid creating
  -- an expensive global instance.
  [toIsAddTorsionFree : IsAddTorsionFree R]
  /-- A multichoose function, giving the quotient of Pochhammer evaluations by factorials. -/
  multichoose : R → ℕ → R
  /-- The `n`th ascending Pochhammer polynomial evaluated at any element is divisible by `n!` -/
  factorial_nsmul_multichoose (r : R) (n : ℕ) :
    n.factorial • multichoose r n = (ascPochhammer ℕ n).smeval r

-- This is only a local instance as it otherwise causes significant slow downs
-- to every call to `grind` involving a ring. Please do not make it a global instance.
-- (~1500 heartbeats measured on `nightly-testing-2025-09-09`.)
attribute [local instance] BinomialRing.toIsAddTorsionFree

section Multichoose

namespace Ring

variable {R : Type*} [AddCommMonoid R] [Pow R ℕ] [BinomialRing R]

/-- The multichoose function is the quotient of ascending Pochhammer evaluation by the corresponding
factorial. When applied to natural numbers, `multichoose k n` describes choosing a multiset of `n`
items from a type of size `k`, i.e., choosing with replacement. -/
def multichoose (r : R) (n : ℕ) : R := BinomialRing.multichoose r n

@[simp]
theorem multichoose_eq_multichoose (r : R) (n : ℕ) :
    BinomialRing.multichoose r n = multichoose r n := rfl

theorem factorial_nsmul_multichoose_eq_ascPochhammer (r : R) (n : ℕ) :
    n.factorial • multichoose r n = (ascPochhammer ℕ n).smeval r :=
  BinomialRing.factorial_nsmul_multichoose r n

@[simp]
theorem multichoose_zero_right' (r : R) : multichoose r 0 = r ^ 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 0),
    factorial_nsmul_multichoose_eq_ascPochhammer, ascPochhammer_zero, smeval_one, Nat.factorial]

theorem multichoose_zero_right [MulOneClass R] [NatPowAssoc R]
    (r : R) : multichoose r 0 = 1 := by
  rw [multichoose_zero_right', npow_zero]

@[simp]
theorem multichoose_one_right' (r : R) : multichoose r 1 = r ^ 1 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 1),
    factorial_nsmul_multichoose_eq_ascPochhammer, ascPochhammer_one, smeval_X, Nat.factorial_one,
    one_smul]

theorem multichoose_one_right [MulOneClass R] [NatPowAssoc R] (r : R) : multichoose r 1 = r := by
  rw [multichoose_one_right', npow_one]

variable {R : Type*} [NonAssocSemiring R] [Pow R ℕ] [NatPowAssoc R] [BinomialRing R]

@[simp]
theorem multichoose_zero_succ (k : ℕ) : multichoose (0 : R) (k + 1) = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1)),
    factorial_nsmul_multichoose_eq_ascPochhammer, smul_zero, ascPochhammer_succ_left,
    smeval_X_mul, zero_mul]

theorem ascPochhammer_succ_succ (r : R) (k : ℕ) :
    smeval (ascPochhammer ℕ (k + 1)) (r + 1) = Nat.factorial (k + 1) • multichoose (r + 1) k +
    smeval (ascPochhammer ℕ (k + 1)) r := by
  nth_rw 1 [ascPochhammer_succ_right, ascPochhammer_succ_left, mul_comm (ascPochhammer ℕ k)]
  simp only [smeval_mul, smeval_comp, smeval_add, smeval_X]
  rw [Nat.factorial, mul_smul, factorial_nsmul_multichoose_eq_ascPochhammer]
  simp only [smeval_one, npow_one, npow_zero, one_smul]
  rw [← C_eq_natCast, smeval_C, npow_zero, add_assoc, add_mul, add_comm 1, @nsmul_one, add_mul]
  rw [← @nsmul_eq_mul, @add_rotate', @succ_nsmul, add_assoc]
  simp_all only [Nat.cast_id, nsmul_eq_mul, one_mul]

theorem multichoose_succ_succ (r : R) (k : ℕ) :
    multichoose (r + 1) (k + 1) = multichoose r (k + 1) + multichoose (r + 1) k := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]
  simp only [factorial_nsmul_multichoose_eq_ascPochhammer, smul_add]
  rw [add_comm (smeval (ascPochhammer ℕ (k+1)) r), ascPochhammer_succ_succ r k]

@[simp]
theorem multichoose_one (k : ℕ) : multichoose (1 : R) k = 1 := by
  induction k with
  | zero => exact multichoose_zero_right 1
  | succ n ih =>
    rw [show (1 : R) = 0 + 1 by exact (@zero_add R _ 1).symm, multichoose_succ_succ,
      multichoose_zero_succ, zero_add, zero_add, ih]

theorem multichoose_two (k : ℕ) : multichoose (2 : R) k = k + 1 := by
  induction k with
  | zero =>
    rw [multichoose_zero_right, Nat.cast_zero, zero_add]
  | succ n ih =>
    rw [one_add_one_eq_two.symm, multichoose_succ_succ, multichoose_one, one_add_one_eq_two, ih,
      Nat.cast_succ, add_comm]

end Ring

end Multichoose

section Pochhammer

namespace Polynomial

@[simp]
theorem ascPochhammer_smeval_cast (R : Type*) [Semiring R] {S : Type*} [NonAssocSemiring S]
    [Pow S ℕ] [Module R S] [IsScalarTower R S S] [NatPowAssoc S]
    (x : S) (n : ℕ) : (ascPochhammer R n).smeval x = (ascPochhammer ℕ n).smeval x := by
  induction n with
  | zero => simp only [ascPochhammer_zero, smeval_one, one_smul]
  | succ n hn =>
    simp only [ascPochhammer_succ_right, mul_add, smeval_add, smeval_mul_X, ← Nat.cast_comm]
    simp only [← C_eq_natCast, smeval_C_mul, hn, Nat.cast_smul_eq_nsmul R n]
    simp only [nsmul_eq_mul, Nat.cast_id]

variable {R : Type*}

theorem ascPochhammer_smeval_eq_eval [Semiring R] (r : R) (n : ℕ) :
    (ascPochhammer ℕ n).smeval r = (ascPochhammer R n).eval r := by
  rw [eval_eq_smeval, ascPochhammer_smeval_cast R]

variable [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R]

theorem descPochhammer_smeval_eq_ascPochhammer (r : R) (n : ℕ) :
    (descPochhammer ℤ n).smeval r = (ascPochhammer ℕ n).smeval (r - n + 1) := by
  induction n with
  | zero => simp only [descPochhammer_zero, ascPochhammer_zero, smeval_one, npow_zero]
  | succ n ih =>
    rw [Nat.cast_succ, sub_add, add_sub_cancel_right, descPochhammer_succ_right, smeval_mul, ih,
      ascPochhammer_succ_left, X_mul, smeval_mul_X, smeval_comp, smeval_sub, ← C_eq_natCast,
      smeval_add, smeval_one, smeval_C]
    simp only [smeval_X, npow_one, npow_zero, zsmul_one, Int.cast_natCast, one_smul]

theorem descPochhammer_smeval_eq_descFactorial (n k : ℕ) :
    (descPochhammer ℤ k).smeval (n : R) = n.descFactorial k := by
  induction k with
  | zero =>
    rw [descPochhammer_zero, Nat.descFactorial_zero, Nat.cast_one, smeval_one, npow_zero, one_smul]
  | succ k ih =>
    rw [descPochhammer_succ_right, Nat.descFactorial_succ, smeval_mul, ih, mul_comm, Nat.cast_mul,
      smeval_sub, smeval_X, smeval_natCast, npow_one, npow_zero, nsmul_one]
    by_cases h : n < k
    · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero, zero_mul]
    · rw [Nat.cast_sub <| not_lt.mp h]

theorem ascPochhammer_smeval_neg_eq_descPochhammer (r : R) (k : ℕ) :
    (ascPochhammer ℕ k).smeval (-r) = Int.negOnePow k • (descPochhammer ℤ k).smeval r := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [ascPochhammer_succ_right, smeval_mul, ih, descPochhammer_succ_right, sub_eq_add_neg]
    have h : (X + (k : ℕ[X])).smeval (-r) = - (X + (-k : ℤ[X])).smeval r := by
      simp [smeval_natCast, add_comm]
    rw [h, ← neg_mul_comm, Int.natCast_add, Int.natCast_one, Int.negOnePow_succ, Units.neg_smul,
      Units.smul_def, Units.smul_def, ← smul_mul_assoc, neg_mul]

end Polynomial

end Pochhammer

section Basic_Instances

open Polynomial

instance Nat.instBinomialRing : BinomialRing ℕ where
  multichoose := Nat.multichoose
  factorial_nsmul_multichoose r n := by
    rw [smul_eq_mul, Nat.multichoose_eq r n, ← Nat.descFactorial_eq_factorial_mul_choose,
      ← eval_eq_smeval r (ascPochhammer ℕ n), ascPochhammer_nat_eq_descFactorial]

/-- The multichoose function for integers. -/
def Int.multichoose (n : ℤ) (k : ℕ) : ℤ :=
  match n with
  | ofNat n => (Nat.choose (n + k - 1) k : ℤ)
  | negSucc n => Int.negOnePow k * Nat.choose (n + 1) k

instance Int.instBinomialRing : BinomialRing ℤ where
  multichoose := Int.multichoose
  factorial_nsmul_multichoose r k := by
    rw [Int.multichoose.eq_def, nsmul_eq_mul]
    cases r with
    | ofNat n =>
      simp only [Int.ofNat_eq_coe, Int.ofNat_mul_out]
      rw [← Nat.descFactorial_eq_factorial_mul_choose, smeval_at_natCast, ← eval_eq_smeval n,
        ascPochhammer_nat_eq_descFactorial]
    | negSucc n =>
      simp only
      rw [mul_comm, mul_assoc, ← Nat.cast_mul, mul_comm _ (k.factorial),
        ← Nat.descFactorial_eq_factorial_mul_choose, ← descPochhammer_smeval_eq_descFactorial,
        ← Int.neg_ofNat_succ, ascPochhammer_smeval_neg_eq_descPochhammer]
      norm_cast

-- This instance will fire for any type `R`, so is local unless needed elsewhere.
local instance {R : Type*} [AddCommMonoid R] [Module ℚ≥0 R] : IsAddTorsionFree R where
  nsmul_right_injective {n} hn r s hrs := by
    rw [← one_smul ℚ≥0 r, ← one_smul ℚ≥0 s, show 1 = (n : ℚ≥0)⁻¹ • (n : ℚ≥0) by simp_all]
    simp_all only [smul_assoc, Nat.cast_smul_eq_nsmul]

noncomputable instance {R : Type*} [AddCommMonoid R] [Module ℚ≥0 R] [Pow R ℕ] : BinomialRing R where
  multichoose r n := (n.factorial : ℚ≥0)⁻¹ • Polynomial.smeval (ascPochhammer ℕ n) r
  factorial_nsmul_multichoose r n := by
    match_scalars
    field_simp

end Basic_Instances

section Neg

namespace Ring

open Polynomial

variable {R : Type*} [NonAssocRing R] [Pow R ℕ] [BinomialRing R]

@[simp]
theorem smeval_ascPochhammer_self_neg : ∀ n : ℕ,
    smeval (ascPochhammer ℕ n) (-n : ℤ) = (-1)^n * n.factorial
  | 0 => by
    rw [Nat.cast_zero, neg_zero, ascPochhammer_zero, Nat.factorial_zero, smeval_one, pow_zero,
      one_smul, pow_zero, Nat.cast_one, one_mul]
  | n + 1 => by
    rw [ascPochhammer_succ_left, smeval_X_mul, smeval_comp, smeval_add, smeval_X, smeval_one,
      pow_zero, pow_one, one_smul, Nat.cast_add, Nat.cast_one, neg_add_rev, neg_add_cancel_comm,
      smeval_ascPochhammer_self_neg n, ← mul_assoc, mul_comm _ ((-1) ^ n),
      show (-1 + -↑n = (-1 : ℤ) * (n + 1)) by cutsat, ← mul_assoc, pow_add, pow_one,
      Nat.factorial, Nat.cast_mul, ← mul_assoc, Nat.cast_succ]

@[simp]
theorem smeval_ascPochhammer_succ_neg (n : ℕ) :
    smeval (ascPochhammer ℕ (n + 1)) (-n : ℤ) = 0 := by
  rw [ascPochhammer_succ_right, smeval_mul, smeval_add, smeval_X, ← C_eq_natCast, smeval_C,
    pow_zero, pow_one, Nat.cast_id, nsmul_eq_mul, mul_one, neg_add_cancel, mul_zero]

theorem smeval_ascPochhammer_neg_add (n : ℕ) : ∀ k : ℕ,
    smeval (ascPochhammer ℕ (n + k + 1)) (-n : ℤ) = 0
  | 0 => by
    rw [add_zero, smeval_ascPochhammer_succ_neg]
  | k + 1 => by
    rw [ascPochhammer_succ_right, smeval_mul, ← add_assoc, smeval_ascPochhammer_neg_add n k,
      zero_mul]

@[simp]
theorem smeval_ascPochhammer_neg_of_lt {n k : ℕ} (h : n < k) :
    smeval (ascPochhammer ℕ k) (-n : ℤ) = 0 := by
  rw [show k = n + (k - n - 1) + 1 by cutsat, smeval_ascPochhammer_neg_add]

theorem smeval_ascPochhammer_nat_cast {R} [NonAssocSemiring R] [Pow R ℕ] [NatPowAssoc R] (n k : ℕ) :
    smeval (ascPochhammer ℕ k) (n : R) = smeval (ascPochhammer ℕ k) n := by
  rw [smeval_at_natCast (ascPochhammer ℕ k) n]

theorem multichoose_neg_self (n : ℕ) : multichoose (-n : ℤ) n = (-1)^n := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero _),
    factorial_nsmul_multichoose_eq_ascPochhammer, smeval_ascPochhammer_self_neg, nsmul_eq_mul,
    Nat.cast_comm]

@[simp]
theorem multichoose_neg_succ (n : ℕ) : multichoose (-n : ℤ) (n + 1) = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero _),
    factorial_nsmul_multichoose_eq_ascPochhammer, smeval_ascPochhammer_succ_neg, smul_zero]

theorem multichoose_neg_add (n k : ℕ) : multichoose (-n : ℤ) (n + k + 1) = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (n + k + 1)),
    factorial_nsmul_multichoose_eq_ascPochhammer, smeval_ascPochhammer_neg_add, smul_zero]

@[simp]
theorem multichoose_neg_of_lt (n k : ℕ) (h : n < k) : multichoose (-n : ℤ) k = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k),
    factorial_nsmul_multichoose_eq_ascPochhammer, smeval_ascPochhammer_neg_of_lt h, smul_zero]

theorem multichoose_succ_neg_natCast [NatPowAssoc R] (n : ℕ) :
    multichoose (-n : R) (n + 1) = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (n + 1)), smul_zero,
    factorial_nsmul_multichoose_eq_ascPochhammer, smeval_neg_nat,
    smeval_ascPochhammer_succ_neg n, Int.cast_zero]

theorem smeval_ascPochhammer_int_ofNat {R} [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R] (r : R) :
    ∀ n : ℕ, smeval (ascPochhammer ℤ n) r = smeval (ascPochhammer ℕ n) r
  | 0 => by
    simp only [ascPochhammer_zero, smeval_one]
  | n + 1 => by
    simp only [ascPochhammer_succ_right, smeval_mul]
    rw [smeval_ascPochhammer_int_ofNat r n]
    simp only [smeval_add, smeval_X, ← C_eq_natCast, smeval_C, natCast_zsmul, nsmul_eq_mul,
      Nat.cast_id]

end Ring

end Neg

section Choose

namespace Ring

open Polynomial

variable {R : Type*}

section

/-- The binomial coefficient `choose r n` generalizes the natural number `Nat.choose` function,
  interpreted in terms of choosing without replacement. -/
def choose [AddCommGroupWithOne R] [Pow R ℕ] [BinomialRing R] (r : R) (n : ℕ) : R :=
  multichoose (r - n + 1) n

variable [NonAssocRing R] [Pow R ℕ] [BinomialRing R]

theorem descPochhammer_eq_factorial_smul_choose [NatPowAssoc R] (r : R) (n : ℕ) :
    (descPochhammer ℤ n).smeval r = n.factorial • choose r n := by
  rw [choose, factorial_nsmul_multichoose_eq_ascPochhammer, descPochhammer_eq_ascPochhammer,
    smeval_comp, add_comm_sub, smeval_add, smeval_X, npow_one]
  have h : smeval (1 - n : Polynomial ℤ) r = 1 - n := by
    rw [← C_eq_natCast, ← C_1, ← C_sub, smeval_C]
    simp only [npow_zero, zsmul_one, Int.cast_sub, Int.cast_one, Int.cast_natCast]
  rw [h, ascPochhammer_smeval_cast, add_comm_sub]

theorem choose_natCast [NatPowAssoc R] (n k : ℕ) : choose (n : R) k = Nat.choose n k := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k),
    ← descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul, ← Nat.cast_mul,
    ← Nat.descFactorial_eq_factorial_mul_choose, ← descPochhammer_smeval_eq_descFactorial]

@[simp]
theorem choose_zero_right' (r : R) : choose r 0 = (r + 1) ^ 0 := by
  dsimp only [choose]
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 0)]
  simp

theorem choose_zero_right [NatPowAssoc R] (r : R) : choose r 0 = 1 := by
  rw [choose_zero_right', npow_zero]

@[simp]
theorem choose_zero_succ (R) [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R] [BinomialRing R]
    (n : ℕ) : choose (0 : R) (n + 1) = 0 := by
  rw [choose, Nat.cast_succ, zero_sub, neg_add, neg_add_cancel_right, multichoose_succ_neg_natCast]

theorem choose_zero_pos (R) [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R] [BinomialRing R]
    {k : ℕ} (h_pos : 0 < k) : choose (0 : R) k = 0 := by
  rw [← Nat.succ_pred_eq_of_pos h_pos, choose_zero_succ]

theorem choose_zero_ite (R) [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R] [BinomialRing R]
    (k : ℕ) : choose (0 : R) k = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · rw [hk, choose_zero_right]
  · rw [choose_zero_pos R <| Nat.pos_of_ne_zero hk]

@[simp]
theorem choose_one_right' (r : R) : choose r 1 = r ^ 1 := by
  rw [choose, Nat.cast_one, sub_add_cancel, multichoose_one_right']

theorem choose_one_right [NatPowAssoc R] (r : R) : choose r 1 = r := by
  rw [choose_one_right', npow_one]

theorem choose_neg [NatPowAssoc R] (r : R) (n : ℕ) :
    choose (-r) n = Int.negOnePow n • choose (r + n - 1) n := by
  apply (nsmul_right_inj (Nat.factorial_ne_zero n)).mp
  rw [← descPochhammer_eq_factorial_smul_choose, smul_comm,
    ← descPochhammer_eq_factorial_smul_choose, descPochhammer_smeval_eq_ascPochhammer,
    show (-r - n + 1) = -(r + n - 1) by abel, ascPochhammer_smeval_neg_eq_descPochhammer]

theorem descPochhammer_succ_succ_smeval {R} [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R]
    (r : R) (k : ℕ) : smeval (descPochhammer ℤ (k + 1)) (r + 1) =
    (k + 1) • smeval (descPochhammer ℤ k) r + smeval (descPochhammer ℤ (k + 1)) r := by
  nth_rw 1 [descPochhammer_succ_left]
  rw [descPochhammer_succ_right, mul_comm (descPochhammer ℤ k)]
  simp only [smeval_comp, smeval_sub, smeval_mul, smeval_X, smeval_one, npow_one,
    npow_zero, one_smul, add_sub_cancel_right, sub_mul, add_mul, add_smul, one_mul]
  rw [← C_eq_natCast, smeval_C, npow_zero, add_comm (k • smeval (descPochhammer ℤ k) r) _,
    add_assoc, add_comm (k • smeval (descPochhammer ℤ k) r) _, ← add_assoc, ← add_sub_assoc,
    nsmul_eq_mul, zsmul_one, Int.cast_natCast, sub_add_cancel, add_comm]

theorem choose_succ_succ [NatPowAssoc R] (r : R) (k : ℕ) :
    choose (r + 1) (k + 1) = choose r k + choose r (k + 1) := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]
  simp only [smul_add, ← descPochhammer_eq_factorial_smul_choose]
  rw [Nat.factorial_succ, mul_smul,
    ← descPochhammer_eq_factorial_smul_choose r, descPochhammer_succ_succ_smeval r k]

@[deprecated (since := "2025-08-17")] alias choose_eq_nat_choose := choose_natCast

theorem choose_smul_choose [NatPowAssoc R] (r : R) {n k : ℕ} (hkn : k ≤ n) :
    (Nat.choose n k) • choose r n = choose r k * choose (r - k) (n - k) := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero n),
    nsmul_left_comm, ← descPochhammer_eq_factorial_smul_choose,
    ← Nat.choose_mul_factorial_mul_factorial hkn, ← smul_mul_smul_comm,
    ← descPochhammer_eq_factorial_smul_choose, mul_nsmul',
    ← descPochhammer_eq_factorial_smul_choose, smul_mul_assoc]
  nth_rw 2 [← Nat.sub_add_cancel hkn]
  rw [add_comm, ← descPochhammer_mul, smeval_mul, smeval_comp, smeval_sub, smeval_X,
    ← C_eq_natCast, smeval_C, npow_one, npow_zero, zsmul_one, Int.cast_natCast, nsmul_eq_mul]

theorem choose_add_smul_choose [NatPowAssoc R] (r : R) (n k : ℕ) :
    (Nat.choose (n + k) k) • choose (r + k) (n + k) = choose (r + k) k * choose r n := by
  rw [choose_smul_choose (r + k) (Nat.le_add_left k n), Nat.add_sub_cancel,
    add_sub_cancel_right]

end

theorem choose_eq_smul [Field R] [CharZero R] {a : R} {n : ℕ} :
    Ring.choose a n = (n.factorial : R)⁻¹ • (descPochhammer ℤ n).smeval a := by
  rw [Ring.descPochhammer_eq_factorial_smul_choose, ← Nat.cast_smul_eq_nsmul R, inv_smul_smul₀]
  simpa using Nat.factorial_ne_zero n

open Finset

/-- Pochhammer version of Chu-Vandermonde identity -/
theorem descPochhammer_smeval_add [Ring R] {r s : R} (k : ℕ) (h : Commute r s) :
    (descPochhammer ℤ k).smeval (r + s) = ∑ ij ∈ antidiagonal k,
    Nat.choose k ij.1 * ((descPochhammer ℤ ij.1).smeval r * (descPochhammer ℤ ij.2).smeval s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right, mul_comm, smeval_mul, sum_antidiagonal_choose_succ_mul
      fun i j => ((descPochhammer ℤ i).smeval r * (descPochhammer ℤ j).smeval s),
      ← sum_add_distrib, smeval_sub, smeval_X, smeval_natCast, pow_zero, pow_one, ih, mul_sum]
    refine sum_congr rfl ?_
    intro ij hij -- try to move `descPochhammer`s to right, gather multipliers.
    have hdx : (descPochhammer ℤ ij.1).smeval r * (X - (ij.2 : ℤ[X])).smeval s =
        (X - (ij.2 : ℤ[X])).smeval s * (descPochhammer ℤ ij.1).smeval r := by
      refine (commute_iff_eq ((descPochhammer ℤ ij.1).smeval r)
        ((X - (ij.2 : ℤ[X])).smeval s)).mp ?_
      exact smeval_commute ℤ (descPochhammer ℤ ij.1) (X - (ij.2 : ℤ[X])) h
    rw [descPochhammer_succ_right, mul_comm, smeval_mul, descPochhammer_succ_right, mul_comm,
      smeval_mul, ← mul_assoc ((descPochhammer ℤ ij.1).smeval r), hdx]
    simp only [mul_assoc _ ((descPochhammer ℤ ij.1).smeval r) _,
      ← mul_assoc _ _ (((descPochhammer ℤ ij.1).smeval r) * _)]
    have hl : (r + s - k • 1) * (k.choose ij.1) = (k.choose ij.1) * (X - (ij.2 : ℤ[X])).smeval s +
        ↑(k.choose ij.2) * (X - (ij.1 : ℤ[X])).smeval r := by
      simp only [smeval_sub, smeval_X, pow_one, smeval_natCast, pow_zero]
      rw [← Nat.choose_symm_of_eq_add (List.Nat.mem_antidiagonal.mp hij).symm,
        (List.Nat.mem_antidiagonal.mp hij).symm, ← mul_add, Nat.cast_comm, add_smul]
      abel_nf
    rw [hl, ← add_mul]

/-- The Chu-Vandermonde identity for binomial rings -/
theorem add_choose_eq [Ring R] [BinomialRing R] {r s : R} (k : ℕ) (h : Commute r s) :
    choose (r + s) k =
      ∑ ij ∈ antidiagonal k, choose r ij.1 * choose s ij.2 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k),
    ← descPochhammer_eq_factorial_smul_choose, smul_sum, descPochhammer_smeval_add _ h]
  refine sum_congr rfl ?_
  intro x hx
  rw [← Nat.choose_mul_factorial_mul_factorial (antidiagonal.fst_le hx),
    tsub_eq_of_eq_add_rev (List.Nat.mem_antidiagonal.mp hx).symm, mul_assoc, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_mul, ← mul_assoc _ (x.1.factorial : R), mul_assoc _ (x.2.factorial : R),
    ← mul_assoc (x.2.factorial : R), Nat.cast_commute x.2.factorial,
    mul_assoc _ (x.2.factorial : R), ← nsmul_eq_mul x.2.factorial]
  simp [mul_assoc, descPochhammer_eq_factorial_smul_choose]

end Ring

end Choose
