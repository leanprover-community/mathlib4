/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Polynomial.Smeval

/-!
# Binomial rings

In this file we introduce the binomial property as a Prop-valued mixin, and define the `multichoose`
and `choose` functions generalizing binomial coefficients.

According to our main reference [elliott2006binomial] (which lists many equivalent conditions), a
binomial ring is a torsion-free commutative ring `R` such that for any `x ∈ R` and any `k ∈ ℕ`, the
product `x(x-1)⋯(x-k+1)` is divisible by `k!`.  The torsion-free condition lets us divide by `k!`
unambiguously, so we get uniquely defined binomial coefficients.

The defining condition doesn't require commutativity or associativity, and we get a theory with
essentially the same power by replacing subtraction with addition.  Thus, we consider any
non-associative semiring `R` with notion of natural nunber exponents, in which multiplication by
factorials is injective, and demand that the evaluation of the ascending Pochhammer polynomial
`X(X+1)⋯(X+(k-1))` at any element is divisible by `k!`.  The quotient is called `multichoose r k`,
following the convention given for natural numbers.

## References
* [J. Elliott, *Binomial rings, integer-valued polynomials, and λ-rings*][elliott2006binomial]

-/

universe u

section Mixin_test

/-- A `Prop`-valued mixin for multi-binomial coefficients. -/
class Binomial (R : Type*) [NonAssocSemiring R] [Pow R ℕ]: Prop where
  /-- Scalar multiplication by positive integers is injective. -/
  inj_smul_pos (n : ℕ) (r s : R) (h: n ≠ 0) : n • r = n • s → r = s
  /-- The `n`th ascending Pochhammer polynomial evaluated at any element is divisible by `n!`. -/
  factorial_smul_multichoose : ∀ (r : R) (n : ℕ), ∃ (s : R),
    n.factorial • s = Polynomial.smeval r (ascPochhammer ℕ n)

namespace Ring

open Polynomial

variable {R : Type u}

theorem inj_smul_pos [NonAssocSemiring R] [Pow R ℕ] [Binomial R] (n : ℕ) (r s : R) (h: n ≠ 0) :
    n • r = n • s → r = s := Binomial.inj_smul_pos n r s h

theorem eq_of_smul_factorial_eq [NonAssocSemiring R] [Pow R ℕ] [Binomial R] {r s : R} (n : ℕ)
    (h : n.factorial • r = n.factorial • s) : r = s :=
  inj_smul_pos n.factorial r s (Nat.factorial_ne_zero n) h

/-- This is a generalization of the combinatorial multichoose function, given by choosing with
replacement. -/
noncomputable def multichoose [NonAssocSemiring R] [Pow R ℕ] [Binomial R] (r : R) (n : ℕ) : R :=
  Exists.choose (Binomial.factorial_smul_multichoose r n)

theorem factorial_smul_multichoose_eq_ascPochhammer [NonAssocSemiring R] [Pow R ℕ] [Binomial R]
    (r : R) (n : ℕ) : n.factorial • multichoose r n = smeval r (ascPochhammer ℕ n) :=
  Exists.choose_spec (Binomial.factorial_smul_multichoose r n)

theorem multichoose_zero_right' [NonAssocSemiring R] [Pow R ℕ] [Binomial R] (r : R) :
    multichoose r 0 = r ^ 0 := by
  refine eq_of_smul_factorial_eq 0 ?_
  rw [factorial_smul_multichoose_eq_ascPochhammer, ascPochhammer_zero, smeval_one, Nat.factorial]

theorem multichoose_zero_right [NonAssocSemiring R] [Pow R ℕ] [Binomial R] [NatPowAssoc R]
    (r : R) : multichoose r 0 = 1 := by
  rw [multichoose_zero_right', npow_zero]

instance naturals_binomial : Binomial ℕ := by
  refine Binomial.mk ?inj_smul_pos ?factorial_mul_multichoose
  intro n r s npos h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero npos) h
  intro n k
  use Nat.multichoose n k
  rw [Nat.multichoose_eq, smul_eq_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
    smeval_eq_eval (ascPochhammer ℕ k) n, ascPochhammer_nat_eq_descFactorial]

theorem ascPochhammer_smeval_eq_eval [Semiring R] (r : R) (k : ℕ) :
    smeval r (ascPochhammer ℕ k) = eval r (ascPochhammer R k) := by
  induction k with
  | zero =>
    rw [ascPochhammer_zero, ascPochhammer_zero, eval_one, smeval_one, nsmul_eq_mul, pow_zero,
      mul_one, Nat.cast_one]
  | succ n ih =>
    rw [ascPochhammer_succ_right, ascPochhammer_succ_right, smeval_mul ℕ r, ih,
      mul_add (ascPochhammer R n), smeval_add, smeval_X r, pow_one, ← C_eq_nat_cast, smeval_C,
      pow_zero, nsmul_one, Nat.cast_id, eval_add, eval_mul_X, ← Nat.cast_comm, eval_nat_cast_mul,
      mul_add, Nat.cast_comm]

theorem multichoose_eq_nat_multichoose (n k : ℕ) : multichoose n k = Nat.multichoose n k := by
  refine eq_of_smul_factorial_eq k ?_
  rw [factorial_smul_multichoose_eq_ascPochhammer, Nat.multichoose_eq, ascPochhammer_smeval_eq_eval,
    ascPochhammer_nat_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose, smul_eq_mul]

instance integers_binomial_ring : Binomial ℤ := by
  refine Binomial.mk ?_ ?_
  intro _ _ _ hn hmul
  exact nat_mul_inj' hmul hn
  intro r k
  cases r with
  | ofNat n =>
    use ((Nat.multichoose n k):ℤ)
    rw [nsmul_eq_mul, Int.ofNat_mul_out, ← multichoose_eq_nat_multichoose, ← Nat.nsmul_eq_mul,
      factorial_smul_multichoose_eq_ascPochhammer]
    simp only [ascPochhammer_smeval_eq_eval, ascPochhammer_eval_cast, Int.ofNat_eq_coe]
  | negSucc n =>
    use (-1)^k * Nat.choose n.succ k
    rw [nsmul_eq_mul, mul_comm, mul_assoc, ← Nat.cast_mul, mul_comm _ (k.factorial),
      ← Nat.descFactorial_eq_factorial_mul_choose, ← descPochhammer_int_eq_descFactorial,
      ascPochhammer_smeval_eq_eval, ← Int.neg_ofNat_succ, ascPochhammer_eval_neg_eq_descPochhammer]

end Ring

end Mixin_test

section choose

namespace Ring

open Polynomial

variable {R : Type u}

variable [NonAssocRing R] [Pow R ℕ] [Binomial R]

theorem ascPochhammer_smeval_neg : ∀(n : ℕ),
    smeval (-n : ℤ) (ascPochhammer ℕ n) = (-1)^n * n.factorial
  | 0 => by
    rw [Nat.cast_zero, neg_zero, ascPochhammer_zero, Nat.factorial_zero, smeval_one, pow_zero,
      one_smul, pow_zero, Nat.cast_one, one_mul]
  | n + 1 => by
    rw [ascPochhammer_succ_left, smeval_X_mul, smeval_comp, smeval_add, smeval_X, smeval_one,
      pow_zero, pow_one, one_smul, Nat.cast_add, Nat.cast_one, neg_add_rev, neg_add_cancel_comm,
      ascPochhammer_smeval_neg n, ← mul_assoc, mul_comm _ ((-1) ^ n),
      show (-1 + -↑n = (-1 : ℤ) * (n + 1)) by linarith, ← mul_assoc, pow_add, pow_one,
      Nat.factorial, Nat.cast_mul, ← mul_assoc, Nat.cast_succ]

theorem ascPochhammer_succ_smeval_neg (n : ℕ) :
    smeval (-n : ℤ) (ascPochhammer ℕ (n + 1)) = 0 := by
  rw [ascPochhammer_succ_right, smeval_mul, smeval_add, smeval_X, ← C_eq_nat_cast, smeval_C,
    pow_zero, pow_one, Nat.cast_id, nsmul_eq_mul, mul_one, add_left_neg, mul_zero]

theorem ascPochhammer_smeval_neg_add (n : ℕ) : ∀(k : ℕ),
    smeval (-n : ℤ) (ascPochhammer ℕ (n + k + 1)) = 0
  | 0 => by
    rw [add_zero, ascPochhammer_succ_smeval_neg]
  | k + 1 => by
    rw [ascPochhammer_succ_right, smeval_mul, ← add_assoc, ascPochhammer_smeval_neg_add n k,
      zero_mul]

theorem ascPochhammer_smeval_neg_lt (n k : ℕ) (h : n < k) :
    smeval (-n : ℤ) (ascPochhammer ℕ k) = 0 := by
  have hk : k = n + (k - n - 1) + 1 := by
    rw [add_rotate, Nat.sub_sub, Nat.add_right_comm, Nat.add_assoc, Nat.sub_add_cancel h]
  rw [hk, ascPochhammer_smeval_neg_add]

theorem ascPochhammer_smeval_nat_cast [NatPowAssoc R] (n k : ℕ) :
    smeval (n : R) (ascPochhammer ℕ k) = smeval n (ascPochhammer ℕ k) := by
  rw [smeval_at_nat_cast (ascPochhammer ℕ k) n]

theorem multichoose_neg (n : ℕ) : multichoose (-n : ℤ) n = (-1)^n := by
    refine eq_of_smul_factorial_eq n ?_
    rw [factorial_smul_multichoose_eq_ascPochhammer, ascPochhammer_smeval_neg, nsmul_eq_mul,
      Nat.cast_comm]

theorem multichoose_succ_smeval_neg (n : ℕ) : multichoose (-n : ℤ) (n + 1) = 0 := by
  refine eq_of_smul_factorial_eq (n + 1) ?_
  rw [factorial_smul_multichoose_eq_ascPochhammer, ascPochhammer_succ_smeval_neg, smul_zero]

theorem multichoose_smeval_neg_add (n k : ℕ) : multichoose (-n : ℤ) (n + k + 1) = 0 := by
  refine eq_of_smul_factorial_eq (n + k + 1) ?_
  rw [factorial_smul_multichoose_eq_ascPochhammer, ascPochhammer_smeval_neg_add, smul_zero]

theorem multichoose_smeval_neg_lt (n k : ℕ) (h : n < k) : multichoose (-n : ℤ) k = 0 := by
  refine eq_of_smul_factorial_eq k ?_
  rw [factorial_smul_multichoose_eq_ascPochhammer, ascPochhammer_smeval_neg_lt n k h, smul_zero]

theorem multichoose_succ_smeval_neg_cast [NatPowAssoc R] (n : ℕ) :
    multichoose (-n : R) (n + 1) = 0 := by
  refine eq_of_smul_factorial_eq (n + 1) ?_
  rw [factorial_smul_multichoose_eq_ascPochhammer, smul_zero, smeval_at_neg_nat,
    ascPochhammer_succ_smeval_neg, Int.cast_zero]

theorem ascPochhammer_smeval_nat_int [NatPowAssoc R] (r : R) : ∀(n : ℕ),
    smeval r (ascPochhammer ℤ n) = smeval r (ascPochhammer ℕ n)
  | 0 => by
    simp only [ascPochhammer_zero, smeval_one]
  | n + 1 => by
    simp only [ascPochhammer_succ_right, smeval_mul]
    rw [ascPochhammer_smeval_nat_int r n]
    simp only [smeval_add, smeval_X, ← C_eq_nat_cast, smeval_C, coe_nat_zsmul, nsmul_eq_mul,
    Nat.cast_id]

/-- The binomial coefficient `choose r n` generalizes the natural number choose function,
  interpreted in terms of choosing without replacement. -/
noncomputable def choose {R: Type _} [NonAssocRing R] [Pow R ℕ] [Binomial R]
    (r : R) (n : ℕ): R :=
  multichoose (r-n+1) n

theorem descPochhammer_eq_factorial_smul_choose [NatPowAssoc R] (r : R) (n : ℕ) :
    smeval r (descPochhammer ℤ n) = n.factorial • choose r n := by
  unfold choose
  rw [factorial_smul_multichoose_eq_ascPochhammer, descPochhammer_eq_ascPochhammer, smeval_comp ℤ r,
    add_comm_sub, smeval_add, smeval_X, npow_one]
  have h : smeval r (1 - n : Polynomial ℤ) = 1 - n := by
    rw [← C_eq_nat_cast, ← C_1, ← C_sub, smeval_C]
    simp only [npow_zero, zsmul_eq_mul, Int.cast_sub, Int.cast_one, Int.cast_ofNat, zsmul_one]
  rw [h, ascPochhammer_smeval_nat_int, add_comm_sub]

theorem choose_zero_right' (r : R) : choose r 0 = (r + 1) ^ 0 := by
  unfold choose
  refine eq_of_smul_factorial_eq 0 ?_
  rw [factorial_smul_multichoose_eq_ascPochhammer, Nat.factorial_zero, ascPochhammer_zero,
    smeval_one, one_smul, one_smul, Nat.cast_zero, sub_zero]

theorem choose_zero_right [NatPowAssoc R] (r : R) : choose r 0 = 1 := by
  rw [choose_zero_right', npow_zero]

theorem choose_zero_succ (S : Type u) [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S] [Binomial S]
    (n : ℕ) : choose (0 : S) (Nat.succ n) = 0 := by
  unfold choose
  rw [Nat.cast_succ, zero_sub, neg_add, neg_add_cancel_right, ← Nat.add_one,
    multichoose_succ_smeval_neg_cast]

theorem choose_zero_pos (S : Type u) [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S] [Binomial S] (k : ℕ)
    (h_pos: 0 < k) : choose (0 : S) k = 0 := by
  rw [← Nat.succ_pred_eq_of_pos h_pos, choose_zero_succ]

theorem choose_zero_ite (S : Type u) [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S] [Binomial S]
    (k : ℕ) : choose (0 : S) k = if k = 0 then 1 else 0 := by
  rw [eq_ite_iff]
  by_cases hk: k = 0
  constructor
  rw [hk, choose_zero_right, ← Prod.mk.inj_iff]
  right
  constructor
  exact hk
  rw [← @Nat.le_zero, Nat.not_le] at hk
  rw [choose_zero_pos S k hk]

theorem descPochhammer_succ_succ_smeval {S : Type u} [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S]
    (r : S) (k : ℕ) : smeval (r + 1) (descPochhammer ℤ (Nat.succ k)) =
    (k + 1) • smeval r (descPochhammer ℤ k) + smeval r (descPochhammer ℤ (Nat.succ k)) := by
  nth_rw 1 [descPochhammer_succ_left]
  rw [descPochhammer_succ_right, mul_comm (descPochhammer ℤ k)]
  simp only [smeval_comp ℤ (r + 1), smeval_sub, smeval_add, smeval_mul, smeval_X, smeval_one,
    npow_one, npow_zero, one_smul, add_sub_cancel, sub_mul, add_mul, add_smul, one_mul]
  rw [← C_eq_nat_cast, smeval_C, npow_zero, add_comm (k • smeval r (descPochhammer ℤ k)) _,
    add_assoc, add_comm (k • smeval r (descPochhammer ℤ k)) _, ← add_assoc,  ← add_sub_assoc,
    nsmul_eq_mul, zsmul_one, Int.cast_ofNat, sub_add_cancel, add_comm]

theorem choose_succ_succ [NatPowAssoc R] (r:R) (k : ℕ) :
    choose (r+1) (Nat.succ k) = choose r k + choose r (Nat.succ k) := by
  refine eq_of_smul_factorial_eq (Nat.succ k) ?_
  simp only [smul_add, ← descPochhammer_eq_factorial_smul_choose]
  rw [Nat.factorial_succ, mul_smul,
    ← descPochhammer_eq_factorial_smul_choose r, descPochhammer_succ_succ_smeval r k]

end Ring

end choose
