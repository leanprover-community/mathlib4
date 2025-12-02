/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.Cast.Commute
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.Abel

/-! # Bernoulli's inequality

In this file we prove several versions of Bernoulli's inequality.
Besides the standard version `1 + n * a ≤ (1 + a) ^ n`,
we also prove `a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n`,
which can be regarded as Bernoulli's inequality for `b / a` multiplied by `a ^ n`.

Also, we prove versions for different typeclass assumptions on the (semi)ring.
-/

@[expose] public section

variable {R : Type*}

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {a b : R}

/-- Bernoulli's inequality for `b / a`, written after multiplication by the denominators. -/
lemma Commute.pow_add_mul_le_add_pow_of_sq_nonneg (Hcomm : Commute a b) (ha : 0 ≤ a)
    (Hsq : 0 ≤ b ^ 2) (Hsq' : 0 ≤ (a + b) ^ 2) (H : 0 ≤ 2 * a + b) :
    ∀ n : ℕ, a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n
  | 0 => by simp
  | 1 => by simp
  | 2 =>
    calc
      a ^ 2 + (2 : ℕ) * a ^ 1 * b ≤ a ^ 2 + (2 : ℕ) * a ^ 1 * b + b ^ 2 :=
        le_add_of_nonneg_right Hsq
      _ = (a + b) ^ 2 := by simp [sq, add_mul, mul_add, two_mul, Hcomm.eq, add_assoc]
  | n + 3 => by
    calc
      _ ≤ a ^ (n + 3) + ↑(n + 3) * a ^ (n + 2) * b +
            ((n + 1) * (b ^ 2 * (2 * a + b) * a ^ n) + a ^ (n + 1) * b ^ 2) :=
        le_add_of_nonneg_right <| by
          apply_rules [add_nonneg, mul_nonneg, Nat.cast_nonneg, pow_nonneg, zero_le_one]
      _ = (a + b) ^ 2 * (a ^ (n + 1) + ↑(n + 1) * a ^ n * b) := by
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ', add_mul, mul_add,
          two_mul, pow_zero, mul_one,
          Hcomm.eq, (n.cast_commute (_ : R)).symm.left_comm, mul_assoc, (Hcomm.pow_left _).eq,
          (Hcomm.pow_left _).left_comm, Hcomm.left_comm, ← @two_add_one_eq_three R, one_mul]
        abel
      _ ≤ (a + b) ^ 2 * (a + b) ^ (n + 1) := by
        gcongr
        · assumption
        · apply Commute.pow_add_mul_le_add_pow_of_sq_nonneg <;> assumption
      _ = (a + b) ^ (n + 3) := by simp [pow_succ', mul_assoc]

/-- **Bernoulli's inequality**. This version works for semirings but requires
additional hypotheses `0 ≤ a ^ 2` and `0 ≤ (1 + a) ^ 2`. -/
lemma one_add_mul_le_pow_of_sq_nonneg (Hsq : 0 ≤ a ^ 2) (Hsq' : 0 ≤ (1 + a) ^ 2) (H : 0 ≤ 2 + a)
    (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n := by
  simpa using (Commute.one_left a).pow_add_mul_le_add_pow_of_sq_nonneg zero_le_one Hsq Hsq'
    (by simpa using H) n

/-- **Bernoulli's inequality**. This version works for semirings but requires
additional hypotheses `0 ≤ a * a` and `0 ≤ (1 + a) * (1 + a)`. -/
@[deprecated one_add_mul_le_pow_of_sq_nonneg (since := "2025-11-11")]
lemma one_add_mul_le_pow' (Hsq : 0 ≤ a * a) (Hsq' : 0 ≤ (1 + a) * (1 + a)) (H : 0 ≤ 2 + a) (n : ℕ) :
    1 + n * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow_of_sq_nonneg (by rwa [sq]) (by rwa [sq]) H n

end OrderedSemiring

/-- Bernoulli's inequality for `b / a`, written after multiplication by the denominators.

This version works for partially ordered commutative semirings,
but explicitly assumes that `b ^ 2` and `(a + b) ^ 2` are nonnegative. -/
lemma pow_add_mul_le_add_pow_of_sq_nonneg [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {a b : R} (ha : 0 ≤ a) (Hsq : 0 ≤ b ^ 2) (Hsq' : 0 ≤ (a + b) ^ 2) (H : 0 ≤ 2 * a + b)
    (n : ℕ) : a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n :=
  (Commute.all a b).pow_add_mul_le_add_pow_of_sq_nonneg ha Hsq Hsq' H n

/-- Bernoulli's inequality for `b / a`, written after multiplication by the denominators.

This is a version for a linear ordered semiring. -/
lemma Commute.pow_add_mul_le_add_pow [Semiring R] [LinearOrder R] [IsOrderedRing R]
    [ExistsAddOfLE R] {a b : R} (Hcomm : Commute a b) (ha : 0 ≤ a) (H : 0 ≤ 2 * a + b)
    (n : ℕ) : a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n :=
  Hcomm.pow_add_mul_le_add_pow_of_sq_nonneg ha (sq_nonneg _) (sq_nonneg _) H n

/-- Bernoulli's inequality for `b / a`, written after multiplication by the denominators.

This is a version for a linear ordered semiring. -/
lemma pow_add_mul_le_add_pow [CommSemiring R] [LinearOrder R] [IsOrderedRing R] [ExistsAddOfLE R]
    {a b : R} (ha : 0 ≤ a) (H : 0 ≤ 2 * a + b) (n : ℕ) :
    a ^ n + n * a ^ (n - 1) * b ≤ (a + b) ^ n :=
  (Commute.all a b).pow_add_mul_le_add_pow ha H n

/-- Bernoulli's inequality for linear ordered semirings. -/
lemma one_add_le_pow_of_two_add_nonneg [Semiring R] [LinearOrder R] [IsOrderedRing R]
    [ExistsAddOfLE R] {a : R} (H : 0 ≤ 2 + a) (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow_of_sq_nonneg (sq_nonneg _) (sq_nonneg _) H _

section LinearOrderedRing
variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R} {n : ℕ}

/-- **Bernoulli's inequality** for `n : ℕ`, `-2 ≤ a`. -/
lemma one_add_mul_le_pow (H : -2 ≤ a) (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n :=
  one_add_le_pow_of_two_add_nonneg (neg_le_iff_add_nonneg'.mp H) n

/-- **Bernoulli's inequality** reformulated to estimate `a^n`. -/
lemma one_add_mul_sub_le_pow (H : -1 ≤ a) (n : ℕ) : 1 + n * (a - 1) ≤ a ^ n := by
  have : -2 ≤ a - 1 := by
    rwa [← one_add_one_eq_two, neg_add, ← sub_eq_add_neg, sub_le_sub_iff_right]
  simpa only [add_sub_cancel] using one_add_mul_le_pow this n

end LinearOrderedRing
