/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Nat.Cast.Order.Ring

/-! # Bernoulli's inequality -/

variable {R : Type*}

section OrderedSemiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {a : R}

/-- **Bernoulli's inequality**. This version works for semirings but requires
additional hypotheses `0 ≤ a * a` and `0 ≤ (1 + a) * (1 + a)`. -/
lemma one_add_mul_le_pow' (Hsq : 0 ≤ a * a) (Hsq' : 0 ≤ (1 + a) * (1 + a)) (H : 0 ≤ 2 + a) :
    ∀ n : ℕ, 1 + n * a ≤ (1 + a) ^ n
  | 0 => by simp
  | 1 => by simp
  | n + 2 =>
    have : 0 ≤ n * (a * a * (2 + a)) + a * a :=
      add_nonneg (mul_nonneg n.cast_nonneg (mul_nonneg Hsq H)) Hsq
    calc
      _ ≤ 1 + ↑(n + 2) * a + (n * (a * a * (2 + a)) + a * a) := le_add_of_nonneg_right this
      _ = (1 + a) * (1 + a) * (1 + n * a) := by
          simp only [Nat.cast_add, add_mul, mul_add, one_mul, mul_one, ← one_add_one_eq_two,
            Nat.cast_one, add_assoc, add_right_inj]
          simp only [← add_assoc, add_comm _ (↑n * a)]
          simp only [add_assoc, (n.cast_commute (_ : R)).left_comm]
          simp only [add_comm, add_left_comm]
      _ ≤ (1 + a) * (1 + a) * (1 + a) ^ n :=
        mul_le_mul_of_nonneg_left (one_add_mul_le_pow' Hsq Hsq' H _) Hsq'
      _ = (1 + a) ^ (n + 2) := by simp only [pow_succ', mul_assoc]

end OrderedSemiring

section LinearOrderedRing
variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R} {n : ℕ}

/-- **Bernoulli's inequality** for `n : ℕ`, `-2 ≤ a`. -/
lemma one_add_mul_le_pow (H : -2 ≤ a) (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n :=
  one_add_mul_le_pow' (mul_self_nonneg _) (mul_self_nonneg _) (neg_le_iff_add_nonneg'.1 H) _

/-- **Bernoulli's inequality** reformulated to estimate `a^n`. -/
lemma one_add_mul_sub_le_pow (H : -1 ≤ a) (n : ℕ) : 1 + n * (a - 1) ≤ a ^ n := by
  have : -2 ≤ a - 1 := by
    rwa [← one_add_one_eq_two, neg_add, ← sub_eq_add_neg, sub_le_sub_iff_right]
  simpa only [add_sub_cancel] using one_add_mul_le_pow this n

end LinearOrderedRing
