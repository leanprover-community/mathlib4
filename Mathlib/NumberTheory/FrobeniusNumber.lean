/-
Copyright (c) 2021 Alex Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Zhao
-/
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Frobenius Number in Two Variables

In this file we first define a predicate for Frobenius numbers, then solve the 2-variable variant
of this problem.

## Theorem Statement

Given a finite set of relatively prime integers all greater than 1, their Frobenius number is the
largest positive integer that cannot be expressed as a sum of nonnegative multiples of these
integers. Here we show the Frobenius number of two relatively prime integers `m` and `n` greater
than 1 is `m * n - m - n`. This result is also known as the Chicken McNugget Theorem.

## Implementation Notes

First we define Frobenius numbers in general using `IsGreatest` and `AddSubmonoid.closure`. Then
we proceed to compute the Frobenius number of `m` and `n`.

For the upper bound, we begin with an auxiliary lemma showing `m * n` is not attainable, then show
`m * n - m - n` is not attainable. Then for the construction, we create a `k_1` which is `k mod n`
and `0 mod m`, then show it is at most `k`. Then `k_1` is a multiple of `m`, so `(k-k_1)`
is a multiple of n, and we're done.

## Tags

frobenius number, chicken mcnugget, chinese remainder theorem, add_submonoid.closure
-/


open Nat

/-- A natural number `n` is the **Frobenius number** of a set of natural numbers `s` if it is an
upper bound on the complement of the additive submonoid generated by `s`.
In other words, it is the largest number that can not be expressed as a sum of numbers in `s`. -/
def FrobeniusNumber (n : ℕ) (s : Set ℕ) : Prop :=
  IsGreatest { k | k ∉ AddSubmonoid.closure s } n

variable {m n : ℕ}

/-- The **Chicken McNugget theorem** stating that the Frobenius number
  of positive numbers `m` and `n` is `m * n - m - n`. -/
theorem frobeniusNumber_pair (cop : Coprime m n) (hm : 1 < m) (hn : 1 < n) :
    FrobeniusNumber (m * n - m - n) {m, n} := by
  simp_rw [FrobeniusNumber, AddSubmonoid.mem_closure_pair]
  have hmn : m + n ≤ m * n := add_le_mul hm hn
  constructor
  · push_neg
    intro a b h
    apply cop.mul_add_mul_ne_mul (add_one_ne_zero a) (add_one_ne_zero b)
    simp only [Nat.sub_sub, smul_eq_mul] at h
    zify [hmn] at h ⊢
    rw [← sub_eq_zero] at h ⊢
    rw [← h]
    ring
  · intro k hk
    dsimp at hk
    contrapose! hk
    let x := chineseRemainder cop 0 k
    have hx : x.val < m * n := chineseRemainder_lt_mul cop 0 k (ne_bot_of_gt hm) (ne_bot_of_gt hn)
    suffices key : x.1 ≤ k by
      obtain ⟨a, ha⟩ := modEq_zero_iff_dvd.mp x.2.1
      obtain ⟨b, hb⟩ := (modEq_iff_dvd' key).mp x.2.2
      exact ⟨a, b, by rw [mul_comm, ← ha, mul_comm, ← hb, Nat.add_sub_of_le key]⟩
    refine ModEq.le_of_lt_add x.2.2 (lt_of_le_of_lt ?_ (add_lt_add_right hk n))
    rw [Nat.sub_add_cancel (le_tsub_of_add_le_left hmn)]
    exact
      ModEq.le_of_lt_add
        (x.2.1.trans (modEq_zero_iff_dvd.mpr (Nat.dvd_sub' (dvd_mul_right m n) dvd_rfl)).symm)
        (lt_of_lt_of_le hx le_tsub_add)
