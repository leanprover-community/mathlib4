/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Data.Nat.Fib.Basic

/-!

# Fibonacci numbers extended onto the integers

This file defines the Fibonacci sequence on the integers.

Definition of the sequence: `F₀ = 0`, `F₁ = 1`, and `Fₙ₊₂ = Fₙ₊₁ + Fₙ`
(same as the natural number version `Nat.fib`, but here `n` is an integer).

-/

/-- The Fibonacci sequence for integers. This satisfies `fib 0 = 0`, `fib 1 = 1`,
`fib (n + 2) = fib n + fib (n + 1)`.

This is an extension of `Nat.fib`. -/
def Int.fib (n : ℤ) : ℤ :=
  if 0 ≤ n then Nat.fib n.toNat
  else if n % 2 = 0 then -(-n).toNat.fib else (-n).toNat.fib

@[simp] theorem Int.fib_nat (n : ℕ) : Int.fib n = Nat.fib n := rfl
@[simp] theorem Int.fib_zero : Int.fib 0 = 0 := rfl
@[simp] theorem Int.fib_one : Int.fib 1 = 1 := rfl
@[simp] theorem Int.fib_two : Int.fib 2 = 1 := rfl
@[simp] theorem Int.fib_neg_one : Int.fib (-1) = 1 := rfl
@[simp] theorem Int.fib_neg_two : Int.fib (-2) = -1 := rfl

theorem Int.fib_neg_nat (n : ℕ) : Int.fib (-n) = (-1) ^ (n + 1) * n.fib := by
  simp only [fib, Int.neg_nonneg, natCast_nonpos_iff, toNat_neg_natCast, Nat.fib_zero,
    neg_emod_two, neg_neg, toNat_natCast, reduceNeg]
  split_ifs with hn h
  · simp [hn]
  · obtain ⟨a, rfl⟩ : Even n := by grind
    simp [← two_mul, Odd.neg_one_pow (Exists.intro a rfl)]
  · obtain ⟨a, rfl⟩ : Odd n := by grind
    simp [add_assoc, ← two_mul, ← mul_add_one]

theorem Int.fib_add_two {n : ℤ} :
    fib (n + 2) = fib n + fib (n + 1) := by
  rcases n with (n | n)
  · dsimp
    rw [show (n : ℤ) + 2 = (n + 2 : ℕ) by rfl, fib_nat, Nat.fib_add_two]
    rfl
  · rw [show negSucc n = -((n + 1 : ℕ) : ℤ) by rfl, fib_neg_nat]
    simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, reduceNeg, add_comm,
      add_assoc, reduceAdd, add_neg_cancel_comm_assoc, fib_neg_nat]
    if hn0 : n = 0 then simp [hn0] else
    symm
    calc _ = (-1) ^ (n + 1) * ((n.fib - (n + 1).fib : ℤ)) := by grind
      _ = _ := by
        have : -(n : ℤ) + 1 = -((n - 1 : ℕ) : ℤ) := by grind
        obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
        · rw [Nat.fib_add_one hn0, this, fib_neg_nat, pow_add, ← two_mul,
            Nat.sub_add_cancel (by grind)]
          simp
        · rw [Nat.fib_add_one hn0, this, fib_neg_nat, pow_add]
          simp

theorem Int.fib_eq_fib_add_two_sub_fib_succ {n : ℤ} :
    fib n = fib (n + 2) - fib (n + 1) := by
  simp only [fib_add_two, add_sub_cancel_right]

theorem Int.fib_add_one {n : ℤ} :
    fib (n + 1) = fib (n + 2) - fib n := by
  simp only [fib_add_two, add_sub_cancel_left]
