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

namespace Int

/-- The Fibonacci sequence for integers. This satisfies `fib 0 = 0`, `fib 1 = 1`,
`fib (n + 2) = fib n + fib (n + 1)`.

This is an extension of `Nat.fib`. -/
@[pp_nodot]
def fib (n : ℤ) : ℤ :=
  if 0 ≤ n then n.toNat.fib else
  if Even n then -(-n).toNat.fib else (-n).toNat.fib

@[simp] theorem fib_natCast (n : ℕ) : fib n = Nat.fib n := rfl
@[simp] theorem fib_zero : fib 0 = 0 := rfl
@[simp] theorem fib_one : fib 1 = 1 := rfl
@[simp] theorem fib_two : fib 2 = 1 := rfl
@[simp] theorem fib_neg_one : fib (-1) = 1 := rfl
@[simp] theorem fib_neg_two : fib (-2) = -1 := rfl
theorem fib_of_nonneg {n : ℤ} (hn : 0 ≤ n) : fib n = n.toNat.fib := by simp [fib, hn]
theorem fib_of_odd {n : ℤ} (hn : Odd n) : fib n = (natAbs n).fib := by grind [fib]
theorem fib_two_mul_add_one {n : ℤ} : fib (2 * n + 1) = (natAbs (2 * n + 1)).fib :=
  fib_of_odd <| odd_two_mul_add_one n
theorem fib_two_mul_add_one_nonneg {n : ℤ} : 0 ≤ fib (2 * n + 1) := by
  simp [fib_two_mul_add_one]

theorem fib_neg_natCast (n : ℕ) : fib (-n) = (-1) ^ (n + 1) * n.fib := by
  rcases n.even_or_odd with (hn | hn)
  · simp [fib, hn, pow_add]
  · simp [fib_of_odd, hn]

theorem coe_fib_neg (n : ℤ) : (fib (-n) : ℚ) = (-1) ^ (n + 1) * fib n := by
  obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
  · exact_mod_cast fib_neg_natCast _
  · rw [fib_neg_natCast, pow_add, Rat.zpow_add (by simp)]
    simp

theorem fib_add_two (n : ℤ) : fib (n + 2) = fib n + fib (n + 1) := by
  rcases n with (n | n)
  · dsimp
    rw [show (n : ℤ) + 2 = (n + 2 : ℕ) by rfl, fib_natCast, Nat.fib_add_two]
    rfl
  · rw [show negSucc n = -((n + 1 : ℕ) : ℤ) by rfl, fib_neg_natCast]
    simp only [Nat.cast_add, Nat.cast_one, neg_add_rev, reduceNeg, add_comm,
      add_assoc, reduceAdd, add_neg_cancel_comm_assoc, fib_neg_natCast]
    if hn0 : n = 0 then simp [hn0] else
    symm
    calc _ = (-1) ^ (n + 1) * ((n.fib - (n + 1).fib : ℤ)) := by grind
      _ = _ := by
        have : -(n : ℤ) + 1 = -((n - 1 : ℕ) : ℤ) := by grind
        obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
        · rw [Nat.fib_add_one hn0, this, fib_neg_natCast, pow_add, ← two_mul,
            Nat.sub_add_cancel (by grind)]
          simp
        · rw [Nat.fib_add_one hn0, this, fib_neg_natCast, pow_add]
          simp

theorem fib_eq_fib_add_two_sub_fib_add_one (n : ℤ) :
    fib n = fib (n + 2) - fib (n + 1) := by
  simp only [fib_add_two, add_sub_cancel_right]

theorem fib_add_one (n : ℤ) : fib (n + 1) = fib (n + 2) - fib n := by
  simp only [fib_add_two, add_sub_cancel_left]

@[simp] theorem fib_eq_zero {n : ℤ} : fib n = 0 ↔ n = 0 := by
  obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg <;> simp [fib_neg_natCast]

-- auxiliary for `fib_add`
theorem fib_natCast_add : ∀ (m : ℕ) (n : ℤ), fib (m + n) = fib (m - 1) * fib n + fib m * fib (n + 1)
  | 0, _ => by simp
  | 1, _ => by simp [add_comm]
  | m + 2, n => by
      calc _ = fib (m + n) + fib (m + n + 1) := by grind [fib_add_two]
        _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib ((m + 1 : ℕ) + n) := by
          rw [fib_natCast_add]; grind
        _ = fib (m - 1) * fib n + fib m * fib (n + 1) + fib m * fib n +
            fib (m + 1) * fib (n + 1) := by rw [fib_natCast_add]; grind
        _ = (fib (m - 1) + fib m) * fib n + (fib m + fib (m + 1)) * fib (n + 1) := by grind
        _ = fib (m + 1) * fib n + fib (m + 2) * fib (n + 1) := by grind [fib_add_two]
        _ = _ := by grind

-- TODO: `fib_add`, `fib_two_mul`, `fib_two_mul_add_one'`, `fib_two_mul_add_two`, `fib_dvd`, ...

end Int
