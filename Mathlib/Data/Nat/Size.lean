/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Bits

/-! Lemmas about `size`. -/

public section

namespace Nat

/-! ### `shiftLeft` and `shiftRight` -/

theorem shiftLeft_eq_mul_pow (m) : ∀ n, m <<< n = m * 2 ^ n := shiftLeft_eq _

theorem shiftLeft'_true_eq_mul_pow (m) : ∀ n, shiftLeft' true m n + 1 = (m + 1) * 2 ^ n
  | 0 => by simp [shiftLeft', Nat.pow_zero]
  | k + 1 => by
    rw [shiftLeft', bit_val, Bool.toNat_true, Nat.add_assoc, ← Nat.mul_add_one,
      shiftLeft'_true_eq_mul_pow m k, Nat.mul_left_comm, Nat.mul_comm 2, Nat.pow_succ]

@[deprecated (since := "2026-03-22")] alias shiftLeft'_tt_eq_mul_pow := shiftLeft'_true_eq_mul_pow

theorem shiftLeft'_ne_zero_left (b) {m} (h : m ≠ 0) (n) : shiftLeft' b m n ≠ 0 := by
  induction n <;> simp [shiftLeft', *]

theorem shiftLeft'_true_ne_zero (m) : ∀ {n}, (n ≠ 0) → shiftLeft' true m n ≠ 0
  | 0, h => absurd rfl h
  | succ _, _ => by simp [shiftLeft', bit]

@[deprecated (since := "2026-03-22")] alias shiftLeft'_tt_ne_zero := shiftLeft'_true_ne_zero

/-! ### `size` -/


@[simp]
theorem size_zero : size 0 = 0 := rfl

@[simp]
theorem size_bit {b n} (h : bit b n ≠ 0) : size (bit b n) = succ (size n) :=
  Nat.binaryRec_eq _ _ (.inr <| Nat.bit_ne_zero_iff.mp h)

@[simp]
theorem size_one : size 1 = 1 := rfl

@[simp]
theorem size_shiftLeft' {b m n} (h : shiftLeft' b m n ≠ 0) :
    size (shiftLeft' b m n) = size m + n := by
  induction n with
  | zero => simp [shiftLeft']
  | succ n IH =>
    simp only [shiftLeft', ne_eq] at h ⊢
    rw [size_bit h, Nat.add_succ]
    by_cases s0 : shiftLeft' b m n = 0
    case neg => rw [IH s0]
    rw [s0] at h ⊢
    cases b; · exact absurd rfl h
    have : shiftLeft' true m n + 1 = 1 := congr_arg (· + 1) s0
    rw [shiftLeft'_true_eq_mul_pow] at this
    obtain rfl := succ.inj (eq_one_of_dvd_one ⟨_, this.symm⟩)
    simp only [Nat.zero_add, Nat.one_mul, Nat.pow_eq_one, succ_ne_self, false_or] at this
    rw [this, Nat.add_zero]

@[simp]
theorem size_shiftLeft {m} (h : m ≠ 0) (n) : size (m <<< n) = size m + n := by
  simp only [size_shiftLeft' (shiftLeft'_ne_zero_left _ h _), ← shiftLeft'_false]

theorem lt_size_self (n : ℕ) : n < 2 ^ size n := by
  induction n using binaryRec' with
  | zero => simp
  | bit b n h IH =>
    rw [← Nat.bit_ne_zero_iff] at h
    rwa [size_bit h, bit_lt_two_pow_succ_iff]

theorem size_le {m n : ℕ} : size m ≤ n ↔ m < 2 ^ n :=
  ⟨fun h => Nat.lt_of_lt_of_le (lt_size_self _) (Nat.pow_le_pow_right (by decide) h), fun h ↦ by
    induction m using binaryRec' generalizing n with
    | zero => simp
    | bit b m e IH =>
      rw [← Nat.bit_ne_zero_iff] at e
      rw [size_bit e]
      cases n with
      | zero => exact (e (Nat.lt_one_iff.mp h)).elim
      | succ n => exact succ_le_succ (IH (bit_lt_two_pow_succ_iff.mp h))⟩

theorem lt_size {m n : ℕ} : m < size n ↔ 2 ^ m ≤ n := by
  rw [← Nat.not_lt, Decidable.iff_not_comm, Nat.not_lt, size_le]

theorem size_pos {n : ℕ} : 0 < size n ↔ 0 < n := by rw [lt_size]; rfl

theorem size_eq_zero {n : ℕ} : size n = 0 ↔ n = 0 := by
  simpa [Nat.pos_iff_ne_zero, Decidable.not_iff_not] using size_pos

theorem size_pow {n : ℕ} : size (2 ^ n) = n + 1 := by
  simpa [shiftLeft_eq, Nat.add_comm] using size_shiftLeft (m := 1) (by decide) n

theorem size_le_size {m n : ℕ} (h : m ≤ n) : size m ≤ size n :=
  size_le.2 <| Nat.lt_of_le_of_lt h (lt_size_self _)

theorem size_eq_bits_len (n : ℕ) : n.bits.length = n.size := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit _ _ h ih =>
    rw [size_bit, bits_append_bit _ _ h]
    · simp [ih]
    · simpa [bit_eq_zero_iff]

end Nat
