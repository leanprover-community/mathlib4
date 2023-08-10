/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Nat.Bits

#align_import data.nat.size from "leanprover-community/mathlib"@"18a5306c091183ac90884daa9373fa3b178e8607"

/-! Lemmas about `size`. -/

namespace Nat

/-! ### `shiftl` and `shiftr` -/

section
set_option linter.deprecated false

theorem shiftl_eq_mul_pow (m) : ∀ n, shiftl m n = m * 2 ^ n
  | 0 => (Nat.mul_one _).symm
  | k + 1 => by
    show bit0 (shiftl m k) = m * (2 ^ k * 2)
    rw [bit0_val, shiftl_eq_mul_pow m k, mul_comm 2, mul_assoc]
#align nat.shiftl_eq_mul_pow Nat.shiftl_eq_mul_pow

theorem shiftl'_tt_eq_mul_pow (m) : ∀ n, shiftl' true m n + 1 = (m + 1) * 2 ^ n
  | 0 => by simp [shiftl, shiftl', pow_zero, Nat.one_mul]
  | k + 1 => by
    change bit1 (shiftl' true m k) + 1 = (m + 1) * (2 ^ k * 2)
    rw [bit1_val]
    change 2 * (shiftl' true m k + 1) = _
    rw [shiftl'_tt_eq_mul_pow m k, mul_left_comm, mul_comm 2]
#align nat.shiftl'_tt_eq_mul_pow Nat.shiftl'_tt_eq_mul_pow

end

theorem one_shiftl (n) : shiftl 1 n = 2 ^ n :=
  (shiftl_eq_mul_pow _ _).trans (Nat.one_mul _)
#align nat.one_shiftl Nat.one_shiftl

@[simp]
theorem zero_shiftl (n) : shiftl 0 n = 0 :=
  (shiftl_eq_mul_pow _ _).trans (Nat.zero_mul _)
#align nat.zero_shiftl Nat.zero_shiftl

theorem shiftr_eq_div_pow (m) : ∀ n, shiftr m n = m / 2 ^ n
  | 0 => (Nat.div_one _).symm
  | k + 1 =>
    (congr_arg div2 (shiftr_eq_div_pow m k)).trans <| by
      rw [div2_val, Nat.div_div_eq_div_mul, Nat.pow_succ]
#align nat.shiftr_eq_div_pow Nat.shiftr_eq_div_pow

@[simp]
theorem zero_shiftr (n) : shiftr 0 n = 0 :=
  (shiftr_eq_div_pow _ _).trans (Nat.zero_div _)
#align nat.zero_shiftr Nat.zero_shiftr

theorem shiftl'_ne_zero_left (b) {m} (h : m ≠ 0) (n) : shiftl' b m n ≠ 0 := by
  induction n <;> simp [bit_ne_zero, shiftl', *]
#align nat.shiftl'_ne_zero_left Nat.shiftl'_ne_zero_left

theorem shiftl'_tt_ne_zero (m) : ∀ {n}, (n ≠ 0) → shiftl' true m n ≠ 0
  | 0, h => absurd rfl h
  | succ _, _ => Nat.bit1_ne_zero _
#align nat.shiftl'_tt_ne_zero Nat.shiftl'_tt_ne_zero

/-! ### `size` -/


@[simp]
theorem size_zero : size 0 = 0 := by simp [size]
#align nat.size_zero Nat.size_zero

@[simp]
theorem size_bit {b n} (h : bit b n ≠ 0) : size (bit b n) = succ (size n) := by
  rw [size]
  conv =>
    lhs
    rw [binaryRec]
    simp [h]
  rw [div2_bit]
#align nat.size_bit Nat.size_bit

section
set_option linter.deprecated false

@[simp]
theorem size_bit0 {n} (h : n ≠ 0) : size (bit0 n) = succ (size n) :=
  @size_bit false n (Nat.bit0_ne_zero h)
#align nat.size_bit0 Nat.size_bit0

@[simp]
theorem size_bit1 (n) : size (bit1 n) = succ (size n) :=
  @size_bit true n (Nat.bit1_ne_zero n)
#align nat.size_bit1 Nat.size_bit1

@[simp]
theorem size_one : size 1 = 1 :=
  show size (bit1 0) = 1 by rw [size_bit1, size_zero]
#align nat.size_one Nat.size_one

end

@[simp]
theorem size_shiftl' {b m n} (h : shiftl' b m n ≠ 0) : size (shiftl' b m n) = size m + n := by
  induction' n with n IH <;> simp [shiftl'] at h ⊢
  rw [size_bit h, Nat.add_succ]
  by_cases s0 : shiftl' b m n = 0 <;> [skip; rw [IH s0]]
  rw [s0] at h ⊢
  cases b; · exact absurd rfl h
  have : shiftl' true m n + 1 = 1 := congr_arg (· + 1) s0
  rw [shiftl'_tt_eq_mul_pow] at this
  obtain rfl := succ.inj (eq_one_of_dvd_one ⟨_, this.symm⟩)
  simp only [zero_add, one_mul] at this
  obtain rfl : n = 0 :=
    Nat.eq_zero_of_le_zero
      (le_of_not_gt fun hn => ne_of_gt (pow_lt_pow_of_lt_right (by decide) hn) this)
  rfl
#align nat.size_shiftl' Nat.size_shiftl'

@[simp]
theorem size_shiftl {m} (h : m ≠ 0) (n) : size (shiftl m n) = size m + n :=
  size_shiftl' (shiftl'_ne_zero_left _ h _)
#align nat.size_shiftl Nat.size_shiftl

theorem lt_size_self (n : ℕ) : n < 2 ^ size n := by
  rw [← one_shiftl]
  have : ∀ {n}, n = 0 → n < shiftl 1 (size n) := by simp
  apply binaryRec _ _ n
  · apply this rfl
  intro b n IH
  by_cases h : bit b n = 0
  · apply this h
  rw [size_bit h, shiftl_succ]
  exact bit_lt_bit0 _ IH
#align nat.lt_size_self Nat.lt_size_self

theorem size_le {m n : ℕ} : size m ≤ n ↔ m < 2 ^ n :=
  ⟨fun h => lt_of_lt_of_le (lt_size_self _) (pow_le_pow_of_le_right (by decide) h), by
    rw [← one_shiftl]; revert n
    apply binaryRec _ _ m
    · intro n
      simp
    · intro b m IH n h
      by_cases e : bit b m = 0
      · simp [e]
      rw [size_bit e]
      cases' n with n
      · exact e.elim (Nat.eq_zero_of_le_zero (le_of_lt_succ h))
      · apply succ_le_succ (IH _)
        apply lt_imp_lt_of_le_imp_le (fun h' => bit0_le_bit _ h') h⟩
#align nat.size_le Nat.size_le

theorem lt_size {m n : ℕ} : m < size n ↔ 2 ^ m ≤ n := by
  rw [← not_lt, Decidable.iff_not_comm, not_lt, size_le]
#align nat.lt_size Nat.lt_size

theorem size_pos {n : ℕ} : 0 < size n ↔ 0 < n := by rw [lt_size]; rfl
#align nat.size_pos Nat.size_pos

theorem size_eq_zero {n : ℕ} : size n = 0 ↔ n = 0 := by
  have := @size_pos n; simp [pos_iff_ne_zero] at this; exact Decidable.not_iff_not.1 this
#align nat.size_eq_zero Nat.size_eq_zero

theorem size_pow {n : ℕ} : size (2 ^ n) = n + 1 :=
  le_antisymm (size_le.2 <| pow_lt_pow_of_lt_right (by decide) (lt_succ_self _))
    (lt_size.2 <| le_rfl)
#align nat.size_pow Nat.size_pow

theorem size_le_size {m n : ℕ} (h : m ≤ n) : size m ≤ size n :=
  size_le.2 <| lt_of_le_of_lt h (lt_size_self _)
#align nat.size_le_size Nat.size_le_size

theorem size_eq_bits_len (n : ℕ) : n.bits.length = n.size := by
  induction' n using Nat.binaryRec' with b n h ih; · simp
  rw [size_bit, bits_append_bit _ _ h]
  · simp [ih]
  · simpa [bit_eq_zero_iff]
#align nat.size_eq_bits_len Nat.size_eq_bits_len

end Nat
