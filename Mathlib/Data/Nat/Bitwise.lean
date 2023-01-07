/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module data.nat.bitwise
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Basic
import Mathbin.Data.Nat.Bits
import Mathbin.Tactic.Linarith.Default

/-!
# Bitwise operations on natural numbers

In the first half of this file, we provide theorems for reasoning about natural numbers from their
bitwise properties. In the second half of this file, we show properties of the bitwise operations
`lor`, `land` and `lxor`, which are defined in core.

## Main results
* `eq_of_test_bit_eq`: two natural numbers are equal if they have equal bits at every position.
* `exists_most_significant_bit`: if `n ≠ 0`, then there is some position `i` that contains the most
  significant `1`-bit of `n`.
* `lt_of_test_bit`: if `n` and `m` are numbers and `i` is a position such that the `i`-th bit of
  of `n` is zero, the `i`-th bit of `m` is one, and all more significant bits are equal, then
  `n < m`.

## Future work

There is another way to express bitwise properties of natural number: `digits 2`. The two ways
should be connected.

## Keywords

bitwise, and, or, xor
-/


open Function

namespace Nat

@[simp]
theorem bit_ff : bit false = bit0 :=
  rfl
#align nat.bit_ff Nat.bit_ff

@[simp]
theorem bit_tt : bit true = bit1 :=
  rfl
#align nat.bit_tt Nat.bit_tt

@[simp]
theorem bit_eq_zero {n : ℕ} {b : Bool} : n.bit b = 0 ↔ n = 0 ∧ b = ff := by
  cases b <;> simp [Nat.bit0_eq_zero, Nat.bit1_ne_zero]
#align nat.bit_eq_zero Nat.bit_eq_zero

theorem zero_of_test_bit_eq_ff {n : ℕ} (h : ∀ i, testBit n i = ff) : n = 0 :=
  by
  induction' n using Nat.binaryRec with b n hn
  · rfl
  · have : b = ff := by simpa using h 0
    rw [this, bit_ff, bit0_val, hn fun i => by rw [← h (i + 1), test_bit_succ], mul_zero]
#align nat.zero_of_test_bit_eq_ff Nat.zero_of_test_bit_eq_ff

@[simp]
theorem zero_test_bit (i : ℕ) : testBit 0 i = ff := by simp [test_bit]
#align nat.zero_test_bit Nat.zero_test_bit

/-- The ith bit is the ith element of `n.bits`. -/
theorem test_bit_eq_inth (n i : ℕ) : n.testBit i = n.bits.inth i :=
  by
  induction' i with i ih generalizing n
  · simp [test_bit, shiftr, bodd_eq_bits_head, List.getI_zero_eq_head!]
  conv_lhs => rw [← bit_decomp n]
  rw [test_bit_succ, ih n.div2, div2_bits_eq_tail]
  cases n.bits <;> simp
#align nat.test_bit_eq_inth Nat.test_bit_eq_inth

/-- Bitwise extensionality: Two numbers agree if they agree at every bit position. -/
theorem eq_of_test_bit_eq {n m : ℕ} (h : ∀ i, testBit n i = testBit m i) : n = m :=
  by
  induction' n using Nat.binaryRec with b n hn generalizing m
  · simp only [zero_test_bit] at h
    exact (zero_of_test_bit_eq_ff fun i => (h i).symm).symm
  induction' m using Nat.binaryRec with b' m hm
  · simp only [zero_test_bit] at h
    exact zero_of_test_bit_eq_ff h
  suffices h' : n = m
  · rw [h', show b = b' by simpa using h 0]
  exact hn fun i => by convert h (i + 1) using 1 <;> rw [test_bit_succ]
#align nat.eq_of_test_bit_eq Nat.eq_of_test_bit_eq

theorem exists_most_significant_bit {n : ℕ} (h : n ≠ 0) :
    ∃ i, testBit n i = tt ∧ ∀ j, i < j → testBit n j = ff :=
  by
  induction' n using Nat.binaryRec with b n hn
  · exact False.elim (h rfl)
  by_cases h' : n = 0
  · subst h'
    rw [show b = tt by
        revert h
        cases b <;> simp]
    refine' ⟨0, ⟨by rw [test_bit_zero], fun j hj => _⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (ne_of_gt hj)
    rw [test_bit_succ, zero_test_bit]
  · obtain ⟨k, ⟨hk, hk'⟩⟩ := hn h'
    refine' ⟨k + 1, ⟨by rw [test_bit_succ, hk], fun j hj => _⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (show j ≠ 0 by linarith)
    exact (test_bit_succ _ _ _).trans (hk' _ (lt_of_succ_lt_succ hj))
#align nat.exists_most_significant_bit Nat.exists_most_significant_bit

theorem lt_of_test_bit {n m : ℕ} (i : ℕ) (hn : testBit n i = ff) (hm : testBit m i = tt)
    (hnm : ∀ j, i < j → testBit n j = testBit m j) : n < m :=
  by
  induction' n using Nat.binaryRec with b n hn' generalizing i m
  · contrapose! hm
    rw [le_zero_iff] at hm
    simp [hm]
  induction' m using Nat.binaryRec with b' m hm' generalizing i
  · exact False.elim (Bool.ff_ne_tt ((zero_test_bit i).symm.trans hm))
  by_cases hi : i = 0
  · subst hi
    simp only [test_bit_zero] at hn hm
    have : n = m :=
      eq_of_test_bit_eq fun i => by convert hnm (i + 1) (by decide) using 1 <;> rw [test_bit_succ]
    rw [hn, hm, this, bit_ff, bit_tt, bit0_val, bit1_val]
    exact lt_add_one _
  · obtain ⟨i', rfl⟩ := exists_eq_succ_of_ne_zero hi
    simp only [test_bit_succ] at hn hm
    have :=
      hn' _ hn hm fun j hj => by convert hnm j.succ (succ_lt_succ hj) using 1 <;> rw [test_bit_succ]
    cases b <;> cases b' <;>
        simp only [bit_ff, bit_tt, bit0_val n, bit1_val n, bit0_val m, bit1_val m] <;>
      linarith
#align nat.lt_of_test_bit Nat.lt_of_test_bit

@[simp]
theorem test_bit_two_pow_self (n : ℕ) : testBit (2 ^ n) n = tt := by
  rw [test_bit, shiftr_eq_div_pow, Nat.div_self (pow_pos zero_lt_two n), bodd_one]
#align nat.test_bit_two_pow_self Nat.test_bit_two_pow_self

theorem test_bit_two_pow_of_ne {n m : ℕ} (hm : n ≠ m) : testBit (2 ^ n) m = ff :=
  by
  rw [test_bit, shiftr_eq_div_pow]
  cases' hm.lt_or_lt with hm hm
  · rw [Nat.div_eq_zero, bodd_zero]
    exact Nat.pow_lt_pow_of_lt_right one_lt_two hm
  · rw [pow_div hm.le zero_lt_two, ← tsub_add_cancel_of_le (succ_le_of_lt <| tsub_pos_of_lt hm)]
    simp [pow_succ]
#align nat.test_bit_two_pow_of_ne Nat.test_bit_two_pow_of_ne

theorem test_bit_two_pow (n m : ℕ) : testBit (2 ^ n) m = (n = m) :=
  by
  by_cases n = m
  · cases h
    simp
  · rw [test_bit_two_pow_of_ne h]
    simp [h]
#align nat.test_bit_two_pow Nat.test_bit_two_pow

/-- If `f` is a commutative operation on bools such that `f ff ff = ff`, then `bitwise f` is also
    commutative. -/
theorem bitwise_comm {f : Bool → Bool → Bool} (hf : ∀ b b', f b b' = f b' b)
    (hf' : f false false = ff) (n m : ℕ) : bitwise f n m = bitwise f m n :=
  suffices bitwise f = swap (bitwise f) by conv_lhs => rw [this]
  calc
    bitwise f = bitwise (swap f) := congr_arg _ <| funext fun _ => funext <| hf _
    _ = swap (bitwise f) := bitwise'_swap hf'
    
#align nat.bitwise_comm Nat.bitwise_comm

theorem lor_comm (n m : ℕ) : lor n m = lor m n :=
  bitwise_comm Bool.or_comm rfl n m
#align nat.lor_comm Nat.lor_comm

theorem land_comm (n m : ℕ) : land n m = land m n :=
  bitwise_comm Bool.and_comm rfl n m
#align nat.land_comm Nat.land_comm

theorem lxor_comm (n m : ℕ) : lxor' n m = lxor' m n :=
  bitwise_comm Bool.xor_comm rfl n m
#align nat.lxor_comm Nat.lxor_comm

@[simp]
theorem zero_lxor (n : ℕ) : lxor' 0 n = n := by simp [lxor]
#align nat.zero_lxor Nat.zero_lxor

@[simp]
theorem lxor_zero (n : ℕ) : lxor' n 0 = n := by simp [lxor]
#align nat.lxor_zero Nat.lxor_zero

@[simp]
theorem zero_land (n : ℕ) : land 0 n = 0 := by simp [land]
#align nat.zero_land Nat.zero_land

@[simp]
theorem land_zero (n : ℕ) : land n 0 = 0 := by simp [land]
#align nat.land_zero Nat.land_zero

@[simp]
theorem zero_lor (n : ℕ) : lor 0 n = n := by simp [lor]
#align nat.zero_lor Nat.zero_lor

@[simp]
theorem lor_zero (n : ℕ) : lor n 0 = n := by simp [lor]
#align nat.lor_zero Nat.lor_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- Proving associativity of bitwise operations in general essentially boils down to a huge case
    distinction, so it is shorter to use this tactic instead of proving it in the general case. -/
unsafe def bitwise_assoc_tac : tactic Unit :=
  sorry
#align nat.bitwise_assoc_tac nat.bitwise_assoc_tac

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic nat.bitwise_assoc_tac -/
theorem lxor_assoc (n m k : ℕ) : lxor' (lxor' n m) k = lxor' n (lxor' m k) := by
  run_tac
    bitwise_assoc_tac
#align nat.lxor_assoc Nat.lxor_assoc

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic nat.bitwise_assoc_tac -/
theorem land_assoc (n m k : ℕ) : land (land n m) k = land n (land m k) := by
  run_tac
    bitwise_assoc_tac
#align nat.land_assoc Nat.land_assoc

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic nat.bitwise_assoc_tac -/
theorem lor_assoc (n m k : ℕ) : lor (lor n m) k = lor n (lor m k) := by
  run_tac
    bitwise_assoc_tac
#align nat.lor_assoc Nat.lor_assoc

@[simp]
theorem lxor_self (n : ℕ) : lxor' n n = 0 :=
  zero_of_test_bit_eq_ff fun i => by simp
#align nat.lxor_self Nat.lxor_self

-- These lemmas match `mul_inv_cancel_right` and `mul_inv_cancel_left`.
theorem lxor_cancel_right (n m : ℕ) : lxor' (lxor' m n) n = m := by
  rw [lxor_assoc, lxor_self, lxor_zero]
#align nat.lxor_cancel_right Nat.lxor_cancel_right

theorem lxor_cancel_left (n m : ℕ) : lxor' n (lxor' n m) = m := by
  rw [← lxor_assoc, lxor_self, zero_lxor]
#align nat.lxor_cancel_left Nat.lxor_cancel_left

theorem lxor_right_injective {n : ℕ} : Function.Injective (lxor' n) := fun m m' h => by
  rw [← lxor_cancel_left n m, ← lxor_cancel_left n m', h]
#align nat.lxor_right_injective Nat.lxor_right_injective

theorem lxor_left_injective {n : ℕ} : Function.Injective fun m => lxor' m n :=
  fun m m' (h : lxor' m n = lxor' m' n) => by
  rw [← lxor_cancel_right n m, ← lxor_cancel_right n m', h]
#align nat.lxor_left_injective Nat.lxor_left_injective

@[simp]
theorem lxor_right_inj {n m m' : ℕ} : lxor' n m = lxor' n m' ↔ m = m' :=
  lxor_right_injective.eq_iff
#align nat.lxor_right_inj Nat.lxor_right_inj

@[simp]
theorem lxor_left_inj {n m m' : ℕ} : lxor' m n = lxor' m' n ↔ m = m' :=
  lxor_left_injective.eq_iff
#align nat.lxor_left_inj Nat.lxor_left_inj

@[simp]
theorem lxor_eq_zero {n m : ℕ} : lxor' n m = 0 ↔ n = m := by
  rw [← lxor_self n, lxor_right_inj, eq_comm]
#align nat.lxor_eq_zero Nat.lxor_eq_zero

theorem lxor_ne_zero {n m : ℕ} : lxor' n m ≠ 0 ↔ n ≠ m :=
  lxor_eq_zero.Not
#align nat.lxor_ne_zero Nat.lxor_ne_zero

theorem lxor_trichotomy {a b c : ℕ} (h : a ≠ lxor' b c) :
    lxor' b c < a ∨ lxor' a c < b ∨ lxor' a b < c :=
  by
  set v := lxor a (lxor b c) with hv
  -- The xor of any two of `a`, `b`, `c` is the xor of `v` and the third.
  have hab : lxor a b = lxor c v := by
    rw [hv]
    conv_rhs =>
      rw [lxor_comm]
      simp [lxor_assoc]
  have hac : lxor a c = lxor b v := by
    rw [hv]
    conv_rhs =>
      congr
      skip
      rw [lxor_comm]
    rw [← lxor_assoc, ← lxor_assoc, lxor_self, zero_lxor, lxor_comm]
  have hbc : lxor b c = lxor a v := by simp [hv, ← lxor_assoc]
  -- If `i` is the position of the most significant bit of `v`, then at least one of `a`, `b`, `c`
  -- has a one bit at position `i`.
  obtain ⟨i, ⟨hi, hi'⟩⟩ := exists_most_significant_bit (lxor_ne_zero.2 h)
  have : test_bit a i = tt ∨ test_bit b i = tt ∨ test_bit c i = tt :=
    by
    contrapose! hi
    simp only [Bool.eq_false_eq_not_eq_true, Ne, test_bit_lxor] at hi⊢
    rw [hi.1, hi.2.1, hi.2.2, Bool.xor_false, Bool.xor_false]
  -- If, say, `a` has a one bit at position `i`, then `a xor v` has a zero bit at position `i`, but
      -- the same bits as `a` in positions greater than `j`, so `a xor v < a`.
      rcases this with (h | h | h) <;>
      [·
        left
        rw [hbc],
      · right
        left
        rw [hac],
      · right
        right
        rw [hab]] <;>
    exact lt_of_test_bit i (by simp [h, hi]) h fun j hj => by simp [hi' _ hj]
#align nat.lxor_trichotomy Nat.lxor_trichotomy

theorem lt_lxor_cases {a b c : ℕ} (h : a < lxor' b c) : lxor' a c < b ∨ lxor' a b < c :=
  (or_iff_right fun h' => (h.asymm h').elim).1 <| lxor_trichotomy h.Ne
#align nat.lt_lxor_cases Nat.lt_lxor_cases

end Nat

