/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Alex Keizer
-/
import Lean.Elab.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

#align_import data.nat.bitwise from "leanprover-community/mathlib"@"6afc9b06856ad973f6a2619e3e8a0a8d537a58f2"

/-!
# Bitwise operations on natural numbers

In the first half of this file, we provide theorems for reasoning about natural numbers from their
bitwise properties. In the second half of this file, we show properties of the bitwise operations
`lor`, `land` and `xor'`, which are defined in core.

## Main results
* `eq_of_testBit_eq`: two natural numbers are equal if they have equal bits at every position.
* `exists_most_significant_bit`: if `n ≠ 0`, then there is some position `i` that contains the most
  significant `1`-bit of `n`.
* `lt_of_testBit`: if `n` and `m` are numbers and `i` is a position such that the `i`-th bit of
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

set_option linter.deprecated false

section
variable {f : Bool → Bool → Bool}

@[simp]
lemma bitwise_zero_left (m : Nat) : bitwise f 0 m = if f false true then m else 0 :=
  rfl
#align nat.bitwise_zero_left Nat.bitwise_zero_left

@[simp]
lemma bitwise_zero_right (n : Nat) : bitwise f n 0 = if f true false then n else 0 := by
  unfold bitwise
  simp only [ite_self, decide_False, Nat.zero_div, ite_true, ite_eq_right_iff]
  rintro ⟨⟩
  split_ifs <;> rfl
#align nat.bitwise_zero_right Nat.bitwise_zero_right

lemma bitwise_zero : bitwise f 0 0 = 0 := by
  simp only [bitwise_zero_right, ite_self]
#align nat.bitwise_zero Nat.bitwise_zero

@[simp]
lemma bitwise_of_ne_zero {n m : Nat} (hn : n ≠ 0) (hm : m ≠ 0) :
    bitwise f n m = bit (f (bodd n) (bodd m)) (bitwise f (n / 2) (m / 2)) := by
  conv_lhs => { unfold bitwise }
  have mod_two_iff_bod x : (x % 2 = 1 : Bool) = bodd x := by
    simp [mod_two_of_bodd, cond]; cases bodd x <;> rfl
  simp only [hn, hm, mod_two_iff_bod, ite_false, bit, bit1, bit0, Bool.cond_eq_ite]
  split_ifs <;> rfl

@[simp]
lemma bitwise_bit {f : Bool → Bool → Bool} (h : f false false = false := by rfl) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  conv_lhs => { unfold bitwise }
  simp only [bit, bit1, bit0, Bool.cond_eq_ite]
  have h1 x :     (x + x) % 2 = 0   := by ring_nf; apply mul_mod_left
  have h2 x : (x + x + 1) % 2 = 1   := by ring_nf; apply add_mul_mod_self_right
  have h3 x :     (x + x) / 2 = x   := by ring_nf; apply mul_div_left _ zero_lt_two
  have h4 x : (x + x + 1) / 2 = x   := by ring_nf; simp [add_mul_div_right]
  cases a <;> cases b <;> simp [h1, h2, h3, h4] <;> split_ifs <;> simp_all
#align nat.bitwise_bit Nat.bitwise_bit

@[simp]
theorem lor_bit : ∀ a m b n, lor (bit a m) (bit b n) = bit (a || b) (lor m n) :=
  bitwise_bit
#align nat.lor_bit Nat.lor_bit

@[simp]
theorem land_bit : ∀ a m b n, land (bit a m) (bit b n) = bit (a && b) (land m n) :=
  bitwise_bit
#align nat.land_bit Nat.land_bit

@[simp]
theorem ldiff_bit : ∀ a m b n, ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n) :=
  bitwise_bit
#align nat.ldiff_bit Nat.ldiff_bit

@[simp]
theorem xor_bit : ∀ a m b n, xor (bit a m) (bit b n) = bit (bne a b) (xor m n) :=
  bitwise_bit
#align nat.xor_bit Nat.xor_bit

@[simp]
theorem testBit_bitwise {f : Bool → Bool → Bool} (h : f false false = false) (m n k) :
    testBit (bitwise f m n) k = f (testBit m k) (testBit n k) := by
  induction' k with k ih generalizing m n
  <;> cases' m using bitCasesOn with a m
  <;> cases' n using bitCasesOn with b n
  <;> rw [bitwise_bit h]
  · simp [testBit_zero]
  · simp [testBit_succ, ih]

@[simp]
theorem testBit_lor : ∀ m n k, testBit (lor m n) k = (testBit m k || testBit n k) :=
  testBit_bitwise rfl
#align nat.test_bit_lor Nat.testBit_lor

@[simp]
theorem testBit_land : ∀ m n k, testBit (land m n) k = (testBit m k && testBit n k) :=
  testBit_bitwise rfl
#align nat.test_bit_land Nat.testBit_land

@[simp]
theorem testBit_ldiff : ∀ m n k, testBit (ldiff m n) k = (testBit m k && not (testBit n k)) :=
  testBit_bitwise rfl
#align nat.test_bit_ldiff Nat.testBit_ldiff

@[simp]
theorem testBit_xor : ∀ m n k, testBit (xor m n) k = bne (testBit m k) (testBit n k) :=
  testBit_bitwise rfl
#align nat.test_bit_lxor Nat.testBit_xor

end

@[simp]
theorem bit_false : bit false = bit0 :=
  rfl
#align nat.bit_ff Nat.bit_false

@[simp]
theorem bit_true : bit true = bit1 :=
  rfl
#align nat.bit_tt Nat.bit_true

@[simp]
theorem bit_eq_zero {n : ℕ} {b : Bool} : n.bit b = 0 ↔ n = 0 ∧ b = false := by
  cases b <;> simp [Nat.bit0_eq_zero, Nat.bit1_ne_zero]
#align nat.bit_eq_zero Nat.bit_eq_zero

theorem zero_of_testBit_eq_false {n : ℕ} (h : ∀ i, testBit n i = false) : n = 0 := by
  induction' n using Nat.binaryRec with b n hn
  · rfl
  · have : b = false := by simpa using h 0
    rw [this, bit_false, bit0_val, hn fun i => by rw [← h (i + 1), testBit_succ], mul_zero]
#align nat.zero_of_test_bit_eq_ff Nat.zero_of_testBit_eq_false

@[simp]
theorem zero_testBit (i : ℕ) : testBit 0 i = false := by
  simp only [testBit, zero_shiftRight, bodd_zero]
#align nat.zero_test_bit Nat.zero_testBit

/-- The ith bit is the ith element of `n.bits`. -/
theorem testBit_eq_inth (n i : ℕ) : n.testBit i = n.bits.getI i := by
  induction' i with i ih generalizing n
  · simp [testBit, bodd_eq_bits_head, List.getI_zero_eq_headI]
  conv_lhs => rw [← bit_decomp n]
  rw [testBit_succ, ih n.div2, div2_bits_eq_tail]
  cases n.bits <;> simp
#align nat.test_bit_eq_inth Nat.testBit_eq_inth

/-- Bitwise extensionality: Two numbers agree if they agree at every bit position. -/
theorem eq_of_testBit_eq {n m : ℕ} (h : ∀ i, testBit n i = testBit m i) : n = m := by
  induction' n using Nat.binaryRec with b n hn generalizing m
  · simp only [zero_testBit] at h
    exact (zero_of_testBit_eq_false fun i => (h i).symm).symm
  induction' m using Nat.binaryRec with b' m
  · simp only [zero_testBit] at h
    exact zero_of_testBit_eq_false h
  suffices h' : n = m by
    rw [h', show b = b' by simpa using h 0]
  exact hn fun i => by convert h (i + 1) using 1 <;> rw [testBit_succ]
#align nat.eq_of_test_bit_eq Nat.eq_of_testBit_eq

theorem exists_most_significant_bit {n : ℕ} (h : n ≠ 0) :
    ∃ i, testBit n i = true ∧ ∀ j, i < j → testBit n j = false := by
  induction' n using Nat.binaryRec with b n hn
  · exact False.elim (h rfl)
  by_cases h' : n = 0
  · subst h'
    rw [show b = true by
        revert h
        cases b <;> simp]
    refine' ⟨0, ⟨by rw [testBit_zero], fun j hj => _⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (ne_of_gt hj)
    rw [testBit_succ, zero_testBit]
  · obtain ⟨k, ⟨hk, hk'⟩⟩ := hn h'
    refine' ⟨k + 1, ⟨by rw [testBit_succ, hk], fun j hj => _⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (show j ≠ 0 by intro x; subst x; simp at hj)
    exact (testBit_succ _ _ _).trans (hk' _ (lt_of_succ_lt_succ hj))
#align nat.exists_most_significant_bit Nat.exists_most_significant_bit

theorem lt_of_testBit {n m : ℕ} (i : ℕ) (hn : testBit n i = false) (hm : testBit m i = true)
    (hnm : ∀ j, i < j → testBit n j = testBit m j) : n < m := by
  induction' n using Nat.binaryRec with b n hn' generalizing i m
  · contrapose! hm
    rw [le_zero_iff] at hm
    simp [hm]
  induction' m using Nat.binaryRec with b' m hm' generalizing i
  · exact False.elim (Bool.ff_ne_tt ((zero_testBit i).symm.trans hm))
  by_cases hi : i = 0
  · subst hi
    simp only [testBit_zero] at hn hm
    have : n = m :=
      eq_of_testBit_eq fun i => by convert hnm (i + 1) (Nat.zero_lt_succ _) using 1
      <;> rw [testBit_succ]
    rw [hn, hm, this, bit_false, bit_true, bit0_val, bit1_val]
    exact lt_add_one _
  · obtain ⟨i', rfl⟩ := exists_eq_succ_of_ne_zero hi
    simp only [testBit_succ] at hn hm
    have :=
      hn' _ hn hm fun j hj => by convert hnm j.succ (succ_lt_succ hj) using 1 <;> rw [testBit_succ]
    cases b <;> cases b'
    <;> simp only [bit_false, bit_true, bit0_val n, bit1_val n, bit0_val m, bit1_val m]
    <;> linarith only [this]
#align nat.lt_of_test_bit Nat.lt_of_testBit

@[simp]
theorem testBit_two_pow_self (n : ℕ) : testBit (2 ^ n) n = true := by
  rw [testBit, shiftRight_eq_div_pow, Nat.div_self (pow_pos (α := ℕ) zero_lt_two n), bodd_one]
#align nat.test_bit_two_pow_self Nat.testBit_two_pow_self

theorem testBit_two_pow_of_ne {n m : ℕ} (hm : n ≠ m) : testBit (2 ^ n) m = false := by
  rw [testBit, shiftRight_eq_div_pow]
  cases' hm.lt_or_lt with hm hm
  · rw [Nat.div_eq_zero, bodd_zero]
    exact Nat.pow_lt_pow_of_lt_right one_lt_two hm
  · rw [pow_div hm.le zero_lt_two, ← tsub_add_cancel_of_le (succ_le_of_lt <| tsub_pos_of_lt hm)]
    -- Porting note: XXX why does this make it work?
    rw [(rfl : succ 0 = 1)]
    simp only [ge_iff_le, tsub_le_iff_right, pow_succ, bodd_mul,
      Bool.and_eq_false_eq_eq_false_or_eq_false, or_true]
#align nat.test_bit_two_pow_of_ne Nat.testBit_two_pow_of_ne

theorem testBit_two_pow (n m : ℕ) : testBit (2 ^ n) m = (n = m) := by
  by_cases h : n = m
  · cases h
    simp
  · rw [testBit_two_pow_of_ne h]
    simp [h]
#align nat.test_bit_two_pow Nat.testBit_two_pow

theorem bitwise_swap {f : Bool → Bool → Bool} :
    bitwise (Function.swap f) = Function.swap (bitwise f) := by
  funext m n
  simp only [Function.swap]
  induction' m using Nat.strongInductionOn with m ih generalizing n
  cases' m with m
  <;> cases' n with n
  <;> try rw [bitwise_zero_left, bitwise_zero_right]
  · specialize ih ((m+1) / 2) (div_lt_self' ..)
    simp [bitwise_of_ne_zero, ih]
#align nat.bitwise_swap Nat.bitwise_swap

/-- If `f` is a commutative operation on bools such that `f false false = false`, then `bitwise f`
    is also commutative. -/
theorem bitwise_comm {f : Bool → Bool → Bool} (hf : ∀ b b', f b b' = f b' b) (n m : ℕ) :
    bitwise f n m = bitwise f m n :=
  suffices bitwise f = swap (bitwise f) by conv_lhs => rw [this]
  calc
    bitwise f = bitwise (swap f) := congr_arg _ <| funext fun _ => funext <| hf _
    _ = swap (bitwise f) := bitwise_swap
#align nat.bitwise_comm Nat.bitwise_comm

theorem lor_comm (n m : ℕ) : lor n m = lor m n :=
  bitwise_comm Bool.or_comm n m
#align nat.lor_comm Nat.lor_comm

theorem land_comm (n m : ℕ) : land n m = land m n :=
  bitwise_comm Bool.and_comm n m
#align nat.land_comm Nat.land_comm

theorem xor_comm (n m : ℕ) : xor n m = xor m n :=
  bitwise_comm (Bool.bne_eq_xor ▸ Bool.xor_comm) n m
#align nat.lxor_comm Nat.xor_comm

@[simp]
theorem zero_xor (n : ℕ) : xor 0 n = n := by
 simp only [xor, bitwise_zero_left, ite_true]
#align nat.zero_lxor Nat.zero_xor

@[simp]
theorem xor_zero (n : ℕ) : xor n 0 = n := by simp [xor]
#align nat.lxor_zero Nat.xor_zero

@[simp]
theorem zero_land (n : ℕ) : land 0 n = 0 := by
  simp only [land, bitwise_zero_left, ite_false];
#align nat.zero_land Nat.zero_land

@[simp]
theorem land_zero (n : ℕ) : land n 0 = 0 := by
  simp only [land, bitwise_zero_right, ite_false]
#align nat.land_zero Nat.land_zero

@[simp]
theorem zero_lor (n : ℕ) : lor 0 n = n := by
  simp only [lor, bitwise_zero_left, ite_true]
#align nat.zero_lor Nat.zero_lor

@[simp]
theorem lor_zero (n : ℕ) : lor n 0 = n := by
  simp only [lor, bitwise_zero_right, ite_true]
#align nat.lor_zero Nat.lor_zero


/-- Proving associativity of bitwise operations in general essentially boils down to a huge case
    distinction, so it is shorter to use this tactic instead of proving it in the general case. -/
macro "bitwise_assoc_tac" : tactic => set_option hygiene false in `(tactic| (
  induction' n using Nat.binaryRec with b n hn generalizing m k
  · simp
  induction' m using Nat.binaryRec with b' m hm
  · simp
  induction' k using Nat.binaryRec with b'' k hk
  -- Porting note: was `simp [hn]`
  -- This is necessary because these are simp lemmas in mathlib
  <;> simp [hn, Bool.or_assoc, Bool.and_assoc, Bool.bne_eq_xor]))

theorem xor_assoc (n m k : ℕ) : xor (xor n m) k = xor n (xor m k) := by bitwise_assoc_tac
#align nat.lxor_assoc Nat.xor_assoc

theorem land_assoc (n m k : ℕ) : land (land n m) k = land n (land m k) := by bitwise_assoc_tac
#align nat.land_assoc Nat.land_assoc

theorem lor_assoc (n m k : ℕ) : lor (lor n m) k = lor n (lor m k) := by bitwise_assoc_tac
#align nat.lor_assoc Nat.lor_assoc

@[simp]
theorem xor_self (n : ℕ) : xor n n = 0 :=
  zero_of_testBit_eq_false fun i => by simp
#align nat.lxor_self Nat.xor_self

-- These lemmas match `mul_inv_cancel_right` and `mul_inv_cancel_left`.
theorem lxor_cancel_right (n m : ℕ) : xor (xor m n) n = m := by
  rw [xor_assoc, xor_self, xor_zero]
#align nat.lxor_cancel_right Nat.lxor_cancel_right

theorem xor_cancel_left (n m : ℕ) : xor n (xor n m) = m := by
  rw [← xor_assoc, xor_self, zero_xor]
#align nat.lxor_cancel_left Nat.xor_cancel_left

theorem xor_right_injective {n : ℕ} : Function.Injective (xor n) := fun m m' h => by
  rw [← xor_cancel_left n m, ← xor_cancel_left n m', h]
#align nat.lxor_right_injective Nat.xor_right_injective

theorem xor_left_injective {n : ℕ} : Function.Injective fun m => xor m n :=
  fun m m' (h : xor m n = xor m' n) => by
  rw [← lxor_cancel_right n m, ← lxor_cancel_right n m', h]
#align nat.lxor_left_injective Nat.xor_left_injective

@[simp]
theorem xor_right_inj {n m m' : ℕ} : xor n m = xor n m' ↔ m = m' :=
  xor_right_injective.eq_iff
#align nat.lxor_right_inj Nat.xor_right_inj

@[simp]
theorem xor_left_inj {n m m' : ℕ} : xor m n = xor m' n ↔ m = m' :=
  xor_left_injective.eq_iff
#align nat.lxor_left_inj Nat.xor_left_inj

@[simp]
theorem xor_eq_zero {n m : ℕ} : xor n m = 0 ↔ n = m := by
  rw [← xor_self n, xor_right_inj, eq_comm]
#align nat.lxor_eq_zero Nat.xor_eq_zero

theorem xor_ne_zero {n m : ℕ} : xor n m ≠ 0 ↔ n ≠ m :=
  xor_eq_zero.not
#align nat.lxor_ne_zero Nat.xor_ne_zero

theorem xor_trichotomy {a b c : ℕ} (h : a ≠ xor b c) :
    xor b c < a ∨ xor a c < b ∨ xor a b < c := by
  set v := xor a (xor b c) with hv
  -- The xor of any two of `a`, `b`, `c` is the xor of `v` and the third.
  have hab : xor a b = xor c v := by
    rw [hv]
    conv_rhs =>
      rw [xor_comm]
      simp [xor_assoc]
  have hac : xor a c = xor b v := by
    rw [hv]
    conv_rhs =>
      right
      rw [← xor_comm]
    rw [← xor_assoc, ← xor_assoc, xor_self, zero_xor, xor_comm]
  have hbc : xor b c = xor a v := by simp [hv, ← xor_assoc]
  -- If `i` is the position of the most significant bit of `v`, then at least one of `a`, `b`, `c`
  -- has a one bit at position `i`.
  obtain ⟨i, ⟨hi, hi'⟩⟩ := exists_most_significant_bit (xor_ne_zero.2 h)
  have : testBit a i = true ∨ testBit b i = true ∨ testBit c i = true := by
    contrapose! hi
    simp only [Bool.eq_false_eq_not_eq_true, Ne, testBit_xor, Bool.bne_eq_xor] at hi ⊢
    rw [hi.1, hi.2.1, hi.2.2, Bool.xor_false, Bool.xor_false]
  -- If, say, `a` has a one bit at position `i`, then `a xor v` has a zero bit at position `i`, but
  -- the same bits as `a` in positions greater than `j`, so `a xor v < a`.
  rcases this with (h | h | h)
  on_goal 1 => left; rw [hbc]
  on_goal 2 => right; left; rw [hac]
  on_goal 3 => right; right; rw [hab]
  all_goals
    exact lt_of_testBit i (by
      -- Porting note: this was originally `simp [h, hi]`
      rw [Nat.testBit_xor, h, Bool.bne_eq_xor, Bool.true_xor,hi]
      rfl
    ) h fun j hj => by
      -- Porting note: this was originally `simp [hi' _ hj]`
      rw [Nat.testBit_xor, hi' _ hj, Bool.bne_eq_xor, Bool.xor_false_right, eq_self_iff_true]
      trivial
#align nat.lxor_trichotomy Nat.xor_trichotomy

theorem lt_xor_cases {a b c : ℕ} (h : a < xor b c) : xor a c < b ∨ xor a b < c :=
  (or_iff_right fun h' => (h.asymm h').elim).1 <| xor_trichotomy h.ne
#align nat.lt_lxor_cases Nat.lt_xor_cases

end Nat
