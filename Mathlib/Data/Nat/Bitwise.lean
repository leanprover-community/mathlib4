/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Alex Keizer
-/
import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bits
import Mathlib.Algebra.Ring.Nat
import Mathlib.Order.Basic
import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.Common

#align_import data.nat.bitwise from "leanprover-community/mathlib"@"6afc9b06856ad973f6a2619e3e8a0a8d537a58f2"

/-!
# Bitwise operations on natural numbers

In the first half of this file, we provide theorems for reasoning about natural numbers from their
bitwise properties. In the second half of this file, we show properties of the bitwise operations
`lor`, `land` and `xor`, which are defined in core.

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
lemma bitwise_zero_left (m : Nat) : bitwise f 0 m = if f false true then m else 0 := by
  simp [bitwise]
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

lemma bitwise_of_ne_zero {n m : Nat} (hn : n ≠ 0) (hm : m ≠ 0) :
    bitwise f n m = bit (f (bodd n) (bodd m)) (bitwise f (n / 2) (m / 2)) := by
  conv_lhs => unfold bitwise
  have mod_two_iff_bod x : (x % 2 = 1 : Bool) = bodd x := by
    simp only [mod_two_of_bodd, cond]; cases bodd x <;> rfl
  simp only [hn, hm, mod_two_iff_bod, ite_false, bit, bit1, bit0, Bool.cond_eq_ite]
  split_ifs <;> rfl

theorem binaryRec_of_ne_zero {C : Nat → Sort*} (z : C 0) (f : ∀ b n, C n → C (bit b n)) {n}
    (h : n ≠ 0) :
    binaryRec z f n = bit_decomp n ▸ f (bodd n) (div2 n) (binaryRec z f (div2 n)) := by
  rw [Eq.rec_eq_cast]
  rw [binaryRec]
  dsimp only
  rw [dif_neg h, eq_mpr_eq_cast]

@[simp]
lemma bitwise_bit {f : Bool → Bool → Bool} (h : f false false = false := by rfl) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  conv_lhs => unfold bitwise
  #adaptation_note /-- nightly-2024-03-16: simp was
  -- simp (config := { unfoldPartialApp := true }) only [bit, bit1, bit0, Bool.cond_eq_ite] -/
  simp only [bit, ite_apply, bit1, bit0, Bool.cond_eq_ite]
  have h1 x :     (x + x) % 2 = 0 := by rw [← two_mul, mul_comm]; apply mul_mod_left
  have h2 x : (x + x + 1) % 2 = 1 := by rw [← two_mul, add_comm]; apply add_mul_mod_self_left
  have h3 x :     (x + x) / 2 = x := by omega
  have h4 x : (x + x + 1) / 2 = x := by rw [← two_mul, add_comm]; simp [add_mul_div_left]
  cases a <;> cases b <;> simp [h1, h2, h3, h4] <;> split_ifs
    <;> simp_all (config := {decide := true})
#align nat.bitwise_bit Nat.bitwise_bit

lemma bit_mod_two (a : Bool) (x : ℕ) :
    bit a x % 2 = if a then 1 else 0 := by
  #adaptation_note /-- nightly-2024-03-16: simp was
  -- simp (config := { unfoldPartialApp := true }) only [bit, bit1, bit0, ← mul_two,
  --   Bool.cond_eq_ite] -/
  simp only [bit, ite_apply, bit1, bit0, ← mul_two, Bool.cond_eq_ite]
  split_ifs <;> simp [Nat.add_mod]

@[simp]
lemma bit_mod_two_eq_zero_iff (a x) :
    bit a x % 2 = 0 ↔ !a := by
  rw [bit_mod_two]; split_ifs <;> simp_all

@[simp]
lemma bit_mod_two_eq_one_iff (a x) :
    bit a x % 2 = 1 ↔ a := by
  rw [bit_mod_two]; split_ifs <;> simp_all

@[simp]
theorem lor_bit : ∀ a m b n, bit a m ||| bit b n = bit (a || b) (m ||| n) :=
  bitwise_bit
#align nat.lor_bit Nat.lor_bit

@[simp]
theorem land_bit : ∀ a m b n, bit a m &&& bit b n = bit (a && b) (m &&& n) :=
  bitwise_bit
#align nat.land_bit Nat.land_bit

@[simp]
theorem ldiff_bit : ∀ a m b n, ldiff (bit a m) (bit b n) = bit (a && not b) (ldiff m n) :=
  bitwise_bit
#align nat.ldiff_bit Nat.ldiff_bit

@[simp]
theorem xor_bit : ∀ a m b n, bit a m ^^^ bit b n = bit (bne a b) (m ^^^ n) :=
  bitwise_bit
#align nat.lxor_bit Nat.xor_bit

attribute [simp] Nat.testBit_bitwise
#align nat.test_bit_bitwise Nat.testBit_bitwise

theorem testBit_lor : ∀ m n k, testBit (m ||| n) k = (testBit m k || testBit n k) :=
  testBit_bitwise rfl
#align nat.test_bit_lor Nat.testBit_lor

theorem testBit_land : ∀ m n k, testBit (m &&& n) k = (testBit m k && testBit n k) :=
  testBit_bitwise rfl
#align nat.test_bit_land Nat.testBit_land

@[simp]
theorem testBit_ldiff : ∀ m n k, testBit (ldiff m n) k = (testBit m k && not (testBit n k)) :=
  testBit_bitwise rfl
#align nat.test_bit_ldiff Nat.testBit_ldiff

attribute [simp] testBit_xor
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

theorem bit_ne_zero_iff {n : ℕ} {b : Bool} : n.bit b ≠ 0 ↔ n = 0 → b = true := by
  simpa only [not_and, Bool.not_eq_false] using (@bit_eq_zero n b).not

/-- An alternative for `bitwise_bit` which replaces the `f false false = false` assumption
with assumptions that neither `bit a m` nor `bit b n` are `0`
(albeit, phrased as the implications `m = 0 → a = true` and `n = 0 → b = true`) -/
lemma bitwise_bit' {f : Bool → Bool → Bool} (a : Bool) (m : Nat) (b : Bool) (n : Nat)
    (ham : m = 0 → a = true) (hbn : n = 0 → b = true) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) := by
  conv_lhs => unfold bitwise
  rw [← bit_ne_zero_iff] at ham hbn
  simp only [ham, hbn, bit_mod_two_eq_one_iff, Bool.decide_coe, ← div2_val, div2_bit, ne_eq,
    ite_false]
  conv_rhs => simp only [bit, bit1, bit0, Bool.cond_eq_ite]
  split_ifs with hf <;> rfl

lemma bitwise_eq_binaryRec (f : Bool → Bool → Bool) :
    bitwise f =
    binaryRec (fun n => cond (f false true) n 0) fun a m Ia =>
      binaryRec (cond (f true false) (bit a m) 0) fun b n _ => bit (f a b) (Ia n) := by
  funext x y
  induction x using binaryRec' generalizing y with
  | z => simp only [bitwise_zero_left, binaryRec_zero, Bool.cond_eq_ite]
  | f xb x hxb ih =>
    rw [← bit_ne_zero_iff] at hxb
    simp_rw [binaryRec_of_ne_zero _ _ hxb, bodd_bit, div2_bit, eq_rec_constant]
    induction y using binaryRec' with
    | z => simp only [bitwise_zero_right, binaryRec_zero, Bool.cond_eq_ite]
    | f yb y hyb =>
      rw [← bit_ne_zero_iff] at hyb
      simp_rw [binaryRec_of_ne_zero _ _ hyb, bitwise_of_ne_zero hxb hyb, bodd_bit, ← div2_val,
        div2_bit, eq_rec_constant, ih]

theorem zero_of_testBit_eq_false {n : ℕ} (h : ∀ i, testBit n i = false) : n = 0 := by
  induction' n using Nat.binaryRec with b n hn
  · rfl
  · have : b = false := by simpa using h 0
    rw [this, bit_false, bit0_val, hn fun i => by rw [← h (i + 1), testBit_bit_succ], mul_zero]
#align nat.zero_of_test_bit_eq_ff Nat.zero_of_testBit_eq_false

theorem testBit_eq_false_of_lt {n i} (h : n < 2 ^ i) : n.testBit i = false := by
  simp [testBit, shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

#align nat.zero_test_bit Nat.zero_testBit

/-- The ith bit is the ith element of `n.bits`. -/
theorem testBit_eq_inth (n i : ℕ) : n.testBit i = n.bits.getI i := by
  induction' i with i ih generalizing n
  · simp only [testBit, zero_eq, shiftRight_zero, and_one_is_mod, mod_two_of_bodd,
      bodd_eq_bits_head, List.getI_zero_eq_headI]
    cases List.headI (bits n) <;> rfl
  conv_lhs => rw [← bit_decomp n]
  rw [testBit_bit_succ, ih n.div2, div2_bits_eq_tail]
  cases n.bits <;> simp
#align nat.test_bit_eq_inth Nat.testBit_eq_inth

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
    refine ⟨0, ⟨by rw [testBit_bit_zero], fun j hj => ?_⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (ne_of_gt hj)
    rw [testBit_bit_succ, zero_testBit]
  · obtain ⟨k, ⟨hk, hk'⟩⟩ := hn h'
    refine ⟨k + 1, ⟨by rw [testBit_bit_succ, hk], fun j hj => ?_⟩⟩
    obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (show j ≠ 0 by intro x; subst x; simp at hj)
    exact (testBit_bit_succ _ _ _).trans (hk' _ (lt_of_succ_lt_succ hj))
#align nat.exists_most_significant_bit Nat.exists_most_significant_bit

theorem lt_of_testBit {n m : ℕ} (i : ℕ) (hn : testBit n i = false) (hm : testBit m i = true)
    (hnm : ∀ j, i < j → testBit n j = testBit m j) : n < m := by
  induction' n using Nat.binaryRec with b n hn' generalizing i m
  · rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp at hm
  induction' m using Nat.binaryRec with b' m hm' generalizing i
  · exact False.elim (Bool.false_ne_true ((zero_testBit i).symm.trans hm))
  by_cases hi : i = 0
  · subst hi
    simp only [testBit_bit_zero] at hn hm
    have : n = m :=
      eq_of_testBit_eq fun i => by convert hnm (i + 1) (Nat.zero_lt_succ _) using 1
      <;> rw [testBit_bit_succ]
    rw [hn, hm, this, bit_false, bit_true, bit0_val, bit1_val]
    exact Nat.lt_succ_self _
  · obtain ⟨i', rfl⟩ := exists_eq_succ_of_ne_zero hi
    simp only [testBit_bit_succ] at hn hm
    have := hn' _ hn hm fun j hj => by
      convert hnm j.succ (succ_lt_succ hj) using 1 <;> rw [testBit_bit_succ]
    have this' : 2 * n < 2 * m := Nat.mul_lt_mul' (le_refl _) this Nat.two_pos
    cases b <;> cases b'
    <;> simp only [bit_false, bit_true, bit0_val n, bit1_val n, bit0_val m, bit1_val m]
    · exact this'
    · exact Nat.lt_add_right 1 this'
    · calc
        2 * n + 1 < 2 * n + 2 := lt.base _
        _ ≤ 2 * m := mul_le_mul_left 2 this
    · exact Nat.succ_lt_succ this'
#align nat.lt_of_test_bit Nat.lt_of_testBit

@[simp]
theorem testBit_two_pow_self (n : ℕ) : testBit (2 ^ n) n = true := by
  rw [testBit, shiftRight_eq_div_pow, Nat.div_self (Nat.pow_pos Nat.zero_lt_two)]
  simp
#align nat.test_bit_two_pow_self Nat.testBit_two_pow_self

theorem testBit_two_pow_of_ne {n m : ℕ} (hm : n ≠ m) : testBit (2 ^ n) m = false := by
  rw [testBit, shiftRight_eq_div_pow]
  cases' hm.lt_or_lt with hm hm
  · rw [Nat.div_eq_of_lt]
    · simp
    · exact Nat.pow_lt_pow_right Nat.one_lt_two hm
  · rw [Nat.pow_div hm.le Nat.two_pos, ← Nat.sub_add_cancel (succ_le_of_lt <| Nat.sub_pos_of_lt hm)]
    -- Porting note: XXX why does this make it work?
    rw [(rfl : succ 0 = 1)]
    simp [pow_succ, and_one_is_mod, mul_mod_left]
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

theorem lor_comm (n m : ℕ) : n ||| m = m ||| n :=
  bitwise_comm Bool.or_comm n m
#align nat.lor_comm Nat.lor_comm

theorem land_comm (n m : ℕ) : n &&& m = m &&& n :=
  bitwise_comm Bool.and_comm n m
#align nat.land_comm Nat.land_comm

protected lemma xor_comm (n m : ℕ) : n ^^^ m = m ^^^ n :=
  bitwise_comm (Bool.bne_eq_xor ▸ Bool.xor_comm) n m
#align nat.lxor_comm Nat.xor_comm

lemma and_two_pow (n i : ℕ) : n &&& 2 ^ i = (n.testBit i).toNat * 2 ^ i := by
  refine eq_of_testBit_eq fun j => ?_
  obtain rfl | hij := Decidable.eq_or_ne i j <;> cases' h : n.testBit i
  · simp [h]
  · simp [h]
  · simp [h, testBit_two_pow_of_ne hij]
  · simp [h, testBit_two_pow_of_ne hij]

lemma two_pow_and (n i : ℕ) : 2 ^ i &&& n = 2 ^ i * (n.testBit i).toNat := by
  rw [mul_comm, land_comm, and_two_pow]

@[simp]
theorem zero_xor (n : ℕ) : 0 ^^^ n = n := by simp [HXor.hXor, Xor.xor, xor]
#align nat.zero_lxor Nat.zero_xor

@[simp]
theorem xor_zero (n : ℕ) : n ^^^ 0 = n := by simp [HXor.hXor, Xor.xor, xor]
#align nat.lxor_zero Nat.xor_zero

#align nat.zero_land Nat.zero_and
#align nat.land_zero Nat.and_zero
#align nat.zero_lor Nat.zero_or
#align nat.lor_zero Nat.or_zero


/-- Proving associativity of bitwise operations in general essentially boils down to a huge case
    distinction, so it is shorter to use this tactic instead of proving it in the general case. -/
macro "bitwise_assoc_tac" : tactic => set_option hygiene false in `(tactic| (
  induction' n using Nat.binaryRec with b n hn generalizing m k
  · simp
  induction' m using Nat.binaryRec with b' m hm
  · simp
  induction' k using Nat.binaryRec with b'' k hk
  -- porting note (#10745): was `simp [hn]`
  -- This is necessary because these are simp lemmas in mathlib
  <;> simp [hn, Bool.or_assoc, Bool.and_assoc, Bool.bne_eq_xor]))

protected lemma xor_assoc (n m k : ℕ) : (n ^^^ m) ^^^ k = n ^^^ (m ^^^ k) := by bitwise_assoc_tac
#align nat.lxor_assoc Nat.xor_assoc

theorem land_assoc (n m k : ℕ) : (n &&& m) &&& k = n &&& (m &&& k) := by bitwise_assoc_tac
#align nat.land_assoc Nat.land_assoc

theorem lor_assoc (n m k : ℕ) : (n ||| m) ||| k = n ||| (m ||| k) := by bitwise_assoc_tac
#align nat.lor_assoc Nat.lor_assoc

@[simp]
theorem xor_self (n : ℕ) : n ^^^ n = 0 :=
  zero_of_testBit_eq_false fun i => by simp
#align nat.lxor_self Nat.xor_self

-- These lemmas match `mul_inv_cancel_right` and `mul_inv_cancel_left`.
theorem xor_cancel_right (n m : ℕ) : (m ^^^ n) ^^^ n = m := by
  rw [Nat.xor_assoc, xor_self, xor_zero]
#align nat.lxor_cancel_right Nat.xor_cancel_right

theorem xor_cancel_left (n m : ℕ) : n ^^^ (n ^^^ m) = m := by
  rw [← Nat.xor_assoc, xor_self, zero_xor]
#align nat.lxor_cancel_left Nat.xor_cancel_left

theorem xor_right_injective {n : ℕ} : Function.Injective (HXor.hXor n : ℕ → ℕ) := fun m m' h => by
  rw [← xor_cancel_left n m, ← xor_cancel_left n m', h]
#align nat.lxor_right_injective Nat.xor_right_injective

theorem xor_left_injective {n : ℕ} : Function.Injective fun m => m ^^^ n :=
  fun m m' (h : m ^^^ n = m' ^^^ n) => by
  rw [← xor_cancel_right n m, ← xor_cancel_right n m', h]
#align nat.lxor_left_injective Nat.xor_left_injective

@[simp]
theorem xor_right_inj {n m m' : ℕ} : n ^^^ m = n ^^^ m' ↔ m = m' :=
  xor_right_injective.eq_iff
#align nat.lxor_right_inj Nat.xor_right_inj

@[simp]
theorem xor_left_inj {n m m' : ℕ} : m ^^^ n = m' ^^^ n ↔ m = m' :=
  xor_left_injective.eq_iff
#align nat.lxor_left_inj Nat.xor_left_inj

@[simp]
theorem xor_eq_zero {n m : ℕ} : n ^^^ m = 0 ↔ n = m := by
  rw [← xor_self n, xor_right_inj, eq_comm]
#align nat.lxor_eq_zero Nat.xor_eq_zero

theorem xor_ne_zero {n m : ℕ} : n ^^^ m ≠ 0 ↔ n ≠ m :=
  xor_eq_zero.not
#align nat.lxor_ne_zero Nat.xor_ne_zero

theorem xor_trichotomy {a b c : ℕ} (h : a ≠ b ^^^ c) :
    b ^^^ c < a ∨ a ^^^ c < b ∨ a ^^^ b < c := by
  set v := a ^^^ (b ^^^ c) with hv
  -- The xor of any two of `a`, `b`, `c` is the xor of `v` and the third.
  have hab : a ^^^ b = c ^^^ v := by
    rw [hv]
    conv_rhs =>
      rw [Nat.xor_comm]
      simp [Nat.xor_assoc]
  have hac : a ^^^ c = b ^^^ v := by
    rw [hv]
    conv_rhs =>
      right
      rw [← Nat.xor_comm]
    rw [← Nat.xor_assoc, ← Nat.xor_assoc, xor_self, zero_xor, Nat.xor_comm]
  have hbc : b ^^^ c = a ^^^ v := by simp [hv, ← Nat.xor_assoc]
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
    exact lt_of_testBit i (by simp [h, hi]) h fun j hj => by simp [hi' _ hj]
#align nat.lxor_trichotomy Nat.xor_trichotomy

theorem lt_xor_cases {a b c : ℕ} (h : a < b ^^^ c) : a ^^^ c < b ∨ a ^^^ b < c :=
  (or_iff_right fun h' => (h.asymm h').elim).1 <| xor_trichotomy h.ne
#align nat.lt_lxor_cases Nat.lt_xor_cases

@[simp] theorem bit_lt_two_pow_succ_iff {b x n} : bit b x < 2 ^ (n + 1) ↔ x < 2 ^ n := by
  cases b <;> simp [bit0, bit1] <;> omega

/-- If `x` and `y` fit within `n` bits, then the result of any bitwise operation on `x` and `y` also
fits within `n` bits -/
theorem bitwise_lt {f x y n} (hx : x < 2 ^ n) (hy : y < 2 ^ n) :
    bitwise f x y < 2 ^ n := by
  induction x using Nat.binaryRec' generalizing n y with
  | z =>
    simp only [bitwise_zero_left]
    split <;> assumption
  | @f bx nx hnx ih =>
    cases y using Nat.binaryRec' with
    | z =>
      simp only [bitwise_zero_right]
      split <;> assumption
    | f «by» ny hny =>
      rw [bitwise_bit' _ _ _ _ hnx hny]
      cases n <;> simp_all

lemma shiftLeft_lt {x n m : ℕ} (h : x < 2 ^ n) : x <<< m < 2 ^ (n + m) := by
  simp only [Nat.pow_add, shiftLeft_eq, Nat.mul_lt_mul_right (Nat.two_pow_pos _), h]

/-- Note that the LHS is the expression used within `Std.BitVec.append`, hence the name. -/
lemma append_lt {x y n m} (hx : x < 2 ^ n) (hy : y < 2 ^ m) : y <<< n ||| x < 2 ^ (n + m) := by
  apply bitwise_lt
  · rw [add_comm]; apply shiftLeft_lt hy
  · apply lt_of_lt_of_le hx <| Nat.pow_le_pow_right (le_succ _) (le_add_right _ _)

end Nat
