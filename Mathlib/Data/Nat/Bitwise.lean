/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Harun Khan, Abdalrhman M Mohamed

! This file was ported from Lean 3 source module data.nat.bitwise
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Lean.Elab.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Bitwise operations on natural numbers

In the first part of this file, we provide theorems for reasoning about natural numbers from their
bitwise properties. In particular, we reason about unsigned less than and bitwise addition.
In the second part of this file, we show properties of the bitwise operations
`lor'`, `land'` and `lxor'`, which are defined in core.

## Main results

* `mod_two_pow_succ` expresses a number modulo `2^(i+1)` in terms of its value modulo `2^i`.
* `eq_of_testBit_eq`: two natural numbers are equal if they have equal bits at every position.
* `exists_most_significant_bit`: if `n ≠ 0`, then there is some position `i` that contains the most
  significant `1`-bit of `n`.
* `lt_of_testBit`: if `n` and `m` are numbers and `i` is a position such that the `i`-th bit of
  of `n` is zero, the `i`-th bit of `m` is one, and all more significant bits are equal, then
  `n < m`.
* `of_lt_of_testBit`: if `x < y` then there exists a bit `i` such that
  `x.testBit i = false` and `y.testBit i = true`.
* `testBit_add`: the `testBit` of the sum of two bitvectors is equal to the bitwise
  xor of the `testBit` of the two bitvectors and the `testBit` of their carry.

## Notation

`^^`: boolean `xor`

## Future work

There is another way to express bitwise properties of natural number: `digits 2`. The two ways
should be connected.
Prove correctness of other bitwise operators: multiplication, negation, append etc.

## Keywords

bitwise, and, or, xor
-/

infix:30 " ^^ " => xor

open Function

namespace Nat

set_option linter.deprecated false

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

lemma bit_toNat (b : Bool) : bit b 0 = b.toNat := by cases' b <;> simp

@[simp] lemma testBit_bool : testBit b.toNat 0 = b := by cases' b <;> simp

lemma shiftr_mod_two_eq_testBit : Nat.shiftr n i % 2 = (n.testBit i).toNat := by
  simp [Nat.testBit, Nat.mod_two_of_bodd]

lemma div_add_mod_two_pow (m n : Nat) : n = 2^m * Nat.shiftr n m + n % (2^m) := by
  simp_rw [Nat.shiftr_eq_div_pow, Nat.div_add_mod]

lemma bit_lt_bit_iff : bit b n < bit b' m ↔ n < m ∨ (n = m ∧ b = false ∧ b' = true) := by
  cases' b <;> cases' b'
  <;> simp [le_iff_lt_or_eq]

/-- `n % 2^(i+1)` can be espressed in terms of `n % (2^i)`.
This is useful for induction on the most significant bit.-/
theorem mod_two_pow_succ (n i : Nat) : n % 2^(i+1) = 2^i * (n.testBit i).toNat + n % (2^i):= by
  have h1 := div_add_mod_two_pow i n
  have h3 := div_add_mod (Nat.shiftr n i) 2
  rw [← h3, mul_add, ← mul_assoc, ← pow_succ, shiftr_mod_two_eq_testBit] at h1
  have h : 2 ^ i * Bool.toNat (testBit n i) + n % 2 ^ i < 2 ^ (i + 1) := by
    rw [two_pow_succ]
    exact add_lt_add_of_le_of_lt (by simp [Bool.toNat_le_one (n.testBit i)]) (by simp [mod_lt])
  simp [(Nat.div_mod_unique (two_pow_pos (i + 1))).mpr ⟨add_rotate _ _ (n % (2^i)) ▸ h1.symm, h⟩]

theorem bodd_eq_bodd_iff : bodd n = bodd m ↔ n % 2 = m % 2 := by
  cases' hn : bodd n <;> cases' hm : bodd m
  <;> simp [mod_two_of_bodd, hn, hm]

theorem zero_of_testBit_eq_false {n : ℕ} (h : ∀ i, testBit n i = false) : n = 0 := by
  induction' n using Nat.binaryRec with b n hn
  · rfl
  · have : b = false := by simpa using h 0
    rw [this, bit_false, bit0_val, hn fun i => by rw [← h (i + 1), testBit_succ], mul_zero]
#align nat.zero_of_test_bit_eq_ff Nat.zero_of_testBit_eq_false

@[simp]
theorem zero_testBit (i : ℕ) : testBit 0 i = false := by simp only [testBit, shiftr_zero, bodd_zero]
#align nat.zero_test_bit Nat.zero_testBit

/-- The ith bit is the ith element of `n.bits`. -/
theorem testBit_eq_inth (n i : ℕ) : n.testBit i = n.bits.getI i := by
  induction' i with i ih generalizing n
  · simp [testBit, shiftr, bodd_eq_bits_head, List.getI_zero_eq_headI]
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
  suffices h' : n = m
  · rw [h', show b = b' by simpa using h 0]
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

theorem exists_most_significant_bit_of_lt (h: n < m) : ∃ i, Nat.testBit n i = false ∧
    Nat.testBit m i = true ∧ ∀ j, i < j → Nat.testBit m j = Nat.testBit n j := by
  induction' n using Nat.binaryRec with b n ih generalizing m
  · have ⟨i, _, _⟩ := exists_most_significant_bit (ne_of_lt h).symm
    use i; simpa [*]
  · rw [← bit_decomp m] at h ⊢
    cases' bit_lt_bit_iff.mp h with h3 h3
    · have ⟨i, iH⟩ := ih h3
      use Nat.succ i; simp only [testBit_succ]
      exact ⟨iH.1, iH.2.1, by
             intros j hj; cases' j with j
             · simp at hj
             · simp [testBit_succ, iH.2.2 j (by linarith)]⟩
    · use 0; simp only [testBit_zero]
      exact ⟨ h3.2.1, h3.2.2, by intros j hj
                                 have ⟨j', hj⟩ := exists_eq_add_of_le' hj
                                 simp[hj, testBit_succ, h3.1]⟩

theorem testBit_eq_false_of_lt (h: n < 2^i) : n.testBit i = false := by
  simp [testBit, shiftr_eq_div_pow, Nat.div_eq_zero h]

theorem lt_of_testBit_eq_true (h: n.testBit i = true) (hn : n < 2^w) : i < w := by
  by_contra'; simp [testBit_eq_false_of_lt (lt_of_lt_of_le hn (pow_le_pow (by decide) this))] at h

@[simp]
theorem testBit_two_pow_self (n : ℕ) : testBit (2 ^ n) n = true := by
  rw [testBit, shiftr_eq_div_pow, Nat.div_self (pow_pos (α := ℕ) zero_lt_two n), bodd_one]
#align nat.test_bit_two_pow_self Nat.testBit_two_pow_self

theorem testBit_two_pow_of_ne {n m : ℕ} (hm : n ≠ m) : testBit (2 ^ n) m = false := by
  rw [testBit, shiftr_eq_div_pow]
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

theorem testBit_two_pow_mul_add (h: i < w) : Nat.testBit (2^w * b + n) i = Nat.testBit n i := by
  simp only [testBit, shiftr_eq_div_pow, bodd_eq_bodd_iff]
  rw [Nat.add_div_of_dvd_right (by simp [Dvd.dvd.mul_right, pow_dvd_pow, le_of_lt h]), add_mod]
  have h1: (2^w / 2^i) % 2 = 0 := by
    rw [← Nat.dvd_iff_mod_eq_zero]
    use 2^(w - (i + 1))
    rw [Nat.pow_div (by linarith) (by decide), mul_comm, ← pow_succ 2 _, succ_eq_add_one]
    simp [← Nat.sub_add_comm, succ_le_of_lt h]
  simp [mul_comm, Nat.mul_div_assoc b (pow_dvd_pow 2 (le_of_lt h)), mul_mod, h1]

theorem testBit_two_pow_mul_toNat_add (h: n < 2^w) : Nat.testBit (2^w * b.toNat + n) w = b:= by
  simp only [Nat.testBit, Nat.shiftr_eq_div_pow]
  rw [Nat.add_div_of_dvd_right (Dvd.intro _ rfl), Nat.div_eq_zero h, add_zero]
  cases' b <;> simp

theorem testBit_two_pow_add (h : i < w) :
  Nat.testBit (2^w + n) i = Nat.testBit n i := mul_one (2^w) ▸ (testBit_two_pow_mul_add h)

theorem testBit_two_pow_add' (h : n < 2^w) : Nat.testBit (2^w + n) w = true :=
  mul_one (2^w) ▸ Bool.toNat_true ▸ (@testBit_two_pow_mul_toNat_add n w true h)

/-- Generic method to create a natural number by appending bits tail-recursively.
It takes a boolean function `f` on each bit and `z` the starting point and the number of bits `i`.
It is almost always specialized with `z = 0` and `i = w`; the length of the binary representation.
Note that `ofBits f z i = 2^i * z + ofBits f 0 i` which we prove next.
This is an alternative to using `List`. It will be used for bitadd, bitneg, bitmul etc.-/
def ofBits (f : Nat → Bool) (z : Nat) : Nat → Nat
  | 0 => z
  | i + 1 => ofBits f (z.bit (f i)) i

theorem ofBits_eq_pow_mul_add : ofBits f z i = 2^i * z + ofBits f 0 i := by
  induction' i with i ih generalizing z
  · simp [ofBits, bit_val]
  · simp only [ofBits, @ih (bit (f i) 0), @ih (bit (f i) z)]
    rw [bit_val, mul_add, ← mul_assoc, ← pow_succ]
    simp [bit_val, add_assoc]

theorem ofBits_lt : ofBits f 0 i < 2^i := by
  induction' i with i ih
  · simp [ofBits, bit_val, lt_succ, Bool.toNat_le_one]
  · simp only [ofBits]
    rw [ofBits_eq_pow_mul_add]
    cases' (f i) <;> simp [two_pow_succ, ih]; linarith

/-- The `ith` bit of `ofBits` is the function at `i`.
This is used extensively in the proof of each of the bitadd, bitneg, bitmul etc.-/
theorem testBit_ofBits (h1: i < j): (ofBits f 0 j).testBit i = f i := by
  induction' j, (pos_of_gt h1) using Nat.le_induction with j _ ih generalizing i
  · simp [lt_one_iff.1 h1, ofBits]
  · cases' lt_or_eq_of_le (lt_succ_iff.mp h1) with h1 h1
    · rw [← ih h1, ofBits, ofBits_eq_pow_mul_add, testBit_two_pow_mul_add h1]
    · rw [h1, ofBits, ofBits_eq_pow_mul_add, bit_toNat, testBit_two_pow_mul_toNat_add (ofBits_lt)]


/-! ### Unsigned Less Than-/

/-- Unsigned less than criterion (`n < m`) for natural numbers `n`, `m`
and `w` - the length of their binary representation.-/
def bitult (n m w : Nat) := loop n m (w - 1)
where
  loop (n m : Nat) : Nat →  Prop
    | 0     => ¬ n.testBit 0  ∧ m.testBit 0
    | i + 1 => (¬ n.testBit (i + 1) ∧ m.testBit (i + 1))
               ∨ (¬ (n.testBit (i + 1) ∧ ¬ m.testBit (i + 1)) ∧ loop n m i)

theorem bitult_of_ult (hm: m < 2^w) (h1: n < m) : bitult n m w := by
  have ⟨i, hi1, hi2, hi3⟩ := exists_most_significant_bit_of_lt h1
  suffices goal: ∀ j, i + 1 ≤ j → bitult n m j from goal w (lt_of_testBit_eq_true hi2 hm)
  apply le_induction
  · cases' i <;> simp [bitult, bitult.loop, hi1, hi2]
  · intros j hj ih
    have ⟨j', hj'⟩ := exists_eq_add_of_le' (le_of_add_le_right hj)
    simp only [bitult, bitult.loop, hj', succ_sub_one j'] at ih ⊢
    simp [ih, hi3 (j' + 1) (by linarith)]


/-! ### Addition-/

/-- Carry function at the `i`th bit for binary addition on `n` and `m`.-/
def addCarry (n m : Nat) : Nat → Bool
  | 0     => false
  | i + 1 => (n.testBit i && m.testBit i) || ((n.testBit i ^^ m.testBit i) && addCarry n m i)

/-- Binary addition is `ofBits` specialized with the right function on the bits `f`.-/
@[simp] def bitadd (n m i : Nat) :=
  ofBits (λ j => (n.testBit j ^^ m.testBit j) ^^ addCarry n m j) 0 i

lemma addCarry_def (n m i : Nat) : (addCarry n m (i + 1)).toNat =
    ((Nat.testBit n i && Nat.testBit m i) ||
    ((Nat.testBit n i ^^ Nat.testBit m i) && addCarry n m i)).toNat := by
  simp [addCarry]

lemma bitadd_add_two_pow_mul_addCarry : n % (2^i) + m % (2^i) =
  bitadd n m i + 2^i * (addCarry n m i).toNat := by
  induction' i with i hi
  · simp [mod_one, ofBits, addCarry]
  · rw [mod_two_pow_succ n, mod_two_pow_succ m]
    rw [add_assoc, add_comm _ (m % 2^i), ← add_assoc (n % 2^i)]
    rw [hi, addCarry_def n m i, two_pow_succ i]
    cases' hn : Nat.testBit n i <;> cases' hm : Nat.testBit m i
    <;> cases' hc : addCarry n m i
    <;> simp [Bool.toNat, @ofBits_eq_pow_mul_add _ 1 i, two_pow_succ, hn, hm, hc, ofBits]
    <;> ring

theorem bitadd_eq_add : bitadd n m i = (n + m) % 2^i := by
  rw [Nat.add_mod, bitadd_add_two_pow_mul_addCarry]
  cases' i with i i
  · simp [mod_one, ofBits]
  · simp [bitadd, Nat.mod_eq_of_lt ofBits_lt]

theorem testBit_add : (n + m).testBit i = ((n.testBit i ^^ m.testBit i) ^^ addCarry n m i):= by
  have := lt_of_lt_of_le
          (lt_trans (lt_two_pow (n + m)) (pow_lt_pow_succ (by decide) (n + m)))
          (pow_le_pow_of_le_right (show 0 < 2 by decide) (@le_add_self _ _ _ i))
  rw [← Nat.mod_eq_of_lt this, ← add_assoc, ← bitadd_eq_add]
  simp [testBit_ofBits (show i < i + (n + m) + 1 by linarith)]

/-- If `f` is a commutative operation on bools such that `f false false = false`, then `bitwise f`
    is also commutative. -/
theorem bitwise'_comm {f : Bool → Bool → Bool} (hf : ∀ b b', f b b' = f b' b)
    (hf' : f false false = false) (n m : ℕ) : bitwise' f n m = bitwise' f m n :=
  suffices bitwise' f = swap (bitwise' f) by conv_lhs => rw [this]
  calc
    bitwise' f = bitwise' (swap f) := congr_arg _ <| funext fun _ => funext <| hf _
    _ = swap (bitwise' f) := bitwise'_swap hf'
#align nat.bitwise_comm Nat.bitwise'_comm

theorem lor'_comm (n m : ℕ) : lor' n m = lor' m n :=
  bitwise'_comm Bool.or_comm rfl n m
#align nat.lor_comm Nat.lor'_comm

theorem land'_comm (n m : ℕ) : land' n m = land' m n :=
  bitwise'_comm Bool.and_comm rfl n m
#align nat.land_comm Nat.land'_comm

theorem lxor'_comm (n m : ℕ) : lxor' n m = lxor' m n :=
  bitwise'_comm Bool.xor_comm rfl n m
#align nat.lxor_comm Nat.lxor'_comm

@[simp]
theorem zero_lxor' (n : ℕ) : lxor' 0 n = n := by
 simp only [Bool.xor_false_left, Nat.bitwise'_zero_left, eq_self_iff_true, Bool.cond_true, lxor']
#align nat.zero_lxor Nat.zero_lxor'

@[simp]
theorem lxor'_zero (n : ℕ) : lxor' n 0 = n := by simp [lxor']
#align nat.lxor_zero Nat.lxor'_zero

@[simp]
theorem zero_land' (n : ℕ) : land' 0 n = 0 := by
  simp only [Nat.bitwise'_zero_left, Bool.cond_false, eq_self_iff_true, land', Bool.false_and]
#align nat.zero_land Nat.zero_land'

@[simp]
theorem land'_zero (n : ℕ) : land' n 0 = 0 := by simp [land']
#align nat.land_zero Nat.land'_zero

@[simp]
theorem zero_lor' (n : ℕ) : lor' 0 n = n := by --simp [lor']
  simp only [Nat.bitwise'_zero_left, Bool.false_or, eq_self_iff_true, Bool.cond_true, Nat.lor']
#align nat.zero_lor Nat.zero_lor'

@[simp]
theorem lor'_zero (n : ℕ) : lor' n 0 = n := by simp [lor']
#align nat.lor_zero Nat.lor'_zero


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
  <;> simp [hn, Bool.or_assoc, Bool.and_assoc]))

theorem lxor'_assoc (n m k : ℕ) : lxor' (lxor' n m) k = lxor' n (lxor' m k) := by bitwise_assoc_tac
#align nat.lxor_assoc Nat.lxor'_assoc

theorem land'_assoc (n m k : ℕ) : land' (land' n m) k = land' n (land' m k) := by bitwise_assoc_tac
#align nat.land_assoc Nat.land'_assoc

theorem lor'_assoc (n m k : ℕ) : lor' (lor' n m) k = lor' n (lor' m k) := by bitwise_assoc_tac
#align nat.lor_assoc Nat.lor'_assoc

@[simp]
theorem lxor'_self (n : ℕ) : lxor' n n = 0 :=
  zero_of_testBit_eq_false fun i => by simp
#align nat.lxor_self Nat.lxor'_self

-- These lemmas match `mul_inv_cancel_right` and `mul_inv_cancel_left`.
theorem lxor_cancel_right (n m : ℕ) : lxor' (lxor' m n) n = m := by
  rw [lxor'_assoc, lxor'_self, lxor'_zero]
#align nat.lxor_cancel_right Nat.lxor_cancel_right

theorem lxor'_cancel_left (n m : ℕ) : lxor' n (lxor' n m) = m := by
  rw [← lxor'_assoc, lxor'_self, zero_lxor']
#align nat.lxor_cancel_left Nat.lxor'_cancel_left

theorem lxor'_right_injective {n : ℕ} : Function.Injective (lxor' n) := fun m m' h => by
  rw [← lxor'_cancel_left n m, ← lxor'_cancel_left n m', h]
#align nat.lxor_right_injective Nat.lxor'_right_injective

theorem lxor'_left_injective {n : ℕ} : Function.Injective fun m => lxor' m n :=
  fun m m' (h : lxor' m n = lxor' m' n) => by
  rw [← lxor_cancel_right n m, ← lxor_cancel_right n m', h]
#align nat.lxor_left_injective Nat.lxor'_left_injective

@[simp]
theorem lxor'_right_inj {n m m' : ℕ} : lxor' n m = lxor' n m' ↔ m = m' :=
  lxor'_right_injective.eq_iff
#align nat.lxor_right_inj Nat.lxor'_right_inj

@[simp]
theorem lxor'_left_inj {n m m' : ℕ} : lxor' m n = lxor' m' n ↔ m = m' :=
  lxor'_left_injective.eq_iff
#align nat.lxor_left_inj Nat.lxor'_left_inj

@[simp]
theorem lxor'_eq_zero {n m : ℕ} : lxor' n m = 0 ↔ n = m := by
  rw [← lxor'_self n, lxor'_right_inj, eq_comm]
#align nat.lxor_eq_zero Nat.lxor'_eq_zero

theorem lxor'_ne_zero {n m : ℕ} : lxor' n m ≠ 0 ↔ n ≠ m :=
  lxor'_eq_zero.not
#align nat.lxor_ne_zero Nat.lxor'_ne_zero

theorem lxor'_trichotomy {a b c : ℕ} (h : a ≠ lxor' b c) :
    lxor' b c < a ∨ lxor' a c < b ∨ lxor' a b < c := by
  set v := lxor' a (lxor' b c) with hv
  -- The xor of any two of `a`, `b`, `c` is the xor of `v` and the third.
  have hab : lxor' a b = lxor' c v := by
    rw [hv]
    conv_rhs =>
      rw [lxor'_comm]
      simp [lxor'_assoc]
  have hac : lxor' a c = lxor' b v := by
    rw [hv]
    conv_rhs =>
      right
      rw [← lxor'_comm]
    rw [← lxor'_assoc, ← lxor'_assoc, lxor'_self, zero_lxor', lxor'_comm]
  have hbc : lxor' b c = lxor' a v := by simp [hv, ← lxor'_assoc]
  -- If `i` is the position of the most significant bit of `v`, then at least one of `a`, `b`, `c`
  -- has a one bit at position `i`.
  obtain ⟨i, ⟨hi, hi'⟩⟩ := exists_most_significant_bit (lxor'_ne_zero.2 h)
  have : testBit a i = true ∨ testBit b i = true ∨ testBit c i = true := by
    contrapose! hi
    simp only [Bool.eq_false_eq_not_eq_true, Ne, testBit_lxor'] at hi ⊢
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
      rw [Nat.testBit_lxor', h, Bool.true_xor,hi]
      rfl
    ) h fun j hj => by
      -- Porting note: this was originally `simp [hi' _ hj]`
      rw [Nat.testBit_lxor', hi' _ hj, Bool.xor_false_right, eq_self_iff_true]
      trivial
#align nat.lxor_trichotomy Nat.lxor'_trichotomy

theorem lt_lxor'_cases {a b c : ℕ} (h : a < lxor' b c) : lxor' a c < b ∨ lxor' a b < c :=
  (or_iff_right fun h' => (h.asymm h').elim).1 <| lxor'_trichotomy h.ne
#align nat.lt_lxor_cases Nat.lt_lxor'_cases

end Nat
