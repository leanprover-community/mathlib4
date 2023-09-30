/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
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
`lor'`, `land'` and `lxor'`, which are defined in core.

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

lemma div2_add_two (x) :
    div2 (x + 2) = div2 x + 1 := by
  simp only [div2_succ, bodd_succ, Bool.cond_not]
  cases bodd x <;> simp only [cond_false, cond_true]

lemma div2_eq_zero {x : ℕ} :
    div2 x = 0 → x = 0 ∨ x = 1 := by
  intro h
  rcases x with ⟨⟩ | ⟨⟩ | x
  · apply Or.inl rfl
  · apply Or.inr rfl
  · rw[div2_add_two] at h
    contradiction

section
variable {f : Bool → Bool → Bool}

lemma bitwise'_bit' {f : Bool → Bool → Bool} (a : Bool) (m : Nat) (b : Bool) (n : Nat)
    (ham : m = 0 → a = true) (hbn : n = 0 → b = true) :
    bitwise' f (bit a m) (bit b n) = bit (f a b) (bitwise' f m n) := by
  rw [bitwise', binaryRec_eq', binaryRec_eq']
  · apply Or.inr hbn
  · apply Or.inr ham

@[simp]
lemma bitwise_zero_left {m : Nat} : bitwise f 0 m = if f false true then m else 0 := by
  rfl

@[simp]
lemma bitwise_zero_right {n : Nat} : bitwise f n 0 = if f true false then n else 0 := by
  unfold bitwise
  simp only [ite_self, decide_False, Nat.zero_div, ite_true, ite_eq_right_iff]
  rintro ⟨⟩
  split_ifs <;> rfl

/-
  This theorem already exists as `bitwise'_zero_right` in `Mathlib.Init.Data.Nat.Bitwise`, but that
  one has the dreaded `f false false = false` assumption.
  The following proof does not need this assumption, but instead relies on `eq_mpr_eq_cast` from
  `Mathlib.Logic.Basic`. Since the other version exists in an `Init` file, we probably don't
  want to add this dependency there
-/
@[simp]
theorem bitwise'_zero_right' {m : Nat} :
    bitwise' f m 0 = if f true false then m else 0 := by
  unfold bitwise' binaryRec
  simp only [Bool.cond_eq_ite, eq_mpr_eq_cast, cast_eq, dite_eq_ite]
  split_ifs with hx <;> simp only [bit_decomp, binaryRec_zero, hx]

@[simp]
lemma bitwise_zero : bitwise f 0 0 = 0 := by
  simp only [bitwise_zero_right, ite_self]

@[simp]
lemma bitwise_succ {n m : Nat} :
    bitwise f (n + 1) (m + 1) =
    bitwise f ((n+1) / 2) ((m+1) / 2) + bitwise f ((n+1) / 2) ((m+1) / 2)
      + if f (!bodd n) (!bodd m) then 1 else 0 := by
  conv_lhs => { unfold bitwise }
  have mod_two_iff_bod x : ((x+1) % 2 = 1 : Bool) = !bodd x := by
    simp [mod_two_of_bodd, cond]; cases bodd x <;> rfl
  simp only [add_eq_zero_iff, and_false, ite_false, mod_two_iff_bod]
  split_ifs <;> rfl

@[simp]
lemma bitwise'_succ {n m : Nat} :
    bitwise' f (n + 1) (m + 1) =
    bitwise' f (div2 (n + 1)) (div2 (m + 1)) + bitwise' f (div2 (n + 1)) (div2 (m + 1))
      + if f (!bodd n) (!bodd m) then 1 else 0 := by
  conv_lhs => { rw [←bit_decomp (n + 1), ←bit_decomp (m + 1)] }
  simp only [bodd_succ, div2_succ, Bool.cond_eq_ite]
  rw [bitwise'_bit', bit]
  case ham =>
    rcases n with ⟨⟩|⟨⟩|n
    <;> simp only [div2_succ, cond, bodd_succ, Bool.not_not]
    cases bodd n <;> simp only [Bool.not_false, Bool.not_true, succ_ne_zero, IsEmpty.forall_iff,
      ite_true, ite_false]
  case hbn =>
    rcases m with ⟨⟩|⟨⟩|m
    <;> simp only [div2_succ, cond, bodd_succ, Bool.not_not]
    cases bodd m <;> simp only [Bool.not_false, Bool.not_true, succ_ne_zero, IsEmpty.forall_iff,
      ite_true, ite_false]
  simp [bit1, bit0]
  cases f (!bodd n) (!bodd m)
  <;> simp only [Bool.cond_eq_ite, ite_false, add_zero, ite_true]

lemma bitwise_eq_bitwise' (f) : bitwise f = bitwise' f := by
  funext x y
  induction' x using Nat.strongInductionOn with x ih generalizing y
  cases' x with x <;> cases' y with y
  · simp only [bitwise_zero, bitwise'_zero]
  · simp only [bitwise_zero_left, bitwise'_zero_left, Bool.cond_eq_ite]
  · simp only [bitwise_zero_right, bitwise'_zero_right', Bool.cond_eq_ite]
  · specialize ih ((x+1) / 2) (div_lt_self' ..)
    simp only [bitwise_succ, bitwise'_succ, div2_val, ih]

end

end Nat
