/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala, Yuyang Zhao
-/

/-!
# Binary recursion on `Nat`

This file defines binary recursion on `Nat`.

## Main results
* `Nat.binaryRec`: A recursion principle for `bit` representations of natural numbers.
* `Nat.binaryRec'`: The same as `binaryRec`, but the induction step can assume that if `n=0`,
  the bit being appended is `true`.
* `Nat.binaryRecFromOne`: The same as `binaryRec`, but special casing both 0 and 1 as base cases.
-/

universe u

namespace Nat

/-- `bit b` appends the digit `b` to the little end of the binary representation of
  its natural number input. -/
def bit (b : Bool) (n : Nat) : Nat :=
  cond b (n + n + 1) (n + n)

theorem shiftRight_one (n) : n >>> 1 = n / 2 := rfl

theorem bit_testBit_zero_shiftRight_one (n : Nat) : bit (n.testBit 0) (n >>> 1) = n := by
  simp only [bit, testBit_zero]
  cases mod_two_eq_zero_or_one n with | _ h =>
    simpa [h, shiftRight_one] using Eq.trans (by simp [h, Nat.two_mul]) (Nat.div_add_mod n 2)

theorem bit_eq_zero_iff {n : Nat} {b : Bool} : bit b n = 0 ↔ n = 0 ∧ b = false := by
  cases n <;> cases b <;> simp [bit, ← Nat.add_assoc]

/-- For a predicate `C : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for any given natural number. -/
@[inline]
def bitCasesOn {C : Nat → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n :=
  -- `1 &&& n != 0` is faster than `n.testBit 0`. This may change when we have faster `testBit`.
  let x := h (1 &&& n != 0) (n >>> 1)
  -- `congrArg C _` is `rfl` in non-dependent case
  congrArg C n.bit_testBit_zero_shiftRight_one ▸ x

/-- A recursion principle for `bit` representations of natural numbers.
  For a predicate `C : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for all natural numbers. -/
@[elab_as_elim, specialize]
def binaryRec {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) (n : Nat) : C n :=
  if n0 : n = 0 then congrArg C n0 ▸ z
  else
    let x := f (1 &&& n != 0) (n >>> 1) (binaryRec z f (n >>> 1))
    congrArg C n.bit_testBit_zero_shiftRight_one ▸ x
decreasing_by exact bitwise_rec_lemma n0

/-- The same as `binaryRec`, but the induction step can assume that if `n=0`,
  the bit being appended is `true`-/
@[elab_as_elim, specialize]
def binaryRec' {C : Nat → Sort u} (z : C 0)
    (f : ∀ b n, (n = 0 → b = true) → C n → C (bit b n)) : ∀ n, C n :=
  binaryRec z fun b n ih =>
    if h : n = 0 → b = true then f b n h ih
    else
      have : bit b n = 0 := by
        rw [bit_eq_zero_iff]
        cases n <;> cases b <;> simp at h <;> simp [h]
      congrArg C this ▸ z

/-- The same as `binaryRec`, but special casing both 0 and 1 as base cases -/
@[elab_as_elim, specialize]
def binaryRecFromOne {C : Nat → Sort u} (z₀ : C 0) (z₁ : C 1)
    (f : ∀ b n, n ≠ 0 → C n → C (bit b n)) : ∀ n, C n :=
  binaryRec' z₀ fun b n h ih =>
    if h' : n = 0 then
      have : bit b n = bit true 0 := by
        rw [h', h h']
      congrArg C this ▸ z₁
    else f b n h' ih

theorem bit_val (b n) : bit b n = 2 * n + b.toNat := by
  rw [Nat.mul_comm]
  induction b with
  | false => exact congrArg (· + n) n.zero_add.symm
  | true => exact congrArg (· + n + 1) n.zero_add.symm

@[simp]
theorem bit_div_two (b n) : bit b n / 2 = n := by
  rw [bit_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add]
  · cases b <;> decide
  · decide

@[simp]
theorem bit_mod_two (b n) : bit b n % 2 = b.toNat := by
  cases b <;> simp [bit_val, mul_add_mod]

@[simp] theorem bit_shiftRight_one (b n) : bit b n >>> 1 = n :=
  bit_div_two b n

theorem bit_testBit_zero (b n) : (bit b n).testBit 0 = b := by
  simp

@[simp]
theorem bitCasesOn_bit {C : Nat → Sort u} (h : ∀ b n, C (bit b n)) (b : Bool) (n : Nat) :
    bitCasesOn (bit b n) h = h b n := by
  change congrArg C (bit b n).bit_testBit_zero_shiftRight_one ▸ h _ _ = h b n
  generalize congrArg C (bit b n).bit_testBit_zero_shiftRight_one = e; revert e
  rw [bit_testBit_zero, bit_shiftRight_one]
  intros; rfl

unseal binaryRec in
@[simp]
theorem binaryRec_zero {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) :
    binaryRec z f 0 = z :=
  rfl

theorem binaryRec_eq {C : Nat → Sort u} {z : C 0} {f : ∀ b n, C n → C (bit b n)} (b n)
    (h : f false 0 z = z ∨ (n = 0 → b = true)) :
    binaryRec z f (bit b n) = f b n (binaryRec z f n) := by
  by_cases h' : bit b n = 0
  case pos =>
    obtain ⟨rfl, rfl⟩ := bit_eq_zero_iff.mp h'
    simp only [forall_const, or_false] at h
    unfold binaryRec
    exact h.symm
  case neg =>
    rw [binaryRec, dif_neg h']
    change congrArg C (bit b n).bit_testBit_zero_shiftRight_one ▸ f _ _ _ = _
    generalize congrArg C (bit b n).bit_testBit_zero_shiftRight_one = e; revert e
    rw [bit_testBit_zero, bit_shiftRight_one]
    intros; rfl

end Nat
