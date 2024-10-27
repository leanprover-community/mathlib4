/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Praneeth Kolichala, Yuyang Zhao
-/
import Batteries.Tactic.Alias
import Mathlib.Init

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

/-- `bit b` appends the digit `b` to the binary representation of its natural number input. -/
def bit (b : Bool) : Nat → Nat := cond b (2 * · + 1) (2 * ·)

theorem shiftRight_one (n) : n >>> 1 = n / 2 := rfl

@[simp]
theorem bit_decide_mod_two_eq_one_shiftRight_one (n : Nat) : bit (n % 2 = 1) (n >>> 1) = n := by
  simp only [bit, shiftRight_one]
  cases mod_two_eq_zero_or_one n with | _ h => simpa [h] using Nat.div_add_mod n 2

theorem bit_testBit_zero_shiftRight_one (n : Nat) : bit (n.testBit 0) (n >>> 1) = n := by
  simp

@[simp]
theorem bit_eq_zero_iff {n : Nat} {b : Bool} : bit b n = 0 ↔ n = 0 ∧ b = false := by
  cases n <;> cases b <;> simp [bit, Nat.shiftLeft_succ, Nat.two_mul, ← Nat.add_assoc]

/-- For a predicate `motive : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for any given natural number. -/
@[inline]
def bitCasesOn {motive : Nat → Sort u} (n) (h : ∀ b n, motive (bit b n)) : motive n :=
  -- `1 &&& n != 0` is faster than `n.testBit 0`. This may change when we have faster `testBit`.
  let x := h (1 &&& n != 0) (n >>> 1)
  -- `congrArg motive _ ▸ x` is defeq to `x` in non-dependent case
  congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x

/-- A recursion principle for `bit` representations of natural numbers.
  For a predicate `motive : Nat → Sort u`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for all natural numbers. -/
@[elab_as_elim, specialize]
def binaryRec {motive : Nat → Sort u} (z : motive 0) (f : ∀ b n, motive n → motive (bit b n))
    (n : Nat) : motive n :=
  if n0 : n = 0 then congrArg motive n0 ▸ z
  else
    let x := f (1 &&& n != 0) (n >>> 1) (binaryRec z f (n >>> 1))
    congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x
decreasing_by exact bitwise_rec_lemma n0

/-- The same as `binaryRec`, but the induction step can assume that if `n=0`,
  the bit being appended is `true`-/
@[elab_as_elim, specialize]
def binaryRec' {motive : Nat → Sort u} (z : motive 0)
    (f : ∀ b n, (n = 0 → b = true) → motive n → motive (bit b n)) :
    ∀ n, motive n :=
  binaryRec z fun b n ih =>
    if h : n = 0 → b = true then f b n h ih
    else
      have : bit b n = 0 := by
        rw [bit_eq_zero_iff]
        cases n <;> cases b <;> simp at h ⊢
      congrArg motive this ▸ z

/-- The same as `binaryRec`, but special casing both 0 and 1 as base cases -/
@[elab_as_elim, specialize]
def binaryRecFromOne {motive : Nat → Sort u} (z₀ : motive 0) (z₁ : motive 1)
    (f : ∀ b n, n ≠ 0 → motive n → motive (bit b n)) :
    ∀ n, motive n :=
  binaryRec' z₀ fun b n h ih =>
    if h' : n = 0 then
      have : bit b n = bit true 0 := by
        rw [h', h h']
      congrArg motive this ▸ z₁
    else f b n h' ih

theorem bit_val (b n) : bit b n = 2 * n + b.toNat := by
  cases b <;> rfl

@[simp]
theorem bit_div_two (b n) : bit b n / 2 = n := by
  rw [bit_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add]
  · cases b <;> decide
  · decide

@[simp]
theorem bit_mod_two (b n) : bit b n % 2 = b.toNat := by
  cases b <;> simp [bit_val, mul_add_mod]

@[simp]
theorem bit_shiftRight_one (b n) : bit b n >>> 1 = n :=
  bit_div_two b n

theorem testBit_bit_zero (b n) : (bit b n).testBit 0 = b := by
  simp

variable {motive : Nat → Sort u}

@[simp]
theorem bitCasesOn_bit (h : ∀ b n, motive (bit b n)) (b : Bool) (n : Nat) :
    bitCasesOn (bit b n) h = h b n := by
  change congrArg motive (bit b n).bit_testBit_zero_shiftRight_one ▸ h _ _ = h b n
  generalize congrArg motive (bit b n).bit_testBit_zero_shiftRight_one = e; revert e
  rw [testBit_bit_zero, bit_shiftRight_one]
  intros; rfl

unseal binaryRec in
@[simp]
theorem binaryRec_zero (z : motive 0) (f : ∀ b n, motive n → motive (bit b n)) :
    binaryRec z f 0 = z :=
  rfl

@[simp]
theorem binaryRec_one (z : motive 0) (f : ∀ b n, motive n → motive (bit b n)) :
    binaryRec (motive := motive) z f 1 = f true 0 z := by
  rw [binaryRec]
  simp only [add_one_ne_zero, ↓reduceDIte, Nat.reduceShiftRight, binaryRec_zero]
  rfl

theorem binaryRec_eq {z : motive 0} {f : ∀ b n, motive n → motive (bit b n)}
    (b n) (h : f false 0 z = z ∨ (n = 0 → b = true)) :
    binaryRec z f (bit b n) = f b n (binaryRec z f n) := by
  by_cases h' : bit b n = 0
  case pos =>
    obtain ⟨rfl, rfl⟩ := bit_eq_zero_iff.mp h'
    simp only [Bool.false_eq_true, imp_false, not_true_eq_false, or_false] at h
    unfold binaryRec
    exact h.symm
  case neg =>
    rw [binaryRec, dif_neg h']
    change congrArg motive (bit b n).bit_testBit_zero_shiftRight_one ▸ f _ _ _ = _
    generalize congrArg motive (bit b n).bit_testBit_zero_shiftRight_one = e; revert e
    rw [testBit_bit_zero, bit_shiftRight_one]
    intros; rfl

@[deprecated (since := "2024-10-21")] alias binaryRec_eq' := binaryRec_eq

end Nat
