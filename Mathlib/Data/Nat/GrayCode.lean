/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Units

/-!
# Gray Code

This file defines [the binary reflected Gray code](https://en.wikipedia.org/wiki/Gray_code), both
as a permutation of `ℕ`, in `Nat.grayCode`, and then, using that, as a permutation of `BitVec n`,
in `Nat.partialGrayCode`. We also prove some theorems about them:

* `grayCode_prop`: the xor of `grayCode n` and `grayCode (n + 1)` is a power of 2
for all `n`.
* `grayCode_size`: `grayCode` preserves the binary length of integers.
* `partialGrayCode_prop`: the xor of `n.partialGrayCode m` and `n.partialGrayCode (m + 1)`
is a power of 2 for all `n ≠ 0` and `m`.
-/
namespace Nat

/-- The inverse of `f(n) = n ⊕ ⌊n / 2⌋`, defined by `g(n) = n ⊕ g(⌊n / 2⌋)`. -/
def grayCodeInv : ℕ → ℕ
  | 0 => 0
  | n+1 => (n+1) ^^^ grayCodeInv (n+1).div2
  decreasing_by
    apply Nat.binaryRec_decreasing
    simp

theorem grayCodeInv_val : (n : ℕ) → grayCodeInv n = n ^^^ grayCodeInv n.div2
  | 0 => rfl
  | _+1 => rfl

/-- Gray code, `f(n) = n ⊕ ⌊n / 2⌋`, as a permutation of `ℕ`. -/
def grayCode : Equiv.Perm ℕ where
  toFun (n : ℕ) := n ^^^ n.div2
  invFun := grayCodeInv
  left_inv := by
    intro n
    apply Nat.binaryRec (n := n)
    rfl
    clear n
    intro _ n h
    simp only [div2_bit]
    rw [grayCodeInv_val]
    simp [h, Nat.xor_assoc]
  right_inv := by
    intro n
    apply Nat.binaryRec (n := n)
    rfl
    clear n
    intro _ n h
    dsimp only at h
    rw [grayCodeInv_val]
    simp only [div2_bit, xor_div2, Nat.xor_assoc]
    conv =>
      lhs
      rhs
      rw [Nat.xor_comm, Nat.xor_assoc]
      rhs
      rw [Nat.xor_comm, h]
    simp

theorem grayCode_prop (n : ℕ) : (grayCode n ^^^ grayCode n.succ).isPowerOfTwo := by
  apply Nat.binaryRec (n := n)
  exists 0
  clear n
  intro b n h
  unfold grayCode
  dsimp only [Equiv.coe_fn_mk, Nat.succ_eq_add_one]
  cases b with
  | false =>
    exists 0
    simp only [Nat.bit_false, Nat.div2_bit0, Nat.succ_eq_add_one, Nat.div2_succ, Nat.bodd_bit0,
      cond_false, pow_zero]
    rw [Nat.xor_assoc]
    conv =>
      lhs
      rhs
      rw [Nat.xor_comm, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [← bit1.eq_1, ← Nat.bit_false, ← Nat.bit_true, Nat.xor_bit]
    simp only [Bool.bne_true, Bool.not_false, Nat.xor_self]
    rfl
  | true =>
    simp only [div2_bit, bit_true_succ]
    have ⟨k, hk⟩ := h
    exists k+1
    simp only [pow_succ, Nat.div2_bit1, Nat.succ_eq_add_one, Nat.div2_succ, Nat.bodd_bit1,
      cond_true, ← hk]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [mul_two, ← bit0, ← Nat.bit_false]
    cases i
    · simp [h, Nat.testBit_bit_zero, succ_testBit_zero, -Nat.testBit_zero]
    · unfold grayCode
      dsimp only [Equiv.coe_fn_mk]
      simp only [testBit_xor, testBit_bit_succ, Bool.bne_assoc, div2_testBit]

theorem grayCode_size (n : ℕ) : n.size = (grayCode n).size := by
  unfold grayCode
  dsimp only [Equiv.coe_fn_mk]
  cases v : n.size
  · rw [Nat.size_eq_zero] at v
    rw [v]
    rfl
  · apply Eq.symm
    rw [size_eq_iff_testBit] at v
    apply (size_eq_iff_testBit ..).mpr
    constructor
    · rw [testBit_xor]
      convert_to true.xor false = true
      congr
      exact v.1
      simp only [div2_testBit]
      apply v.2
      simp
      rfl
    · intro j hj
      simp only [testBit_xor, div2_testBit, bne_eq_false_iff_eq]
      trans false
      apply v.2 j hj
      refine' (v.2 ..).symm
      omega

/-- Gray code, `f(n) = n ⊕ ⌊n / 2⌋`, as a permutation of `BitVec n`. -/
def partialGrayCode (n : ℕ) : Equiv.Perm (BitVec n) where
  toFun (n : BitVec n) := ⟨grayCode n.toNat,
    by rw [← Nat.size_le, ← grayCode_size, Nat.size_le]; simp [BitVec.isLt]⟩
  invFun (n : BitVec n) := ⟨grayCode.symm n.toNat,
    by rw [← Nat.size_le, grayCode_size, Equiv.apply_symm_apply, Nat.size_le]; simp [BitVec.isLt]⟩
  left_inv := by intro n; simp; norm_cast
  right_inv := by intro n; simp; norm_cast

theorem partialGrayCode_prop (n : ℕ) (h : n ≠ 0) (m : BitVec n) :
    (n.partialGrayCode m ^^^ n.partialGrayCode (m + 1)).toNat.isPowerOfTwo := by
  unfold partialGrayCode grayCode
  simp only [Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, BitVec.ofNat_eq_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofNat, add_mod_mod, BitVec.toNat_xor, BitVec.toNat_ofFin]
  by_cases h : m.toNat = 2^n - 1
  · rw [h]
    have : 2^n - 1 + 1 = 2^n := by omega
    rw [this]
    simp only [mod_self, div2_zero, xor_self, xor_zero]
    exists n-1
    apply eq_of_testBit_eq
    intro i
    by_cases h₂ : i = n-1
    · simp only [h₂, testBit_xor, testBit_two_pow_sub_one, div2_testBit, testBit_two_pow_self,
      bne_iff_ne, ne_eq, decide_eq_decide]
      omega
    · simp only [testBit_xor, testBit_two_pow_sub_one, div2_testBit]
      trans false
      simp only [bne_eq_false_iff_eq, decide_eq_decide]; omega
      exact (Nat.testBit_two_pow_of_ne (Ne.symm h₂)).symm
  · rw [Nat.mod_eq_of_lt]
    apply grayCode_prop m.toNat
    have : m.toNat < 2^n := BitVec.isLt m
    omega

end Nat
