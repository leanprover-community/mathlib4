/-
Copyright (c) 2023 Harun Khan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Alex Keizer
-/

import Std.Data.BitVec
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors, as defined in `Std`.

Note that `Std.BitVec` is distinct from mathlibs `Bitvec` type, this file is about the former.
For the latter, go to `Data.Bitvec` (notice the difference in capitalization).
Eventually, `Std.BitVec` will replace `Bitvec`, so we include the relevant `#align`s, but
comment them out for now
-/

namespace Std.BitVec

open Nat

variable {w v : Nat}

@[simp]
lemma cast_eq (x : BitVec w) : x.cast rfl = x :=
  rfl

/-!
## Conversions
Theorems about `ofNat`, `toNat`, `ofFin`, `toFin`, `ofBool`, etc.
-/

/-! ### toNat -/

theorem toNat_inj {x y : BitVec w} : x.toNat = y.toNat ↔ x = y :=
  ⟨(match x, y, · with | ⟨_, _⟩,⟨_, _⟩, rfl => rfl), (· ▸ rfl)⟩

/-- `x < y` as natural numbers if and only if `x < y` as `BitVec w`. -/
theorem toNat_lt_toNat {x y : BitVec w} : x.toNat < y.toNat ↔ x < y :=
  ⟨id, id⟩

theorem toNat_lt {n : ℕ} (v : BitVec n) : v.toNat < 2 ^ n :=
  v.toFin.isLt
-- #align bitvec.to_nat_lt Std.BitVec.toNat_lt

theorem toNat_ofNat {m} (h : m < 2^w) : (BitVec.ofNat w m).toNat = m := Fin.val_cast_of_lt h
-- #align bitvec.to_nat_of_nat Std.BitVec.toNat_ofNat

@[simp] lemma toNat_ofFin (x : Fin (2^w)) : (ofFin x).toNat = x.val := rfl

-- #noalign bitvec.bits_to_nat_to_bool

/-! ### ofNat -/

@[simp]
lemma ofNat_eq_mod_two_pow (n : Nat) : (BitVec.ofNat w n).toNat = n % 2^w := rfl

@[simp]
lemma ofNat_toNat (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  rcases x with ⟨x⟩
  simp [BitVec.ofNat]
  apply Fin.cast_val_eq_self x
#align bitvec.of_nat_to_nat Std.BitVec.ofNat_toNat

lemma ofNat_toNat' (x : BitVec w) (h : w = v):
    BitVec.ofNat v x.toNat = x.cast h := by
  cases h; rw [ofNat_toNat, cast_eq]

/-! ### OfFin / ToFin -/

theorem ofFin_val {n : ℕ} (i : Fin <| 2 ^ n) : (ofFin i).toNat = i.val := by
  rfl
-- #align bitvec.of_fin_val Std.BitVec.ofFin_val

theorem toFin_val {n : ℕ} (v : BitVec n) : (toFin v : ℕ) = v.toNat := by
  rfl
-- #align bitvec.to_fin_val Std.BitVec.toFin_val

theorem toFin_le_toFin_of_le {n} {v₀ v₁ : BitVec n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
  show (v₀.toFin : ℕ) ≤ v₁.toFin by
    rw [toFin_val, toFin_val]
    exact h
-- #align bitvec.to_fin_le_to_fin_of_le Std.BitVec.toFin_le_toFin_of_le

theorem ofFin_le_ofFin_of_le {n : ℕ} {i j : Fin (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j := by
  exact h
-- #align bitvec.of_fin_le_of_fin_of_le Std.BitVec.ofFin_le_ofFin_of_le

theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i :=
  Fin.eq_of_veq (by simp [toFin_val, ofFin, toNat_ofNat, Nat.mod_eq_of_lt, i.is_lt])
-- #align bitvec.to_fin_of_fin Std.BitVec.toFin_ofFin

theorem ofFin_toFin {n} (v : BitVec n) : ofFin (toFin v) = v := by
  rfl
-- #align bitvec.of_fin_to_fin Std.BitVec.ofFin_toFin

/-!
  ### Distributivity of ofFin
  We add simp-lemmas that show how `ofFin` distributes over various bitvector operations, showing
  that bitvector operations are equivalent to `Fin` operations
-/
@[simp] lemma neg_ofFin (x : Fin (2^w)) : -(ofFin x) = ofFin (-x) := by
  rw [neg_eq_zero_sub]; rfl

@[simp] lemma ofFin_and_ofFin (x y : Fin (2^w)) : ofFin x &&& ofFin y = ofFin (x &&& y) := rfl
@[simp] lemma ofFin_or_ofFin  (x y : Fin (2^w)) : ofFin x ||| ofFin y = ofFin (x ||| y) := rfl
@[simp] lemma ofFin_xor_ofFin (x y : Fin (2^w)) : ofFin x ^^^ ofFin y = ofFin (x ^^^ y) := rfl
@[simp] lemma ofFin_add_ofFin (x y : Fin (2^w)) : ofFin x + ofFin y   = ofFin (x + y)   := rfl
@[simp] lemma ofFin_sub_ofFin (x y : Fin (2^w)) : ofFin x - ofFin y   = ofFin (x - y)   := rfl
@[simp] lemma ofFin_mul_ofFin (x y : Fin (2^w)) : ofFin x * ofFin y   = ofFin (x * y)   := rfl

/-!
## Extract / Get bits
-/

@[simp]
lemma extractLsb_eq {w : ℕ} (hi lo : ℕ) (a : BitVec w) :
    extractLsb hi lo a = extractLsb' lo (hi - lo + 1) a :=
  rfl

theorem toNat_extractLsb' {i j} {x : BitVec w} :
    (extractLsb' i j x).toNat = x.toNat / 2 ^ i % (2 ^ j) := by
  simp only [extractLsb', ofNat_eq_mod_two_pow, shiftRight_eq_div_pow]

theorem getLsb_eq_testBit {i} {x : BitVec w} : getLsb x i = x.toNat.testBit i := by
  simp only [getLsb, Nat.shiftLeft_eq, one_mul, Nat.and_two_pow]
  cases' testBit (BitVec.toNat x) i
  <;> simp [pos_iff_ne_zero.mp (Nat.two_pow_pos i)]

/-!
## Ring
-/

lemma zero_eq_ofFin_zero : 0#w = ofFin 0 := rfl
lemma one_eq_ofFin_one   : 1#w = ofFin 1 := rfl

/-! Now we can define an instance of `CommRing (BitVector w)` straightforwardly in terms of the
    existing instance `CommRing (Fin (2^w))` -/
instance : CommRing (BitVec w) where
  add_assoc       := by intro ⟨_⟩ ⟨_⟩ ⟨_⟩; simp [add_assoc]
  zero_add        := by intro ⟨_⟩; simp [zero_eq_ofFin_zero]
  add_zero        := by intro ⟨_⟩; simp [zero_eq_ofFin_zero]
  sub_eq_add_neg  := by intro ⟨_⟩ ⟨_⟩; simp [sub_eq_add_neg]
  add_comm        := by intro ⟨_⟩ ⟨_⟩; simp [add_comm]
  left_distrib    := by intro ⟨_⟩ ⟨_⟩ ⟨_⟩; simp [left_distrib]
  right_distrib   := by intro ⟨_⟩ ⟨_⟩ ⟨_⟩; simp [right_distrib]
  zero_mul        := by intro ⟨_⟩; simp [zero_eq_ofFin_zero]
  mul_zero        := by intro ⟨_⟩; simp [zero_eq_ofFin_zero]
  mul_assoc       := by intro ⟨_⟩ ⟨_⟩ ⟨_⟩; simp [mul_assoc]
  mul_comm        := by intro ⟨_⟩ ⟨_⟩; simp [mul_comm]
  one_mul         := by intro ⟨_⟩; simp [one_eq_ofFin_one]
  mul_one         := by intro ⟨_⟩; simp [one_eq_ofFin_one]
  add_left_neg    := by intro ⟨_⟩; simp [zero_eq_ofFin_zero]

/-!
## Ext
-/

-- TODO: this results supersedes `Bool.beq_eq_decide_eq` and should go in its own PR
theorem Bool.beq_eq_decide_eq' {α : Type*} (a b : α) [BEq α] [LawfulBEq α] [DecidableEq α] :
    (a == b) = decide (a = b) := by
  cases h : a == b
  · simp [ne_of_beq_false h]
  · simp [eq_of_beq h]

namespace Nat
open Nat

lemma two_pow_succ_eq_bit_false (x : Nat) :
    2^(x+1) = bit false (2^x) := by
  rw [Nat.pow_succ, Nat.mul_two]; rfl

lemma bit_and_two_pow_succ (x₀ : Bool) (x n : Nat) :
    bit x₀ x &&& 2^(n + 1) = bit false (x &&& 2^n) := by
  show bitwise .. = bit _ (bitwise ..)
  rw [two_pow_succ_eq_bit_false, bitwise_bit, Bool.and_false]

@[simp]
lemma bit_and_one (x₀ : Bool) (x : Nat) :
    bit x₀ x &&& 1 = x₀.toNat := by
  show bitwise _ _ (bit true 0) = _
  rw [bitwise_bit, Bool.and_true]
  simp only [ne_eq, bitwise_zero_right, ite_false]
  cases x₀ <;> rfl

set_option linter.deprecated false in
@[simp] lemma bit0_bne_zero (x : Nat) : (bit0 x != 0) = (x != 0) := by
  cases x <;> rfl

set_option linter.deprecated false in
lemma lt_pow_of_bit_lt_pow_succ {w x : Nat} {x₀ : Bool} :
    bit x₀ x < 2 ^ (w + 1) → x < 2 ^ w := by
  have h0 : bit0 x < 2 ^ w * 2 → x < 2 ^ w := by
    simp [bit0, ←mul_two]
  cases x₀
  · exact h0
  · rw [bit_true]
    intro h
    apply h0
    apply Nat.lt_trans (Nat.bit0_lt_bit1 le_rfl) h

-- theorem and_one_eq_mod_two (x : Nat) :
--     x &&& 1 = x % 2 := by
--   cases' x using Nat.binaryRec with b x
--   · rfl
--   · rw [bit_and_one, bit_val, add_mod, mul_mod_right, zero_add, mod_mod]
--     cases b <;> rfl

end Nat

@[ext]
theorem ext {x y : BitVec w} (h : ∀ (i : Fin w), x.getLsb i = y.getLsb i) : x = y := by
  rcases x with ⟨⟨x, hx⟩⟩
  rcases y with ⟨⟨y, hy⟩⟩
  simp only [getLsb, toNat_ofFin, Nat.shiftLeft_eq, one_mul] at h
  simp only [ofFin.injEq, Fin.mk.injEq]
  induction' x using Nat.binaryRec with x₀ x ih generalizing y w
  · simp only [zero_land, bne_self_eq_false, eq_comm (a:=false)] at h
    simp only [bne, Bool.not_eq_false', beq_iff_eq] at h
    clear hx
    induction' y using Nat.binaryRec with y₀ y ih generalizing w
    · rfl
    · cases' w with w
      · cases y₀ <;> simp [bit_val] at hy
        rw [hy]
        rfl
      · obtain ⟨⟩ : y₀ = false := by
          have h0 := h 0
          change bitwise _ _ (bit true 0) = _ at h0
          rw [Nat.bitwise_bit] at h0
          cases y₀
          · rfl
          · simp [bit_val] at h0
        rw [←ih (Nat.lt_pow_of_bit_lt_pow_succ hy)]
        · rfl
        · intro i
          specialize h i.succ
          simp only [Fin.val_succ, Nat.bit_and_two_pow_succ, bit_eq_zero, and_true] at h
          exact h
  · cases' w with w
    · rw [Nat.lt_one_iff.mp hx, Nat.lt_one_iff.mp hy]
    · rw [←bit_decomp y] at hy h ⊢
      congr
      · specialize h 0
        simp only [Fin.val_zero, _root_.pow_zero, Nat.bit_and_one, Bool.toNat_bne_zero] at h
        exact h
      · apply ih (w:=w) (Nat.lt_pow_of_bit_lt_pow_succ hx) _ (Nat.lt_pow_of_bit_lt_pow_succ hy)
        intro i
        specialize h (Fin.succ i)
        simp [Nat.bit_and_two_pow_succ] at h
        exact h

theorem extMsb {w : ℕ} {x y : BitVec w} (h : ∀ (i : Fin w), x.getMsb i = y.getMsb i) : x = y := by
  apply ext
  intro i
  simp only [getMsb, Fin.is_lt, decide_True, ge_iff_le, tsub_le_iff_right, Bool.true_and] at h
  specialize h i.rev
  have h_lt : 1 ≤ w - ↑i :=
    Nat.le_of_lt_succ <| Nat.succ_lt_succ <| Nat.zero_lt_sub_of_lt i.isLt
  conv at h => {
    simp only [ge_iff_le, Fin.val_rev, tsub_le_iff_right]
    rw [←Nat.sub_add_eq w 1, Nat.add_comm 1, Nat.sub_add_eq w i.val 1, Nat.sub_add_cancel h_lt,
      Nat.sub_sub_self (Nat.le_of_lt i.isLt)]
  }
  exact h

end Std.BitVec
