/-
Copyright (c) 2023 Harun Khan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

import Mathlib.Data.Bitvec.Defs

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors.
-/

namespace Std.BitVec

open Nat

variable {w v : Nat}

-- @[norm_cast]
theorem toNat_inj {x y : BitVec w} : x.toNat = y.toNat ↔ x = y :=
  ⟨(match x, y, · with | ⟨_, _⟩,⟨_, _⟩, rfl => rfl), (· ▸ rfl)⟩

/-- `x < y` as natural numbers if and only if `x < y` as `BitVec w`. -/
-- @[norm_cast]
theorem toFin_lt_toFin {x y : BitVec w} : (x.toFin < y.toFin) = (x < y) := rfl

@[simp]
lemma ofNat_eq_mod_two_pow (n : Nat) : (BitVec.ofNat w n).toNat = n % 2^w := rfl

-- @[norm_cast]
lemma toNat_ofNat {m} (h : m < 2^w) : (BitVec.ofNat w m).toNat = m := Fin.val_cast_of_lt h

@[simp]
lemma toNat_ofFin (x : Fin (2^w)) : (ofFin x).toNat = x.val := rfl

-- @[norm_cast]
lemma ofNat_toNat (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  rcases x with ⟨x⟩
  simp [BitVec.ofNat]
  apply Fin.cast_val_eq_self x

lemma ofNat_toNat' (x : BitVec w) (h : v = w):
    HEq x (BitVec.ofNat v x.toNat) := h ▸ heq_of_eq (ofNat_toNat x).symm

theorem toNat_append {x : BitVec w} {y : BitVec v} :
    (x ++ y).toNat = x.toNat <<< v ||| y.toNat := by
  -- `rfl` no longer works
  sorry

theorem toNat_extractLsb {i j} {x : BitVec w} :
    (extractLsb i j x).toNat = x.toNat / 2 ^ j % (2 ^ (i - j)) := by
  simp [extractLsb, extractLsb', shiftRight_eq_div_pow]
  -- The goal here is
  -- `⊢ BitVec.toNat x / 2 ^ j % 2 ^ (i - j + 1) = BitVec.toNat x / 2 ^ j % 2 ^ (i - j)`
  -- That seems like it's false, maybe `extractLsb` behaves different from `extract` before
  sorry

lemma bne_eq_not (x y : BitVec w) : (x != y) = !(decide (x = y)) := by
  cases' h : x == y <;> rfl

theorem get_eq_testBit {x : BitVec w} {i} : x.getLsb i = x.toNat.testBit i := by
  cases' h : bodd (x.toNat >>> i)
  <;> simp [bne_eq_not, mod_two_of_bodd, h, ← toNat_inj, testBit]
  <;> sorry

end Std.BitVec
