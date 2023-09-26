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

namespace BitVec

open Nat

variable {w v : Nat}

@[norm_cast]
theorem val_inj {x y : BitVec w} : x.val = y.val ↔ x = y :=
  ⟨(match x, y, · with | ⟨_, _⟩,⟨_, _⟩, rfl => rfl), (· ▸ rfl)⟩

/-- `x < y` as natural numbers if and only if `x < y` as `BitVec w`. -/
@[norm_cast]
theorem val_lt_val {x y : BitVec w} : x.val < y.val ↔ x < y := by
  simp [LT.lt, BitVec.lt]

/-- `x ≠ y` as natural numbers if and only if `x != y` as `BitVec w`. -/
@[norm_cast]
theorem val_ne_val_iff_bne {x y : BitVec w} : x.val ≠ y.val ↔ x != y := by
  simp [bne, val_inj]

lemma val_ofNat {m} (h : m < 2^w) : (BitVec.ofNat w m).val = m := by
  simp [BitVec.ofNat, Fin.ofNat', mod_eq_of_lt h]

lemma ofNat_val (x : BitVec w) : BitVec.ofNat w x.val = x := by
  simp [BitVec.ofNat, Fin.ofNat', mod_eq_of_lt x.isLt]

lemma ofNat_val' (x : BitVec w) (h : v = w):
  HEq x (BitVec.ofNat v x.val) := h ▸ heq_of_eq (ofNat_val x).symm

theorem val_append {x : BitVec w} {y : BitVec v} :
  (x ++ y).val = x.val <<< v ||| y.val := rfl

theorem val_extract {i j} {x : BitVec w} :
  (extract i j x).val = x.val / 2 ^ j % (2 ^ (i - j + 1)) := by
  simp [extract, BitVec.ofNat, Fin.ofNat', shiftRight_eq_div_pow]

theorem get_eq_testBit {x : BitVec w} {i} : x.get i = x.val.testBit i := by
  cases' h: Nat.bodd (x.val >>> i)
  <;> simp [testBit, BitVec.ofNat, Fin.ofNat', h,
            mod_two_of_bodd, ← val_inj]
  norm_cast

end BitVec
