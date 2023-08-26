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

lemma testBit_eq_ofNat {k : ℕ} {x : BitVec w} :
  Bool.toNat (testBit (x.val) k) = (BitVec.ofNat 1 (x.val >>> k)).val:= by
  simp only [BitVec.ofNat, Fin.ofNat', testBit, mod_two_of_bodd, pow_one]
  aesop

lemma val_to_ofNat {m : ℕ} (h: m < 2^w) : (BitVec.ofNat w m).val = m := by
  simp [BitVec.ofNat, Fin.ofNat', mod_eq_of_lt h]

lemma ofNat_to_val (x : BitVec w) : BitVec.ofNat w x.val = x := by
  simp [BitVec.ofNat, Fin.ofNat', mod_eq_of_lt x.isLt]

lemma ofNat_to_val' (x : BitVec w) (h : v = w):
  HEq x (BitVec.ofNat v x.val) := h ▸ heq_of_eq (ofNat_to_val x).symm

theorem concat_ext {x : BitVec w} {y : BitVec v} :
  (x ++ y).val = x.val <<< v ||| y.val := rfl

theorem extract_ext {i j : ℕ} {x : BitVec w} :
  (extract i j x).val = x.val / 2 ^ j % (2 ^ (i - j + 1)) := by
  simp [extract, BitVec.ofNat, Fin.ofNat', shiftRight_eq_div_pow]

theorem get_eq_testBit {x : BitVec w} {i : ℕ} : x.get i = x.val.testBit i := by
  cases' h: Nat.bodd (x.val >>> i)
  <;> simp [testBit, BitVec.ofNat, Fin.ofNat', h,
            mod_two_of_bodd, ← val_bitvec_eq]
  norm_cast

theorem testBit_eq_rep {x: BitVec w} (i : Nat) (h: i< w): x[i] = testBit x.val i := rfl

theorem testBit_eq_rep' {x: Nat} (i : Nat) (h: i< w) (h2: x< 2^w):
  (BitVec.ofNat w x)[i] = testBit x i := by
  simp [BitVec.ofNat, GetElem.getElem, get, extract, Fin.ofNat', mod_eq_of_lt, h2]

end BitVec
