/-
Copyright (c) 2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harun Khan
-/

import Mathlib.Data.Bitvec.Defs

open BitVec Nat


lemma testBit_eq_ofNat {x: BitVec w} :
  Bool.toNat (testBit (x.val) k) = (BitVec.ofNat 1 (x.val >>> k)).val:= by
  simp only [BitVec.ofNat, Fin.ofNat', testBit, shiftRight_eq_shiftr, mod_two_of_bodd, pow_one]
  aesop

lemma val_to_ofNat (h: m < 2^w) : (BitVec.ofNat w m).val = m := by
  simp [BitVec.ofNat, Fin.ofNat', mod_eq_of_lt h]

lemma ofNat_to_val (x : BitVec w) : BitVec.ofNat w x.val = x := by
  simp [BitVec.ofNat, Fin.ofNat', mod_eq_of_lt x.isLt]

lemma ofNat_to_val' (x : BitVec w) (h : v = w):
  HEq x (BitVec.ofNat v x.val) := h ▸ heq_of_eq (ofNat_to_val x).symm

theorem concat_ext {x : BitVec a} {y : BitVec b} :
  (x ++ y).val = x.val <<< b ||| y.val := rfl

theorem extract_ext : (extract i j x).val = x.val/2^j % (2^(i - j + 1)) := by
  simp [extract, BitVec.ofNat, Fin.ofNat', shiftRight_eq_shiftr, shiftr_eq_div_pow]

theorem testBit_eq_rep {x: BitVec w} (i : Nat) (h: i< w): x[i] = testBit x.val i := by rfl

theorem testBit_eq_rep' {x: Nat} (i : Nat) (h: i< w) (h2: x< 2^w):
  (BitVec.ofNat w x)[i] = testBit x i := by
  simp [BitVec.ofNat, GetElem.getElem, get, extract, Fin.ofNat', mod_eq_of_lt, h2]


/-! ### Equivalence between bitwise and BitVec operations -/

theorem BV_add {x y : BitVec w}: bitadd x.val y.val w = (x + y).val := by
  rw [bitadd_eq_add]
  norm_cast

-- theorem BV_neg {x : BitVec w}: bitwise_neg x.val w = x.neg.val := by
--   simp only [bitwise_neg_eq_neg, x.isLt]
--   norm_cast

-- theorem BV_mul {x y : BitVec w} (h : 0 < w): bitwise_mul x.val y.val w = (x * y).val := by
--   rw [bitwise_mul_eq_mul h]
--   norm_cast

-- theorem BV_extract {x : BitVec w} : bitwise_extract x.val i j = (extract i j x).val := by
--   rw [bitwise_extract_eq_extract]
--   norm_cast

-- theorem BV_concat {x : BitVec w} {y : BitVec v} :
--  bitwise_concat y.val x.val v w  = (x ++ y).val := by
--   rw [bitwise_concat_eq_concat y.isLt x.isLt]
--   norm_cast

-- theorem BV_eq {x y : BitVec w} (h: 0 < w): bitwise_eq x.val y.val w = (x = y) := by
--   simp [← bitwise_eq_eq h x.isLt y.isLt]

theorem BV_ult {x y : BitVec w} (h1: x < y) :
  bitult x.val y.val w:= bitult_of_ult y.isLt (val_bitvec_lt.mpr h1)

-- theorem BV_slt {x y : BitVec w} (h1: x < y) : bitwise_slt x.val y.val w:= sorry

-- theorem BV_signExtend {x : BitVec w} (h: 0 < w) :
-- (signExtend i x).val = bitwise_ext x.val w i := sorry
