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
  simp only [Fin.val_fin_lt]

@[simp]
lemma ofNat_eq_mod_two_pow (n : Nat) : (n : BitVec w).val = n % 2^w := rfl

@[norm_cast]
lemma val_ofNat {m} (h : m < 2^w) : (m : BitVec w).val = m := Fin.val_cast_of_lt h

@[norm_cast]
lemma ofNat_val (x : BitVec w) : (x.val : BitVec w) = x := Fin.cast_val_eq_self x

lemma ofNat_val' (x : BitVec w) (h : v = w):
  HEq x (x.val : BitVec v) := h ▸ heq_of_eq (ofNat_val x).symm

theorem val_append {x : BitVec w} {y : BitVec v} :
  (x ++ y).val = x.val <<< v ||| y.val := rfl

theorem val_extract {i j} {x : BitVec w} :
    (extract i j x).val = x.val / 2 ^ j % (2 ^ (i - j)) := by
  simp [extract, shiftRight_eq_div_pow]

theorem get_eq_testBit {x : BitVec w} {i} : x.get i = x.val.testBit i := by
  cases' h : bodd (x.val >>> i)
  <;> simp [mod_two_of_bodd, h, ← val_inj, testBit]




end BitVec
