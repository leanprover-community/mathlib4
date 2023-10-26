/-
Copyright (c) 2023 Harun Khan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan
-/

import Mathlib.Data.BitVec.Defs

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors.
-/

namespace Std.BitVec

open Nat

variable {w v : Nat}

/-! We add simp-lemmas that rewrite bitvector operations into the equivalent notation -/
@[simp] lemma append_eq (x : BitVec w) (y : BitVec v)   : BitVec.append x y = x ++ y        := rfl
@[simp] lemma shiftLeft_eq (x : BitVec w) (n: Nat)      : BitVec.shiftLeft x n = x <<< n    := rfl
@[simp] lemma ushiftRight_eq (x : BitVec w) (n: Nat)    : BitVec.ushiftRight x n = x >>> n  := rfl
@[simp] lemma not_eq (x : BitVec w)                     : BitVec.not x = ~~~x               := rfl
@[simp] lemma and_eq (x y : BitVec w)                   : BitVec.and x y = x &&& y          := rfl
@[simp] lemma or_eq (x y : BitVec w)                    : BitVec.or x y = x ||| y           := rfl
@[simp] lemma xor_eq (x y : BitVec w)                   : BitVec.xor x y = x ^^^ y          := rfl
@[simp] lemma neg_eq (x : BitVec w)                     : BitVec.neg x = -x                 := rfl
@[simp] lemma add_eq (x y : BitVec w)                   : BitVec.add x y = x + y            := rfl
@[simp] lemma sub_eq (x y : BitVec w)                   : BitVec.sub x y = x - y            := rfl
@[simp] lemma mul_eq (x y : BitVec w)                   : BitVec.mul x y = x * y            := rfl

theorem toNat_inj {x y : BitVec w} : x.toNat = y.toNat ↔ x = y :=
  ⟨(match x, y, · with | ⟨_, _⟩,⟨_, _⟩, rfl => rfl), (· ▸ rfl)⟩

/-- `x < y` as natural numbers if and only if `x < y` as `BitVec w`. -/
theorem toNat_lt_toNat {x y : BitVec w} : x.toNat < y.toNat ↔ x < y :=
  ⟨id, id⟩

@[simp]
lemma ofNat_eq_mod_two_pow (n : Nat) : (BitVec.ofNat w n).toNat = n % 2^w := rfl

lemma toNat_ofNat {m} (h : m < 2^w) : (BitVec.ofNat w m).toNat = m := Fin.val_cast_of_lt h

@[simp]
lemma toNat_ofFin (x : Fin (2^w)) : (ofFin x).toNat = x.val := rfl

@[simp]
lemma ofNat_toNat (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  rcases x with ⟨x⟩
  simp [BitVec.ofNat]
  apply Fin.cast_val_eq_self x

@[simp]
lemma cast_eq (x : BitVec w) : x.cast rfl = x :=
  rfl

lemma ofNat_toNat' (x : BitVec w) (h : w = v):
    BitVec.ofNat v x.toNat = x.cast h := by
  cases h; rw [ofNat_toNat, cast_eq]

theorem toNat_append {msbs : BitVec w} {lsbs : BitVec v} :
    (msbs ++ lsbs).toNat = msbs.toNat <<< v ||| lsbs.toNat := by
  rcases msbs with ⟨msbs, hm⟩
  rcases lsbs with ⟨lsbs, hl⟩
  simp only [HAppend.hAppend, append, toNat_ofFin]
  rw [toNat_ofNat (Nat.add_comm w v ▸ append_lt hl hm)]

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
  <;> simp [pos_iff_ne_zero.mp (two_pow_pos i)]

end Std.BitVec
