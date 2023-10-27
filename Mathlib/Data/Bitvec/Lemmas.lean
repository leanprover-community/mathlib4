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
theorem toNat_lt_toNat {x y : BitVec w} : (x.toNat < y.toNat) = (x < y) := rfl

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

lemma ofNat_toNat' (x : BitVec w) (h : v = w):
    HEq x (BitVec.ofNat v x.toNat) := h ▸ heq_of_eq (ofNat_toNat x).symm

theorem toNat_append {msbs : BitVec w} {lsbs : BitVec v} :
    (msbs ++ lsbs).toNat = msbs.toNat <<< v ||| lsbs.toNat := by
  rcases msbs with ⟨msbs, hm⟩
  rcases lsbs with ⟨lsbs, hl⟩
  simp only [HAppend.hAppend, append, toNat_ofFin]
  rw [toNat_ofNat (Nat.add_comm w v ▸ append_lt hl hm)]

theorem toNat_extractLsb {i j} {x : BitVec w} :
    (extractLsb i j x).toNat = x.toNat / 2 ^ j % (2 ^ (i - j + 1)) := by
  simp [extractLsb, extractLsb', shiftRight_eq_div_pow]

/-!
  ## Distributivity of ofFin
  We add simp-lemmas that show how `ofFin` distributes over various bitvector operations, showing
  that bitvector operations are equivalent to `Fin` operations
-/
@[simp] lemma neg_ofFin (x : Fin (2^w)) : -(ofFin x) = ofFin (-x) := by
  rw [neg_eq_zero_sub]; rfl

@[simp] lemma ofFin_and_ofFin (x y : Fin (2^w)) : (ofFin x) &&& (ofFin y) = ofFin (x &&& y) := rfl
@[simp] lemma ofFin_or_ofFin  (x y : Fin (2^w)) : (ofFin x) ||| (ofFin y) = ofFin (x ||| y) := rfl
@[simp] lemma ofFin_xor_ofFin (x y : Fin (2^w)) : (ofFin x) ^^^ (ofFin y) = ofFin (x ^^^ y) := rfl
@[simp] lemma ofFin_add_ofFin (x y : Fin (2^w)) : (ofFin x) + (ofFin y) = ofFin (x + y)     := rfl
@[simp] lemma ofFin_sub_ofFin (x y : Fin (2^w)) : (ofFin x) - (ofFin y) = ofFin (x - y)     := rfl
@[simp] lemma ofFin_mul_ofFin (x y : Fin (2^w)) : (ofFin x) * (ofFin y) = ofFin (x * y)     := rfl

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
## Extensionality
-/

/-- The empty bitvector -/
def nil : BitVec 0 := 0

/-- Add a new most signicifant bit to a bitvector -/
def consMsb {w} (newMsb : Bool) (x : BitVec w) : BitVec (w+1) :=
  let x : Fin (2^(w+1)) := x.toFin.castLE (by simp[Nat.pow_succ])
  ofFin <|
    bif newMsb then
      x + ⟨2^w, by simp[Nat.pow_succ]⟩
    else
      x

/-- Every bitvector of length `0` is equal to the empty bitvector `nil` -/
lemma nil_eq {x : BitVec 0} : x = nil := by
  cases' x with x
  cases x using Fin.succRec
  case zero     => rfl
  case succ x _ => exact x.elim0

def dropMsb {w} (x : BitVec (w+1)) : BitVec w :=
  ofFin <| Fin.ofNat' x.toNat (by simp)

#print consMsb

lemma consMsb_msb_dropMsb (x : BitVec (w+1)) :
    consMsb x.msb x.dropMsb = x := by
  rcases x with ⟨⟨x, h⟩⟩
  simp [consMsb, Fin.castLE, dropMsb, Fin.ofNat', BitVec.toNat, cond, BitVec.msb, getMsb, getLsb]
  split
  · simp[Fin.add]
  · simp


/-- Two bitvectors are equal if they agree on each bit -/
@[ext]
lemma extLsb {w} {x y : BitVec w} (h : ∀ i, x.getLsb i = y.getLsb i) : x = y := by
  induction w
  · simp [nil_eq]
  · simp

/-- Two bitvectors are equal if they agree on each bit -/
lemma extMsb {w} {x y : BitVec w} (h : ∀ i, x.getMsb i = y.getMsb i) : x = y := by
  sorry
end Std.BitVec
