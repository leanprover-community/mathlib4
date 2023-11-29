/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Harun Khan
-/

import Mathlib.Data.BitVec.Defs

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors.
-/

namespace Std.BitVec

open Nat

#noalign bitvec.bits_to_nat_to_list
#noalign bitvec.to_nat_append

variable {w v : Nat}

theorem toNat_injective {n : Nat} : Function.Injective (@Std.BitVec.toNat n)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem toNat_inj {x y : BitVec w} : x.toNat = y.toNat ↔ x = y :=
  toNat_injective.eq_iff

theorem toFin_injective {n : Nat} : Function.Injective (@Std.BitVec.toFin n)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem toFin_inj {x y : BitVec w} : x.toFin = y.toFin ↔ x = y :=
  toFin_injective.eq_iff

/-- `x < y` as natural numbers if and only if `x < y` as `BitVec w`. -/
theorem toNat_lt_toNat {x y : BitVec w} : x.toNat < y.toNat ↔ x < y :=
  Iff.rfl

attribute [simp] toNat_ofNat toNat_ofFin

lemma toNat_ofNat_of_lt {m} (h : m < 2^w) : (BitVec.ofNat w m).toNat = m := by
  simp only [toNat_ofNat, mod_eq_of_lt h]

#noalign bitvec.bits_to_nat_to_bool

-- The statement in the new API would be: `n#(k.succ) = ((n / 2)#k).concat (n % 2 != 0)`
#noalign bitvec.of_nat_succ

#align bitvec.to_nat_of_nat Std.BitVec.toNat_ofNat

@[simp]
lemma extractLsb_eq {w : ℕ} (hi lo : ℕ) (a : BitVec w) :
    extractLsb hi lo a = extractLsb' lo (hi - lo + 1) a :=
  rfl

theorem toNat_extractLsb' {i j} {x : BitVec w} :
    (extractLsb' i j x).toNat = x.toNat / 2 ^ i % (2 ^ j) := by
  simp only [extractLsb', toNat_ofNat, shiftRight_eq_div_pow]

theorem ofFin_val {n : ℕ} (i : Fin <| 2 ^ n) : (ofFin i).toNat = i.val :=
  rfl
#align bitvec.of_fin_val Std.BitVec.ofFin_val

theorem addLsb_eq_twice_add_one {x b} : addLsb x b = 2 * x + cond b 1 0 := by
  simp [addLsb, two_mul]; cases b <;> rfl
#align bitvec.add_lsb_eq_twice_add_one Std.BitVec.addLsb_eq_twice_add_one

-- The previous statement was `(v : BitVec n) : v.toNat = v.toList.reverse.foldr (flip addLsb) 0`.
-- Since the statement is awkward and `Std.BitVec` has no comparable API, we just drop it.
#noalign bitvec.to_nat_eq_foldr_reverse

theorem toNat_lt {n : ℕ} (v : BitVec n) : v.toNat < 2 ^ n := by
  exact v.toFin.2
#align bitvec.to_nat_lt Std.BitVec.toNat_lt

theorem addLsb_div_two {x b} : addLsb x b / 2 = x := by
  rw [addLsb, ← Nat.div2_val, Nat.div2_bit]
#align bitvec.add_lsb_div_two Std.BitVec.addLsb_div_two

theorem decide_addLsb_mod_two {x b} : decide (addLsb x b % 2 = 1) = b := by
  simp [addLsb]
#align bitvec.to_bool_add_lsb_mod_two Std.BitVec.decide_addLsb_mod_two

lemma ofNat_toNat' (x : BitVec w) : (x.toNat)#w = x := by
  rw [ofNat_toNat, truncate_eq]

lemma ofNat_toNat_of_eq (x : BitVec w) (h : w = v):
    BitVec.ofNat v x.toNat = x.cast h := by
  cases h; rw [ofNat_toNat', cast_eq]

theorem toFin_val {n : ℕ} (v : BitVec n) : (toFin v : ℕ) = v.toNat := by
  rfl
#align bitvec.to_fin_val Std.BitVec.toFin_val

theorem toFin_le_toFin_of_le {n} {v₀ v₁ : BitVec n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
  show (v₀.toFin : ℕ) ≤ v₁.toFin by
    rw [toFin_val, toFin_val]
    exact h
#align bitvec.to_fin_le_to_fin_of_le Std.BitVec.toFin_le_toFin_of_le

theorem ofFin_le_ofFin_of_le {n : ℕ} {i j : Fin (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j := by
  exact h
#align bitvec.of_fin_le_of_fin_of_le Std.BitVec.ofFin_le_ofFin_of_le

theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i :=
  Fin.eq_of_veq (by simp [toFin_val, ofFin, toNat_ofNat, Nat.mod_eq_of_lt, i.is_lt])
#align bitvec.to_fin_of_fin Std.BitVec.toFin_ofFin

theorem ofFin_toFin {n} (v : BitVec n) : ofFin (toFin v) = v := by
  rfl
#align bitvec.of_fin_to_fin Std.BitVec.ofFin_toFin

/-!
  ## Distributivity of ofFin
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

end Std.BitVec
