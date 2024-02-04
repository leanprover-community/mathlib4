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

theorem toFin_injective {n : Nat} : Function.Injective (toFin : BitVec n → _)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem toFin_inj {x y : BitVec w} : x.toFin = y.toFin ↔ x = y :=
  toFin_injective.eq_iff

theorem toNat_injective {n : Nat} : Function.Injective (BitVec.toNat : BitVec n → _) :=
  Fin.val_injective.comp toFin_injective

theorem toNat_inj {x y : BitVec w} : x.toNat = y.toNat ↔ x = y :=
  toNat_injective.eq_iff

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
### Distributivity of `Std.BitVec.ofFin`
-/
section
variable (x y : Fin (2^w))

@[simp] lemma ofFin_neg : ofFin (-x) = -(ofFin x) := by
  rw [neg_eq_zero_sub]; rfl

@[simp] lemma ofFin_and : ofFin (x &&& y) = ofFin x &&& ofFin y := by
  simp only [HAnd.hAnd, AndOp.and, Fin.land, BitVec.and, toNat_ofFin, ofFin.injEq, Fin.mk.injEq]
  exact mod_eq_of_lt (Nat.and_lt_two_pow _ y.prop)

@[simp] lemma ofFin_or  : ofFin (x ||| y) = ofFin x ||| ofFin y := by
  simp only [HOr.hOr, OrOp.or, Fin.lor, BitVec.or, toNat_ofFin, ofFin.injEq, Fin.mk.injEq]
  exact mod_eq_of_lt (Nat.or_lt_two_pow x.prop y.prop)

@[simp] lemma ofFin_xor : ofFin (x ^^^ y) = ofFin x ^^^ ofFin y := by
  simp only [HXor.hXor, Xor.xor, Fin.xor, BitVec.xor, toNat_ofFin, ofFin.injEq, Fin.mk.injEq]
  exact mod_eq_of_lt (Nat.xor_lt_two_pow x.prop y.prop)

@[simp] lemma ofFin_add : ofFin (x + y)   = ofFin x + ofFin y   := rfl
@[simp] lemma ofFin_sub : ofFin (x - y)   = ofFin x - ofFin y   := rfl
@[simp] lemma ofFin_mul : ofFin (x * y)   = ofFin x * ofFin y   := rfl

-- These should be simp, but Std's simp-lemmas do not allow this yet.
lemma ofFin_zero : ofFin (0 : Fin (2^w)) = 0 := rfl
lemma ofFin_one  : ofFin (1 : Fin (2^w)) = 1 := by
  simp only [OfNat.ofNat, BitVec.ofNat, and_pow_two_is_mod]

lemma ofFin_nsmul (n : ℕ) (x : Fin (2^w)) : ofFin (n • x) = n • ofFin x := rfl
lemma ofFin_zsmul (z : ℤ) (x : Fin (2^w)) : ofFin (z • x) = z • ofFin x := rfl
@[simp] lemma ofFin_pow (n : ℕ) : ofFin (x ^ n) = ofFin x ^ n := rfl

@[simp] lemma ofFin_natCast (n : ℕ) : ofFin (n : Fin (2^w)) = n := by
  simp only [Nat.cast, NatCast.natCast, OfNat.ofNat, BitVec.ofNat, and_pow_two_is_mod]
  rfl

-- See Note [no_index around OfNat.ofNat]
@[simp] lemma ofFin_ofNat (n : ℕ) :
    ofFin (no_index (OfNat.ofNat n : Fin (2^w))) = OfNat.ofNat n := by
  simp only [OfNat.ofNat, Fin.ofNat', BitVec.ofNat, and_pow_two_is_mod]

end

/-!
### Distributivity of `Std.BitVec.toFin`
-/
section
variable (x y : BitVec w)

@[simp] lemma toFin_neg : toFin (-x) = -(toFin x) := by
  rw [neg_eq_zero_sub]; rfl

@[simp] lemma toFin_and : toFin (x &&& y) = toFin x &&& toFin y := by
  apply toFin_inj.mpr; simp only [ofFin_and]

@[simp] lemma toFin_or  : toFin (x ||| y) = toFin x ||| toFin y := by
  apply toFin_inj.mpr; simp only [ofFin_or]

@[simp] lemma toFin_xor : toFin (x ^^^ y) = toFin x ^^^ toFin y := by
  apply toFin_inj.mpr; simp only [ofFin_xor]

@[simp] lemma toFin_add : toFin (x + y)   = toFin x + toFin y   := rfl
@[simp] lemma toFin_sub : toFin (x - y)   = toFin x - toFin y   := rfl
@[simp] lemma toFin_mul : toFin (x * y)   = toFin x * toFin y   := rfl

-- These should be simp, but Std's simp-lemmas do not allow this yet.
lemma toFin_zero : toFin (0 : BitVec w) = 0 := rfl
lemma toFin_one  : toFin (1 : BitVec w) = 1 := by
  apply toFin_inj.mpr; simp only [ofNat_eq_ofNat, ofFin_ofNat]

lemma toFin_nsmul (n : ℕ) (x : BitVec w) : toFin (n • x) = n • x.toFin := rfl
lemma toFin_zsmul (z : ℤ) (x : BitVec w) : toFin (z • x) = z • x.toFin := rfl
@[simp] lemma toFin_pow (n : ℕ) : toFin (x ^ n) = x.toFin ^ n := rfl

@[simp] lemma toFin_natCast (n : ℕ) : toFin (n : BitVec w) = n := by
  apply toFin_inj.mpr; simp only [ofFin_natCast]

-- See Note [no_index around OfNat.ofNat]
lemma toFin_ofNat (n : ℕ) :
    toFin (no_index (OfNat.ofNat n : BitVec w)) = OfNat.ofNat n := by
  simp only [OfNat.ofNat, BitVec.ofNat, and_pow_two_is_mod, Fin.ofNat']

end

/-!
### Distributivity of `Std.BitVec.toNat`
-/

section
variable (x y : BitVec w)
open BitVec (toNat)

@[simp] lemma toNat_and : (x &&& y).toNat = x.toNat &&& y.toNat := rfl
@[simp] lemma toNat_or  : (x ||| y).toNat = x.toNat ||| y.toNat := rfl
@[simp] lemma toNat_xor : (x ^^^ y).toNat = x.toNat ^^^ y.toNat := rfl

/- `Std.BitVec.toNat_add` already exists in Std. -/
attribute [simp] Std.BitVec.toNat_add

lemma toNat_mul : (x * y).toNat = (x.toNat * y.toNat) % 2 ^ w           := rfl
lemma toNat_sub : (x - y).toNat = (x.toNat + (2 ^ w - y.toNat)) % 2 ^ w := rfl

lemma toNat_neg : (-x).toNat = (2 ^ w - x.toNat) % 2 ^ w := by
  simp only [Neg.neg, BitVec.neg, BitVec.sub_eq, toNat_sub, ofNat_eq_ofNat, toNat_zero, zero_add]

lemma toNat_natCast (n : ℕ) : toNat (n : BitVec w) = n % 2 ^ w := by
  rw [toNat, toFin_natCast, Fin.coe_ofNat_eq_mod]

end

/-!
### `IntCast`
-/

-- Either of these follows trivially from the other. Which one to
-- prove is not yet clear.
proof_wanted ofFin_intCast (z : ℤ) : ofFin (z : Fin (2^w)) = z

proof_wanted toFin_intCast (z : ℤ) : toFin (z : BitVec w) = z

/-!
## Ring
-/

-- TODO: generalize to `CommRing` after `ofFin_intCast` is proven
instance : CommSemiring (BitVec w) :=
  toFin_injective.commSemiring _
    toFin_zero toFin_one toFin_add toFin_mul (Function.swap toFin_nsmul)
    toFin_pow toFin_natCast

/-!
## Extensionality
-/

/-- If two bitvectors agree on all in-bound bits, then they agree on all bits -/
private lemma getLsb_eq_of_getLsb' {x y : BitVec w} (h : ∀ (i : Fin w), x.getLsb' i = y.getLsb' i) :
    ∀ (i : ℕ), x.getLsb i = y.getLsb i := by
  simp only [getLsb, testBit]
  intro i
  cases' lt_or_le i w with hi hi
  · exact h ⟨i, hi⟩
  · have (z : BitVec w) : z.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le z.toNat_lt (pow_le_pow_right (le_succ 1) hi)
    rw [Nat.shiftRight_eq_zero_iff_lt.mpr (this x), Nat.shiftRight_eq_zero_iff_lt.mpr (this y)]

/-- If two bitvectors agree on all bits, then they are equal. See also `Std.BitVec.ext_msb` -/
@[ext]
theorem ext_lsb {x y : BitVec w} (h : ∀ i, x.getLsb' i = y.getLsb' i) : x = y := by
  apply toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  simp only [testBit_toNat]
  exact getLsb_eq_of_getLsb' h

theorem getLsb'_rev (x : BitVec w) (i : Fin w) :
    x.getLsb' i.rev = x.getMsb' i := by
  simp [getMsb', getMsb, getLsb', tsub_add_eq_tsub_tsub_swap]

theorem getMsb'_rev (x : BitVec w) (i : Fin w) :
    x.getMsb' i.rev = x.getLsb' i := by
  rw [← getLsb'_rev, Fin.rev_involutive]

/-- If two bitvectors agree on all bits, then they are equal. See also `Std.BitVec.ext_lsb` -/
theorem ext_msb {x y : BitVec w} (h : ∀ i, x.getMsb' i = y.getMsb' i) : x = y := by
  ext i; simpa [← getLsb'_rev] using h i.rev

/-!
### Distributivity of `Std.BitVec.getLsb'`
-/

section
variable (x y : BitVec w) (i : Fin w)

@[simp] lemma getLsb'_and : (x &&& y).getLsb' i = (x.getLsb' i && y.getLsb' i) := by
  simp only [getLsb', getLsb, toNat_and, testBit_land]

@[simp] lemma getLsb'_or : (x ||| y).getLsb' i = (x.getLsb' i || y.getLsb' i) := by
  simp only [getLsb', getLsb, toNat_or, testBit_lor]

@[simp] lemma getLsb'_xor : (x ^^^ y).getLsb' i = (xor (x.getLsb' i) (y.getLsb' i)) := by
  simp only [getLsb', getLsb, toNat_xor, testBit_xor]

@[simp] lemma getLsb'_not : (~~~x).getLsb' i = !(x.getLsb' i) := by
  simp only [getLsb', getLsb, Complement.complement, BitVec.not, toNat_xor, toNat_ofFin,
    testBit_xor, Nat.testBit_ones, Fin.is_lt, decide_True, Bool.true_xor]

@[simp] lemma getLsb'_ofNat_zero : getLsb' 0#w i = false := by
  simp only [getLsb', getLsb, toNat_ofNat, zero_mod, zero_testBit]

proof_wanted getLsb'_negOne : getLsb' (-1) i = true

end

/-!
### Distributivity of `Std.BitVec.getMsb'`
-/

section
variable (x y : BitVec w) (i : Fin w)

@[simp] lemma getMsb'_and : (x &&& y).getMsb' i = (x.getMsb' i && y.getMsb' i) := by
  simp only [← getLsb'_rev, getLsb'_and]

@[simp] lemma getMsb'_or : (x ||| y).getMsb' i = (x.getMsb' i || y.getMsb' i) := by
  simp only [← getLsb'_rev, getLsb'_or]

@[simp] lemma getMsb'_xor : (x ^^^ y).getMsb' i = (xor (x.getMsb' i) (y.getMsb' i)) := by
  simp only [← getLsb'_rev, getLsb'_xor]

@[simp] lemma getMsb'_not : (~~~x).getMsb' i = !(x.getMsb' i) := by
  simp only [← getLsb'_rev, getLsb'_not]

@[simp] lemma getMsb'_ofNat_zero : getMsb' 0#w i = false := by
  simp only [← getLsb'_rev, getLsb'_ofNat_zero]

proof_wanted getMsb'_negOne : getMsb' (-1) i = true
  -- Once we have `getLsb'_negOne`, this lemma trivially follows by
  --   `simp only [← getLsb'_rev, getLsb'_negOne]`

end

end Std.BitVec
