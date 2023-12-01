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

theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i := rfl
#align bitvec.to_fin_of_fin Std.BitVec.toFin_ofFin

theorem ofFin_toFin {n} (v : BitVec n) : ofFin (toFin v) = v := rfl
#align bitvec.of_fin_to_fin Std.BitVec.ofFin_toFin

/-!
### `Std.BitVec.ofLEFn` and `Std.BitVec.ofBEFn`
-/

@[simp] lemma ofLEFn_zero (f : Fin 0 → Bool) : ofLEFn f = nil := rfl

@[simp] lemma ofLEFn_cons {w} (b : Bool) (f : Fin w → Bool) :
    ofLEFn (Fin.cons b f) = concat (ofLEFn f) b :=
  rfl

proof_wanted ofLEFn_snoc {w} (b : Bool) (f : Fin w → Bool) :
    ofLEFn (Fin.snoc f b) = cons b (ofLEFn f)

@[simp] lemma ofBEFn_zero (f : Fin 0 → Bool) : ofBEFn f = nil := rfl

proof_wanted ofBEFn_cons {w} (b : Bool) (f : Fin w → Bool) :
    ofBEFn (Fin.cons b f) = cons b (ofBEFn f)

proof_wanted ofBEFn_snoc {w} (b : Bool) (f : Fin w → Bool) :
    ofBEFn (Fin.snoc f b) = concat (ofBEFn f) b

/-!
### Distributivity of `Std.BitVec.toNat`
-/

section
variable (x y : BitVec w)

@[simp] lemma toNat_and : (x &&& y).toNat = x.toNat &&& y.toNat := rfl
@[simp] lemma toNat_or  : (x ||| y).toNat = x.toNat ||| y.toNat := rfl
@[simp] lemma toNat_xor : (x ^^^ y).toNat = x.toNat ^^^ y.toNat := rfl

end

/-!
## Extensionality
-/

/-- If two bitvectors agree on all in-bound bits, then they agree on all bits -/
theorem getLsb_eq_of_getLsb' {x y : BitVec w} (h : ∀ (i : Fin w), x.getLsb' i = y.getLsb' i) :
    ∀ (i : ℕ), x.getLsb i = y.getLsb i := by
  simp only [getLsb, testBit]
  intro i
  by_cases hi : i < w
  · exact h ⟨i, hi⟩
  · have (z : BitVec w) : z.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le z.toNat_lt (pow_le_pow (le_succ 1) (Nat.not_lt.mp hi))
    rw [Nat.shiftRight_eq_zero_of_lt (this x), Nat.shiftRight_eq_zero_of_lt (this y)]

/-- If two bitvectors agree on all bits, then they are equal. See also `Std.BitVec.ext_msb` -/
@[ext]
theorem ext_lsb {x y : BitVec w} (h : ∀ i, x.getLsb' i = y.getLsb' i) : x = y := by
  apply toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  simp only [testBit_toNat]
  exact getLsb_eq_of_getLsb' h

theorem getMsb'_eq_getLsb' (x : BitVec w) (i : Fin w) :
    x.getMsb' i = x.getLsb' i.rev := by
  simp [getMsb', getMsb, getLsb', tsub_add_eq_tsub_tsub_swap]

/-- If two bitvectors agree on all bits, then they are equal. See also `Std.BitVec.ext_lsb` -/
theorem ext_msb {x y : BitVec w} (h : ∀ i, x.getMsb' i = y.getMsb' i) : x = y := by
  ext i; simpa [getMsb'_eq_getLsb'] using h i.rev

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

@[simp] lemma getLsb'_ofNat_zero : getLsb' 0#w i = false := by
  simp only [getLsb', getLsb, toNat_ofNat, zero_mod, zero_testBit]

proof_wanted getLsb'_negOne : getLsb' (-1) i = true

end



end Std.BitVec
