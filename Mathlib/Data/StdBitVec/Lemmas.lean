/-
Copyright (c) 2023 Harun Khan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Alex Keizer
-/

import Std.Data.BitVec
import Mathlib.Algebra.GroupPower.Ring
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors, as defined in `Std`.

Note that `Std.BitVec` is distinct from mathlibs `Bitvec` type, this file is about the former.
For the latter, go to `Data.Bitvec` (notice the difference in capitalization).
Eventually, `Std.BitVec` will replace `Bitvec`, so we include the relevant `#align`s, but
comment them out for now
-/

namespace Std.BitVec

open Nat

variable {w v : Nat}

/-!
## Conversions
Theorems about `ofNat`, `toNat`, `ofFin`, `toFin`, `ofBool`, etc.
-/

/-! ### toNat -/

theorem toNat_inj {x y : BitVec w} : x.toNat = y.toNat ↔ x = y :=
  ⟨(match x, y, · with | ⟨_, _⟩,⟨_, _⟩, rfl => rfl), (· ▸ rfl)⟩

/-- `x < y` as natural numbers if and only if `x < y` as `BitVec w`. -/
theorem toNat_lt_toNat {x y : BitVec w} : x.toNat < y.toNat ↔ x < y :=
  ⟨id, id⟩

theorem toNat_lt {n : ℕ} (v : BitVec n) : v.toNat < 2 ^ n :=
  v.toFin.isLt
-- #align bitvec.to_nat_lt Std.BitVec.toNat_lt

theorem toNat_ofNat {m} (h : m < 2^w) : (BitVec.ofNat w m).toNat = m := Fin.val_cast_of_lt h
-- #align bitvec.to_nat_of_nat Std.BitVec.toNat_ofNat

@[simp] lemma toNat_ofFin (x : Fin (2^w)) : (ofFin x).toNat = x.val := rfl

-- #noalign bitvec.bits_to_nat_to_bool

/-! ### ofNat -/

@[simp]
lemma ofNat_eq_mod_two_pow (n : Nat) : (BitVec.ofNat w n).toNat = n % 2^w := rfl

@[simp]
lemma ofNat_toNat (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  rcases x with ⟨x⟩
  simp [BitVec.ofNat]
  apply Fin.cast_val_eq_self x
#align bitvec.of_nat_to_nat Std.BitVec.ofNat_toNat

lemma ofNat_toNat' (x : BitVec w) (h : w = v):
    BitVec.ofNat v x.toNat = x.cast h := by
  cases h; rw [ofNat_toNat, cast_eq]

/-! ### OfFin / ToFin -/

theorem ofFin_val {n : ℕ} (i : Fin <| 2 ^ n) : (ofFin i).toNat = i.val := by
  rfl
-- #align bitvec.of_fin_val Std.BitVec.ofFin_val

theorem toFin_val {n : ℕ} (v : BitVec n) : (toFin v : ℕ) = v.toNat := by
  rfl
-- #align bitvec.to_fin_val Std.BitVec.toFin_val

theorem toFin_le_toFin_of_le {n} {v₀ v₁ : BitVec n} (h : v₀ ≤ v₁) : v₀.toFin ≤ v₁.toFin :=
  show (v₀.toFin : ℕ) ≤ v₁.toFin by
    rw [toFin_val, toFin_val]
    exact h
-- #align bitvec.to_fin_le_to_fin_of_le Std.BitVec.toFin_le_toFin_of_le

theorem ofFin_le_ofFin_of_le {n : ℕ} {i j : Fin (2 ^ n)} (h : i ≤ j) : ofFin i ≤ ofFin j := by
  exact h
-- #align bitvec.of_fin_le_of_fin_of_le Std.BitVec.ofFin_le_ofFin_of_le

theorem toFin_ofFin {n} (i : Fin <| 2 ^ n) : (ofFin i).toFin = i :=
  Fin.eq_of_veq (by simp [toFin_val, ofFin, toNat_ofNat, Nat.mod_eq_of_lt, i.is_lt])
-- #align bitvec.to_fin_of_fin Std.BitVec.toFin_ofFin

theorem ofFin_toFin {n} (v : BitVec n) : ofFin (toFin v) = v := by
  rfl
-- #align bitvec.of_fin_to_fin Std.BitVec.ofFin_toFin

/-!
  ### Distributivity of ofFin
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

@[simp] lemma toFin_sub (x y : BitVec w) : (x - y).toFin = x.toFin - y.toFin := rfl

/-!
## Extract / Get bits
-/

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
  <;> simp [pos_iff_ne_zero.mp (Nat.two_pow_pos i)]

/-!
## Ext
-/

namespace Nat
open Nat

lemma two_pow_succ_eq_bit_false (x : Nat) :
    2^(x+1) = bit false (2^x) := by
  rw [Nat.pow_succ, Nat.mul_two]; rfl

@[simp] lemma bit_and_two_pow_succ (x₀ : Bool) (x n : Nat) :
    bit x₀ x &&& 2^(n + 1) = bit false (x &&& 2^n) := by
  show bitwise .. = bit _ (bitwise ..)
  rw [two_pow_succ_eq_bit_false, bitwise_bit, Bool.and_false]

@[simp] theorem bit_mod_two_pow_succ (b x w) :
    bit b x % 2 ^ (w + 1) = bit b (x % 2 ^ w) := by
  simp [bit_val, Nat.pow_succ, mul_comm 2]
  cases b <;> simp [mul_mod_mul_right]
  · have h1 : 1 = 1 % (2 ^ w * 2) :=
      (mod_eq_of_lt <| one_lt_mul (one_le_two_pow w) (by decide)).symm
    conv_rhs => {
      rw [←mul_mod_mul_right, h1, ←add_mod_of_add_mod_lt <| by
        rw [mul_mod_mul_right, mul_two, mul_two, add_assoc, add_comm]
        have : x % 2 ^ w < 2 ^ w :=
          mod_lt x (Nat.pow_two_pos w)
        apply add_lt_add_of_le_of_lt _ this
        · rw [←mul_two, ←h1]; exact this
      ]
    }

theorem two_pow_succ_sub_one_eq_bit (w : Nat) : 2 ^ succ w - 1 = bit true (2^w - 1) := by
  induction' w with w ih
  · rfl
  · simp only [Nat.pow_succ, Nat.mul_two, Nat.add_sub_assoc (one_le_two_pow _), ih, bit_val,
      Nat.two_mul, Bool.cond_true]
    conv_rhs => {
      rw [←add_assoc]
      change 2 ^ w + (2 ^ w - 1) + 2 ^ w + ((2 ^ w - 1) + 1)
      rw [
        Nat.sub_add_cancel (one_le_two_pow _),
        add_assoc, ←two_mul (2 ^ w),
        Nat.self_add_sub_one, Nat.sub_one_add_self
      ]
    }
    ring_nf

end Nat

/-!
## Cons
-/

theorem Nat.mod_two_pow (x n : Nat) :
    x % (2^n) = x &&& 2^n - 1 := by
  induction' n with n ih generalizing x
  · simp only [Nat.zero_eq, _root_.pow_zero, mod_one, le_refl, tsub_eq_zero_of_le, land_zero]
  · cases' x using Nat.binaryRec with x₀ x _xih
    · rfl
    · simp [Nat.two_pow_succ_sub_one_eq_bit, -bit_true, ih]

@[simp] lemma Nat.bit_div_two (b : Bool) (x : Nat) : bit b x / 2 = x := by
  rw [←div2_val, div2_bit]

@[simp (high)]
lemma Nat.bit_shiftRight_succ (b : Bool) (x n : ℕ) :
    bit b x >>> (n + 1) = x >>> n := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.mul_comm, ←Nat.div_div_eq_div_mul,
    bit_div_two]


@[simp] lemma toNat_ofBool (b : Bool) : BitVec.toNat (ofBool b) = b.toNat := by
  cases b <;> rfl

theorem bitwise_self (f : Bool → Bool → Bool) (x : ℕ) (hf : f false false = false) :
    bitwise f x x = if f true true = true then x else 0 := by
  split_ifs with hf' <;> (
    induction' x using Nat.binaryRec with x₀ x ih
    · simp only [ne_eq, not_true_eq_false, bitwise_zero_right, ite_self]
    · rw [bitwise_bit (h:=hf), ih]
      cases x₀ <;> simp [hf, hf']
  )

theorem bitwise_self_eq_self (f : Bool → Bool → Bool)
    (hf : f false false = false) (hf' : f true true = true) (x : ℕ) :
    bitwise f x x = x := by
  simp [bitwise_self _ _ hf, hf']

theorem bitwise_self_eq_zero (f : Bool → Bool → Bool)
    (hf : f false false = false) (hf' : f true true = false) (x : ℕ) :
    bitwise f x x = 0 := by
  simp [bitwise_self _ _ hf, hf']

@[simp] lemma land_self (x : Nat) : x &&& x = x :=
  bitwise_self_eq_self _ rfl rfl _

@[simp] lemma lor_self (x : Nat) : x ||| x = x :=
  bitwise_self_eq_self _ rfl rfl _

@[simp] lemma xor_self (x : Nat) : x ^^^ x = 0 :=
  bitwise_self_eq_zero _ rfl rfl _

@[simp] lemma land_land_self (x y : Nat) :
    x &&& y &&& y = x &&& y := by
  rw [land_assoc, land_self]

theorem and_two_pow_or_and_two_pow_sub_one (x n : ℕ) :
    x &&& 2^n ||| x &&& 2^n - 1 = x &&& 2^(n+1) - 1 := by
  induction' x using Nat.binaryRec with x₀ x ih generalizing n
  · rfl
  · cases' n with n
    · simp
    · simp [-bit_false, -bit_true, Nat.two_pow_succ_sub_one_eq_bit, ih]

@[simp]
theorem cons_msb_truncate : ∀ (xs : BitVec (w+1)), cons xs.msb (xs.truncate w) = xs
  | ⟨⟨xs, h⟩⟩ => by
      simp [
        cons, BitVec.msb, getMsb, truncate, zeroExtend, (· ++ ·), BitVec.append, cast,
        Fin.cast, BitVec.ofNat, Fin.ofNat', Nat.zero_lt_succ, Nat.succ_sub_one, Nat.mod_two_pow
      ]
      rw [
        getLsb_eq_testBit, toNat_ofFin, ←and_two_pow, and_two_pow_or_and_two_pow_sub_one xs w,
        Nat.add_comm 1 w, land_land_self, ←Nat.mod_two_pow, Nat.mod_eq_of_lt h
      ]

def consRecOn {motive : ∀ {w}, BitVec w → Sort*}
    (nil  : motive BitVec.nil)
    (cons : ∀ {w} (x : Bool) (xs : BitVec w), motive xs → motive (cons x xs)) :
    ∀ {w} (x : BitVec w), motive x
  | 0,    x => _root_.cast (by rw[eq_nil x]) nil
  | w+1,  x => _root_.cast (by rw[cons_msb_truncate]) <|
      cons x.msb (x.truncate w) (consRecOn nil cons <| x.truncate w)



end Std.BitVec
