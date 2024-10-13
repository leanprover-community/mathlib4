/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Harun Khan, Alex Keizer
-/
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.ZMod.Defs


/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors which can only be stated in Mathlib or downstream
because they refer to other notions defined in Mathlib.

Please do not extend this file further: material about BitVec needed in downstream projects
can either be PR'd to Lean, or kept downstream if it also relies on Mathlib.
-/

namespace BitVec

variable {w v : Nat}

/-!
## Injectivity
-/

theorem toNat_injective {n : Nat} : Function.Injective (BitVec.toNat : BitVec n → _)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem toFin_injective {n : Nat} : Function.Injective (toFin : BitVec n → _)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-!
## Scalar Multiplication and Powers
Having instance of `SMul ℕ`, `SMul ℤ` and `Pow` are prerequisites for a `CommRing` instance
-/

instance : SMul ℕ (BitVec w) := ⟨fun x y => ofFin <| x • y.toFin⟩
instance : SMul ℤ (BitVec w) := ⟨fun x y => ofFin <| x • y.toFin⟩
instance : Pow (BitVec w) ℕ  := ⟨fun x n => ofFin <| x.toFin ^ n⟩

lemma toFin_nsmul (n : ℕ) (x : BitVec w)  : toFin (n • x) = n • x.toFin := rfl
lemma toFin_zsmul (z : ℤ) (x : BitVec w)  : toFin (z • x) = z • x.toFin := rfl
lemma toFin_pow (x : BitVec w) (n : ℕ)    : toFin (x ^ n) = x.toFin ^ n := rfl

/-!
## Ring
-/

instance : CommSemiring (BitVec w) :=
  toFin_injective.commSemiring _
    rfl /- toFin_zero -/
    rfl /- toFin_one -/
    toFin_add
    toFin_mul
    toFin_nsmul
    toFin_pow
    (fun _ => rfl) /- toFin_natCast -/
-- The statement in the new API would be: `n#(k.succ) = ((n / 2)#k).concat (n % 2 != 0)`

theorem ofInt_negSucc (w n : Nat ) :
    BitVec.ofInt w (Int.negSucc n) = ~~~.ofNat w n := by
  simp [BitVec.ofInt]
  rw [BitVec.toNat_eq]
  simp only [Int.toNat, toNat_ofNatLt, toNat_not, toNat_ofNat]
  split
  · rename_i a b c
    simp only [Int.ofNat_eq_coe] at c
    rw [Int.negSucc_emod] at c
    symm
    rw [← Int.natCast_inj]
    rw [Nat.cast_sub]
    rw [Nat.cast_sub]
    have _ : 0 < 2 ^ w := by simp
    simp_all only [gt_iff_lt, Nat.ofNat_pos, pow_pos, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one, Int.ofNat_emod]
    have h : 0 < 2 ^ w := by simp
    · omega
    · omega
    · omega
  · have nonneg : Int.negSucc n % 2 ^ w ≥ 0 := by
      simp only [ge_iff_le, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
        not_false_eq_true, Int.emod_nonneg (Int.negSucc n) _]
    simp_all only [Nat.ofNat_pos, gt_iff_lt, pow_pos, ne_eq, pow_eq_zero_iff',
      OfNat.ofNat_ne_zero, false_and, not_false_eq_true, ge_iff_le, Int.negSucc_not_nonneg]

@[simp] lemma ofFin_neg {x : Fin (2 ^ w)} : ofFin (-x) = -(ofFin x) := by
  ext; rw [neg_eq_zero_sub]; simp; rfl

@[simp] lemma ofFin_ofNat (n : ℕ) :
    ofFin (no_index (OfNat.ofNat n : Fin (2^w))) = OfNat.ofNat n := by
  simp only [OfNat.ofNat, Fin.ofNat', BitVec.ofNat, Nat.and_pow_two_sub_one_eq_mod]

theorem toFin_inj {x y : BitVec w} : x.toFin = y.toFin ↔ x = y :=
  toFin_injective.eq_iff

@[simp] lemma ofFin_natCast (n : ℕ) : ofFin (n : Fin (2^w)) = n := by
  simp only [Nat.cast, NatCast.natCast, OfNat.ofNat, BitVec.ofNat, Nat.and_pow_two_sub_one_eq_mod]
  rfl

lemma toFin_natCast (n : ℕ) : toFin (n : BitVec w) = n := by
  rw [toFin_inj]; simp only [ofFin_natCast]

theorem ofFin_intCast (z : ℤ) : ofFin (z : Fin (2^w)) = Int.cast z := by
  cases w
  case zero =>
    simp only [eq_nil]
  case succ w =>
    simp only [Int.cast, IntCast.intCast]
    unfold Int.castDef
    cases' z with z z
    · rfl
    · rw [ofInt_negSucc]
      simp only [Nat.cast_add, Nat.cast_one, neg_add_rev]
      rw [← add_ofFin, ofFin_neg, ofFin_ofNat, ofNat_eq_ofNat, ofFin_neg, ofFin_natCast,
        natCast_eq_ofNat, negOne_eq_allOnes, ← sub_toAdd, allOnes_sub_eq_not]

theorem toFin_intCast (z : ℤ) : toFin (z : BitVec w) = z := by
  apply toFin_inj.mpr <| (ofFin_intCast z).symm

lemma toFin_zero : toFin (0 : BitVec w) = 0 := rfl
lemma toFin_one  : toFin (1 : BitVec w) = 1 := by
  rw [toFin_inj]; simp only [ofNat_eq_ofNat, ofFin_ofNat]

instance : CommRing (BitVec w) :=
  toFin_injective.commRing _
    toFin_zero toFin_one toFin_add toFin_mul toFin_neg toFin_sub
    toFin_nsmul toFin_zsmul toFin_pow toFin_natCast toFin_intCast

end BitVec
