/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Harun Khan, Alex Keizer
-/
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.ZMod.Defs

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors which can only be stated in Mathlib or downstream
because they refer to other notions defined in Mathlib.

Please do not extend this file further: material about BitVec needed in downstream projects
can either be PR'd to Lean, or kept downstream if it also relies on Mathlib.
-/

namespace BitVec

variable {w : Nat}

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

@[simp] lemma ofFin_neg {x : Fin (2 ^ w)} : ofFin (-x) = -(ofFin x) := by
  rfl

@[simp] lemma ofFin_natCast (n : ℕ) : ofFin (n : Fin (2^w)) = n := by
  rfl

lemma toFin_natCast (n : ℕ) : toFin (n : BitVec w) = n := by
  rfl

theorem ofFin_intCast (z : ℤ) : ofFin (z : Fin (2^w)) = ↑z := by
  cases w
  case zero =>
    simp only [eq_nil]
  case succ w =>
    simp only [Int.cast, IntCast.intCast]
    unfold Int.castDef
    cases' z with z z
    · rfl
    · rw [ofInt_negSucc_eq_not_ofNat]
      simp only [Nat.cast_add, Nat.cast_one, neg_add_rev]
      rw [← add_ofFin, ofFin_neg, ofFin_ofNat, ofNat_eq_ofNat, ofFin_neg, ofFin_natCast,
        natCast_eq_ofNat, negOne_eq_allOnes, ← sub_toAdd, allOnes_sub_eq_not]

theorem toFin_intCast (z : ℤ) : toFin (z : BitVec w) = z := by
  apply toFin_inj.mpr <| (ofFin_intCast z).symm

instance : CommRing (BitVec w) :=
  toFin_injective.commRing _
    toFin_zero toFin_one toFin_add toFin_mul toFin_neg toFin_sub
    toFin_nsmul toFin_zsmul toFin_pow toFin_natCast toFin_intCast

/-- The ring `BitVec m` is isomorphic to `Fin (2 ^ m)`. -/
@[simps]
def equivFin {m : ℕ} : BitVec m ≃+* Fin (2 ^ m) where
  toFun a := a.toFin
  invFun a := ofFin a
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end BitVec
