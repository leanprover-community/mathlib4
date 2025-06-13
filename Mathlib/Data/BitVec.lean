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

open Fin.NatCast

instance : SMul ℕ (BitVec w) := ⟨fun x y => ofFin <| x • y.toFin⟩
instance : SMul ℤ (BitVec w) := ⟨fun x y => ofFin <| x • y.toFin⟩
lemma toFin_nsmul (n : ℕ) (x : BitVec w)  : toFin (n • x) = n • x.toFin := rfl
lemma toFin_zsmul (z : ℤ) (x : BitVec w)  : toFin (z • x) = z • x.toFin := rfl
lemma toFin_pow (x : BitVec w) (n : ℕ)    : toFin (x ^ n) = x.toFin ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, BitVec.pow_succ, pow_succ]

/-!
## Ring
-/

-- Verify that the `HPow` instance from Lean agrees definitionally with the instance via `Monoid`.
example : @instHPow (Fin (2 ^ w)) ℕ Monoid.toNatPow = Lean.Grind.Fin.instHPowFinNatOfNeZero := rfl

instance : CommSemiring (BitVec w) :=
  open Fin.CommRing in
  toFin_injective.commSemiring _
    rfl /- toFin_zero -/
    rfl /- toFin_one -/
    toFin_add
    toFin_mul
    toFin_nsmul
    (by convert toFin_pow)
    (fun _ => rfl) /- toFin_natCast -/
-- The statement in the new API would be: `n#(k.succ) = ((n / 2)#k).concat (n % 2 != 0)`

-- Variant of `Fin.intCast_def` for when we are using the `Fin.CommRing` instance.
open Fin.CommRing in
theorem _root_.Fin.intCast_def' {n : Nat} [NeZero n] (x : Int) :
    (x : Fin n) = if 0 ≤ x then Fin.ofNat n x.natAbs else -Fin.ofNat n x.natAbs := by
  unfold Fin.instCommRing
  dsimp [Int.cast, IntCast.intCast, Int.castDef]
  split <;> (simp [Fin.intCast]; omega)

open Fin.CommRing in
@[simp] theorem _root_.Fin.val_intCast {n : Nat} [NeZero n] (x : Int) :
    (x : Fin n).val = (x % n).toNat := by
  rw [Fin.intCast_def']
  split <;> rename_i h
  · simp [Int.emod_natAbs_of_nonneg h]
  · simp only [Fin.ofNat_eq_cast, Fin.val_neg, Fin.natCast_eq_zero, Fin.val_natCast]
    split <;> rename_i h
    · rw [← Int.natCast_dvd] at h
      rw [Int.emod_eq_zero_of_dvd h, Int.toNat_zero]
    · rw [Int.emod_natAbs_of_neg (by omega) (NeZero.ne n), if_neg (by rwa [← Int.natCast_dvd] at h)]
      have : x % n < n := Int.emod_lt_of_pos x (by have := NeZero.ne n; omega)
      omega

-- TODO: move to the Lean4 repository.
open Fin.CommRing in
theorem ofFin_intCast (z : ℤ) : ofFin (z : Fin (2^w)) = ↑z := by
  cases w
  case zero =>
    simp only [eq_nil]
  case succ w =>
    apply BitVec.eq_of_toInt_eq
    rw [toInt_ofFin, Fin.val_intCast, Int.natCast_pow, Nat.cast_ofNat, Int.ofNat_toNat,
      toInt_intCast]
    rw [Int.max_eq_left]
    · have h : (2 ^ (w + 1) : Int) = (2 ^ (w + 1) : Nat) := by simp
      rw [h, Int.emod_bmod]
    · refine Int.emod_nonneg z ?_
      exact pow_ne_zero (w + 1) (by decide)

open Fin.CommRing in
theorem toFin_intCast (z : ℤ) : toFin (z : BitVec w) = z := by
  apply toFin_inj.mpr <| (ofFin_intCast z).symm

instance : CommRing (BitVec w) :=
  open Fin.CommRing in
  toFin_injective.commRing _
    toFin_zero toFin_one toFin_add toFin_mul toFin_neg toFin_sub
    toFin_nsmul toFin_zsmul toFin_pow toFin_natCast toFin_intCast

/-- The ring `BitVec m` is isomorphic to `Fin (2 ^ m)`. -/
@[simps]
def equivFin {m : ℕ} : BitVec m ≃+* Fin (2 ^ m) where
  toFun a := a.toFin
  invFun a := ofFin a
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

end BitVec
