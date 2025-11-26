/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Harun Khan, Alex Keizer
-/
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors which can only be stated in Mathlib or downstream
because they refer to other notions defined in Mathlib.

Please do not extend this file further: material about BitVec needed in downstream projects
can either be PR'd to Lean, or kept downstream if it also relies on Mathlib.
-/

namespace BitVec

variable {w : Nat}

-- TODO: move to the Lean4 repository.
open Fin.CommRing in
theorem ofFin_intCast (z : ℤ) : ofFin (z : Fin (2 ^ w)) = ↑z := by
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
    · omega

open Fin.CommRing in
@[simp] theorem toFin_intCast (z : ℤ) : (z : BitVec w).toFin = ↑z := by
  rw [← ofFin_intCast]

/-!
## Injectivity
-/

theorem toNat_injective {n : Nat} : Function.Injective (BitVec.toNat : BitVec n → _)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem toFin_injective {n : Nat} : Function.Injective (toFin : BitVec n → _)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-!
## Scalar Multiplication and Powers
-/

open Fin.NatCast

lemma toFin_nsmul (n : ℕ) (x : BitVec w) : toFin (n • x) = n • x.toFin :=
  toFin_mul _ _ |>.trans <| by
    open scoped Fin.CommRing in
    simp only [natCast_eq_ofNat, toFin_ofNat, Fin.ofNat_eq_cast, nsmul_eq_mul]

lemma toFin_zsmul (z : ℤ) (x : BitVec w) : toFin (z • x) = z • x.toFin :=
  toFin_mul _ _ |>.trans <| by
    open scoped Fin.CommRing in
    simp only [zsmul_eq_mul, toFin_intCast]

lemma toFin_pow (x : BitVec w) (n : ℕ) : toFin (x ^ n) = x.toFin ^ n := by
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
    toFin_zero
    toFin_one
    toFin_add
    toFin_mul
    toFin_nsmul
    toFin_pow
    toFin_natCast
-- The statement in the new API would be: `n#(k.succ) = ((n / 2)#k).concat (n % 2 != 0)`

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
  map_mul' := toFin_mul
  map_add' := toFin_add

end BitVec
