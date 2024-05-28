/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Harun Khan, Alex Keizer
-/
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Data.ZMod.Defs

/-!
# Basic Theorems About Bitvectors

This file contains theorems about bitvectors.
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

end BitVec
