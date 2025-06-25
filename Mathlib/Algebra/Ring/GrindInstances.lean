/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Basic

/-!
# Instances for `grind`.
-/

open Lean

variable (α : Type*)

instance CommRing.toGrindCommRing [s : CommRing α] :
    Grind.CommRing α :=
  { s with
    ofNat | 0 | 1 | n + 2 => inferInstance
    natCast := inferInstance
    intCast := inferInstance
    add_zero := by simp [add_zero]
    neg_add_cancel := by simp [neg_add_cancel]
    mul_one := by simp [mul_one]
    zero_mul := by simp [zero_mul]
    pow_zero := by simp
    pow_succ := by simp [pow_succ]
    ofNat_eq_natCast
    | 0 => Nat.cast_zero.symm
    | 1 => Nat.cast_one.symm
    | n + 2 => rfl
    ofNat_succ
    | 0 => by simp [zero_add]
    | 1 => by
      show Nat.cast 2 = 1 + 1
      rw [one_add_one_eq_two]
      rfl
    | n + 2 => by
      show Nat.cast (n + 2 + 1) = Nat.cast (n + 2) + 1
      rw [← AddMonoidWithOne.natCast_succ]
    intCast_ofNat
    | 0 => Int.cast_zero
    | 1 => Int.cast_one
    | n + 2 => Int.cast_ofNat _
    intCast_neg := Int.cast_neg }

theorem CommRing.toGrindCommRing_ofNat [CommRing α] (n : ℕ) :
    @OfNat.ofNat α n (Lean.Grind.Semiring.ofNat n) = n.cast := by
  match n with
  | 0 => simp [zero_add]
  | 1 => simp [one_add_one_eq_two]
  | n + 2 => rfl

attribute [local instance] Grind.Semiring.natCast Grind.Ring.intCast in
-- Verify that we can construct a `CommRing` from a `Lean.Grind.CommRing`.
-- This is not an instance (or even a `def`) because this direction should never be used.
-- There is no reason to expect that using `CommRing.toGrindCommRing` and then this construction
-- will give a result defeq to the original `CommRing α`.
example (s : Grind.CommRing α) : CommRing α :=
  { s with
    zero_add := Grind.Semiring.zero_add
    right_distrib := Grind.Semiring.right_distrib
    mul_zero := Grind.Semiring.mul_zero
    one_mul := Grind.Semiring.one_mul
    nsmul := nsmulRec
    zsmul := zsmulRec
    natCast := Nat.cast
    natCast_zero :=  Grind.Semiring.natCast_zero
    natCast_succ n := Grind.Semiring.natCast_succ n
    intCast := Int.cast
    intCast_ofNat := Grind.Ring.intCast_natCast
    intCast_negSucc n := by
      rw [Int.negSucc_eq, Grind.Ring.intCast_neg,
        Grind.Ring.intCast_natCast_add_one, Grind.Semiring.natCast_succ] }
