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

-- This is a low priority instance so that the built-in `Lean.Grind.Semiring Nat` instance
-- (which has a non-defeq `ofNat` instance) is used preferentially.
instance (priority := 100) Semiring.toGrindSemiring [s : Semiring α] :
    Grind.Semiring α :=
  { s with
    nsmul := ⟨s.nsmul⟩
    npow := ⟨fun a n => a^n⟩
    ofNat | 0 | 1 | n + 2 => inferInstance
    natCast := inferInstance
    add_zero := by simp [add_zero]
    mul_one := by simp [mul_one]
    zero_mul := by simp [zero_mul]
    pow_zero a := by simp
    pow_succ a n := by simp [pow_succ]
    ofNat_eq_natCast
    | 0 => Nat.cast_zero.symm
    | 1 => Nat.cast_one.symm
    | n + 2 => rfl
    ofNat_succ
    | 0 => by simp [zero_add]
    | 1 => by
      change Nat.cast 2 = 1 + 1
      rw [one_add_one_eq_two]
      rfl
    | n + 2 => by
      change Nat.cast (n + 2 + 1) = Nat.cast (n + 2) + 1
      rw [← AddMonoidWithOne.natCast_succ]
    nsmul_eq_natCast_mul n a := nsmul_eq_mul n a }

instance (priority := 100) CommSemiring.toGrindCommSemiring [s : CommSemiring α] :
    Grind.CommSemiring α :=
  { Semiring.toGrindSemiring α with
    mul_comm := s.mul_comm }

instance (priority := 100) Ring.toGrindRing [s : Ring α] :
    Grind.Ring α :=
  { s, Semiring.toGrindSemiring α with
    nsmul := ⟨s.nsmul⟩
    npow := ⟨fun a n => a^n⟩
    zsmul := ⟨s.zsmul⟩
    natCast := inferInstance
    intCast := inferInstance
    neg_zsmul i a := neg_zsmul a i
    neg_add_cancel := by simp [neg_add_cancel]
    intCast_ofNat
    | 0 => Int.cast_zero
    | 1 => Int.cast_one
    | _ + 2 => Int.cast_ofNat _
    intCast_neg := Int.cast_neg
    zsmul_natCast_eq_nsmul n a := natCast_zsmul a n }

instance (priority := 100) CommRing.toGrindCommRing [s : CommRing α] :
    Grind.CommRing α :=
  { Ring.toGrindRing α with
    mul_comm := s.mul_comm }

theorem Semiring.toGrindSemiring_ofNat [Semiring α] (n : ℕ) :
    @OfNat.ofNat α n (Lean.Grind.Semiring.ofNat n) = n.cast := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => rfl

attribute [local instance] Grind.Semiring.natCast Grind.Ring.intCast in
-- Verify that we can construct a `CommRing` from a `Lean.Grind.CommRing`.
-- This is not an instance (or even a `def`) because this direction should never be used.
-- There is no reason to expect that using `CommRing.toGrindCommRing` and then this construction
-- will give a result defeq to the original `CommRing α`.
example (s : Grind.CommRing α) : CommRing α :=
  { s with
    zero_add := Grind.AddCommMonoid.zero_add
    right_distrib := Grind.Semiring.right_distrib
    mul_zero := Grind.Semiring.mul_zero
    one_mul := Grind.Semiring.one_mul
    nsmul := nsmulRec
    zsmul := zsmulRec
    npow := npowRec
    natCast := Nat.cast
    natCast_zero :=  Grind.Semiring.natCast_zero
    natCast_succ n := Grind.Semiring.natCast_succ n
    intCast := Int.cast
    intCast_ofNat := Grind.Ring.intCast_natCast
    intCast_negSucc n := by
      rw [Int.negSucc_eq, Grind.Ring.intCast_neg,
        Grind.Ring.intCast_natCast_add_one, Grind.Semiring.natCast_succ] }

-- Verify that we do not have a defeq problems in `Lean.Grind.Semiring` instances.
example : (inferInstance : Lean.Grind.Semiring Nat) =
    (Lean.Grind.CommSemiring.toSemiring : Lean.Grind.Semiring Nat) := rfl
example : (inferInstance : Lean.Grind.Semiring UInt8) =
    (Lean.Grind.CommSemiring.toSemiring : Lean.Grind.Semiring UInt8) := rfl
