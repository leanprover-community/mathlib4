/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Int.Cast.Basic

/-!
# `ULift` instances for ring

This file defines instances for ring, semiring and related structures on `ULift` types.

(Recall `ULift R` is just a "copy" of a type `R` in a higher universe.)

We also provide `ULift.ringEquiv : ULift R ≃+* R`.
-/


universe u

variable {R : Type u}
namespace ULift

instance mulZeroClass {M₀ : Type*} [MulZeroClass M₀] : MulZeroClass (ULift M₀) where
  zero_mul _ := (Equiv.ulift).injective (by simp)
  mul_zero _ := (Equiv.ulift).injective (by simp)

instance distrib [Distrib R] : Distrib (ULift R) where
  left_distrib _ _ _ := (Equiv.ulift).injective (by simp [left_distrib])
  right_distrib _ _ _ := (Equiv.ulift).injective (by simp [right_distrib])

instance instNatCast [NatCast R] : NatCast (ULift R) := ⟨(up ·)⟩
instance instIntCast [IntCast R] : IntCast (ULift R) := ⟨(up ·)⟩

@[simp, norm_cast]
theorem up_natCast [NatCast R] (n : ℕ) : up (n : R) = n :=
  rfl

@[simp]
theorem up_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    up (ofNat(n) : R) = ofNat(n) :=
  rfl

@[simp, norm_cast]
theorem up_intCast [IntCast R] (n : ℤ) : up (n : R) = n :=
  rfl

@[simp, norm_cast]
theorem down_natCast [NatCast R] (n : ℕ) : down (n : ULift R) = n :=
  rfl

@[simp]
theorem down_ofNat [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    down (ofNat(n) : ULift R) = ofNat(n) :=
  rfl

@[simp, norm_cast]
theorem down_intCast [IntCast R] (n : ℤ) : down (n : ULift R) = n :=
  rfl

instance addMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne (ULift R) where
  natCast_zero := congr_arg ULift.up Nat.cast_zero
  natCast_succ _ := congr_arg ULift.up (Nat.cast_succ _)

instance addCommMonoidWithOne [AddCommMonoidWithOne R] : AddCommMonoidWithOne (ULift R) where

instance addGroupWithOne [AddGroupWithOne R] : AddGroupWithOne (ULift R) where
  intCast_ofNat _ := congr_arg ULift.up (Int.cast_natCast _)
  intCast_negSucc _ := congr_arg ULift.up (Int.cast_negSucc _)

instance addCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne (ULift R) where

instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (ULift R) where

instance nonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring (ULift R) where

instance nonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring (ULift R) where

instance semiring [Semiring R] : Semiring (ULift R) where

/-- The ring equivalence between `ULift R` and `R`. -/
def ringEquiv [NonUnitalNonAssocSemiring R] : ULift R ≃+* R where
  toFun := ULift.down
  invFun := ULift.up
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

instance nonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemiring (ULift R) where

instance commSemiring [CommSemiring R] : CommSemiring (ULift R) where

instance nonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (ULift R) where

instance nonUnitalRing [NonUnitalRing R] : NonUnitalRing (ULift R) where

instance nonAssocRing [NonAssocRing R] : NonAssocRing (ULift R) where

instance ring [Ring R] : Ring (ULift R) where

instance nonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing (ULift R) where

instance commRing [CommRing R] : CommRing (ULift R) where

end ULift
