/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Ring.Equiv

#align_import algebra.ring.ulift from "leanprover-community/mathlib"@"13e18cfa070ea337ea960176414f5ae3a1534aae"

/-!
# `ULift` instances for ring

This file defines instances for ring, semiring and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)

We also provide `ULift.ringEquiv : ULift R ≃+* R`.
-/


universe u v

variable {α : Type u}
namespace ULift

-- Porting note: All these instances used `refine_struct` and `pi_instance_derive_field`

instance mulZeroClass [MulZeroClass α] : MulZeroClass (ULift α) :=
  { zero_mul := fun _ => (Equiv.ulift).injective (by simp),
    mul_zero := fun _ => (Equiv.ulift).injective (by simp) }
#align ulift.mul_zero_class ULift.mulZeroClass

instance distrib [Distrib α] : Distrib (ULift α) :=
  { left_distrib := fun _ _ _ => (Equiv.ulift).injective (by simp [left_distrib]),
    right_distrib := fun _ _ _ => (Equiv.ulift).injective (by simp [right_distrib]) }
#align ulift.distrib ULift.distrib

instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] :
    NonUnitalNonAssocSemiring (ULift α) :=
  { addCommMonoid, distrib, mulZeroClass with }
#align ulift.non_unital_non_assoc_semiring ULift.nonUnitalNonAssocSemiring

instance nonAssocSemiring [NonAssocSemiring α] : NonAssocSemiring (ULift α) :=
  { ULift.nonUnitalNonAssocSemiring, mulZeroOneClass, addCommMonoidWithOne with }
#align ulift.non_assoc_semiring ULift.nonAssocSemiring

instance nonUnitalSemiring [NonUnitalSemiring α] : NonUnitalSemiring (ULift α) :=
  { ULift.nonUnitalNonAssocSemiring with mul_assoc }
#align ulift.non_unital_semiring ULift.nonUnitalSemiring

instance semiring [Semiring α] : Semiring (ULift α) :=
  { ULift.nonAssocSemiring with
    npow := Monoid.npow,
    mul_assoc,
    npow_zero := fun _ => Monoid.npow_zero _,
    npow_succ := fun _ _ => Monoid.npow_succ _ _ }
#align ulift.semiring ULift.semiring

/-- The ring equivalence between `ULift α` and `α`.-/
def ringEquiv [NonUnitalNonAssocSemiring α] : ULift α ≃+* α where
  toFun := ULift.down
  invFun := ULift.up
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
#align ulift.ring_equiv ULift.ringEquiv

instance nonUnitalCommSemiring [NonUnitalCommSemiring α] : NonUnitalCommSemiring (ULift α) :=
  { nonUnitalSemiring with mul_comm }
#align ulift.non_unital_comm_semiring ULift.nonUnitalCommSemiring

instance commSemiring [CommSemiring α] : CommSemiring (ULift α) :=
  { ULift.semiring with mul_comm }
#align ulift.comm_semiring ULift.commSemiring

instance nonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (ULift α) :=
  { ULift.addCommGroup, ULift.nonUnitalNonAssocSemiring with }
#align ulift.non_unital_non_assoc_ring ULift.nonUnitalNonAssocRing

instance nonUnitalRing [NonUnitalRing α] : NonUnitalRing (ULift α) :=
  { ULift.nonUnitalNonAssocRing with mul_assoc }
#align ulift.non_unital_ring ULift.nonUnitalRing

instance nonAssocRing [NonAssocRing α] : NonAssocRing (ULift α) :=
  { nonUnitalNonAssocRing, ULift.nonAssocSemiring, addGroupWithOne with }
#align ulift.non_assoc_ring ULift.nonAssocRing

instance ring [Ring α] : Ring (ULift α) :=
  { ULift.semiring, ULift.nonAssocRing with mul_assoc }
#align ulift.ring ULift.ring

instance nonUnitalCommRing [NonUnitalCommRing α] : NonUnitalCommRing (ULift α) :=
  { ULift.nonUnitalRing with mul_comm }
#align ulift.non_unital_comm_ring ULift.nonUnitalCommRing

instance commRing [CommRing α] : CommRing (ULift α) :=
  { ULift.ring with mul_comm }
#align ulift.comm_ring ULift.commRing

end ULift
