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
  { zero := (0 : ULift α), mul := (· * ·), zero_mul := fun _ => (Equiv.ulift).injective (by simp),
    mul_zero := fun _ => (Equiv.ulift).injective (by simp) }
#align ulift.mul_zero_class ULift.mulZeroClass

instance distrib [Distrib α] : Distrib (ULift α) :=
  { add := (· + ·), mul := (· * ·),
    left_distrib := fun _ _ _ => (Equiv.ulift).injective (by simp [left_distrib]),
    right_distrib := fun _ _ _ => (Equiv.ulift).injective (by simp [right_distrib]) }
#align ulift.distrib ULift.distrib

instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] :
    NonUnitalNonAssocSemiring (ULift α) :=
  { zero := (0 : ULift α), add := (· + ·), mul := (· * ·), nsmul := AddMonoid.nsmul,
    zero_add, add_zero, zero_mul, mul_zero, left_distrib, right_distrib,
    nsmul_zero := fun _ => AddMonoid.nsmul_zero _,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _,
    add_assoc, add_comm }
#align ulift.non_unital_non_assoc_semiring ULift.nonUnitalNonAssocSemiring

instance nonAssocSemiring [NonAssocSemiring α] : NonAssocSemiring (ULift α) :=
  { ULift.addMonoidWithOne with
      nsmul := AddMonoid.nsmul, natCast := fun n => ULift.up n, add_comm, left_distrib,
      right_distrib, zero_mul, mul_zero, one_mul, mul_one }
#align ulift.non_assoc_semiring ULift.nonAssocSemiring

instance nonUnitalSemiring [NonUnitalSemiring α] : NonUnitalSemiring (ULift α) :=
  { zero := (0 : ULift α), add := (· + ·), mul := (· * ·), nsmul := AddMonoid.nsmul,
    add_assoc, zero_add, add_zero, add_comm, left_distrib, right_distrib, zero_mul, mul_zero,
    mul_assoc, nsmul_zero := fun _ => AddMonoid.nsmul_zero _,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _ }
#align ulift.non_unital_semiring ULift.nonUnitalSemiring

instance semiring [Semiring α] : Semiring (ULift α) :=
  { ULift.addMonoidWithOne with
      nsmul := AddMonoid.nsmul,
      npow := Monoid.npow, natCast := fun n => ULift.up n, add_comm, left_distrib, right_distrib,
      zero_mul, mul_zero, mul_assoc, one_mul, mul_one, npow_zero := fun _ => Monoid.npow_zero _,
      npow_succ := fun _ _ => Monoid.npow_succ _ _ }
#align ulift.semiring ULift.semiring

/-- The ring equivalence between `ULift α` and `α`. -/
def ringEquiv [NonUnitalNonAssocSemiring α] : ULift α ≃+* α where
  toFun := ULift.down
  invFun := ULift.up
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
#align ulift.ring_equiv ULift.ringEquiv

instance nonUnitalCommSemiring [NonUnitalCommSemiring α] : NonUnitalCommSemiring (ULift α) :=
  { zero := (0 : ULift α), add := (· + ·), mul := (· * ·), nsmul := AddMonoid.nsmul, add_assoc,
    zero_add, add_zero, add_comm, left_distrib, right_distrib, zero_mul, mul_zero, mul_assoc,
    mul_comm, nsmul_zero := fun _ => AddMonoid.nsmul_zero _,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _ }
#align ulift.non_unital_comm_semiring ULift.nonUnitalCommSemiring

instance commSemiring [CommSemiring α] : CommSemiring (ULift α) :=
  { ULift.semiring with
      nsmul := AddMonoid.nsmul, natCast := fun n => ULift.up n, npow := Monoid.npow, mul_comm }
#align ulift.comm_semiring ULift.commSemiring

instance nonUnitalNonAssocRing [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (ULift α) :=
  { zero := (0 : ULift α), add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
    nsmul := AddMonoid.nsmul, zsmul := SubNegMonoid.zsmul, add_assoc, zero_add, add_zero,
    add_left_neg, add_comm, left_distrib, right_distrib, zero_mul, mul_zero, sub_eq_add_neg,
    nsmul_zero := fun _ => AddMonoid.nsmul_zero _,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _,
    zsmul_zero' := SubNegMonoid.zsmul_zero', zsmul_succ' := SubNegMonoid.zsmul_succ',
    zsmul_neg' := SubNegMonoid.zsmul_neg' }
#align ulift.non_unital_non_assoc_ring ULift.nonUnitalNonAssocRing

instance nonUnitalRing [NonUnitalRing α] : NonUnitalRing (ULift α) :=
  { zero := (0 : ULift α), add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
    nsmul := AddMonoid.nsmul, zsmul := SubNegMonoid.zsmul, add_assoc, zero_add, add_zero, add_comm,
    add_left_neg, left_distrib, right_distrib, zero_mul, mul_zero, mul_assoc, sub_eq_add_neg
    nsmul_zero := fun _ => AddMonoid.nsmul_zero _,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _,
    zsmul_zero' := SubNegMonoid.zsmul_zero', zsmul_succ' := SubNegMonoid.zsmul_succ',
    zsmul_neg' := SubNegMonoid.zsmul_neg' }
#align ulift.non_unital_ring ULift.nonUnitalRing

instance nonAssocRing [NonAssocRing α] : NonAssocRing (ULift α) :=
  { zero := (0 : ULift α), one := (1 : ULift α), add := (· + ·), mul := (· * ·), sub := Sub.sub,
    neg := Neg.neg, nsmul := AddMonoid.nsmul, natCast := fun n => ULift.up n,
    intCast := fun n => ULift.up n, zsmul := SubNegMonoid.zsmul,
    intCast_ofNat := addGroupWithOne.intCast_ofNat, add_assoc, zero_add,
    add_zero, add_left_neg, add_comm, left_distrib, right_distrib, zero_mul, mul_zero, one_mul,
    mul_one, sub_eq_add_neg, nsmul_zero := fun _ => AddMonoid.nsmul_zero _,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _,
    zsmul_zero' := SubNegMonoid.zsmul_zero', zsmul_succ' := SubNegMonoid.zsmul_succ',
    zsmul_neg' := SubNegMonoid.zsmul_neg',
    natCast_zero := AddMonoidWithOne.natCast_zero, natCast_succ := AddMonoidWithOne.natCast_succ,
    intCast_negSucc := AddGroupWithOne.intCast_negSucc }
#align ulift.non_assoc_ring ULift.nonAssocRing

instance ring [Ring α] : Ring (ULift α) :=
  { zero := (0 : ULift α), one := (1 : ULift α), add := (· + ·), mul := (· * ·), sub := Sub.sub,
    neg := Neg.neg, nsmul := AddMonoid.nsmul, npow := Monoid.npow, zsmul := SubNegMonoid.zsmul,
    intCast_ofNat := addGroupWithOne.intCast_ofNat, add_assoc, zero_add, add_zero, add_comm,
    left_distrib, right_distrib, zero_mul, mul_zero, mul_assoc, one_mul, mul_one, sub_eq_add_neg,
    add_left_neg, nsmul_zero := fun _ => AddMonoid.nsmul_zero _, natCast := fun n => ULift.up n,
    intCast := fun n => ULift.up n, nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _,
    natCast_zero := AddMonoidWithOne.natCast_zero, natCast_succ := AddMonoidWithOne.natCast_succ,
    npow_zero := fun _ => Monoid.npow_zero _, npow_succ := fun _ _ => Monoid.npow_succ _ _,
    zsmul_zero' := SubNegMonoid.zsmul_zero', zsmul_succ' := SubNegMonoid.zsmul_succ',
    zsmul_neg' := SubNegMonoid.zsmul_neg', intCast_negSucc := AddGroupWithOne.intCast_negSucc }
#align ulift.ring ULift.ring

instance nonUnitalCommRing [NonUnitalCommRing α] : NonUnitalCommRing (ULift α) :=
  { zero := (0 : ULift α), add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
    nsmul := AddMonoid.nsmul, zsmul := SubNegMonoid.zsmul, zero_mul, add_assoc, zero_add, add_zero,
    mul_zero, left_distrib, right_distrib, add_comm, mul_assoc, mul_comm,
    nsmul_zero := fun _ => AddMonoid.nsmul_zero _, add_left_neg,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _, sub_eq_add_neg,
    zsmul_zero' := SubNegMonoid.zsmul_zero',
    zsmul_succ' := SubNegMonoid.zsmul_succ',
    zsmul_neg' := SubNegMonoid.zsmul_neg'.. }
#align ulift.non_unital_comm_ring ULift.nonUnitalCommRing

instance commRing [CommRing α] : CommRing (ULift α) :=
  { ULift.ring with mul_comm }
#align ulift.comm_ring ULift.commRing

end ULift
