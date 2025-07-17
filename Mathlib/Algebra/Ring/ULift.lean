/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Ring.Equiv

/-!
# `ULift` instances for ring

This file defines instances for ring, semiring and related structures on `ULift` types.

(Recall `ULift R` is just a "copy" of a type `R` in a higher universe.)

We also provide `ULift.ringEquiv : ULift R ≃+* R`.
-/


universe u v

variable {R : Type u}
namespace ULift

instance mulZeroClass {M₀ : Type*} [MulZeroClass M₀] : MulZeroClass (ULift M₀) :=
  { zero := (0 : ULift M₀), mul := (· * ·), zero_mul := fun _ => (Equiv.ulift).injective (by simp),
    mul_zero := fun _ => (Equiv.ulift).injective (by simp) }

instance distrib [Distrib R] : Distrib (ULift R) :=
  { add := (· + ·), mul := (· * ·),
    left_distrib := fun _ _ _ => (Equiv.ulift).injective (by simp [left_distrib]),
    right_distrib := fun _ _ _ => (Equiv.ulift).injective (by simp [right_distrib]) }

instance nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (ULift R) :=
  { zero := (0 : ULift R), add := (· + ·), mul := (· * ·), nsmul := AddMonoid.nsmul,
    zero_add, add_zero, zero_mul, mul_zero, left_distrib, right_distrib,
    nsmul_zero := fun _ => AddMonoid.nsmul_zero _,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _,
    add_assoc, add_comm }

instance nonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring (ULift R) :=
  { ULift.addMonoidWithOne with
      nsmul := AddMonoid.nsmul, natCast := fun n => ULift.up n, add_comm, left_distrib,
      right_distrib, zero_mul, mul_zero, one_mul, mul_one }

instance nonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring (ULift R) :=
  { zero := (0 : ULift R), add := (· + ·), mul := (· * ·), nsmul := AddMonoid.nsmul,
    add_assoc, zero_add, add_zero, add_comm, left_distrib, right_distrib, zero_mul, mul_zero,
    mul_assoc, nsmul_zero := fun _ => AddMonoid.nsmul_zero _,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _ }

instance semiring [Semiring R] : Semiring (ULift R) :=
  { ULift.addMonoidWithOne with
      nsmul := AddMonoid.nsmul,
      npow := Monoid.npow, natCast := fun n => ULift.up n, add_comm, left_distrib, right_distrib,
      zero_mul, mul_zero, mul_assoc, one_mul, mul_one, npow_zero := fun _ => Monoid.npow_zero _,
      npow_succ := fun _ _ => Monoid.npow_succ _ _ }

/-- The ring equivalence between `ULift R` and `R`. -/
def ringEquiv [NonUnitalNonAssocSemiring R] : ULift R ≃+* R where
  toFun := ULift.down
  invFun := ULift.up
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance nonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemiring (ULift R) :=
  { zero := (0 : ULift R), add := (· + ·), mul := (· * ·), nsmul := AddMonoid.nsmul, add_assoc,
    zero_add, add_zero, add_comm, left_distrib, right_distrib, zero_mul, mul_zero, mul_assoc,
    mul_comm, nsmul_zero := fun _ => AddMonoid.nsmul_zero _,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _ }

instance commSemiring [CommSemiring R] : CommSemiring (ULift R) :=
  { ULift.semiring with
      nsmul := AddMonoid.nsmul, natCast := fun n => ULift.up n, npow := Monoid.npow, mul_comm }

instance nonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (ULift R) :=
  { zero := (0 : ULift R), add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
    nsmul := AddMonoid.nsmul, zsmul := SubNegMonoid.zsmul, add_assoc, zero_add, add_zero,
    neg_add_cancel, add_comm, left_distrib, right_distrib, zero_mul, mul_zero, sub_eq_add_neg,
    nsmul_zero := fun _ => AddMonoid.nsmul_zero _,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _,
    zsmul_zero' := SubNegMonoid.zsmul_zero', zsmul_succ' := SubNegMonoid.zsmul_succ',
    zsmul_neg' := SubNegMonoid.zsmul_neg' }

instance nonUnitalRing [NonUnitalRing R] : NonUnitalRing (ULift R) :=
  { zero := (0 : ULift R), add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
    nsmul := AddMonoid.nsmul, zsmul := SubNegMonoid.zsmul, add_assoc, zero_add, add_zero, add_comm,
    neg_add_cancel, left_distrib, right_distrib, zero_mul, mul_zero, mul_assoc, sub_eq_add_neg
    nsmul_zero := fun _ => AddMonoid.nsmul_zero _,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _,
    zsmul_zero' := SubNegMonoid.zsmul_zero', zsmul_succ' := SubNegMonoid.zsmul_succ',
    zsmul_neg' := SubNegMonoid.zsmul_neg' }

instance nonAssocRing [NonAssocRing R] : NonAssocRing (ULift R) :=
  { zero := (0 : ULift R), one := (1 : ULift R), add := (· + ·), mul := (· * ·), sub := Sub.sub,
    neg := Neg.neg, nsmul := AddMonoid.nsmul, natCast := fun n => ULift.up n,
    intCast := fun n => ULift.up n, zsmul := SubNegMonoid.zsmul,
    intCast_ofNat := addGroupWithOne.intCast_ofNat, add_assoc, zero_add,
    add_zero, neg_add_cancel, add_comm, left_distrib, right_distrib, zero_mul, mul_zero, one_mul,
    mul_one, sub_eq_add_neg, nsmul_zero := fun _ => AddMonoid.nsmul_zero _,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _,
    zsmul_zero' := SubNegMonoid.zsmul_zero', zsmul_succ' := SubNegMonoid.zsmul_succ',
    zsmul_neg' := SubNegMonoid.zsmul_neg',
    natCast_zero := AddMonoidWithOne.natCast_zero, natCast_succ := AddMonoidWithOne.natCast_succ,
    intCast_negSucc := AddGroupWithOne.intCast_negSucc }

instance ring [Ring R] : Ring (ULift R) :=
  { zero := (0 : ULift R), one := (1 : ULift R), add := (· + ·), mul := (· * ·), sub := Sub.sub,
    neg := Neg.neg, nsmul := AddMonoid.nsmul, npow := Monoid.npow, zsmul := SubNegMonoid.zsmul,
    intCast_ofNat := addGroupWithOne.intCast_ofNat, add_assoc, zero_add, add_zero, add_comm,
    left_distrib, right_distrib, zero_mul, mul_zero, mul_assoc, one_mul, mul_one, sub_eq_add_neg,
    neg_add_cancel, nsmul_zero := fun _ => AddMonoid.nsmul_zero _, natCast := fun n => ULift.up n,
    intCast := fun n => ULift.up n, nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _,
    natCast_zero := AddMonoidWithOne.natCast_zero, natCast_succ := AddMonoidWithOne.natCast_succ,
    npow_zero := fun _ => Monoid.npow_zero _, npow_succ := fun _ _ => Monoid.npow_succ _ _,
    zsmul_zero' := SubNegMonoid.zsmul_zero', zsmul_succ' := SubNegMonoid.zsmul_succ',
    zsmul_neg' := SubNegMonoid.zsmul_neg', intCast_negSucc := AddGroupWithOne.intCast_negSucc }

instance nonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing (ULift R) :=
  { zero := (0 : ULift R), add := (· + ·), mul := (· * ·), sub := Sub.sub, neg := Neg.neg,
    nsmul := AddMonoid.nsmul, zsmul := SubNegMonoid.zsmul, zero_mul, add_assoc, zero_add, add_zero,
    mul_zero, left_distrib, right_distrib, add_comm, mul_assoc, mul_comm,
    nsmul_zero := fun _ => AddMonoid.nsmul_zero _, neg_add_cancel,
    nsmul_succ := fun _ _ => AddMonoid.nsmul_succ _ _, sub_eq_add_neg,
    zsmul_zero' := SubNegMonoid.zsmul_zero',
    zsmul_succ' := SubNegMonoid.zsmul_succ',
    zsmul_neg' := SubNegMonoid.zsmul_neg'.. }

instance commRing [CommRing R] : CommRing (ULift R) :=
  { ULift.ring with mul_comm }

end ULift
