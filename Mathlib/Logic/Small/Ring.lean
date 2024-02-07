/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.Small.Defs
import Mathlib.Logic.Equiv.TransferInstance

/-!
# Transfer ring structures from `α` to `Shrink α`.
-/

set_option autoImplicit true

noncomputable section

instance (priority := 10000) [NonUnitalNonAssocSemiring α] [Small α] : NonUnitalNonAssocSemiring (Shrink α) :=
  (equivShrink _).symm.nonUnitalNonAssocSemiring

instance (priority := 10000) [NonUnitalSemiring α] [Small α] : NonUnitalSemiring (Shrink α) :=
  (equivShrink _).symm.nonUnitalSemiring

instance (priority := 10000) [AddMonoidWithOne α] [Small α] : AddMonoidWithOne (Shrink α) :=
  (equivShrink _).symm.addMonoidWithOne

instance (priority := 10000) [AddGroupWithOne α] [Small α] : AddGroupWithOne (Shrink α) :=
  (equivShrink _).symm.addGroupWithOne

instance (priority := 10000) [NonAssocSemiring α] [Small α] : NonAssocSemiring (Shrink α) :=
  (equivShrink _).symm.nonAssocSemiring

instance (priority := 10000) [Semiring α] [Small α] : Semiring (Shrink α) :=
  (equivShrink _).symm.semiring

instance (priority := 10000) [NonUnitalCommSemiring α] [Small α] : NonUnitalCommSemiring (Shrink α) :=
  (equivShrink _).symm.nonUnitalCommSemiring

instance (priority := 10000) [CommSemiring α] [Small α] : CommSemiring (Shrink α) :=
  (equivShrink _).symm.commSemiring

instance (priority := 10000) [NonUnitalNonAssocRing α] [Small α] : NonUnitalNonAssocRing (Shrink α) :=
  (equivShrink _).symm.nonUnitalNonAssocRing

instance (priority := 10000) [NonUnitalRing α] [Small α] : NonUnitalRing (Shrink α) :=
  (equivShrink _).symm.nonUnitalRing

instance (priority := 10000) [Ring α] [Small α] : Ring (Shrink α) :=
  (equivShrink _).symm.ring

instance (priority := 10000) [NonUnitalCommRing α] [Small α] : NonUnitalCommRing (Shrink α) :=
  (equivShrink _).symm.nonUnitalCommRing

instance (priority := 10000) [CommRing α] [Small α] : CommRing (Shrink α) :=
  (equivShrink _).symm.commRing

instance (priority := 10000) [Nontrivial α] [Small α] : Nontrivial (Shrink α) :=
  (equivShrink _).symm.nontrivial

instance (priority := 10000) [DivisionRing α] [Small α] : DivisionRing (Shrink α) :=
  (equivShrink _).symm.divisionRing

instance (priority := 10000) [Field α] [Small α] : Field (Shrink α) :=
  (equivShrink _).symm.field
