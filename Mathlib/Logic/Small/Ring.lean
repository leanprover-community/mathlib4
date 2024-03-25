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

instance [NonUnitalNonAssocSemiring α] [Small α] : NonUnitalNonAssocSemiring (Shrink α) := fast_instance%
  (equivShrink _).symm.nonUnitalNonAssocSemiring

instance [NonUnitalSemiring α] [Small α] : NonUnitalSemiring (Shrink α) := fast_instance%
  (equivShrink _).symm.nonUnitalSemiring

instance [AddMonoidWithOne α] [Small α] : AddMonoidWithOne (Shrink α) := fast_instance%
  (equivShrink _).symm.addMonoidWithOne

instance [AddGroupWithOne α] [Small α] : AddGroupWithOne (Shrink α) := fast_instance%
  (equivShrink _).symm.addGroupWithOne

instance [NonAssocSemiring α] [Small α] : NonAssocSemiring (Shrink α) := fast_instance%
  (equivShrink _).symm.nonAssocSemiring

instance [Semiring α] [Small α] : Semiring (Shrink α) := fast_instance%
  (equivShrink _).symm.semiring

instance [NonUnitalCommSemiring α] [Small α] : NonUnitalCommSemiring (Shrink α) := fast_instance%
  (equivShrink _).symm.nonUnitalCommSemiring

instance [CommSemiring α] [Small α] : CommSemiring (Shrink α) := fast_instance%
  (equivShrink _).symm.commSemiring

instance [NonUnitalNonAssocRing α] [Small α] : NonUnitalNonAssocRing (Shrink α) := fast_instance%
  (equivShrink _).symm.nonUnitalNonAssocRing

instance [NonUnitalRing α] [Small α] : NonUnitalRing (Shrink α) := fast_instance%
  (equivShrink _).symm.nonUnitalRing

instance [Ring α] [Small α] : Ring (Shrink α) := fast_instance%
  (equivShrink _).symm.ring

instance [NonUnitalCommRing α] [Small α] : NonUnitalCommRing (Shrink α) := fast_instance%
  (equivShrink _).symm.nonUnitalCommRing

instance [CommRing α] [Small α] : CommRing (Shrink α) := fast_instance%
  (equivShrink _).symm.commRing

instance [Nontrivial α] [Small α] : Nontrivial (Shrink α) := fast_instance%
  (equivShrink _).symm.nontrivial

instance [DivisionRing α] [Small α] : DivisionRing (Shrink α) := fast_instance%
  (equivShrink _).symm.divisionRing

instance [Field α] [Small α] : Field (Shrink α) := fast_instance%
  (equivShrink _).symm.field
