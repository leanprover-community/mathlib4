/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.Ring.TransferInstance

/-!
# Transfer ring structures from `α` to `Shrink α`
-/

noncomputable section

namespace Shrink
universe v
variable {α : Type*} [Small.{v} α]

variable (α) in
/-- Shrink `α` to a smaller universe preserves ring structure. -/
def ringEquiv [Add α] [Mul α] : Shrink.{v} α ≃+* α := (equivShrink α).symm.ringEquiv

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalNonAssocSemiring

instance [NonUnitalSemiring α] : NonUnitalSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalSemiring

instance [AddMonoidWithOne α] : AddMonoidWithOne (Shrink.{v} α) :=
  (equivShrink α).symm.addMonoidWithOne

instance [AddGroupWithOne α] : AddGroupWithOne (Shrink.{v} α) :=
  (equivShrink α).symm.addGroupWithOne

instance [NonAssocSemiring α] : NonAssocSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonAssocSemiring

instance [Semiring α] : Semiring (Shrink.{v} α) := (equivShrink α).symm.semiring

instance [NonUnitalCommSemiring α] : NonUnitalCommSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalCommSemiring

instance [CommSemiring α] : CommSemiring (Shrink.{v} α) := (equivShrink α).symm.commSemiring

instance [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalNonAssocRing

instance [NonUnitalRing α] : NonUnitalRing (Shrink.{v} α) := (equivShrink α).symm.nonUnitalRing
instance [NonAssocRing α] : NonAssocRing (Shrink.{v} α) := (equivShrink α).symm.nonAssocRing
instance [Ring α] : Ring (Shrink.{v} α) := (equivShrink α).symm.ring

instance [NonUnitalCommRing α] : NonUnitalCommRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalCommRing

instance [CommRing α] : CommRing (Shrink.{v} α) := (equivShrink α).symm.commRing
instance [Semiring α] [IsDomain α] : IsDomain (Shrink.{v} α) := (Shrink.ringEquiv α).isDomain

end Shrink
