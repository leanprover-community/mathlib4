/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Ring.TransferInstance

/-!
# Transfer ring structures from `α` to `Shrink α`
-/

@[expose] public section

namespace Shrink
universe v
variable {α : Type*} [Small.{v} α]

variable (α) in
/-- Shrink `α` to a smaller universe preserves ring structure. -/
noncomputable def ringEquiv [Add α] [Mul α] : Shrink.{v} α ≃+* α := (equivShrink α).symm.ringEquiv

noncomputable instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalNonAssocSemiring

noncomputable instance [NonUnitalSemiring α] : NonUnitalSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalSemiring

noncomputable instance [AddMonoidWithOne α] : AddMonoidWithOne (Shrink.{v} α) :=
  (equivShrink α).symm.addMonoidWithOne

noncomputable instance [AddGroupWithOne α] : AddGroupWithOne (Shrink.{v} α) :=
  (equivShrink α).symm.addGroupWithOne

noncomputable instance [NonAssocSemiring α] : NonAssocSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonAssocSemiring

noncomputable instance [Semiring α] : Semiring (Shrink.{v} α) := (equivShrink α).symm.semiring

noncomputable instance [NonUnitalCommSemiring α] : NonUnitalCommSemiring (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalCommSemiring

noncomputable
instance [CommSemiring α] : CommSemiring (Shrink.{v} α) := (equivShrink α).symm.commSemiring

noncomputable instance [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalNonAssocRing

noncomputable
instance [NonUnitalRing α] : NonUnitalRing (Shrink.{v} α) := (equivShrink α).symm.nonUnitalRing
noncomputable
instance [NonAssocRing α] : NonAssocRing (Shrink.{v} α) := (equivShrink α).symm.nonAssocRing
noncomputable instance [Ring α] : Ring (Shrink.{v} α) := (equivShrink α).symm.ring

noncomputable instance [NonUnitalCommRing α] : NonUnitalCommRing (Shrink.{v} α) :=
  (equivShrink α).symm.nonUnitalCommRing

noncomputable instance [CommRing α] : CommRing (Shrink.{v} α) := (equivShrink α).symm.commRing
instance [Semiring α] [IsDomain α] : IsDomain (Shrink.{v} α) := (Shrink.ringEquiv α).isDomain

end Shrink
