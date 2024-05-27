/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.GroupWithZero.InjSurj

#align_import algebra.group.ulift from "leanprover-community/mathlib"@"564bcc44d2b394a50c0cd6340c14a6b02a50a99a"

/-!
# `ULift` instances for groups and monoids with zero

This file defines instances for group and monoid with zero and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)
-/


universe u

variable {α : Type u}

namespace ULift

instance mulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass (ULift α) :=
  Equiv.ulift.injective.mulZeroOneClass _ rfl rfl (by intros; rfl)
#align ulift.mul_zero_one_class ULift.mulZeroOneClass

instance monoidWithZero [MonoidWithZero α] : MonoidWithZero (ULift α) :=
  Equiv.ulift.injective.monoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.monoid_with_zero ULift.monoidWithZero

instance commMonoidWithZero [CommMonoidWithZero α] : CommMonoidWithZero (ULift α) :=
  Equiv.ulift.injective.commMonoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl
#align ulift.comm_monoid_with_zero ULift.commMonoidWithZero

instance groupWithZero [GroupWithZero α] : GroupWithZero (ULift α) :=
  Equiv.ulift.injective.groupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.group_with_zero ULift.groupWithZero

instance commGroupWithZero [CommGroupWithZero α] : CommGroupWithZero (ULift α) :=
  Equiv.ulift.injective.commGroupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align ulift.comm_group_with_zero ULift.commGroupWithZero

end ULift
