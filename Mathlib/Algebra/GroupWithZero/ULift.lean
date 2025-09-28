/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.GroupWithZero.InjSurj

/-!
# `ULift` instances for groups and monoids with zero

This file defines instances for group and monoid with zero and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)
-/

assert_not_exists Ring

universe u

variable {α : Type u}

namespace ULift

instance mulZeroOneClass [MulZeroOneClass α] : MulZeroOneClass (ULift α) :=
  Equiv.ulift.injective.mulZeroOneClass _ rfl rfl (by intros; rfl)

instance monoidWithZero [MonoidWithZero α] : MonoidWithZero (ULift α) :=
  Equiv.ulift.injective.monoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl

instance commMonoidWithZero [CommMonoidWithZero α] : CommMonoidWithZero (ULift α) :=
  Equiv.ulift.injective.commMonoidWithZero _ rfl rfl (fun _ _ => rfl) fun _ _ => rfl

instance groupWithZero [GroupWithZero α] : GroupWithZero (ULift α) :=
  Equiv.ulift.injective.groupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance commGroupWithZero [CommGroupWithZero α] : CommGroupWithZero (ULift α) :=
  Equiv.ulift.injective.commGroupWithZero _ rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

end ULift
