/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.ULift

#align_import algebra.field.ulift from "leanprover-community/mathlib"@"13e18cfa070ea337ea960176414f5ae3a1534aae"

/-!
# Field instances for `ULift`

This file defines instances for field, semifield and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)
-/

universe u v
variable {α : Type u} {x y : ULift.{v} α}

namespace ULift

instance instNNRatCast [NNRatCast α] : NNRatCast (ULift α) where nnratCast q := up q
instance instRatCast [RatCast α] : RatCast (ULift α) where ratCast q := up q

@[simp, norm_cast] lemma up_nnratCast [NNRatCast α] (q : ℚ≥0) : up (q : α) = q := rfl
@[simp, norm_cast] lemma down_nnratCast [NNRatCast α] (q : ℚ≥0) : down (q : ULift α) = q := rfl
@[simp, norm_cast] lemma up_ratCast [RatCast α] (q : ℚ) : up (q : α) = q := rfl
@[simp, norm_cast] lemma down_ratCast [RatCast α] (q : ℚ) : down (q : ULift α) = q := rfl
#align ulift.up_rat_cast ULift.up_ratCast
#align ulift.down_rat_cast ULift.down_ratCast

instance divisionSemiring [DivisionSemiring α] : DivisionSemiring (ULift α) := by
  refine' down_injective.divisionSemiring down .. <;> intros <;> rfl
#align ulift.division_semiring ULift.divisionSemiring

instance semifield [Semifield α] : Semifield (ULift α) :=
  { ULift.divisionSemiring, ULift.commGroupWithZero with }
#align ulift.semifield ULift.semifield

instance divisionRing [DivisionRing α] : DivisionRing (ULift α) := by
  refine' down_injective.divisionRing down .. <;> intros <;> rfl
#align ulift.division_ring ULift.divisionRing

instance field [Field α] : Field (ULift α) :=
  { ULift.semifield, ULift.divisionRing with }
#align ulift.field ULift.field

end ULift
