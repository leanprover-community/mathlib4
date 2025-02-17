/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.ULift
import Mathlib.Algebra.Ring.ULift

/-!
# Field instances for `ULift`

This file defines instances for field, semifield and related structures on `ULift` types.

(Recall `ULift α` is just a "copy" of a type `α` in a higher universe.)
-/

universe u
variable {α : Type u}

namespace ULift

instance instNNRatCast [NNRatCast α] : NNRatCast (ULift α) where nnratCast q := up q
instance instRatCast [RatCast α] : RatCast (ULift α) where ratCast q := up q

@[simp, norm_cast] lemma up_nnratCast [NNRatCast α] (q : ℚ≥0) : up (q : α) = q := rfl
@[simp, norm_cast] lemma down_nnratCast [NNRatCast α] (q : ℚ≥0) : down (q : ULift α) = q := rfl
@[simp, norm_cast] lemma up_ratCast [RatCast α] (q : ℚ) : up (q : α) = q := rfl
@[simp, norm_cast] lemma down_ratCast [RatCast α] (q : ℚ) : down (q : ULift α) = q := rfl

instance divisionSemiring [DivisionSemiring α] : DivisionSemiring (ULift α) where
  toSemiring := semiring
  __ := groupWithZero
  nnqsmul_def _ _ := congrArg up <| DivisionSemiring.nnqsmul_def _ _
  nnratCast_def _ := congrArg up <| DivisionSemiring.nnratCast_def _

instance semifield [Semifield α] : Semifield (ULift α) :=
  { ULift.divisionSemiring, ULift.commGroupWithZero with }

instance divisionRing [DivisionRing α] : DivisionRing (ULift α) where
  toRing := ring
  __ := groupWithZero
  nnqsmul_def _ _ := congrArg up <| DivisionSemiring.nnqsmul_def _ _
  nnratCast_def _ := congrArg up <| DivisionSemiring.nnratCast_def _
  qsmul_def _ _ := congrArg up <| DivisionRing.qsmul_def _ _
  ratCast_def _ := congrArg up <| DivisionRing.ratCast_def _

instance field [Field α] : Field (ULift α) :=
  { ULift.semifield, ULift.divisionRing with }

end ULift
