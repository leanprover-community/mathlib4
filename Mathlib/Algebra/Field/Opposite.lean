/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.field.opposite
! leanprover-community/mathlib commit acebd8d49928f6ed8920e502a6c90674e75bd441
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Field structure on the multiplicative/additive opposite
-/

namespace MulOpposite

variable (α : Type _)

@[to_additive]
instance [HasRatCast α] : HasRatCast αᵐᵒᵖ :=
  ⟨fun n => op n⟩

variable {α}

@[simp, norm_cast, to_additive]
theorem op_ratCast [HasRatCast α] (q : ℚ) : op (q : α) = q :=
  rfl
#align mul_opposite.op_rat_cast MulOpposite.op_ratCast
#align add_opposite.op_rat_cast AddOpposite.op_ratCast

@[simp, norm_cast, to_additive]
theorem unop_ratCast [HasRatCast α] (q : ℚ) : unop (q : αᵐᵒᵖ) = q :=
  rfl
#align mul_opposite.unop_rat_cast MulOpposite.unop_ratCast
#align add_opposite.unop_rat_cast AddOpposite.unop_ratCast

variable (α)

instance [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ :=
  { instGroupWithZeroMulOpposite α, instSemiringMulOpposite α with }

instance [DivisionRing α] : DivisionRing αᵐᵒᵖ :=
  { MulOpposite.divisionSemiring α,
    MulOpposite.ring α with
    ratCast := fun q => op q
    ratCast_mk := fun a b hb h =>
      by
      rw [Rat.cast_def, op_div, op_nat_cast, op_int_cast]
      exact Int.commute_cast _ _ }

instance [Semifield α] : Semifield αᵐᵒᵖ :=
  { instDivisionSemiringMulOpposite α, MulOpposite.instCommSemiringMulOpposite α with }

instance [Field α] : Field αᵐᵒᵖ :=
  { instDivisionRingMulOpposite α, instCommRingMulOpposite α with }

end MulOpposite

namespace AddOpposite

instance [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ :=
  { instGroupWithZeroAddOpposite α, instSemiringAddOpposite α with }

instance [DivisionRing α] : DivisionRing αᵃᵒᵖ :=
  { instGroupWithZeroAddOpposite α, instRingAddOpposite α with }

instance [Semifield α] : Semifield αᵃᵒᵖ :=
  { instDivisionSemiringAddOpposite, instCommSemiringAddOpposite α with }

instance [Field α] : Field αᵃᵒᵖ :=
  { instDivisionRingAddOpposite, instCommRingAddOpposite α with }

end AddOpposite
