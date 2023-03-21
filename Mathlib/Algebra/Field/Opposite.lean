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
instance ratCast [RatCast α] : RatCast αᵐᵒᵖ :=
  ⟨fun n => op n⟩

variable {α}

@[to_additive (attr := simp, norm_cast)]
theorem op_ratCast [RatCast α] (q : ℚ) : op (q : α) = q :=
  rfl
#align mul_opposite.op_rat_cast MulOpposite.op_ratCast
#align add_opposite.op_rat_cast AddOpposite.op_ratCast

@[to_additive (attr := simp, norm_cast)]
theorem unop_ratCast [RatCast α] (q : ℚ) : unop (q : αᵐᵒᵖ) = q :=
  rfl
#align mul_opposite.unop_rat_cast MulOpposite.unop_ratCast
#align add_opposite.unop_rat_cast AddOpposite.unop_ratCast

variable (α)

instance divisionSemiring [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ :=
  { MulOpposite.groupWithZero α, MulOpposite.semiring α with }

instance divisionRing [DivisionRing α] : DivisionRing αᵐᵒᵖ :=
  { MulOpposite.divisionSemiring α, MulOpposite.ring α with
    ratCast := fun q => op q
    ratCast_mk := fun a b hb h =>
      by
      rw [Rat.cast_def, op_div, op_nat_cast, op_int_cast]
      exact Int.commute_cast _ _ }

instance semifield [Semifield α] : Semifield αᵐᵒᵖ :=
  { MulOpposite.divisionSemiring α, MulOpposite.commSemiring α with }

instance field [Field α] : Field αᵐᵒᵖ :=
  { MulOpposite.divisionRing α, MulOpposite.commRing α with }

end MulOpposite

namespace AddOpposite

instance divisionSemiring [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ :=
  { AddOpposite.groupWithZero α, AddOpposite.semiring α with }

instance divisionRing [DivisionRing α] : DivisionRing αᵃᵒᵖ :=
  { AddOpposite.groupWithZero α, AddOpposite.ring α with }

instance semifield [Semifield α] : Semifield αᵃᵒᵖ :=
  { AddOpposite.divisionSemiring, AddOpposite.commSemiring α with }

instance field [Field α] : Field αᵃᵒᵖ :=
  { AddOpposite.divisionRing, AddOpposite.commRing α with }

end AddOpposite
