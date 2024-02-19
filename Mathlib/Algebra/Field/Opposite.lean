/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Int.Cast.Lemmas

#align_import algebra.field.opposite from "leanprover-community/mathlib"@"76de8ae01554c3b37d66544866659ff174e66e1f"

/-!
# Field structure on the multiplicative/additive opposite
-/

set_option autoImplicit true

namespace MulOpposite

variable (α : Type*)

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
  { MulOpposite.divisionSemiring α, MulOpposite.ring α, MulOpposite.ratCast α with
    ratCast_mk := fun a b hb h => unop_injective <| by
      rw [unop_ratCast, Rat.cast_def, unop_mul, unop_inv, unop_natCast, unop_intCast,
        Int.commute_cast, div_eq_mul_inv] }

instance semifield [Semifield α] : Semifield αᵐᵒᵖ :=
  { MulOpposite.divisionSemiring α, MulOpposite.commSemiring α with }

instance field [Field α] : Field αᵐᵒᵖ :=
  { MulOpposite.divisionRing α, MulOpposite.commRing α with }

end MulOpposite

namespace AddOpposite

instance divisionSemiring [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ :=
  { AddOpposite.groupWithZero α, AddOpposite.semiring α with }

instance divisionRing [DivisionRing α] : DivisionRing αᵃᵒᵖ :=
  { AddOpposite.ring α, AddOpposite.groupWithZero α, AddOpposite.ratCast α with
    ratCast_mk := fun a b hb h => unop_injective <| by
      rw [unop_ratCast, Rat.cast_def, unop_mul, unop_inv, unop_natCast, unop_intCast,
        div_eq_mul_inv] }

instance semifield [Semifield α] : Semifield αᵃᵒᵖ :=
  { AddOpposite.divisionSemiring, AddOpposite.commSemiring α with }

instance field [Field α] : Field αᵃᵒᵖ :=
  { AddOpposite.divisionRing, AddOpposite.commRing α with }

end AddOpposite
