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

instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ :=
  { MulOpposite.instGroupWithZero α, MulOpposite.instSemiring α with }

instance instDivisionRing [DivisionRing α] : DivisionRing αᵐᵒᵖ :=
  { MulOpposite.instDivisionSemiring α, MulOpposite.instRing α, MulOpposite.ratCast α with
    ratCast_mk := fun a b hb h => unop_injective <| by
      rw [unop_ratCast, Rat.cast_def, unop_mul, unop_inv, unop_natCast, unop_intCast,
        Int.commute_cast, div_eq_mul_inv]
    qsmul := qsmulRec _ }

instance instSemifield [Semifield α] : Semifield αᵐᵒᵖ :=
  { MulOpposite.instDivisionSemiring α, MulOpposite.instCommSemiring α with }

instance instField [Field α] : Field αᵐᵒᵖ :=
  { MulOpposite.instDivisionRing α, MulOpposite.instCommRing α with }

end MulOpposite

namespace AddOpposite

variable {α : Type*}

instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ :=
  { AddOpposite.instGroupWithZero α, AddOpposite.instSemiring α with }

instance instDivisionRing [DivisionRing α] : DivisionRing αᵃᵒᵖ :=
  { AddOpposite.instRing α, AddOpposite.instGroupWithZero α, AddOpposite.ratCast α with
    ratCast_mk := fun a b hb h => unop_injective <| by
      rw [unop_ratCast, Rat.cast_def, unop_mul, unop_inv, unop_natCast, unop_intCast,
        div_eq_mul_inv]
    qsmul := qsmulRec _ }

instance instSemifield [Semifield α] : Semifield αᵃᵒᵖ :=
  { AddOpposite.instDivisionSemiring, AddOpposite.instCommSemiring α with }

instance instField [Field α] : Field αᵃᵒᵖ :=
  { AddOpposite.instDivisionRing, AddOpposite.instCommRing α with }

end AddOpposite
