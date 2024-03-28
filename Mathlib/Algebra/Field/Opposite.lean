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

open scoped NNRat

variable {α : Type*}

namespace MulOpposite

@[to_additive] instance instNNRatCast [NNRatCast α] : NNRatCast αᵐᵒᵖ := ⟨fun q ↦ op q⟩
@[to_additive] instance instRatCast [RatCast α] : RatCast αᵐᵒᵖ := ⟨fun q ↦ op q⟩

@[to_additive (attr := simp, norm_cast)]
lemma op_nnratCast [NNRatCast α] (q : ℚ≥0) : op (q : α) = q := rfl

@[to_additive (attr := simp, norm_cast)]
lemma unop_nnratCast [NNRatCast α] (q : ℚ≥0) : unop (q : αᵐᵒᵖ) = q := rfl

@[to_additive (attr := simp, norm_cast)]
lemma op_ratCast [RatCast α] (q : ℚ) : op (q : α) = q := rfl
#align mul_opposite.op_rat_cast MulOpposite.op_ratCast
#align add_opposite.op_rat_cast AddOpposite.op_ratCast

@[to_additive (attr := simp, norm_cast)]
lemma unop_ratCast [RatCast α] (q : ℚ) : unop (q : αᵐᵒᵖ) = q := rfl
#align mul_opposite.unop_rat_cast MulOpposite.unop_ratCast
#align add_opposite.unop_rat_cast AddOpposite.unop_ratCast

instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ where
  toSemiring := instSemiring
  __ := instGroupWithZero
  nnratCast_def q := unop_injective $ by rw [unop_nnratCast, unop_div, unop_natCast, unop_natCast,
    NNRat.cast_def, div_eq_mul_inv, Nat.cast_comm]
  nnqsmul := _

instance instDivisionRing [DivisionRing α] : DivisionRing αᵐᵒᵖ where
  toRing := instRing
  __ := instDivisionSemiring
  ratCast_def q := unop_injective <| by rw [unop_ratCast, Rat.cast_def, unop_div,
    unop_natCast, unop_intCast, Int.commute_cast, div_eq_mul_inv]
  qsmul := qsmulRec _

instance instSemifield [Semifield α] : Semifield αᵐᵒᵖ where
  toCommSemiring := instCommSemiring
  __ := instDivisionSemiring

instance instField [Field α] : Field αᵐᵒᵖ where
  toCommRing := instCommRing
  __ := instDivisionRing

end MulOpposite

namespace AddOpposite

instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ where
  toSemiring := instSemiring
  __ := instGroupWithZero
  nnratCast_def q := unop_injective $ by rw [unop_nnratCast, unop_div, unop_natCast, unop_natCast,
    NNRat.cast_def, div_eq_mul_inv]
  nnqsmul := _

instance instDivisionRing [DivisionRing α] : DivisionRing αᵃᵒᵖ where
  toRing := instRing
  __ := instDivisionSemiring
  ratCast_def q := unop_injective <| by rw [unop_ratCast, Rat.cast_def, unop_div, unop_natCast,
    unop_intCast, div_eq_mul_inv]
  qsmul := qsmulRec _

instance instSemifield [Semifield α] : Semifield αᵃᵒᵖ where
  toCommSemiring := instCommSemiring
  __ := instDivisionSemiring

instance instField [Field α] : Field αᵃᵒᵖ where
  toCommRing := instCommRing
  __ := instDivisionRing

end AddOpposite
