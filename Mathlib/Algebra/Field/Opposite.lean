/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Field structure on the multiplicative/additive opposite
-/

assert_not_exists RelIso

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

@[to_additive (attr := simp, norm_cast)]
lemma unop_ratCast [RatCast α] (q : ℚ) : unop (q : αᵐᵒᵖ) = q := rfl

instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵐᵒᵖ where
  __ := instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  nnratCast_def q := unop_injective <| by rw [unop_nnratCast, unop_div, unop_natCast, unop_natCast,
    NNRat.cast_def, div_eq_mul_inv, Nat.cast_comm]

instance instDivisionRing [DivisionRing α] : DivisionRing αᵐᵒᵖ where
  __ := instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl
  ratCast_def q := unop_injective <| by rw [unop_ratCast, Rat.cast_def, unop_div,
    unop_natCast, unop_intCast, Int.commute_cast, div_eq_mul_inv]

instance instSemifield [Semifield α] : Semifield αᵐᵒᵖ where
  __ := instCommSemiring
  __ := instDivisionSemiring

instance instField [Field α] : Field αᵐᵒᵖ where
  __ := instCommRing
  __ := instDivisionRing

end MulOpposite

namespace AddOpposite

instance instDivisionSemiring [DivisionSemiring α] : DivisionSemiring αᵃᵒᵖ where
  __ := instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  nnratCast_def q := unop_injective <| by rw [unop_nnratCast, unop_div, unop_natCast, unop_natCast,
    NNRat.cast_def, div_eq_mul_inv]

instance instDivisionRing [DivisionRing α] : DivisionRing αᵃᵒᵖ where
  __ := instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl
  ratCast_def q := unop_injective <| by rw [unop_ratCast, Rat.cast_def, unop_div, unop_natCast,
    unop_intCast, div_eq_mul_inv]

instance instSemifield [Semifield α] : Semifield αᵃᵒᵖ where
  __ := instCommSemiring
  __ := instDivisionSemiring

instance instField [Field α] : Field αᵃᵒᵖ where
  __ := instCommRing
  __ := instDivisionRing

end AddOpposite
