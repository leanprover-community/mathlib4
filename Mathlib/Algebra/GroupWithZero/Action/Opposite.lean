/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.GroupWithZero.NeZero

#align_import group_theory.group_action.opposite from "leanprover-community/mathlib"@"4330aae21f538b862f8aead371cfb6ee556398f1"

/-!
# Scalar actions by `Mᵐᵒᵖ`
-/

assert_not_exists Ring

open MulOpposite

variable {R α : Type*}

/-- `Monoid.toOppositeMulAction` is faithful on nontrivial cancellative monoids with zero. -/
instance CancelMonoidWithZero.toFaithfulSMul_opposite [CancelMonoidWithZero α] [Nontrivial α] :
    FaithfulSMul αᵐᵒᵖ α where
  eq_of_smul_eq_smul h := unop_injective <| mul_left_cancel₀ one_ne_zero (h 1)
#align cancel_monoid_with_zero.to_has_faithful_opposite_scalar CancelMonoidWithZero.toFaithfulSMul_opposite
