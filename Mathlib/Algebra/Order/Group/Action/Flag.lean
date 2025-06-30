/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Order.Group.Action.End
import Mathlib.Order.Preorder.Chain

/-!
# Action on flags

Order isomorphisms act on flags.
-/

open scoped Pointwise

variable {α : Type*}

namespace Flag
variable [Preorder α]

instance : SMul (α ≃o α) (Flag α) where smul e := map e

@[simp, norm_cast]
lemma coe_smul (e : α ≃o α) (s : Flag α) : (↑(e • s) : Set α) = e • s := rfl

instance : MulAction (α ≃o α) (Flag α) := SetLike.coe_injective.mulAction _ coe_smul

end Flag
