/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.WithTop

#align_import algebra.order.group.with_top from "leanprover-community/mathlib"@"f178c0e25af359f6cbc72a96a243efd3b12423a3"

/-!
# Adjoining a top element to a `LinearOrderedAddCommGroupWithTop`.
-/

namespace WithTop

variable {α : Type*}

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] {a b c d : α}

instance instNeg : Neg (WithTop α) where neg := Option.map fun a : α => -a

instance linearOrderedAddCommGroupWithTop : LinearOrderedAddCommGroupWithTop (WithTop α) where
  __ := WithTop.linearOrderedAddCommMonoidWithTop
  __ := Option.nontrivial
  neg_top := Option.map_none
  zsmul := zsmulRec
  add_neg_cancel := by
    rintro (a | a) ha
    · exact (ha rfl).elim
    · exact (WithTop.coe_add ..).symm.trans (WithTop.coe_eq_coe.2 (add_neg_self a))
#align with_top.linear_ordered_add_comm_group_with_top WithTop.linearOrderedAddCommGroupWithTop

@[simp, norm_cast]
theorem coe_neg (a : α) : ((-a : α) : WithTop α) = -a :=
  rfl
#align with_top.coe_neg WithTop.coe_neg

end LinearOrderedAddCommGroup

end WithTop
