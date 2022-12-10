/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Order.Group.Instances
import Mathbin.Algebra.Order.Monoid.WithTop

/-!
# Adjoining a top element to a `linear_ordered_add_comm_group_with_top`.
-/


variable {α : Type _}

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α] {a b c d : α}

instance WithTop.linearOrderedAddCommGroupWithTop : LinearOrderedAddCommGroupWithTop (WithTop α) :=
  { WithTop.linearOrderedAddCommMonoidWithTop, Option.nontrivial with
    neg := Option.map fun a : α => -a, neg_top := @Option.map_none _ _ fun a : α => -a,
    add_neg_cancel := by 
      rintro (a | a) ha
      · exact (ha rfl).elim
      · exact with_top.coe_add.symm.trans (WithTop.coe_eq_coe.2 (add_neg_self a)) }
#align with_top.linear_ordered_add_comm_group_with_top WithTop.linearOrderedAddCommGroupWithTop

@[simp, norm_cast]
theorem WithTop.coe_neg (a : α) : ((-a : α) : WithTop α) = -a :=
  rfl
#align with_top.coe_neg WithTop.coe_neg

end LinearOrderedAddCommGroup

