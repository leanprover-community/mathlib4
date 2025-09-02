/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Order.BoundedOrder.Lattice

/-!
# Do not combine OrderedCancelAddCommMonoid with BoundedOrder

This file shows that combining `OrderedCancelAddCommMonoid` with `BoundedOrder` is not a good idea,
as such a structure must be trivial (`⊥ = x = ⊤` for all `x`).
The same applies to any superclasses, e.g. combining `StrictOrderedSemiring` with `CompleteLattice`.
-/

example {α : Type*} [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [BoundedOrder α] [Nontrivial α] : False :=
  have top_pos := pos_of_lt_add_right (bot_le.trans_lt (add_lt_add_left bot_lt_top (⊥ : α)))
  have top_add_top_lt_self := lt_add_of_le_of_pos (@le_top _ _ _ (⊤ + ⊤)) top_pos
  top_add_top_lt_self.false
