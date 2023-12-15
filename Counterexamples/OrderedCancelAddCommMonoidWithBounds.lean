/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.Order.Monoid.Defs

/-!
# OrderedCancelAddCommMonoid + BoundedOrder = bad idea

This file shows that combining `OrderedCancelAddCommMonoid` with `BoundedOrder` is not a good idea,
as it forbids any strict inequalities (`x < y`).
The same applies to any superclasses, e.g. combining
`StrictOrderedSemiring` with `CompleteLattice`.
The crux is that cancellation properties don't like the `⊥` and `⊤` elements.
-/

example {α : Type*} [OrderedCancelAddCommMonoid α] [BoundedOrder α] (x y : α) :
    ¬(x < y) := by
  intro hxy
  have blebpx : ⊥ ≤ ⊥ + x := bot_le
  have bpxlbpy : ⊥ + x < ⊥ + y := add_lt_add_left hxy ⊥
  have blbpy : ⊥ < ⊥ + y := blebpx.trans_lt bpxlbpy
  have zly : 0 < y := pos_of_lt_add_right blbpy
  have tpylet : ⊤ + y ≤ ⊤ := le_top
  have tpyltpy : ⊤ + y < ⊤ + y := lt_add_of_le_of_pos tpylet zly
  exact tpyltpy.false
