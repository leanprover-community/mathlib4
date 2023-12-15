/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Order.CompleteLattice
/-
# OrderedCancelAddCommMonoid + CompleteSemilatticeInf = bad idea

This file shows that combining `OrderedCancelAddCommMonoid` with
`CompleteSemilatticeInf` is not a good idea, as it forbids any strict inequalities (`x < y`).
The same applies to any superclasses, e.g. combining
`StrictOrderedSemiring` with `CompleteLattice`.
The crux is that cancellation properties don't like the `⊥` and `⊤` elements.
-/
private class OrderedCancelAddCommMonoidCompleteSemilatticeInf (α : Type*)
  extends OrderedCancelAddCommMonoid α, CompleteSemilatticeInf α

example {α : Type*} [OrderedCancelAddCommMonoidCompleteSemilatticeInf α] :
    (∃ x y : α, x < y) → False := by
  rintro ⟨x, y, hxy⟩
  --    ⊥ ≤ ⊥ + x
  have blebpx : @sInf α _ Set.univ ≤ @sInf α _ Set.univ + x :=
    sInf_le trivial
  --    ⊥ + x < ⊥ + y
  have bpxlbpy : @sInf α _ Set.univ + x < @sInf α _ Set.univ + y :=
    add_lt_add_left hxy (sInf Set.univ)
  --    ⊥ < ⊥ + y
  have blbpy : @sInf α _ Set.univ < @sInf α _ Set.univ + y :=
    blebpx.trans_lt bpxlbpy
  --    0 < y
  have zly : 0 < y :=
    pos_of_lt_add_right blbpy
  --    ⊤ + y ≤ ⊤
  have tpylet : @sInf α _ ∅ + y ≤ @sInf α _ ∅ :=
    by simp
  --    ⊤ + y < ⊤ + y
  have tpyltpy : @sInf α _ ∅ + y < @sInf α _ ∅ + y :=
    lt_add_of_le_of_pos tpylet zly
  --    contradiction
  exact tpyltpy.false
