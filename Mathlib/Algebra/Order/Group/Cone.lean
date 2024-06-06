/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import Mathlib.Algebra.Order.Group.Defs

#align_import algebra.order.group.defs from "leanprover-community/mathlib"@"b599f4e4e5cf1fbcb4194503671d3d9e569c1fce"

/-!
# Construct ordered groups from positive cones

In this file we provide structures `PositiveCone` and `TotalPositiveCone`
that encode axioms of `OrderedAddCommGroup` and `LinearOrderedAddCommGroup`
in terms of the `(0 ≤ ·)` predicate.

We also provide two constructors,
`OrderedAddCommGroup.mkOfPositiveCone` and `LinearOrderedAddCommGroup.mkOfPositiveCone`,
that turn these structures into instances of the corresponding typeclasses.
-/

namespace AddCommGroup

/-- A collection of elements in an `AddCommGroup` designated as "non-negative".
This is useful for constructing an `OrderedAddCommGroup`
by choosing a positive cone in an existing `AddCommGroup`. -/
-- Porting note(#5171): @[nolint has_nonempty_instance]
structure PositiveCone (α : Type*) [AddCommGroup α] where
  /-- The characteristic predicate of a positive cone. `nonneg a` means that `0 ≤ a` according to
  the cone. -/
  nonneg : α → Prop
  /-- The characteristic predicate of a positive cone. `pos a` means that `0 < a` according to
  the cone. -/
  pos : α → Prop := fun a => nonneg a ∧ ¬nonneg (-a)
  pos_iff : ∀ a, pos a ↔ nonneg a ∧ ¬nonneg (-a) := by intros; rfl
  zero_nonneg : nonneg 0
  add_nonneg : ∀ {a b}, nonneg a → nonneg b → nonneg (a + b)
  nonneg_antisymm : ∀ {a}, nonneg a → nonneg (-a) → a = 0
#align add_comm_group.positive_cone AddCommGroup.PositiveCone

/-- A positive cone in an `AddCommGroup` induces a linear order if
for every `a`, either `a` or `-a` is non-negative. -/
-- Porting note(#5171): @[nolint has_nonempty_instance]
structure TotalPositiveCone (α : Type*) [AddCommGroup α] extends PositiveCone α where
  /-- For any `a` the proposition `nonneg a` is decidable -/
  nonnegDecidable : DecidablePred nonneg
  /-- Either `a` or `-a` is `nonneg` -/
  nonneg_total : ∀ a : α, nonneg a ∨ nonneg (-a)
#align add_comm_group.total_positive_cone AddCommGroup.TotalPositiveCone

/-- Forget that a `TotalPositiveCone` is total. -/
add_decl_doc TotalPositiveCone.toPositiveCone
#align add_comm_group.total_positive_cone.to_positive_cone AddCommGroup.TotalPositiveCone.toPositiveCone

end AddCommGroup

namespace OrderedAddCommGroup

open AddCommGroup

/-- Construct an `OrderedAddCommGroup` by
designating a positive cone in an existing `AddCommGroup`. -/
def mkOfPositiveCone {α : Type*} [AddCommGroup α] (C : PositiveCone α) : OrderedAddCommGroup α :=
  { ‹AddCommGroup α› with
    le := fun a b => C.nonneg (b - a),
    lt := fun a b => C.pos (b - a),
    lt_iff_le_not_le := fun a b => by simp [C.pos_iff],
    le_refl := fun a => by simp [C.zero_nonneg],
    le_trans := fun a b c nab nbc => by simpa using C.add_nonneg nbc nab,
    le_antisymm := fun a b nab nba =>
      eq_of_sub_eq_zero <| C.nonneg_antisymm nba (by rwa [neg_sub]),
    add_le_add_left := fun a b nab c => by simpa using nab }
#align ordered_add_comm_group.mk_of_positive_cone OrderedAddCommGroup.mkOfPositiveCone

end OrderedAddCommGroup

namespace LinearOrderedAddCommGroup

open AddCommGroup

/-- Construct a `LinearOrderedAddCommGroup` by
designating a positive cone in an existing `AddCommGroup`
such that for every `a`, either `a` or `-a` is non-negative. -/
def mkOfPositiveCone {α : Type*} [AddCommGroup α] (C : TotalPositiveCone α) :
    LinearOrderedAddCommGroup α :=
  { OrderedAddCommGroup.mkOfPositiveCone C.toPositiveCone with
    -- Porting note: was `C.nonneg_total (b - a)`
    le_total := fun a b => by simpa [neg_sub] using C.nonneg_total (b - a)
    decidableLE := fun a b => C.nonnegDecidable _ }
#align linear_ordered_add_comm_group.mk_of_positive_cone LinearOrderedAddCommGroup.mkOfPositiveCone

end LinearOrderedAddCommGroup
