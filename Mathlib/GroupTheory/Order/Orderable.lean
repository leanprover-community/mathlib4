/-
Copyright (c) Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Order.Defs.Unbundled

/-!
# Left-orderable groups
This file defines left-orderable groups.

## Main declarations
`IsLeftOrderable` defines when a group is left-orderable.

## To-do
* `IsRightOrderedGroup`, `IsRightOrderableGroup`
* `BiOrderedGroup`, ``IsRightOrderedGroup`
* Positive cone equivalences

-/

@[expose] public section

/-- A left-ordered group `G` is a group equipped with a strict total order `<` such that
left-multiplication preserves the inequality relation. -/
abbrev IsLeftOrderedGroup (G : Type*) [Group G] [LT G] [IsStrictTotalOrder G (· < ·)] : Prop :=
  MulLeftStrictMono G

/-- A group is left-orderable if it admits some left-invariant strict total order. -/
def IsLeftOrderableGroup (G : Type*) [Group G] : Prop :=
  ∃ ord : LT G, letI := ord; ∃ _ : IsStrictTotalOrder G (· < ·), IsLeftOrderedGroup G
