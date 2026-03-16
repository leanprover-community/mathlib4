/-
Copyright (c) Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Order.Defs.LinearOrder

/-!
# Left-, Right-, Bi-Orderable groups

This file defines left-orderable, right-orderable, and bi-orderable groups as well as
their positive cone equivalences.

## Main declarations

-/

@[expose] public section

/-- A group is left-orderable if it admits a left-invariant linear order. -/
class IsLeftOrderable (G : Type*) [Group G] : Prop where
