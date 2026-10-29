/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module -- shake: keep-all

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.RelClasses

/-!
# Bounded and unbounded sets

We prove miscellaneous lemmas about bounded and unbounded sets. Many of these are just variations on
the same ideas, or similar results with a few minor differences. The file is divided into these
different general ideas.
-/

deprecated_module "Use the following replacements:
- `BddAbove` for `Set.Bounded (· ≤ ·)`
- `BddBelow` for `Set.Bounded (· ≥ ·)`
- `IsCofinal` for `Set.Unbounded (· < ·)` in a linear order
- `IsCoinitial` for `Set.Unbounded (· > ·)` in a linear order" (since := "2026-04-16")

public section

assert_not_exists RelIso

namespace Set

variable {α : Type*} {r : α → α → Prop} {s t : Set α}

/-! ### Subsets of bounded and unbounded sets -/


/-! ### Alternate characterizations of unboundedness on orders -/


/-! ### Relation between boundedness by strict and nonstrict orders. -/


/-! #### Less and less or equal -/


/-! #### Greater and greater or equal -/


/-! ### The universal set -/


/-! ### Bounded and unbounded intervals -/


/-! #### Half-open bounded intervals -/


/-! #### Other bounded intervals -/


/-! #### Unbounded intervals -/


/-! ### Bounded initial segments -/


/-! #### Less or equal -/


/-! #### Less than -/


/-! #### Greater or equal -/


/-! #### Greater than -/


end Set
