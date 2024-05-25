/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.Topology.Irreducible

/-!
# Irreducible and Closed Subsets of a Topological Space

The main things defined in this file:
1. Given a topological space `X` and a subset `s : Set X`, `IsIrreducibleClosed s` means
   that `s` is both irreducible and closed.
2. For any topological space `α`, `IrreducibleCloseds α` is the type of all subsets of
   `X` that are closed and irreducible.
-/

variable {X : Type*} [TopologicalSpace X] (s : Set X)

/--
An set `s : Set X` satisfies `IsIrreducibleClosed s` if `s` is irreducible and closed.
-/
def IsIrreducibleClosed : Prop := IsIrreducible s ∧ IsClosed s

namespace IsIrreducibleClosed

theorem nonempty (h : IsIrreducibleClosed s) : s.Nonempty := h.1.1

theorem isPreirreducible (h : IsIrreducibleClosed s) : IsPreirreducible s := h.1.2

theorem isIrreducible (h : IsIrreducibleClosed s) : IsIrreducible s := h.1

theorem isClosed (h : IsIrreducibleClosed s) : IsClosed s := h.2

end IsIrreducibleClosed

namespace TopologicalSpace

variable (α : Type*) [TopologicalSpace α]

structure IrreducibleCloseds where
  carrier : Set α
  irreducible_closed' : IsIrreducibleClosed carrier

namespace IrreducibleCloseds

theorem nonempty' (self : IrreducibleCloseds α) :
    self.carrier.Nonempty := self.irreducible_closed'.1.1

theorem preirreducible' (self : IrreducibleCloseds α) :
    IsPreirreducible self.carrier := self.irreducible_closed'.1.2

theorem irreducible' (self : IrreducibleCloseds α) :
    IsIrreducible self.carrier := self.irreducible_closed'.1

theorem closed' (self : IrreducibleCloseds α) :
    IsClosed self.carrier := self.irreducible_closed'.2

theorem irreducibleClosed' (self : IrreducibleCloseds α) :
    IsIrreducibleClosed self.carrier := self.irreducible_closed'

end IrreducibleCloseds

end TopologicalSpace
