/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Operations

/-!
# Fixed points of a self-map

In this file we define the set `Function.fixedPoints` of fixed points of a function `f : α → α`.
The related predicate `IsFixedPt` is defined in `Mathlib.Logic.Function.Defs`.

## Tags

fixed point
-/

@[expose] public section

namespace Function

variable {α : Type*} {x : α} {f : α → α}

/-- The set of fixed points of a map `f : α → α`. -/
def fixedPoints (f : α → α) : Set α :=
  { x : α | IsFixedPt f x }

instance fixedPoints.decidable [DecidableEq α] (f : α → α) (x : α) :
    Decidable (x ∈ fixedPoints f) :=
  IsFixedPt.decidable

@[simp]
theorem mem_fixedPoints : x ∈ fixedPoints f ↔ IsFixedPt f x :=
  .rfl

theorem mem_fixedPoints_iff {α : Type*} {f : α → α} {x : α} : x ∈ fixedPoints f ↔ f x = x :=
  .rfl

@[simp]
theorem fixedPoints_id : fixedPoints (@id α) = Set.univ :=
  Set.ext fun _ => by simpa using isFixedPt_id _

theorem fixedPoints_subset_range : fixedPoints f ⊆ Set.range f := fun x hx => ⟨x, hx⟩

end Function
