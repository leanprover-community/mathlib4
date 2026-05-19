/-
Copyright (c) 2026 Alex Brodbelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Brodbelt, Eric Wieser
-/
module

public import Mathlib.Data.Finite.Option

/-!
# `Finite`ness conditions on subtypes
-/

@[expose] public section

/-- The subtype of terms not equal to a given term is finite if and only if the type is finite. -/
@[simp]
theorem Subtype.finite_ne_iff {α : Type*} (a₀ : α) : Finite {a // a ≠ a₀} ↔ Finite α := by
  classical
  rw [← (Equiv.optionSubtypeNe a₀).finite_iff, Option.finite_iff]
