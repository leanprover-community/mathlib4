/-
Copyright (c) 2026 Alex Brodbelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Brodbelt and Eric Wieser
-/
module

public import Mathlib.Data.Finite.Option

@[expose] public section

@[simp]
theorem Subtype.finite_ne_iff {α : Type*} (a₀ : α) : Finite {a // a ≠ a₀} ↔ Finite α := by
  classical
  rw [← (Equiv.optionSubtypeNe a₀).finite_iff, Option.finite_iff]
