/-
Copyright (c) 2026 Alex Brodbelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Brodbelt, Eric Wieser
-/
module

public import Mathlib.Basic.Finite.Defs

import Mathlib.Data.Fintype.Option
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finiteness conditions for `Option` types

This file shows that `Option α` is finite iff `α` is. Similarly, `Option α` is infinite iff `α` is.
-/

public section

/-- `Option α` is finite if and only if the underlying type `α` is finite. -/
@[simp]
theorem Option.finite_iff {α : Type*} : Finite (Option α) ↔ Finite α where
  mpr _ := inferInstance
  mp
  | @Finite.intro _ 0 e => (e none).elim0
  | @Finite.intro _ (n + 1) e => ⟨(e.trans (finSuccEquiv n)).removeNone⟩

/-- `Option α` is infinite if and only if the underlying type `α` is infinite. -/
@[simp]
theorem Option.infinite_iff {α : Type*} : Infinite (Option α) ↔ Infinite α := by
  rw [← not_finite_iff_infinite, ← not_finite_iff_infinite, Option.finite_iff]

end
