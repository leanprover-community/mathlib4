/-
Copyright (c) 2026 Alex Brodbelt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Brodbelt, Eric Wieser
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finiteness conditions for `Option` types
-/

@[expose] public section
/-- The `Option` type on a type is finite if and only if the underlying type is finite -/
@[simp]
theorem Option.finite_iff {α : Type*} : Finite (Option α) ↔ Finite α where
  mpr _ := instFiniteOption
  mp
  | @Finite.intro _ 0 e => (e none).elim0
  | @Finite.intro _ (n + 1) e => ⟨(e.trans (finSuccEquiv n)).removeNone⟩
