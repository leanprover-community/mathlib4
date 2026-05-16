/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

import Mathlib.Tactic.ToDual

/-!
# Order definitions for propositions

This file defines orders on `Pi` and `Prop`.
-/

public section

instance Pi.hasLe {ι : Type*} {π : ι → Type*} [∀ i, LE (π i)] : LE (∀ i, π i) where
  le x y := ∀ i, x i ≤ y i

@[to_dual self]
theorem Pi.le_def {ι : Type*} {π : ι → Type*} [∀ i, LE (π i)] {x y : ∀ i, π i} :
    x ≤ y ↔ ∀ i, x i ≤ y i :=
  .rfl

/-- Propositions form a complete Boolean algebra, where the `≤` relation is given by implication. -/
instance Prop.le : LE Prop :=
  ⟨(· → ·)⟩

@[simp]
theorem le_Prop_eq : ((· ≤ ·) : Prop → Prop → Prop) = (· → ·) :=
  rfl
