/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

import Mathlib.Tactic.TypeStar

/-!
# Order definitions for propositions

This file defines orders on `Pi` and `Prop`.
-/

public instance Pi.hasLe {ι : Type*} {π : ι → Type*} [∀ i, LE (π i)] : LE (∀ i, π i) where
  le x y := ∀ i, x i ≤ y i

/-- Propositions form a complete Boolean algebra, where the `≤` relation is given by implication. -/
public instance Prop.le : LE Prop :=
  ⟨(· → ·)⟩
