/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Order.Basic
import Mathlib.Algebra.Group.Pi.Basic

/-!
# Interaction between `Sum.elim`, `≤`, and `0` or `1`

This file provides basic API for part-wise comparison of `Sum.elim` vectors against `0` or `1`.
-/

namespace Sum

variable {α₁ α₂ β : Type*} [LE β] [One β] {v₁ : α₁ → β} {v₂ : α₂ → β}

@[to_additive]
lemma one_le_elim_iff : 1 ≤ Sum.elim v₁ v₂ ↔ 1 ≤ v₁ ∧ 1 ≤ v₂ :=
  const_le_elim_iff

@[to_additive]
lemma elim_le_one_iff : Sum.elim v₁ v₂ ≤ 1 ↔ v₁ ≤ 1 ∧ v₂ ≤ 1 :=
  elim_le_const_iff

end Sum
