/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Order.Basic
import Mathlib.Algebra.Group.Pi.Basic

/-!
# Interaction between `Sum.elim` and `≤`

This file provides basic API for part-wise comparison of `Sum.elim` vectors.
-/

namespace Sum

variable {α₁ α₂ β : Type*} [LE β]

@[simp]
lemma elim_le_elim_iff (u₁ v₁ : α₁ → β) (u₂ v₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ Sum.elim v₁ v₂ ↔ u₁ ≤ v₁ ∧ u₂ ≤ v₂ :=
  Sum.forall

lemma const_le_elim_iff (b : β) (v₁ : α₁ → β) (v₂ : α₂ → β) :
    Function.const _ b ≤ Sum.elim v₁ v₂ ↔ Function.const _ b ≤ v₁ ∧ Function.const _ b ≤ v₂ :=
  elim_const_const b ▸ elim_le_elim_iff ..

@[to_additive]
lemma one_le_elim_iff [One β] (v₁ : α₁ → β) (v₂ : α₂ → β) :
    1 ≤ Sum.elim v₁ v₂ ↔ 1 ≤ v₁ ∧ 1 ≤ v₂ :=
  const_le_elim_iff 1 v₁ v₂

lemma elim_le_const_iff (b : β) (u₁ : α₁ → β) (u₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ Function.const _ b ↔ u₁ ≤ Function.const _ b ∧ u₂ ≤ Function.const _ b :=
  elim_const_const b ▸ elim_le_elim_iff ..

@[to_additive]
lemma elim_le_one_iff [One β] (u₁ : α₁ → β) (u₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ 1 ↔ u₁ ≤ 1 ∧ u₂ ≤ 1 :=
  elim_le_const_iff 1 u₁ u₂

end Sum
