/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Order.Basic
import Mathlib.Algebra.Group.Pi.Basic
/-!
# TODO

Interaction between `Sum.elim` and `≤`
-/

namespace Sum

variable {α₁ α₂ β : Type*} [LE β]

lemma elim_le_elim_iff (u₁ v₁ : α₁ → β) (u₂ v₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ Sum.elim v₁ v₂ ↔ u₁ ≤ v₁ ∧ u₂ ≤ v₂ :=
  ⟨fun h => ⟨fun _ => h <| inl _, fun _ => h <| inr _⟩,
  fun h j => match j with | inl _ => h.1 _ | inr _ => h.2 _⟩

lemma const_le_elim_iff (b : β) (v₁ : α₁ → β) (v₂ : α₂ → β) :
    (Function.const _ b) ≤ Sum.elim v₁ v₂ ↔ (Function.const _ b) ≤ v₁ ∧ (Function.const _ b) ≤ v₂ :=
  elim_const_const _ ▸ elim_le_elim_iff _ _ _ _

lemma zero_le_elim_iff [Zero β] (v₁ : α₁ → β) (v₂ : α₂ → β) :
    0 ≤ Sum.elim v₁ v₂ ↔ 0 ≤ v₁ ∧ 0 ≤ v₂ :=
  const_le_elim_iff 0 v₁ v₂

lemma one_le_elim_iff [One β] (v₁ : α₁ → β) (v₂ : α₂ → β) :
    1 ≤ Sum.elim v₁ v₂ ↔ 1 ≤ v₁ ∧ 1 ≤ v₂ :=
  const_le_elim_iff 1 v₁ v₂

lemma elim_le_const_iff (b : β) (u₁ : α₁ → β) (u₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ (Function.const _ b) ↔ u₁ ≤ (Function.const _ b) ∧ u₂ ≤ (Function.const _ b) :=
  elim_const_const _ ▸ elim_le_elim_iff _ _ _ _

lemma elim_le_zero_iff [Zero β] (u₁ : α₁ → β) (u₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ 0 ↔ u₁ ≤ 0 ∧ u₂ ≤ 0 :=
  elim_le_const_iff 0 u₁ u₂

lemma elim_le_one_iff [One β] (u₁ : α₁ → β) (u₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ 1 ↔ u₁ ≤ 1 ∧ u₂ ≤ 1 :=
  elim_le_const_iff 1 u₁ u₂

end Sum
