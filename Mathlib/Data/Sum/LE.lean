/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Data.Pi.Interval -- TODO minimize imports
/-!
# TODO

Interaction between `Sum.elim` and `≤`
-/

namespace Sum

variable {α₁ α₂ β : Type*} [LE β]

lemma elim_le_elim_iff (u₁ v₁ : α₁ → β) (u₂ v₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ Sum.elim v₁ v₂ ↔ u₁ ≤ v₁ ∧ u₂ ≤ v₂ := by
  constructor <;> intro hyp
  · constructor
    · intro i₁
      have hi₁ := hyp (Sum.inl i₁)
      rwa [Sum.elim_inl, Sum.elim_inl] at hi₁
    · intro i₂
      have hi₂ := hyp (Sum.inr i₂)
      rwa [Sum.elim_inr, Sum.elim_inr] at hi₂
  · intro j
    cases j with
    | inl j₁ =>
      rw [Sum.elim_inl, Sum.elim_inl]
      exact hyp.left j₁
    | inr j₂ =>
      rw [Sum.elim_inr, Sum.elim_inr]
      exact hyp.right j₂

lemma const_le_elim_iff (b : β) (v₁ : α₁ → β) (v₂ : α₂ → β) :
    (Function.const _ b) ≤ Sum.elim v₁ v₂ ↔ (Function.const _ b) ≤ v₁ ∧ (Function.const _ b) ≤ v₂ :=
  by rw [← elim_const_const, elim_le_elim_iff]

lemma zero_le_elim_iff [Zero β] (v₁ : α₁ → β) (v₂ : α₂ → β) :
    0 ≤ Sum.elim v₁ v₂ ↔ 0 ≤ v₁ ∧ 0 ≤ v₂ :=
  const_le_elim_iff 0 v₁ v₂

lemma one_le_elim_iff [One β] (v₁ : α₁ → β) (v₂ : α₂ → β) :
    1 ≤ Sum.elim v₁ v₂ ↔ 1 ≤ v₁ ∧ 1 ≤ v₂ :=
  const_le_elim_iff 1 v₁ v₂

lemma elim_le_const_iff (b : β) (u₁ : α₁ → β) (u₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ (Function.const _ b) ↔ u₁ ≤ (Function.const _ b) ∧ u₂ ≤ (Function.const _ b) :=
  by rw [← elim_const_const, elim_le_elim_iff]

lemma elim_le_zero_iff [Zero β] (u₁ : α₁ → β) (u₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ 0 ↔ u₁ ≤ 0 ∧ u₂ ≤ 0 :=
  elim_le_const_iff 0 u₁ u₂

lemma elim_le_one_iff [One β] (u₁ : α₁ → β) (u₂ : α₂ → β) :
    Sum.elim u₁ u₂ ≤ 1 ↔ u₁ ≤ 1 ∧ u₂ ≤ 1 :=
  elim_le_const_iff 1 u₁ u₂

end Sum
