/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Basic

/-!
# Pairwise relations on a list
-/

namespace List

variable {α β : Type _} {R S T : α → α → Prop} {a : α} {l : List α}

theorem pairwise_append {l₁ l₂ : List α} : Pairwise R (l₁ ++ l₂) ↔
    Pairwise R l₁ ∧ Pairwise R l₂ ∧ (∀ x, x ∈ l₁ → ∀ y, y ∈ l₂ → R x y) := by
  induction l₁ with
  | nil => simp [Pairwise.nil]
  | cons a l₁ ih =>
    simp only [cons_append, Pairwise_cons, forall_mem_append, ih, forall_mem_cons,
      forall_and_distrib, and_assoc, And.left_comm]
    rfl

theorem pairwise_append_comm (s : symmetric R) {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) := by
  have : ∀ l₁ l₂ : List α, (∀ x : α, x ∈ l₁ → ∀ y : α, y ∈ l₂ → R x y) →
    ∀ x : α, x ∈ l₂ → ∀ y : α, y ∈ l₁ → R x y := fun l₁ l₂ a x xm y ym => s (a y ym x xm)
  simp only [pairwise_append, And.left_comm] <;> rw [Iff.intro (this l₁ l₂) (this l₂ l₁)]

theorem pairwise_middle (s : symmetric R) {a : α} {l₁ l₂ : List α} :
    Pairwise R (l₁ ++ a :: l₂) ↔ Pairwise R (a :: (l₁ ++ l₂)) :=
  show Pairwise R (l₁ ++ ([a] ++ l₂)) ↔ Pairwise R ([a] ++ l₁ ++ l₂) by
    rw [← append_assoc, pairwise_append, @pairwise_append _ _ ([a] ++ l₁), pairwise_append_comm s]
    simp only [mem_append, or_comm]
    rfl
