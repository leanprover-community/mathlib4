/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Tactic.SolveByElim

example (h : Nat) : Nat := by solve_by_elim
example {α β : Type} (f : α → β) (a : α) : β := by solve_by_elim
example {α β : Type} (f : α → α → β) (a : α) : β := by solve_by_elim
example {α β γ : Type} (f : α → β) (g : β → γ) (a : α) : γ := by solve_by_elim
example {α β γ : Type} (f : α → β) (g : β → γ) (b : β) : γ := by solve_by_elim
example {α : Nat → Type} (f : (n : Nat) → α n → α (n+1)) (a : α 0) : α 5 := by solve_by_elim

example (h : Nat) : Nat := by solve_by_elim []
example {α β : Type} (f : α → β) (a : α) : β := by solve_by_elim []
example {α β : Type} (f : α → α → β) (a : α) : β := by solve_by_elim []
example {α β γ : Type} (f : α → β) (g : β → γ) (a : α) : γ := by solve_by_elim []
example {α β γ : Type} (f : α → β) (g : β → γ) (b : β) : γ := by solve_by_elim []
example {α : Nat → Type} (f : (n : Nat) → α n → α (n+1)) (a : α 0) : α 5 := by solve_by_elim []

example {α β : Type} (f : α → β) (a : α) : β := by
  fail_if_success solve_by_elim only [f]
  solve_by_elim

example (h : Nat) : Nat := by solve_by_elim only [h]
example {α β : Type} (f : α → β) (a : α) : β := by solve_by_elim only [f, a]
example {α β : Type} (f : α → α → β) (a : α) : β := by solve_by_elim only [f, a]
example {α β γ : Type} (f : α → β) (g : β → γ) (a : α) : γ := by solve_by_elim only [f, g, a]
example {α β γ : Type} (f : α → β) (g : β → γ) (b : β) : γ := by solve_by_elim only [g, b]
example {α : Nat → Type} (f : (n : Nat) → α n → α (n+1)) (a : α 0) : α 5 := by solve_by_elim only [f, a]

-- With proper backtracking this should work (and did in mathlib3).
-- example (P₁ P₂: α → Prop) (f: forall (a: α), P₁ a → P₂ a → β)
--         (a: α) (ha₁: P₁ a)
--         (a': α) (ha'₁: P₁ a') (ha'₂: P₂ a'): β := by
--   solve_by_elim
