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
example {α β γ : Type} (_f : α → β) (g : β → γ) (b : β) : γ := by solve_by_elim
example {α : Nat → Type} (f : (n : Nat) → α n → α (n+1)) (a : α 0) : α 5 := by solve_by_elim

example (h : Nat) : Nat := by solve_by_elim []
example {α β : Type} (f : α → β) (a : α) : β := by solve_by_elim []
example {α β : Type} (f : α → α → β) (a : α) : β := by solve_by_elim []
example {α β γ : Type} (f : α → β) (g : β → γ) (a : α) : γ := by solve_by_elim []
example {α β γ : Type} (_f : α → β) (g : β → γ) (b : β) : γ := by solve_by_elim []
example {α : Nat → Type} (f : (n : Nat) → α n → α (n+1)) (a : α 0) : α 5 := by solve_by_elim []

example {α β : Type} (f : α → β) (a : α) : β := by
  fail_if_success solve_by_elim only [f]
  solve_by_elim

example (h : Nat) : Nat := by solve_by_elim only [h]
example {α β : Type} (f : α → β) (a : α) : β := by solve_by_elim only [f, a]
example {α β : Type} (f : α → α → β) (a : α) : β := by solve_by_elim only [f, a]
example {α β γ : Type} (f : α → β) (g : β → γ) (a : α) : γ := by solve_by_elim only [f, g, a]
example {α β γ : Type} (_f : α → β) (g : β → γ) (b : β) : γ := by solve_by_elim only [g, b]
example {α : Nat → Type} (f : (n : Nat) → α n → α (n+1)) (a : α 0) : α 5 := by
  solve_by_elim only [f, a]

-- Verify that already assigned metavariables are skipped.
example (P₁ P₂ : α → Prop) (f : ∀ (a : α), P₁ a → P₂ a → β)
    (a : α) (ha₁ : P₁ a) (ha₂ : P₂ a) : β := by
  solve_by_elim

example {X : Type} (x : X) : x = x := by
  fail_if_success solve_by_elim only -- needs the `rfl` lemma
  solve_by_elim

-- Needs to apply `rfl` twice, with different implicit arguments each time.
-- A naive implementation of solve_by_elim would get stuck.
example {X : Type} (x y : X) (p : Prop) (h : x = x → y = y → p) : p := by solve_by_elim

example : True := by
  fail_if_success solve_by_elim only -- needs the `trivial` lemma
  solve_by_elim

-- Requires backtracking.
example (P₁ P₂ : α → Prop) (f : ∀ (a: α), P₁ a → P₂ a → β)
    (a : α) (_ha₁ : P₁ a)
    (a' : α) (ha'₁ : P₁ a') (ha'₂ : P₂ a') : β := by
  solve_by_elim

-- TODO this works in mathlib3 but not here yet, for some reason.
-- example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
-- by solve_by_elim

section apply_assumption

example {a b : Type} (h₀ : a → b) (h₁ : a) : b := by
  apply_assumption
  apply_assumption

example {α : Type} {p : α → Prop} (h₀ : ∀ x, p x) (y : α) : p y := by
  apply_assumption

end apply_assumption
