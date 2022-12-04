/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Logic
import Std.Tactic.RCases
import Mathlib.Tactic.Constructor
import Mathlib.Tactic.PermuteGoals
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

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
by
  fail_if_success solve_by_elim (config := {symm := false})
  solve_by_elim

example (P : True → False) : 3 = 7 :=  by
  fail_if_success solve_by_elim (config := {exfalso := false})
  solve_by_elim

-- Verifying that `solve_by_elim` acts only on the main goal.
example (n : ℕ) : ℕ × ℕ := by
  constructor
  solve_by_elim
  solve_by_elim

-- Verifying that `solve_by_elim*` acts on all remaining goals.
example (n : ℕ) : ℕ × ℕ := by
  constructor
  solve_by_elim*

-- Verifying that `solve_by_elim*` backtracks when given multiple goals.
example (n m : ℕ) (f : ℕ → ℕ → Prop) (h : f n m) : ∃ p : ℕ × ℕ, f p.1 p.2 := by
  fconstructor
  fconstructor
  solve_by_elim*

-- test that metavariables created for implicit arguments don't get stuck
example (P : ℕ → Type) (f : {n : ℕ} → P n) : P 2 × P 3 := by
  fconstructor
  solve_by_elim* only [f]

example : 6 = 6 ∧ [7] = [7] := by
  fconstructor
  solve_by_elim* only [@rfl _]

-- Test that `solve_by_elim*`, which works on multiple goals,
-- successfully uses the relevant local hypotheses for each goal.
example (f g : ℕ → Prop) : (∃ k : ℕ, f k) ∨ (∃ k : ℕ, g k) ↔ ∃ k : ℕ, f k ∨ g k := by
  dsimp at *
  fconstructor
  rintro (⟨n, fn⟩ | ⟨n, gn⟩)
  pick_goal 3
  rintro ⟨n, hf | hg⟩
  solve_by_elim* (config := {maxDepth := 13}) [Or.inl, Or.inr, Exists.intro]

-- This worked in mathlib3. Why is it failing here?
-- example (P Q R : Prop) : P ∧ Q → P ∧ Q := by
--   solve_by_elim [And.imp, id]

section apply_assumption

example {a b : Type} (h₀ : a → b) (h₁ : a) : b := by
  apply_assumption
  apply_assumption

example {α : Type} {p : α → Prop} (h₀ : ∀ x, p x) (y : α) : p y := by
  apply_assumption

end apply_assumption
