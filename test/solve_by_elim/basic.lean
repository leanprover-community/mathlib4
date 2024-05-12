/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Logic
import Mathlib.Tactic.Constructor
import Batteries.Tactic.PermuteGoals
import Batteries.Test.Internal.DummyLabelAttr

set_option autoImplicit true

example (h : Nat) : Nat := by solve_by_elim
example {α β : Type} (f : α → β) (a : α) : β := by solve_by_elim
example {α β : Type} (f : α → α → β) (a : α) : β := by solve_by_elim
example {α β γ : Type} (f : α → β) (g : β → γ) (a : α) : γ := by solve_by_elim
example {α β γ : Type} (_f : α → β) (g : β → γ) (b : β) : γ := by solve_by_elim
example {α : Nat → Type} (f : (n : Nat) → α n → α (n+1)) (a : α 0) : α 4 := by solve_by_elim

example (h : Nat) : Nat := by solve_by_elim []
example {α β : Type} (f : α → β) (a : α) : β := by solve_by_elim []
example {α β : Type} (f : α → α → β) (a : α) : β := by solve_by_elim []
example {α β γ : Type} (f : α → β) (g : β → γ) (a : α) : γ := by solve_by_elim []
example {α β γ : Type} (_f : α → β) (g : β → γ) (b : β) : γ := by solve_by_elim []
example {α : Nat → Type} (f : (n : Nat) → α n → α (n+1)) (a : α 0) : α 4 := by solve_by_elim []

example {α β : Type} (f : α → β) (a : α) : β := by
  fail_if_success solve_by_elim [-f]
  fail_if_success solve_by_elim [-a]
  fail_if_success solve_by_elim only [f]
  solve_by_elim

example {α β γ : Type} (f : α → β) (g : β → γ) (b : β) : γ := by
  fail_if_success solve_by_elim [-g]
  solve_by_elim [-f]

example (h : Nat) : Nat := by solve_by_elim only [h]
example {α β : Type} (f : α → β) (a : α) : β := by solve_by_elim only [f, a]
example {α β : Type} (f : α → α → β) (a : α) : β := by solve_by_elim only [f, a]
example {α β γ : Type} (f : α → β) (g : β → γ) (a : α) : γ := by solve_by_elim only [f, g, a]
example {α β γ : Type} (_f : α → β) (g : β → γ) (b : β) : γ := by solve_by_elim only [g, b]
example {α : Nat → Type} (f : (n : Nat) → α n → α (n+1)) (a : α 0) : α 4 := by
  solve_by_elim only [f, a]

example (h₁ h₂ : False) : Empty := by
  -- 'It doesn't make sense to remove local hypotheses when using `only` without `*`.'
  fail_if_success solve_by_elim only [-h₁]
  -- 'It does make sense to use `*` without `only`.'
  fail_if_success solve_by_elim [*, -h₁]
  solve_by_elim only [*, -h₁]

-- Verify that already assigned metavariables are skipped.
example (P₁ P₂ : α → Prop) (f : ∀ (a : α), P₁ a → P₂ a → β)
    (a : α) (ha₁ : P₁ a) (ha₂ : P₂ a) : β := by
  solve_by_elim

example {X : Type} (x : X) : x = x := by
  fail_if_success solve_by_elim (config := {constructor := false}) only -- needs the `rfl` lemma
  solve_by_elim

-- Needs to apply `rfl` twice, with different implicit arguments each time.
-- A naive implementation of solve_by_elim would get stuck.
example {X : Type} (x y : X) (p : Prop) (h : x = x → y = y → p) : p := by solve_by_elim

example : True := by
  fail_if_success solve_by_elim (config := {constructor := false}) only -- needs the `trivial` lemma
  solve_by_elim

example : True := by
  -- uses the `trivial` lemma, which should now be removed from the default set:
  solve_by_elim (config := {constructor := false})

example : True := by
  solve_by_elim only -- uses the constructor discharger.

-- Requires backtracking.
example (P₁ P₂ : α → Prop) (f : ∀ (a: α), P₁ a → P₂ a → β)
    (a : α) (_ha₁ : P₁ a)
    (a' : α) (ha'₁ : P₁ a') (ha'₂ : P₂ a') : β := by
  fail_if_success solve_by_elim (config := .noBackTracking)
  solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y := by
  fail_if_success solve_by_elim (config := {symm := false})
  solve_by_elim

example (P : True → False) : 3 = 7 := by
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
  fconstructor
  rintro (⟨n, fn⟩ | ⟨n, gn⟩)
  pick_goal 3
  rintro ⟨n, hf | hg⟩
  solve_by_elim* (config := {maxDepth := 13}) [Or.inl, Or.inr, Exists.intro]

-- Test that we can disable the `intro` discharger.
example (P : Prop) : P → P := by
  fail_if_success solve_by_elim (config := {intro := false})
  solve_by_elim

example (P Q : Prop) : P ∧ Q → P ∧ Q := by
  solve_by_elim

section apply_assumption

example {a b : Type} (h₀ : a → b) (h₁ : a) : b := by
  apply_assumption
  apply_assumption

example {α : Type} {p : α → Prop} (h₀ : ∀ x, p x) (y : α) : p y := by
  apply_assumption

-- Check that `apply_assumption` uses `symm`.
example (a b : α) (h : b = a) : a = b := by
  fail_if_success apply_assumption (config := {symm := false})
  apply_assumption

-- Check that `apply_assumption` uses `exfalso`.
example {P Q : Prop} (p : P) (q : Q) (h : P → ¬ Q) : ℕ := by
  fail_if_success apply_assumption (config := {exfalso := false})
  apply_assumption <;> assumption

end apply_assumption

section «using»

@[dummy_label_attr] axiom foo : 1 = 2

example : 1 = 2 := by
  fail_if_success solve_by_elim
  solve_by_elim using dummy_label_attr

end «using»

section issue1581

axiom mySorry {α} : α

@[dummy_label_attr] theorem le_rfl [LE α] {b c : α} (_h : b = c) : b ≤ c := mySorry

example : 5 ≤ 7 := by
  apply_rules using dummy_label_attr
  guard_target = 5 = 7
  exact mySorry

example : 5 ≤ 7 := by
  apply_rules [le_rfl]
  guard_target = 5 = 7
  exact mySorry

end issue1581
