/-
Copyright (c) 2022 Alice Laroche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alice Laroche, Frédéric Dupuis, Jireh Loreaux
-/

import Mathlib.Tactic.PushNeg
import Mathlib.Init.Algebra.Order

variable {α β : Type} [LinearOrder β] {p q : Prop} {p' q' : α → Prop}

example : (¬p ∧ ¬q) → ¬(p ∨ q) := by
  intro h
  push_neg
  guard_target = ¬p ∧ ¬q
  exact h

example : ¬(p ∧ q) → (p → ¬q) := by
  intro h
  push_neg at h
  guard_hyp h : p → ¬q
  exact h

example : (∀(x : α), ¬ p' x) → ¬ ∃(x : α), p' x:= by
  intro h
  push_neg
  guard_target = ∀ (x : α), ¬p' x
  exact h

example : (¬ ∀(x : α), p' x) → (∃(x : α), ¬ p' x) :=by
  intro h
  push_neg at h
  guard_hyp h : ∃ (x : α), ¬p' x
  exact h

example (p : Bool) : decide (¬ ¬ p) = p := by
  push_neg
  guard_target = decide p = p
  cases p <;> rfl

example : ((fun x => x+x) 1) = 2 := by
  push_neg
  guard_target = 1 + 1 = 2
  simp

example : ¬ ¬ p = p := by
  push_neg
  guard_target = p = p
  rfl

example (x y : β) (h : y < x) : ¬(x ≤ y) := by
  push_neg
  guard_target = y < x
  exact h

example (x y : α) (h : x = y) : ¬ (x ≠ y) := by
  push_neg
  guard_target = x = y
  exact h

example : ¬∃ (y : Unit), (y ≠ ()) := by
  push_neg
  guard_target = ∀ (y : Unit), y = ()
  simp

example (h : ∃ y : Nat, ¬(y=1)): ¬∀ (y : Nat), (y = 1) := by
  push_neg
  guard_target = ∃ (y : Nat), y ≠ 1
  exact h

example (x y : β) (h : y < x) : ¬¬¬ (x ≤ y) := by
  push_neg
  guard_target = y < x
  exact h

example (x y : β) (h₁ : ¬¬¬(x < y)) (h₂ : ¬∃ (x y : Nat), x = y) : ¬ ∀(x y : Nat), x = y := by
  push_neg at *
  guard_target = ∃ (x y : Nat), x ≠ y
  guard_hyp h₁ : y ≤ x
  guard_hyp h₂ : ∀ (x y : Nat), x ≠ y
  exact ⟨0, 1, by simp⟩

example (x y : β) (h₁ : ¬¬¬(x < y)) (h₂ : ¬∃ (x y : Nat), x = y) : ¬ ∀(x y : Nat), x = y := by
  push_neg at h₁ h₂ ⊢
  guard_target = ∃ (x y : Nat), x ≠ y
  guard_hyp h₁ : y ≤ x
  guard_hyp h₂ : ∀ (x y : Nat), x ≠ y
  exact ⟨0, 1, by simp⟩

example (h : p → ¬ q) : ¬ (p ∧ q) := by
  push_neg
  guard_target = p → ¬q
  exact h

example (a : β) : ¬ ∀ x : β, x < a → ∃ y : β, (y < a) ∧ ∀ z : β, x = z := by
  push_neg
  guard_target = ∃ x, x < a ∧ ∀ (y : β), y < a → ∃ z, x ≠ z
  sorry

set_option push_neg.use_distrib true

example (h : ¬ p ∨ ¬ q): ¬ (p ∧ q) := by
  push_neg
  guard_target = ¬p ∨ ¬q
  exact h

example : p →  ¬ ¬ ¬ ¬ ¬ ¬ p := by
  push_neg
  guard_target = p → p
  exact id

example (h : x = 0 ∧ y ≠ 0) : ¬(x = 0 → y = 0) := by
  push_neg
  guard_target = x = 0 ∧ y ≠ 0
  exact h
