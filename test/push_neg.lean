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
  exact h

example : ¬(p ∧ q) → (p → ¬q) :=by
  intro h
  push_neg at h
  exact h

example : (∀(x : α), ¬ p' x) → ¬ ∃(x : α), p' x:= by
  intro h
  push_neg
  exact h

example : (¬ ∀(x : α), p' x) → (∃(x : α), ¬ p' x) :=by
  intro h
  push_neg at h
  exact h

example (p : Bool) : decide (¬ ¬ p) = p := by
  push_neg
  induction p
  simp
  simp

example : ((fun x => x+x) 1) = 2 := by
  push_neg
  simp

example : ¬ ¬ p = p := by
  push_neg
  rfl

example (x y : β) (h : y < x) : ¬(x ≤ y) := by
  push_neg
  exact h

example : ¬∃ (y : Unit), (y ≠ ()) := by
  push_neg
  simp

example (h : ∃ y : Nat, ¬(y=1)): ¬∀ (y : Nat), (y = 1) := by
  push_neg
  exact h

example (x y : β) (h : y < x) : ¬¬¬ (x ≤ y) := by
  push_neg
  exact h

example (x y : β) (h₁ : ¬¬¬(x < y)) (h₂ : ¬∃ (x y : Nat), x = y) : ¬ ∀(x y : Nat), x = y := by
  push_neg at *
  exact ⟨0, 1, by simp⟩
