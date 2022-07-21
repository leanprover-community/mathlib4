/-
Copyright (c) 2022 Alice Laroche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alice Laroche
-/

import Mathlib.Tactic.PushNeg

variable {α : Type} {p q : Prop} {p' q' : α → Prop}

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
