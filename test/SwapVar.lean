/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.SwapVar

example {P Q : Prop} (q : P) (p : Q) : P ∧ Q := by
  swap_var p ↔ q
  exact ⟨p, q⟩

example {a b : Nat} (h : a = b) : a = b ∧ a = a := by
  swap_var a ↔ b
  guard_hyp h : b = a
  guard_target = b = a ∧ b = b
  exact ⟨h, Eq.refl b⟩

example {a b c d : Nat} (h : a = b ∧ c = d) : a = b ∧ c = d := by
  swap_var a ↔ b, b c
  guard_target = c = a ∧ b = d
  exact h
