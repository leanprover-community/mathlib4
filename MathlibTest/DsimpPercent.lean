/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.Tactic.DsimpPercent
import Mathlib.Data.Nat.Basic

/-!
Tests for the behavior of `dsimp%`.
-/

def f : ℕ → ℕ → ℕ := fun a b => a + b

@[simp]
lemma f_apply (a b : ℕ) : f a b = a + b := rfl

variable {a b c : ℕ} in
/-- info: id (Nat.add_comm (f a b) c) : a + b + c = c + (a + b) -/
#guard_msgs in
#check dsimp% Nat.add_comm (f a b) c
