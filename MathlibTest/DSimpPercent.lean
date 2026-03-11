/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.Tactic.DSimpPercent
import Mathlib.Data.Nat.Basic

/-!
Tests for the behavior of `dsimp%`.
-/

def f : ℕ → ℕ → ℕ := fun a b => a + b

@[simp]
lemma f_apply (a b : ℕ) : f a b = a + b := rfl

-- Testing dsimp% on a proof
variable {a b c : ℕ} in
/-- info: id (Nat.add_comm (f a b) c) : a + b + c = c + (a + b) -/
#guard_msgs in
#check dsimp% Nat.add_comm (f a b) c

-- Testing dsimp% on a term
variable {a b c : ℕ} in
/-- info: a + b : ℕ -/
#guard_msgs in
#check dsimp% f a b

def g : ℕ → ℕ → ℕ := fun a b => a + b
lemma g_apply (a b : ℕ) : g a b = a + b := rfl

-- Testing dsimp% […] on a proof
variable {a b c : ℕ} in
/-- info: id (Nat.add_comm (g a b) c) : a + b + c = c + (a + b) -/
#guard_msgs in
#check dsimp% [g_apply] Nat.add_comm (g a b) c

-- Testing dsimp% […] on a term
variable {a b c : ℕ} in
/-- info: a + b : ℕ -/
#guard_msgs in
#check dsimp% [g_apply] g a b

variable (a b : Int) in
/-- error: `dsimp%` made no progress -/
#guard_msgs in
#check dsimp% a + b
