/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Nat.Order.Basic
import Std.Tactic.SolveByElim

lemma foo (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  apply_rules [mul_ne_zero]
