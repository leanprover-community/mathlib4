/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import Mathlib.Tactic.ShowTerm

example (n : Nat) : Nat × Nat := by
  show_term
    constructor
    exact n
    exact 37

example (n : Nat) : Nat × Nat := by
  show_term constructor
  repeat exact 42
