/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Scott Morrison
-/
import Mathlib.Tactic.ShowTerm

-- TODO can `showTerm` be indenting aware, so we don't have to use braces and semicolons?

example (n : Nat) : Nat × Nat := by
  showTerm
    { constructor;
      exact n;
      exact 37 }

example (n : Nat) : Nat × Nat := by
  showTerm constructor
  repeat exact 42
