/-
Copyright (c) 2023 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Std.Tactic.ShowTerm

/-!
# A helper macro for replacing assumptions with exact statements

## Summary

This file adds a `assumption?` macro that expands to `show_term assumption`
the goal is to make it more efficient to clean up proofs with `assumption`s in by making them
more explicit.

-/


/-- `assumption?` is equivalent to `show_term assumption` -/
macro "assumption?" : tactic => `(tactic| show_term assumption)
