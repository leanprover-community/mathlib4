/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Tactic.Push
import Batteries.Tactic.PermuteGoals

/-!
# The `by_cases` tactic

The `by_cases!` tactic is a variant of the `by_cases` tactic that also calls `push_neg`.
-/

/--
`by_cases! h : p` runs the `by_cases h : p` tactic, followed by
`try push_neg at h` in the second subgoals.

For example, `by_cases! h : a < b` creates one goal with the hypothesis `h : a < b` and
one goal with `h : b ≤ a`.
-/
syntax (name := byCases!) "by_cases! " (atomic(ident " : "))? term : tactic

macro_rules
  | `(tactic| by_cases! $e) => `(tactic| by_cases! h : $e)
  | `(tactic| by_cases! $h : $e) =>
    `(tactic| by_cases $h : $e; try on_goal 2 => push_neg at $h:ident)
