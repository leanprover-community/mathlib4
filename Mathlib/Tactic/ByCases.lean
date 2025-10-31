/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Tactic.Push
import Batteries.Tactic.PermuteGoals

/-!
# The `by_cases!` tactic

The `by_cases!` tactic is a variant of the `by_cases` tactic that also calls `push_neg`
on the generated hypothesis that is a negation.
-/

/--
`by_cases! h : p` runs the `by_cases h : p` tactic, followed by
`try push_neg at h` in the second subgoal. For example,
- `by_cases! h : a < b` creates one goal with hypothesis `h : a < b` and
  another with `h : b ≤ a`.
- `by_cases! h : a ≠ b` creates one goal with hypothesis `h : a ≠ b` and
  another with `h : a = b`.
-/
syntax (name := byCases!) "by_cases! " (atomic(ident " : "))? term : tactic

macro_rules
  | `(tactic| by_cases! $e) => `(tactic| by_cases! h : $e)
  | `(tactic| by_cases! $h : $e) =>
    `(tactic| by_cases $h : $e; try on_goal 2 => push_neg at $h:ident)
