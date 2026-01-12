/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Batteries.Tactic.PermuteGoals
public import Mathlib.Tactic.Push

/-!
# The `by_cases!` tactic

The `by_cases!` tactic is a variant of the `by_cases` tactic that also calls `push_neg`
on the generated hypothesis that is a negation.
-/

public meta section

namespace Mathlib.Tactic.ByCases
open Lean.Parser.Tactic

/--
`by_cases! h : p` runs the `by_cases h : p` tactic, followed by
`push_neg at h` in the second subgoal. For example,
- `by_cases! h : a < b` creates one goal with hypothesis `h : a < b` and
  another with `h : b ≤ a`.
- `by_cases! h : a ≠ b` creates one goal with hypothesis `h : a ≠ b` and
  another with `h : a = b`.
-/
syntax (name := byCases!) "by_cases! " optConfig (atomic(ident " : "))? term : tactic

local elab "try_push_neg_at" cfg:optConfig h:ident : tactic => do
  Push.push (← Push.elabPushConfig cfg) none (.const ``Not) (.targets #[h] false)
    (failIfUnchanged := false)

macro_rules
  | `(tactic| by_cases! $cfg:optConfig $e) => `(tactic| by_cases! $cfg h : $e)
  | `(tactic| by_cases! $cfg:optConfig $h : $e) =>
    `(tactic| by_cases $h : $e; on_goal 2 => try_push_neg_at $cfg $h:ident)

end Mathlib.Tactic.ByCases
