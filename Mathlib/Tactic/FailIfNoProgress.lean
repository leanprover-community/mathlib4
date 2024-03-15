/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Util

/-!
# Fail if no progress

This implements the `fail_if_no_progress` tactic, which fails if no actual progress is made by the
following tactic sequence.

"Actual progress" means that either the number of goals has changed, that the
number or presence of expressions in the context has changed, or that the type of some expression
in the context or the type of the goal is no longer definitionally equal to what it used to be at
reducible transparency.

This means that, for example, `1 - 1` changing to `0` does not count as actual progress, since
```lean
example : (1 - 1 = 0) := by with_reducible rfl
```

This tactic is useful in situations where we want to stop iterating some tactics if they're not
having any effect, e.g. `repeat (fail_if_no_progress simp <;> ring_nf)`.

-/

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

/-- `fail_if_no_progress tacs` evaluates `tacs`, and fails if no progress is made on the main goal
or the local context at reducible transparency. -/
syntax (name := failIfNoProgress) "fail_if_no_progress " tacticSeq : tactic

/-- `lctxIsDefEq l₁ l₂` compares two lists of `Option LocalDecl`s (as returned from e.g.
`(← (← getMainGoal).getDecl).lctx.decls.toList`). It returns `true` if they have the same
local declarations in the same order (up to defeq, without setting mvars), and `false` otherwise.

Assumption: this function is run with one of the local contexts as the current `MetaM` local
context, and one of the two lists consists of the `LocalDecl`s of that context. -/
def lctxIsDefEq : (l₁ l₂ : List (Option LocalDecl)) → MetaM Bool
  | none :: l₁, l₂ => lctxIsDefEq l₁ l₂
  | l₁, none :: l₂ => lctxIsDefEq l₁ l₂
  | some d₁ :: l₁, some d₂ :: l₂ => do
    unless d₁.isLet == d₂.isLet do
      return false
    unless d₁.fvarId == d₂.fvarId do
      -- Without compatible fvarids, `isDefEq` checks for later entries will not make sense
      return false
    unless (← withNewMCtxDepth <| isDefEq d₁.type d₂.type) do
      return false
    if d₁.isLet then
      unless (← withNewMCtxDepth <| isDefEq d₁.value d₂.value) do
        return false
    lctxIsDefEq l₁ l₂
  | [], [] => return true
  | _, _ => return false

/-- Run `tacs : TacticM Unit` on `goal`, and fail if no progress is made. -/
def runAndFailIfNoProgress (goal : MVarId) (tacs : TacticM Unit) : TacticM (List MVarId) := do
  let l ← run goal tacs
  try
    let [newGoal] := l | failure
    goal.withContext do
      -- Check that the local contexts are compatible
      let ctxDecls := (← goal.getDecl).lctx.decls.toList
      let newCtxDecls := (← newGoal.getDecl).lctx.decls.toList
      guard <|← withNewMCtxDepth <| withReducible <| lctxIsDefEq ctxDecls newCtxDecls
      -- They are compatible, so now we can check that the goals are equivalent
      guard <|← withNewMCtxDepth <| withReducible <| isDefEq (← newGoal.getType) (← goal.getType)
  catch _ =>
    return l
  throwError "no progress made on\n{goal}"

elab_rules : tactic
| `(tactic| fail_if_no_progress $tacs) => do
  let goal ← getMainGoal
  let l ← runAndFailIfNoProgress goal (evalTactic tacs)
  replaceMainGoal l
