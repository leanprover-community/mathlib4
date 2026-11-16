/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills, Michael Rothgang
-/
module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.Util
public import Mathlib.Init

/-!
# Tactic combinators about making (no) progress

This implements tactic combinators to check if the following tactic sequence makes actual progress:
the `fail_if_no_progress` tactic combinator fails if no actual progress is made,
the `fail_if_progress` combinator fails if actual progress is made, and
the `fail_if_not_idempotent` combinator fails if running the tactic sequence a second time makes
progress.
following tactic sequence.

"Actual progress" means that either the number of goals has changed, that the
number or presence of expressions in the context has changed, or that the type of some expression
in the context or the type of the goal is no longer definitionally equal to what it used to be at
reducible transparency.

This means that, for example, `1 - 1` changing to `0` does not count as actual progress, since
```lean
example : (1 - 1 = 0) := by with_reducible rfl
```

`fail_if_no_progress` is useful in situations where we want to stop iterating some tactics if
they're not having any effect, e.g. `repeat (fail_if_no_progress simp <;> ring_nf)`.

`fail_if_progress` and `fail_if_not_idempotent` are great for investigating misconfigured
`norm_cast` lemmas, e.g. `fail_if_not_idempotent norm_cast` can be used to detect bad configuration
causing non-idempotency.
-/

public meta section

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

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

/-- Run `tacs : TacticM Unit` on `goal`: return whether `tacs` made progress, and the resulting
goal(s) after running `tacs`. -/
def runAndDetectProgress (goal : MVarId) (tacs : TacticM Unit) : TacticM (Bool × List MVarId) := do
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
    return (true, l,)
  return (false, [goal])

/-- Run `tacs : TacticM Unit` on `goal`, and fail if no progress is made.
Return the resulting goal(s) after running `tacs`. -/
def runAndFailIfNoProgress (goal : MVarId) (tacs : TacticM Unit) : TacticM (List MVarId) := do
  match ← runAndDetectProgress goal tacs with
  | (true, new) => return new
  | (false, _) => throwError "no progress made on\n{goal}"

/-- Run `tacs : TacticM Unit` on `goal`, and fail if progress is made.
Return the resulting goal(s) after running `tacs`. -/
def runAndFailIfProgress (goal : MVarId) (tacs : TacticM Unit) : TacticM (List MVarId) := do
  match ← runAndDetectProgress goal tacs with
  | (true, _) => throwError "progress made on\n{goal}"
  | (false, _) => return [goal]

/-- `fail_if_no_progress tacs` evaluates `tacs`, and fails if no progress is made on the main goal
or the local context at reducible transparency. -/
syntax (name := failIfNoProgress) "fail_if_no_progress " tacticSeq : tactic

elab_rules : tactic
| `(tactic| fail_if_no_progress $tacs) => do
  let goal ← getMainGoal
  replaceMainGoal (← runAndFailIfNoProgress goal (evalTactic tacs))

/-- `fail_if_progress tacs` evaluates `tacs`, and fails if progress is made on the main goal
or the local context at reducible transparency. -/
syntax (name := failIfProgress) "fail_if_progress " tacticSeq : tactic

elab_rules : tactic
| `(tactic| fail_if_progress $tacs) => do
  let goal ← getMainGoal
  replaceMainGoal (← runAndFailIfProgress goal (evalTactic tacs))

/-- `fail_if_not_idempotent tacs` evaluates `tacs`, then evaluates `tacs` again on any remaining
goals, and fails if progress is made in the second run (on the main goal
or the local context at reducible transparency). -/
syntax (name := failIfNotIdempotent) "fail_if_not_idempotent " tacticSeq : tactic

elab_rules : tactic
| `(tactic| fail_if_not_idempotent $tacs) => do
  let goal ← getMainGoal
  let middle ← run goal (evalTactic tacs)
  let newGoals := (← middle.mapM (fun g ↦ runAndFailIfProgress g (evalTactic tacs))).flatten
  replaceMainGoal newGoals

end Mathlib.Tactic
