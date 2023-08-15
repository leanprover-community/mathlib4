/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jon Eugster
-/
import Mathlib.Lean.Meta
/-!
# Additions to `Lean.Elab.Tactic.Basic`
-/

set_option autoImplicit true

open Lean Elab Tactic

namespace Lean.Elab.Tactic

/-- Return expected type for the main goal, cleaning up annotations, using `Lean.MVarId.getType''`.
Remark: note that `MVarId.getType'` uses `whnf` instead of `cleanupAnnotations`, and
`MVarId.getType''` also uses `cleanupAnnotations` -/
def getMainTarget'' : TacticM Expr := do
  (← getMainGoal).getType''

/--
Like `done` but takes a scope (e.g. a tactic name) as an argument
to produce more detailed error messages.
-/
def doneWithScope (scope : MessageData) : TacticM Unit := do
  let gs ← getUnsolvedGoals
  unless gs.isEmpty do
    logError m!"{scope} failed to solve some goals.\n"
    Term.reportUnsolvedGoals gs
    throwAbortTactic

/--
Like `focusAndDone` but takes a scope (e.g. tactic name) as an argument to
produce more detailed error messages.
-/
def focusAndDoneWithScope (scope : MessageData) (tactic : TacticM α) : TacticM α :=
  focus do
    let a ← try tactic catch e =>
      if isAbortTacticException e then throw e
      else throwError "{scope} failed.\n{← nestedExceptionToMessageData e}"
    doneWithScope scope
    pure a

end Lean.Elab.Tactic
