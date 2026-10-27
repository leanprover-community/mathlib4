/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jon Eugster
-/
module

public import Mathlib.Lean.Meta
/-!
# Additions to `Lean.Elab.Tactic.Basic`
-/

@[expose] public section

open Lean Elab Tactic

namespace Lean.Elab.Tactic

/-- Return expected type for the main goal, cleaning up annotations, using `Lean.MVarId.getType''`.
Remark: note that `MVarId.getType'` uses `whnf` instead of `cleanupAnnotations`, and
`MVarId.getType''` also uses `cleanupAnnotations` -/
def getMainTarget'' : TacticM Expr := do
  (← getMainGoal).getType''

/-- Runs `x`, and if `x` throws an exception, rewinds the tactic state *except* for the `InfoState`
and `Messages`. This means that hovers and error messages created within `x` are preserved.

Note: `x` is run under `withSaveInfoContext` in order to propagate hovers and messages correctly.
This means that pre-existing infotrees are not accessible from within `x`. -/
def commitIfNoExPreservingInfoAndMessages {α} (x : TacticM α) : TacticM α := do
  let saved ← saveState
  Tactic.tryCatch (withSaveInfoContext x) fun ex => do
    let saved := { saved with
      term.meta.core.infoState := ← getInfoState
      term.meta.core.messages := (← getThe Core.State).messages }
    restoreState saved
    throw ex

end Lean.Elab.Tactic
