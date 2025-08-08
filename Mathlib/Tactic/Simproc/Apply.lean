/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Simp.Main

/-!
# Procedure to execute a custom Simproc

The only function `Simproc.apply` defined in this file takes a `s : Simproc` and executes it on the
goal.
-/

open Lean Elab Tactic

def Lean.Meta.Simp.Simproc.apply (s : Simproc) : TacticM Unit := do
  liftMetaTactic1 fun e ↦ do
    -- `Simproc` usually does not allow arguments, so we hijacked `Simp.mainCore` to provide a
    -- `Simproc` that accepts arguments (which is `equivCore` here).
    let target ← instantiateMVars (← e.getType)
    let ctx ← Simp.mkContext (simpTheorems := #[])
    let (r, _) ← Simp.mainCore target ctx (methods := {post := s})
    return ← applySimpResultToTarget e target r
