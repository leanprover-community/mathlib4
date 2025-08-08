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

/-- Execute the given `Simproc` on the goal. -/
def Lean.Meta.Simp.Simproc.apply (s : Simproc) : TacticM Unit := do
  liftMetaTactic1 fun e ↦ do
    -- We cannot pass a `Simproc` object into `simp`, because `simp` only accepts names of global
    -- constants. However, the core part of `simp`, i.e. `Simp.mainCore`, actually allows `Simproc`s
    -- to be executed, so this code calls `Simp.mainCore` directly.
    let target ← instantiateMVars (← e.getType)
    let ctx ← Simp.mkContext (simpTheorems := #[])
    let (r, _) ← Simp.mainCore target ctx (methods := {post := s})
    applySimpResultToTarget e target r
