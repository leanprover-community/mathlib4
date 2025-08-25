/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Lean.Elab.Tactic.Location
import Lean.Meta.Tactic.Simp.Main

/-!
# Procedure to execute a custom Simproc

The only function `Simproc.apply` defined in this file takes a `s : Simproc` and executes it on the
goal.
-/

namespace Lean.Meta.Simp.Simproc

open Elab.Tactic

set_option linter.unusedVariables false in
/-- Process the given local hypothesis. -/
def applyAtLocalDecl (s : Simproc) (f : FVarId) : TacticM Unit := do
  let hyp ← instantiateMVars (← f.getType)
  let ctx ← mkContext (simpTheorems := #[])
  let (r, _) ← mainCore hyp ctx (methods := {post := s})
  liftMetaTactic1 fun m ↦ do
    let .some (f, m) ← applySimpResultToLocalDecl m f r false | return m
    return m

/-- Process the goal. -/
def applyAtTarget (s : Simproc) : TacticM Unit := do
  liftMetaTactic1 fun m ↦ do
    -- We cannot pass a `Simproc` object into `simp`, because `simp` only accepts names of global
    -- constants. However, the core part of `simp`, i.e. `Simp.mainCore`, actually allows `Simproc`s
    -- to be executed, so this code calls `Simp.mainCore` directly.
    let target ← instantiateMVars (← m.getType)
    let ctx ← mkContext (simpTheorems := #[])
    let (r, _) ← mainCore target ctx (methods := {post := s})
    let i ← applySimpResultToTarget m target r
    return i
  evalTactic (← `(tactic| try rfl))

/-- Execute the given `Simproc` on the goal. -/
def apply (s : Simproc) (loc : Option Location) : TacticM Unit :=
  match loc with
  | .none => applyAtTarget s
  | .some loc => withLocation loc (applyAtLocalDecl s) (applyAtTarget s) default

end Lean.Meta.Simp.Simproc
