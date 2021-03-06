/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Lean

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

/-- Finds the `Name` and the `FVarId` of a variable given a `LocalContext` and a `Syntax.ident`. -/
def getNameAndFVarId [Monad m] [MonadError m] (ctx : LocalContext) (stx : Syntax) :
    m (Name × FVarId) :=
  if stx.isIdent then
    let name := stx.getId
    match ctx.findFromUserName? name with
    | some decl => return (name, decl.fvarId)
    | none => throwErrorAt stx "unknown variable {name}"
  else
    throwErrorAt stx "not an identifier"

/-- Updates the current `LocalContext` with a transformation function in `MetaM`. -/
def modifyLocalContext (fLCtx : LocalContext → MetaM LocalContext) : TacticM Unit :=
  liftMetaTactic fun mvarId => do
    let newGoal ← mkFreshExprMVarAt (← fLCtx (← getLCtx)) (← getLocalInstances)
      (← getMVarType mvarId) .syntheticOpaque (← getMVarTag mvarId)
    assignExprMVar mvarId newGoal
    return [newGoal.mvarId!]
