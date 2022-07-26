/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Mathlib.Lean.Expr.Basic

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

/-- Updates the current goal with a `Expr` map function in `MetaM`. -/
def modifyTarget (f : Expr → MetaM Expr) : TacticM Unit :=
  liftMetaTactic fun mvarId => do
    let newGoal ← mkFreshExprMVarAt (← getLCtx) (← getLocalInstances)
      (← f (← getMVarType mvarId)) .syntheticOpaque (← getMVarTag mvarId)
    assignExprMVar mvarId newGoal
    return [newGoal.mvarId!]

/-- Updates the current `LocalContext` with a map function in `MetaM`. -/
def modifyLocalContext (f : LocalContext → MetaM LocalContext) : TacticM Unit :=
  liftMetaTactic fun mvarId => do
    let newGoal ← mkFreshExprMVarAt (← f (← getLCtx)) (← getLocalInstances)
      (← getMVarType mvarId) .syntheticOpaque (← getMVarTag mvarId)
    assignExprMVar mvarId newGoal
    return [newGoal.mvarId!]

/-- Updates a `LocalDecl` to be found by its `FVarId` with a map function in `MetaM`. -/
def modifyLocalDecl (fvarId : FVarId) (f : Option LocalDecl → MetaM LocalDecl) :
    TacticM Unit :=
  modifyLocalContext fun lctx => do
    let decl ← f (lctx.find? fvarId)
    return ⟨lctx.fvarIdToDecl.insert decl.fvarId decl, lctx.decls.set decl.index decl⟩

/-- Renames bound variables on a hypothesis. -/
def renameBVarHyp (old new : Name) (fvarId : FVarId) : TacticM Unit :=
  modifyLocalDecl fvarId fun decl? => match decl? with
    | some decl => return decl.setType $ decl.type.renameBVar old new
    | none      => throwError "invalid FVarId: {repr fvarId}"

/-- Renames bound variables in the target. -/
def renameBVarTarget (old new : Name) : TacticM Unit :=
  modifyTarget fun e => return e.renameBVar old new
