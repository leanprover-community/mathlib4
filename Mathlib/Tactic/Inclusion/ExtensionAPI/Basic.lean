/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Lean.Meta.Basic
public meta import Mathlib.Tactic.Inclusion.Core.Inclusion

/-!
# Basic API for `inclusion` extensions

This file defines helpers for safely interacting with the `InclusionM` and `HypothesisM` monads
when constructing extensions for the `inclusion` tactic.
-/

public meta section

open Lean Meta

namespace Inclusion

/-- Return the value of parameter `name`, if it was supplied or has a default. -/
def InclusionM.getParam? (name : Name) : InclusionM (Option Expr) := do
  let some decl := (inclusionParamExt.getState (← getEnv)).find? name
    | throwError "Unknown inclusion parameter `{name}`"
  if let some value := (← read).paramSettings.find? name then
    return some value
  return decl.defaultValue?

/-- Return the value of parameter `name`. -/
def InclusionM.getParam (name : Name) : InclusionM Expr := do
  let some value ← InclusionM.getParam? name
    | throwError "No value was supplied for inclusion parameter `{name}`"
  return value

/-- Return the value of parameter `name`, if it was supplied or has a default. -/
def HypothesisM.getParam? (name : Name) : HypothesisM (Option Expr) := do
  let some decl := (inclusionParamExt.getState (← getEnv)).find? name
    | throwError "Unknown inclusion parameter `{name}`"
  if let some value := (← read).paramSettings.find? name then
    return some value
  return decl.defaultValue?

/-- Return the value of parameter `name`, or report that it was not supplied. -/
def HypothesisM.getParam (name : Name) : HypothesisM Expr := do
  let some value ← HypothesisM.getParam? name
    | throwError "No value was supplied for inclusion parameter `{name}`"
  return value

/-- Check that `iExpr` is well formed in `localContext`. -/
private def checkIVarWellFormed (localContext : LocalContext) (iExpr : IExpr) : MetaM Unit := do
  let ⟨iType, e⟩ := iExpr
  unless ← MetavarContext.isWellFormed localContext e do
    throwError "Cannot create an inclusion variable for {e} because it depends on variables \
      introduced while constructing the inclusion"
  unless ← MetavarContext.isWellFormed localContext iType.elemType do
    throwError "Cannot create an inclusion variable for {e} because its type depends on \
      variables introduced while constructing the inclusion"
  unless ← MetavarContext.isWellFormed localContext iType.setType do
    throwError "Cannot use set type {iType.setType} for {e} because it depends on \
      variables introduced while constructing the inclusion"

open PrettyPrinter Delaborator SubExpr in
/-- Delaborate an inclusion set variable as `I[e]`. -/
@[delab mdata.Inclusion.Internal.iVarDisplay]
def delabIVarDisplay : Delab := do
  let iVarDisplayExpr ← getExpr
  let some (.letE _ _ _ _ _) := annotation? `Inclusion.Internal.iVarDisplay iVarDisplayExpr
    | failure
  let exprSyntax ← withMDataExpr (withLetValue delab)
  let stx ← `($(mkIdent `I)[$exprSyntax])
  let stx ← annotateCurPos ⟨stx.raw.rewriteBottomUp (·.setInfo .none)⟩
  let infoStx : Term := ⟨stx.raw.setKind `Inclusion.Internal.iVarDisplay⟩
  addDelabTermInfo (← getPos) infoStx iVarDisplayExpr (explicit := false)
  return stx

/-- Construct the expression used to display `setVar` as `I[iExpr.expr]`. -/
private def mkIVarDisplay (iExpr : IExpr) (setVar : Expr) : Expr :=
  mkAnnotation `Inclusion.Internal.iVarDisplay <|
    mkLet .anonymous iExpr.iType.elemType iExpr.expr setVar (nondep := true)

/-- Create and register an inclusion variable for `iExpr`. -/
def mkIVar (iExpr : IExpr) (cover? : Option Expr := none) : InclusionM IVar := do
  let ctx ← read
  if ctx.noIVars then
    throwError "Cannot create an inclusion variable for {iExpr.expr} since `noIVars` is set to true"
  checkIVarWellFormed ctx.localContext iExpr
  let setVar ←
    mkFreshExprMVarAt ctx.localContext ctx.localInstances iExpr.iType.setType .syntheticOpaque
  let hypVarType ← iExpr.mkMem setVar
  let hypVar ← mkFreshExprMVarAt ctx.localContext ctx.localInstances hypVarType .syntheticOpaque
  let iVar := { iExpr, setVar, hypVar, cover? }
  modify fun state => { state with iVars := state.iVars.insert iVar.expr iVar }
  if ← isTracingEnabledFor `Tactic.inclusion then
    let iVarDisplayExpr := mkIVarDisplay iExpr setVar
    modify fun state => {
      state with iVarDisplays := state.iVarDisplays.insert setVar iVarDisplayExpr }
  return iVar

/-- Construct an inclusion extension for making non dependently typed inclusion variables. -/
def mkNDIVarExt (family : Name) (iType : IType)
    (mkCover? : InclusionM (Option Expr) := pure none)
    (priority : Nat := eval_prio low) (name : Name := by exact decl_name%) : InclusionExt where
  declName := name
  family := family
  priority := priority
  derive e := do
    let eType ← inferType e
    unless ← isDefEq eType iType.elemType do failure
    let iExpr : IExpr := ⟨iType, e⟩
    return (← mkIVar iExpr (← mkCover?)).toExprInclusionBody

/-- Return the inclusion variable registered for `e`, if there is one. -/
def findIVar? (e : Expr) : HypothesisM (Option IVar) := do
  return (← read).iVarsMap[e]?

/-- Check that two inclusion types are definitionally equal, including their chosen `ToSet`
instances. -/
def ensureOutputType (type expectedType : IType) : MetaM Unit := do
  unless ← pureIsDefEq type.elemType expectedType.elemType do
    throwError "Inclusion has expression type {type.elemType}, expected {expectedType.elemType}"
  unless ← pureIsDefEq type.setType expectedType.setType do
    throwError "Inclusion has set type {type.setType}, expected {expectedType.setType}"
  unless ← pureIsDefEq type.toSetInst expectedType.toSetInst do
    throwError "Inclusion uses an unexpected `ToSet` instance"

/-- Construct a closed inclusion body for an expression argument of a hypothesis rule. -/
def mkHypExprInclusionBody (e : Expr) : HypothesisM ExprInclusionBody := do
  let ctx ← read
  let inclusionContext := { ctx.toContext with noIVars := true }
  let (body, inclusionState) ← (mkExprInclusionBody e).runWith inclusionContext
  unless inclusionState.iVars.isEmpty do
    throwError "The inclusion for {e} depends on inclusion variables"
  if body.inclusionBody.hasFVar then
    throwError "The inclusion hypothesis generated from {e} contains a free variable"
  if body.inclusionBody.hasMVar then
    throwError "The inclusion hypothesis generated from {e} contains a metavariable"
  return body

/-- Add the inclusion hypothesis `body` for `iExpr`. -/
def addInclusionHyp (iExpr : IExpr) (body : ExprInclusionBody) : HypothesisM Unit := do
  ensureOutputType (← body.inferIType iExpr.expr) iExpr.iType
  modify fun state => { state with inclusions := state.inclusions.alter iExpr.expr fun
    | some hyps => hyps.push body
    | none => #[body] }

end Inclusion
