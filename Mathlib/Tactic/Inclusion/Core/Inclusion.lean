/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Expr
public meta import Mathlib.Tactic.Inclusion.Core.Extensions

/-!
# Constructing inclusions

This file defines the main drivers of the `inclusion` tactic.

Given an expression `e`, `mkExprInclusionBody` recursively applies `InclusionExt`s to construct an
`ExprInclusionBody` for `e`. Then `toExprInclusion` applies `HypothesisExt`s to the local context to
construct inclusion hypotheses for the body's inclusion variables and closes the body into an
`ExprInclusion`.

-/

namespace Inclusion

public meta section

open Lean Meta

initialize registerTraceClass `Tactic.inclusion

/-- Given the `userName` of an `InclusionExt` and the name of the inclusion family it belongs to,
print `[family] userName`. -/
private def ppExtensionName (family userName : Name) : MessageData :=
  m!"[{family}] {.ofConstName userName}"

/-- Given `exts : Array InclusionExt`, print each extension in a numbered list. -/
private def ppMatchedExts (exts : Array InclusionExt) : MessageData :=
  m!"\n".joinSep (exts.toList.mapIdx fun i ext =>
    m!"{i + 1}. {ppExtensionName ext.family ext.userName}")

private def ppInclusionExpr (e : Expr) : InclusionM MessageData := do
  let iVarDisplays := (← get).iVarDisplays
  return m!"{e.replace fun e => iVarDisplays[e]?}"

/-- Construct an `ExprInclusionBody` for `e`. -/
def mkExprInclusionBody (e : Expr) : InclusionM ExprInclusionBody := do
  withTraceNode `Tactic.inclusion
    (fun _ => return m!"Making `ExprInclusionBody` for:\n {e}") do
  if let some iVar := (← get).iVars[e]? then
    trace[Tactic.inclusion] "Reusing inclusion variable for {e}"
    return iVar.toExprInclusionBody
  let matchedExts ← getInclusionExtMatches (← read).families e
  trace[Tactic.inclusion]
    "Matched inclusion extensions (in order of priority):\n{ppMatchedExts matchedExts}"
  let savedState ← saveState
  for ext in matchedExts do
    withTraceNode `Tactic.inclusion
      (fun _ => do return m!"Trying {ppExtensionName ext.family ext.userName}") do←
      try
        let body ← ext.derive e
        recordExtraModUseFromDecl (isMeta := true) ext.declName
        trace[Tactic.inclusion] "Inclusion body:\n {← ppInclusionExpr body.inclusionBody}"
        return body
      catch err =>
        trace[Tactic.inclusion]
          "Failed to apply {ppExtensionName ext.family ext.userName} to {e}: \
            {err.toMessageData}"
        restoreState savedState
  throwError "No inclusion extension applies to {e}"

/-- Check that `body.proofBody` is a proof of `e ∈ body.inclusionBody` and infer its `IType`. -/
def ExprInclusionBody.inferIType (body : ExprInclusionBody) (e : Expr) : MetaM IType := do
  let proofBodyType ← inferType body.proofBody
  let invalidProof := m!"{proofBodyType} is not a proof of `{e} ∈ {body.inclusionBody}`"
  let some (e', s, toSetInst) := toSetMem? proofBodyType | throwError invalidProof
  unless ← isDefEq e' e do throwError invalidProof
  unless ← isDefEq s body.inclusionBody do throwError invalidProof
  return ⟨← inferType e, ← inferType body.inclusionBody, toSetInst⟩

/-- Run hypothesis extensions on hypothesis `h`. -/
def runHypothesisExts (h : Expr) : HypothesisM Unit := do
  let type ← instantiateMVars (← inferType h)
  let matchedExts ← getHypothesisExtMatches (← read).families type
  for ext in matchedExts do
    let saved ← saveState
    try
      ext.derive h
      recordExtraModUseFromDecl (isMeta := true) ext.declName
      trace[Tactic.inclusion]
        "{ppExtensionName ext.family ext.userName} processed {type}"
    catch err =>
      trace[Tactic.inclusion]
        "Failed to apply {ppExtensionName ext.family ext.userName} to {type}: \
          {err.toMessageData}"
      restoreState saved

/-- Run hypothesis extensions on all declarations in the local context. -/
def collectHyps : HypothesisM Unit := do
  let context ← read
  if context.iVars.isEmpty then
    return ()
  for ldecl in context.localContext do
    unless ldecl.isImplementationDetail do
      runHypothesisExts ldecl.toExpr

/-- Construct the universal inclusion body for `iExpr`. -/
def mkUniversalHypBody (iExpr : IExpr) : MetaM ExprInclusionBody := do
  let univ ← iExpr.iType.synthUniv
  return ⟨← iExpr.iType.mkUniv univ, ← iExpr.mkMemUniv univ⟩

/-- Combine the candidate hypothesis bodies for `iExpr` using `Refine`, or use its `Univ`
instance when there are no candidates. -/
def combineHypBodies (iExpr : IExpr) (bodies : Array ExprInclusionBody) :
    MetaM ExprInclusionBody := do
  if bodies.isEmpty then
    return ← mkUniversalHypBody iExpr
  let first := bodies[0]!
  if bodies.size = 1 then
    return first
  let refiner ← iExpr.iType.synthRefine
  let mut set := first.inclusionBody
  let mut proof := first.proofBody
  for h : i in [1:bodies.size] do
    let next := bodies[i]
    set ← iExpr.iType.mkRefine refiner set next.inclusionBody
    proof ← mkAppM ``Refine.mem_refine #[proof, next.proofBody]
  return ⟨set, proof⟩

/-- Given an `output : IExpr` and a `body : ExprInclusionBody`, construct an `ExprInclusion` for
`output.expr` by collecting inclusion hypotheses from the local context and closing the body. -/
def mkExprInclusion (output : IExpr) (body : ExprInclusionBody) : HypothesisM ExprInclusion := do
  collectHyps
  let context ← read
  let state ← get
  let coarsen? ← match context.iVars.any (·.cover?.isSome) with
    | true => some <$> output.iType.synthCoarsen
    | false => pure none
  let body ← context.iVars.foldrM (init := body) fun iVar body => do
    let hypBody ← combineHypBodies iVar.iExpr (state.inclusions[iVar.expr]?.getD #[])
    let inclusion ← mkLambdaFVars #[iVar.setVar] body.inclusionBody
      (binderInfoForMVars := .default)
    let proof ← mkLambdaFVars #[iVar.setVar, iVar.hypVar] body.proofBody
      (binderInfoForMVars := .default)
    match iVar.cover? with
    | none =>
      let inclusionBody := mkApp inclusion hypBody.inclusionBody
      let proofBody := mkAppN proof #[hypBody.inclusionBody, hypBody.proofBody]
      return { inclusionBody, proofBody }
    | some cover =>
      let coarsen := coarsen?.get!
      let inclusionBody ← iVar.mkCoverMap output.iType hypBody.inclusionBody cover coarsen inclusion
      let proofBody ← iVar.mkCoverMapProof output hypBody cover coarsen inclusion proof
      return { inclusionBody, proofBody }
  return ⟨body.inclusionBody, body.proofBody⟩

/-- Construct an `ExprInclusion` for `e`. -/
def toExprInclusion (e : Expr) : InclusionM ExprInclusion := do
  let body ← mkExprInclusionBody e
  let iType ← body.inferIType e
  HypothesisM.run <| mkExprInclusion ⟨iType, e⟩ body

end

end Inclusion
