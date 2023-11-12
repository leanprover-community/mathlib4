/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer
-/
import Mathlib.Tactic.Core
import Lean.LabelAttribute
import Mathlib.Tactic.GCongr

open Lean Meta

namespace Mathlib.Tactic.GRW

initialize registerTraceClass `GRW

open Lean in
initialize ext : LabelExtension ← (
  let descr := "A lemma describing how to convert the first argument into the target type, possibly
introducing side goals. These side goals will be solved with `gcongr`"
  let grw := `grw
  registerLabelAttr grw descr grw)

open Lean in
initialize extWeaken : LabelExtension ← (
  let descr := "A lemma that goes from a strict relation to a non strict one."
  let grw_weaken := `grw_weaken
  registerLabelAttr grw_weaken descr grw_weaken)


open GCongr

private partial def getNeedleReplacement (relation_type : Expr) : MetaM (Expr × Expr) := do
  let ⟨_, args⟩ := relation_type.getAppFnArgs
  if args.size < 2 then
    throwError "Expecting relation but got {relation_type}"

  return ⟨args[args.size - 2]!, args[args.size - 1]!⟩

private partial def getNewType (rule : Expr) (rev : Bool) (oldType : Expr) : MetaM Expr := do
  let ruleType ← instantiateMVars (← inferType rule)
  let ⟨needle, replacement⟩ := ← if rev then do
    return (← getNeedleReplacement ruleType).swap
  else
    getNeedleReplacement ruleType
  trace[GRW] "Got needle = {needle} replacement = {replacement}"
  let abst ← kabstract oldType needle
  if !abst.hasLooseBVars then
    throwError "Could not find pattern {needle} in {oldType}"
  let newType := abst.instantiate1 replacement
  trace[GRW] "old type {oldType} new type {newType}"
  return newType


private partial def assignAndValidate (mvar : MVarId) (expr: Expr) : MetaM Unit := do
  if ←isDefEq expr (Expr.mvar mvar) then
    return ⟨⟩
  else
    throwError "Could not assign {expr} to {mvar}"

-- TODO make this extensible
private partial def dischargeSideGoal (rule : Expr) (mvar : MVarId) : MetaM Unit := do
  trace[GRW] "Discharging side goal {mvar}"
  try do
    mvar.assumption
    return
  catch ex =>
  try do
    Mathlib.Meta.Positivity.positivity mvar
    return
  catch ex =>
  return ⟨⟩

private partial def dischargeMainGoal (rule : Expr) (mvar : MVarId) : MetaM Unit := do
  trace[GRW] "Discharging main goal {mvar}"
  try do
    commitIfNoEx mvar.applyRfl
    trace[GRW] "used reflexivity"
    return
  catch ex =>
  try do
    commitIfNoEx <| assignAndValidate mvar rule
    trace[GRW] "used rule {rule}"
    return
  catch ex =>

  throwError "Could not discharge main goal"

private partial def useRule (rule : Expr) (mvar : MVarId) : MetaM Unit := do
  let ⟨progress, names, subgoals⟩ ← mvar.gcongr
    none
    []
    (sideGoalDischarger := dischargeSideGoal rule)
    (mainGoalDischarger := dischargeMainGoal rule)

  trace[GRW] "Got results {progress} {names} {subgoals}"

  if !progress then
    throwError "gcongr could not make progress on {mvar}"
  if !subgoals.isEmpty then
    throwError "gcongr left subgoals {subgoals}"
  trace[GRW] "Got proof {← instantiateMVars (Expr.mvar mvar)}"

private def weaken (rule : Expr) : MetaM Expr := do
  let lemmas ← labelled `grw_weaken

  for lem in lemmas do
    let s ← saveState
    try do
      let result ← mkAppM lem #[rule]
      trace[GRW] "weakened to {← inferType result}"
      return result
    catch ex =>
      s.restore

  return rule

partial def runGrw (expr rule : Expr) (rev isTarget : Bool)
    : MetaM (Expr × Expr × MVarId) := do
  let oldType ← instantiateMVars (← inferType expr)
  let ⟨ruleArgs, _, _⟩ ← forallMetaTelescope (← inferType rule)
  let metaRule := mkAppN rule ruleArgs
  let newType ← getNewType metaRule rev oldType
  let weakRule ← weaken metaRule
  let lemmas ← labelled `grw

  let result ← mkFreshExprMVar newType

  let prf ← withNewMCtxDepth do
    -- todo surely this can be faster
    for lem in lemmas do
      trace[GRW] "trying lemma {lem}"
      let s ← saveState
      try do
        let lemExpr ← mkConstWithFreshMVarLevels lem
        let lemType ← inferType lemExpr
        let ⟨metas, binders, body⟩ ← forallMetaTelescopeReducing lemType
        let mvarToAssign := if isTarget then expr.mvarId! else result.mvarId!
        assignAndValidate mvarToAssign (mkAppN lemExpr metas)

        let firstDefaultArg := binders.findIdx? (λ x ↦ x == .default)
        if let some firstDefaultArg := firstDefaultArg then do
          let valueToAssign := if isTarget then result else expr
          assignAndValidate metas[firstDefaultArg]!.mvarId! valueToAssign
        else
          throwError "Lemma {lem} did not have a default argument"

        trace[GRW] "Lemma {lem} matches, trying to fill args"

        for arg in metas do
          let mvar := arg.mvarId!
          let type ← instantiateMVars (← inferType arg)
          if ← mvar.isAssigned then
            trace[GRW] "mvar already assigned to {← instantiateMVars arg} : {type}"
            continue
          trace[GRW] "Looking for value of type {type}"
          useRule weakRule mvar

        return ← instantiateMVars <| mkAppN lemExpr metas
      catch ex => do
        trace[GRW] "error in lemma {ex.toMessageData}"
        s.restore
    throwError "No grw lemmas worked"
  trace[GRW] "Got proof {prf}"

  return ⟨newType, prf, result.mvarId!⟩
