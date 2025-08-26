/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth
-/
import Mathlib.Init
import Lean.Elab.Tactic.Location
import Lean.Meta.Tactic.Simp.Main

/-!
# Rewriting at specified locations

Many metaprograms have the following general structure: the input is an expression `e` and the
output is a new expression `e'`, together with a proof that `e = e'`.

This file provides convenience functions to turn such a metaprogram into a variety of tactics:
using the metaprogram to modify the goal, a specified hypothesis, or (via `Tactic.Location`) a
combination of these.
-/

/-- Runs the given `atLocal` and `atTarget` methods on each of the locations selected by the given
`loc`.
* If `loc` is a list of locations, runs at each specified hypothesis (and finally the goal if `⊢` is
  included), and fails if any of the tactic applications fail.
* If `loc` is `*`, runs at the nondependent `Prop` hypotheses (those produced by
  `Lean.MVarId.getNondepPropHyps`) and then at the target.

This is a variant of `Lean.Elab.Tactic.withLocation`. -/
def Lean.Elab.Tactic.withNondepPropLocation (loc : Location) (atLocal : FVarId → TacticM Unit)
    (atTarget : TacticM Unit) (failed : MVarId → TacticM Unit) : TacticM Unit := do
  match loc with
  | Location.targets hyps target => do
    (← getFVarIds hyps).forM atLocal
    if target then atTarget
  | Location.wildcard => do
    let mut worked := false
    for hyp in ← (← getMainGoal).getNondepPropHyps do
      worked := worked || (← tryTactic <| atLocal hyp)
    unless worked || (← tryTactic atTarget) do
      failed (← getMainGoal)

namespace Mathlib.Tactic
open Lean Meta Elab.Tactic

/-- Use the procedure `m` to rewrite the provided goal. -/
def transformAtTarget (m : Expr → ReaderT Simp.Context MetaM Simp.Result) (proc : String)
    (failIfUnchanged : Bool) (goal : MVarId) :
    ReaderT Simp.Context MetaM (Option MVarId) := do
  let tgt ← instantiateMVars (← goal.getType)
  let r ← m tgt
  -- we use expression equality here (rather than defeq) to be consistent with, e.g.,
  -- `applySimpResultToTarget`
  let unchanged := tgt.cleanupAnnotations == r.expr.cleanupAnnotations
  if failIfUnchanged && unchanged then throwError "{proc} made no progress on goal"
  if r.expr.isTrue then
    goal.assign (← mkOfEqTrue (← r.getProof))
    pure none
  else
    -- this ensures that we really get the same goal as an `MVarId`,
    -- not a different `MVarId` for which `MVarId.getType` is the same
    if unchanged then return goal
    applySimpResultToTarget goal tgt r

/-- Use the procedure `m` to rewrite hypothesis `fvarId`.

The `simpTheorems` of the simp-context carried with `m` will be modified to remove `fvarId`;
this ensures that if the procedure `m` involves rewriting by this `SimpTheoremsArray`, then, e.g.,
`h : x = y` is not transformed (by rewriting `h`) to `True`. -/
def transformAtLocalDecl (m : Expr → ReaderT Simp.Context MetaM Simp.Result) (proc : String)
    (failIfUnchanged : Bool) (mayCloseGoal : Bool) (fvarId : FVarId) (goal : MVarId) :
    ReaderT Simp.Context MetaM (Option MVarId) := do
  let ldecl ← fvarId.getDecl
  if ldecl.isImplementationDetail then
    throwError "cannot run {proc} at {ldecl.userName}, it is an implementation detail"
  let tgt ← instantiateMVars (← fvarId.getType)
  let eraseFVarId (ctx : Simp.Context) :=
    ctx.setSimpTheorems <| ctx.simpTheorems.eraseTheorem (.fvar fvarId)
  let r ← withReader eraseFVarId <| m tgt
  -- we use expression equality here (rather than defeq) to be consistent with, e.g.,
  -- `applySimpResultToLocalDeclCore`
  if failIfUnchanged && tgt.cleanupAnnotations == r.expr.cleanupAnnotations then
    throwError "{proc} made no progress at {ldecl.userName}"
  return (← applySimpResultToLocalDecl goal fvarId r mayCloseGoal).map Prod.snd

/-- Use the procedure `m` to transform at specified locations (hypotheses and/or goal). -/
def transformAtLocation (m : Expr → ReaderT Simp.Context MetaM Simp.Result) (proc : String)
    (loc : Location) (failIfUnchanged : Bool := true) (mayCloseGoalFromHyp : Bool := false)
    -- streamline the most common use case, in which the procedure `m`'s implementation is not
    -- simp-based and its `Simp.Context` is ignored
    (ctx : Simp.Context := default) :
    TacticM Unit :=
  withLocation loc
    (liftMetaTactic1 ∘ (transformAtLocalDecl m proc failIfUnchanged mayCloseGoalFromHyp · · ctx))
    (liftMetaTactic1 (transformAtTarget m proc failIfUnchanged · ctx))
    fun _ ↦ throwError "{proc} made no progress anywhere"

/-- Use the procedure `m` to transform at specified locations (hypotheses and/or goal).

In the wildcard case (`*`), filter out all dependent and/or non-Prop hypotheses. -/
def transformAtNondepPropLocation (m : Expr → ReaderT Simp.Context MetaM Simp.Result)
    (proc : String) (loc : Location) (failIfUnchanged : Bool := true)
    (mayCloseGoalFromHyp : Bool := false)
    -- streamline the most common use case, in which the procedure `m`'s implementation is not
    -- simp-based and its `Simp.Context` is ignored
    (ctx : Simp.Context := default) :
    TacticM Unit :=
  withNondepPropLocation loc
    (liftMetaTactic1 ∘ (transformAtLocalDecl m proc failIfUnchanged mayCloseGoalFromHyp · · ctx))
    (liftMetaTactic1 (transformAtTarget m proc failIfUnchanged · ctx))
    fun _ ↦ throwError "{proc} made no progress anywhere"

end Mathlib.Tactic
