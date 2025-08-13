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

namespace Mathlib.Tactic
open Lean Meta Elab.Tactic

/-- A metaprogram whose input is an expression `e` and whose output is a new expression `e'`,
together with a proof that `e = e'`.

The metaprogram may optionally depend on `ctx`, a `Simp.Context`; if it does, then when the
metaprogram is run on a local hypothesis `h`, the context `ctx` will be modified to forget `h`. -/
inductive SimprocLike
  /-- Default case: a metaprogram which does not depend on a `Simp.Context`. -/
  | noContext (m : Expr → MetaM Simp.Result)
  /-- A metaprogram which depends on a `Simp.Context`. In this case we must also provide the
  `Simp.Context` to use it with; this will be modified at each hypothesis `h` to forget `h`. -/
  | withContext (ctx : Simp.Context) (m : Simp.Context → Expr → MetaM Simp.Result)

variable (m : SimprocLike)

/-- Use the procedure `m` to rewrite the provided goal. -/
def atTarget (proc : String) (failIfUnchanged : Bool) (goal : MVarId) : MetaM (Option MVarId) := do
  let tgt ← instantiateMVars (← goal.getType)
  let m := match m with
  | .noContext m => m
  | .withContext ctx m => m ctx
  let r ← m tgt
  -- we use expression equality here (rather than defeq) to be consistent with, e.g.,
  -- `applySimpResultToTarget`
  let unchanged := tgt.consumeMData == r.expr.consumeMData
  if failIfUnchanged && unchanged then throwError "{proc} made no progress on goal"
  if r.expr.consumeMData.isConstOf ``True then
    goal.assign (← mkOfEqTrue (← r.getProof))
    pure none
  else
    -- this ensures that we really get the same goal as an `MVarId`,
    -- not a different `MVarId` for which `MVarId.getType` is the same
    if unchanged then return goal
    applySimpResultToTarget goal tgt r

/-- Use the procedure `m` to rewrite hypothesis `fvarId`. -/
def atLocalDecl (proc : String) (failIfUnchanged : Bool) (mayCloseGoal : Bool) (fvarId : FVarId)
    (goal : MVarId) :
    MetaM (Option MVarId) := do
  let ldecl ← fvarId.getDecl
  if ldecl.isImplementationDetail then
    throwError "cannot run {proc} at {ldecl.userName}, it is an implementation detail"
  let tgt ← instantiateMVars (← fvarId.getType)
  let m := match m with
  | .noContext m => m
  | .withContext ctx m => m <| ctx.setSimpTheorems <| ctx.simpTheorems.eraseTheorem (.fvar fvarId)
  let myres ← m tgt
  -- we use expression equality here (rather than defeq) to be consistent with, e.g.,
  -- `applySimpResultToLocalDeclCore`
  if failIfUnchanged && tgt.consumeMData == myres.expr.consumeMData then
    throwError "{proc} made no progress at {ldecl.userName}"
  return (← applySimpResultToLocalDecl goal fvarId myres mayCloseGoal).map Prod.snd

/-- Use the procedure `m` to rewrite at specified locations. -/
def atLocation (proc : String) (loc : Location) (failIfUnchanged : Bool := true)
    (mayCloseGoalFromHyp : Bool := false) :
    TacticM Unit :=
  withLocation loc (liftMetaTactic1 ∘ atLocalDecl m proc failIfUnchanged mayCloseGoalFromHyp)
    (liftMetaTactic1 <| atTarget m proc failIfUnchanged)
    fun _ ↦ throwError "{proc} made no progress anywhere"

end Mathlib.Tactic
