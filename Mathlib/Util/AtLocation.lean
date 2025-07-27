/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
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
variable (m : Expr → MetaM Simp.Result)

/-- Use the procedure `m` to rewrite the main goal. -/
def atTarget (proc : String) (failIfUnchanged : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let r ← m tgt
  if r.expr.consumeMData.isConstOf ``True then
    goal.assign (← mkOfEqTrue (← r.getProof))
    replaceMainGoal []
  else
    let newGoal ← applySimpResultToTarget goal tgt r
    if failIfUnchanged && goal == newGoal then
      throwError "{proc} made no progress"
    replaceMainGoal [newGoal]

/-- Use the procedure `m` to rewrite hypothesis `h`. -/
def atLocalDecl (proc : String) (failIfUnchanged : Bool) (mayCloseGoal : Bool) (fvarId : FVarId) :
    TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← fvarId.getType)
  let goal ← getMainGoal
  let myres ← m tgt
  match ← applySimpResultToLocalDecl goal fvarId myres mayCloseGoal with
  | none => replaceMainGoal []
  | some (_, newGoal) =>
    if failIfUnchanged && goal == newGoal then
      throwError "{proc} made no progress"
    replaceMainGoal [newGoal]

/-- Use the procedure `m` to rewrite at specified locations. -/
def atLocation (proc : String) (failIfUnchanged : Bool := true)
    (mayCloseGoalFromHyp : Bool := false) (loc : Location) : TacticM Unit :=
  withLocation loc (atLocalDecl m proc failIfUnchanged mayCloseGoalFromHyp)
    (atTarget m proc failIfUnchanged)
    fun _ ↦ throwError "{proc} made no progress"

end Mathlib.Tactic
