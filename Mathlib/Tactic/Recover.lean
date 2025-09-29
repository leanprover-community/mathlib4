/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Siddhartha Gadgil, Jannis Limperg
-/
import Mathlib.Init

/-!
# The `recover` tactic modifier

This defines the `recover` tactic modifier, which can be used to debug cases where goals
are not closed correctly. `recover tacs` for a tactic (or tactic sequence) `tacs`
applies the tactics and then adds goals
that are not closed, starting from the original goal.
-/

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

/--
Get all metavariables which `mvarId` depends on. These are the metavariables
which occur in the target or local context or delayed assignment (if any) of
`mvarId`, plus the metavariables which occur in these metavariables, etc.
-/
partial def getUnassignedGoalMVarDependencies (mvarId : MVarId) :
    MetaM (Std.HashSet MVarId) :=
  return (← go mvarId |>.run {}).snd
where
    /-- auxiliary function for `getUnassignedGoalMVarDependencies` -/
    addMVars (e : Expr) : StateRefT (Std.HashSet MVarId) MetaM Unit := do
      let mvars ← getMVars e
      let mut s ← get
      set ({} : Std.HashSet MVarId) -- Ensure that `s` is not shared.
      for mvarId in mvars do
        unless ← mvarId.isDelayedAssigned do
          s := s.insert mvarId
      set s
      mvars.forM go
    /-- auxiliary function for `getUnassignedGoalMVarDependencies` -/
    go (mvarId : MVarId) : StateRefT (Std.HashSet MVarId) MetaM Unit :=
      withIncRecDepth do
        let mdecl ← mvarId.getDecl
        addMVars mdecl.type
        for ldecl in mdecl.lctx do
          addMVars ldecl.type
          if let (some val) := ldecl.value? then
            addMVars val
        if let (some ass) ← getDelayedMVarAssignment? mvarId then
          let pendingMVarId := ass.mvarIdPending
          unless ← pendingMVarId.isAssigned <||> pendingMVarId.isDelayedAssigned do
            modify (·.insert pendingMVarId)
          go pendingMVarId

/-- Modifier `recover` for a tactic (sequence) to debug cases where goals are closed incorrectly.
The tactic `recover tacs` for a tactic (sequence) `tacs` applies the tactics and then adds goals
that are not closed, starting from the original goal. -/
elab "recover " tacs:tacticSeq : tactic => do
  let originalGoals ← getGoals
  evalTactic tacs
  let mut unassigned : Std.HashSet MVarId := {}
  for mvarId in originalGoals do
    unless ← mvarId.isAssigned <||> mvarId.isDelayedAssigned do
      unassigned := unassigned.insert mvarId
    let unassignedMVarDependencies ← getUnassignedGoalMVarDependencies mvarId
    unassigned := unassigned.insertMany unassignedMVarDependencies.toList
  setGoals <| ((← getGoals) ++ unassigned.toList).eraseDups

end Mathlib.Tactic
