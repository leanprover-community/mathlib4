/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Siddhartha Gadgil, Jannis Limperg
-/
import Lean
import Std.Tactic.RCases
import Mathlib.Tactic.Cache

open Lean (HashSet)
open Lean Meta Elab Tactic

namespace Lean.HashSet

/-- Insert many elements into a HashSet. -/
-- This has a primed name to avoid the collision
-- with the same function imported via `Aesop.Util.Basic`.
-- Once it is upstreamed to `Std` or `Core` this should be removed.
def insertMany' [ForIn Id ρ α] [BEq α] [Hashable α] (s : HashSet α) (as : ρ) :
    HashSet α := Id.run do
  let mut s := s
  for a in as do
    s := s.insert a
  return s

end Lean.HashSet

namespace Mathlib.Tactic

/--
Get all metavariables which `mvarId` depends on. These are the metavariables
which occur in the target or local context or delayed assignment (if any) of
`mvarId`, plus the metvariables which occur in these metavariables, etc.
-/
partial def getUnassignedGoalMVarDependencies (mvarId : MVarId) :
    MetaM (HashSet MVarId) :=
  return (← go mvarId |>.run {}).snd
  where
    /-- auxiliary function for `getUnassignedGoalMVarDependencies` -/
    addMVars (e : Expr) : StateRefT (HashSet MVarId) MetaM Unit := do
      let mvars ← getMVars e
      let mut s ← get
      set ({} : HashSet MVarId) -- Ensure that `s` is not shared.
      for mvarId in mvars do
        unless ← mvarId.isDelayedAssigned do
          s := s.insert mvarId
      set s
      mvars.forM go
    /-- auxiliary function for `getUnassignedGoalMVarDependencies` -/
    go (mvarId : MVarId) : StateRefT (HashSet MVarId) MetaM Unit :=
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
The tactic `recover tacs` for a tactic (sequence) tacs applies the tactics and then adds goals
that are not closed starting from the original -/
elab "recover" tacs:tacticSeq : tactic => do
  let originalGoals ← getGoals
  evalTactic tacs
  let mut unassigned : HashSet MVarId := {}
  for mvarId in originalGoals do
    unless ← mvarId.isAssigned <||> mvarId.isDelayedAssigned do
      unassigned := unassigned.insert mvarId
    let unassignedMVarDependencies ← getUnassignedGoalMVarDependencies mvarId
    unassigned := unassigned.insertMany' unassignedMVarDependencies.toList
  setGoals <| ((← getGoals) ++ unassigned.toList).eraseDups
