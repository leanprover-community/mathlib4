/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Lean
import Mathlib.Tactic.Cache
import Mathlib.Tactic.RCases
import Std

open Std (HashSet PHashSet)
open Lean Meta Elab Tactic

/- The code below (up to the tactic) is from Aesop due to Janis Limperg-/
namespace Mathlib.Tactic

namespace Std.HashSet

/-- insert many elements in a HashSet (from Aesop) -/
def insertMany [ForIn Id ρ α] [BEq α] [Hashable α] (s : HashSet α) (as : ρ) :
    HashSet α := Id.run do
  let mut s := s
  for a in as do
    s := s.insert a
  return s

end Std.HashSet

/-- instantiating MVars in goal (from Aesop) -/
def instantiateMVarsInGoal (mvarId : MVarId) : MetaM Unit := do
  discard $ getMVarDecl mvarId
    -- The line above throws an error if the `mvarId` is not declared. The line
    -- below panics.
  instantiateMVarDeclMVars mvarId

/-- Returns unassigned metavariable dependencies (from Aesop) -/
partial def getUnassignedGoalMVarDependencies (mvarId : MVarId) :
    MetaM (HashSet MVarId) :=
  return (← go mvarId |>.run {}).snd
  where
    /-- helper for adding metavariables -/
    addMVars (e : Expr) : StateRefT (HashSet MVarId) MetaM Unit := do
      let mvars ← getMVarsNoDelayed e
      modify (fun s => Std.HashSet.insertMany s mvars)
      mvars.forM go
    /-- main loop for metavariables-/
    go (mvarId : MVarId) : StateRefT (HashSet MVarId) MetaM Unit :=
      withIncRecDepth do
        instantiateMVarsInGoal mvarId
        let mdecl ← getMVarDecl mvarId
        addMVars mdecl.type
        for ldecl in mdecl.lctx do
          addMVars ldecl.type
          if let (some val) := ldecl.value? then
            addMVars val

/- Above code from Aesop -/

/-- Modifier `recover` for a tactic (sequence) to debug cases where goals are closed incorrectly. The tactic `recover tacs` for a tactic (sequence) tacs applies the tactics and then adds goals that are not closed starting from the original -/
elab "recover" tacs:tacticSeq : tactic => do
  let originalGoals ← getGoals
  evalTactic tacs
  let mut unassigned : HashSet MVarId := {}
  for mvarId in originalGoals do
    unless ← isExprMVarAssigned mvarId do
      unassigned := unassigned.insert mvarId
    let unassignedMVarDependencies ←
        getUnassignedGoalMVarDependencies mvarId
    unassigned :=
        Std.HashSet.insertMany
            unassigned unassignedMVarDependencies.toList
  setGoals <| (← getGoals) ++ unassigned.toList
