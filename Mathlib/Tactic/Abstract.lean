/-
Copyright (c) 2025 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sven Manthe, Jovan Gerbscheid
-/
import Mathlib.Init
import Lean.Meta.Closure

/-! # The `abstract` tactic -/

open Lean Meta Elab Tactic Term

/--
Usage: `abstract <tacticSeq>`.

The abstract tactic executes the provided tactic sequence, and "hides" its proof behind a new
auxiliary lemma. This is mostly useful to hide long proofs in the statement of a theorem, since
certain tactics can be slow if the goal contains a large proof as subterm.
-/
elab "abstract" tacs:ppDedent(tacticSeq) : tactic => do
  if (← getGoals).length ≠ 1 then
    throwError "Abstract failed. There are {(← getGoals).length} goals. Expected exactly 1 goal."
  let target ← getMainTarget
  if !(← isProp target) then
    throwError "Abstract failed. The current goal is not a proposition."
  let goal ← getMainGoal
  let newGoal ← mkFreshExprMVar target
  setGoals [newGoal.mvarId!]
  evalTactic tacs
  if !(← getGoals).isEmpty then
    throwError m! "Abstract failed. There are unsolved goals\n{goalsToMessageData (← getGoals)}"
  let newGoal ← instantiateMVars newGoal
  -- `mkAuxTheorem` works when there are universe metavariables,
  -- so we only check for expression metavariabes.
  if newGoal.hasExprMVar then
    throwError m! "Abstract failed. The term contains metavariables {indentExpr newGoal}"
  let auxName ← mkAuxName ((← getDeclName?).getD .anonymous ++ `abstract) 1
  goal.assign <| ← mkAuxTheorem auxName target newGoal
