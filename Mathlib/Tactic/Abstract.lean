/-
Copyright (c) 2025 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sven Manthe
-/
import Mathlib.Init
import Lean.Elab.Tactic.Simp

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
    throwError "Abstract failed. The current goal is not propositional."
  let goal ← getMainGoal
  let newGoal ← mkFreshExprMVar target
  setGoals [newGoal.mvarId!]
  evalTactic tacs
  setGoals [goal]
  let auxName := (← getDeclName?).get! ++ `abstract ++ (← mkFreshId)
  goal.assign <| ← mkAuxTheorem auxName target newGoal
