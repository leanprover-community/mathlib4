/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Tactic.TacticAnalysis
import Mathlib.Tactic.ExtractGoal
import Mathlib.Tactic.FunProp

/-!
# Tactic linters

This file defines passes to run from the tactic analysis framework.
-/

open Lean Mathlib

/--
Define a pass that tries replacing a list of tactics with one better tactic.
* `new` is the `TSyntax` of the tactic itself, such as ``(tactic| fun_prop)`.
  We assume that `new` takes no custom arguments.
* `oldTacticKinds` describes the tactics that are subsumed by `new`:
  is an array of `SyntaxNodeKind`s for the tactics' main parsers
  (such as `Mathlib.Tactic.linarith`).
  Providing several kinds can be useful to cover all variants of one particular tactic in one go.
* `newName` is how the new tactic should be printed in a failure message
* `msg_pass` is the message shown to the user when the new replacement works.
-/
def tacticReplacementWith (oldTacticKinds : Array SyntaxNodeKind) (new : MetaM (TSyntax `tactic))
    (newName : MessageData) (msg_success : MessageData) : TacticAnalysis.Config :=.ofComplex {
  out := (List MVarId × MessageData)
  ctx := Syntax
  trigger _ stx := if oldTacticKinds.contains stx.getKind
    then .accept stx else .skip
  test _stx goal := do
    try
      let (goals, _) ← Lean.Elab.runTactic goal (← new)
      return (goals, m!"")
    catch _e =>
      let name ← mkAuxDeclName `extracted
      let ((sig, _, _), _) ← (Mathlib.Tactic.ExtractGoal.goalSignature name goal).run
      return ([goal], m!"{newName} did not prove {sig}")
  tell _stx _old new :=
    if new.1.1.isEmpty then msg_success
    else none }

/--
Define a pass that tries replacing a specific tactic with `fun_prop`.

`tacticKind` is an array of `SyntaxNodeKind` for the tactic's main parsers,
for example `Mathlib.Tactic.linarith`.
This can be useful to cover all variants of one particular tactic.
-/
def funPropReplacementWith (tacticKinds : Array SyntaxNodeKind) :
    TacticAnalysis.Config :=
  tacticReplacementWith tacticKinds (`(tactic| fun_prop)) m!"fun_prop"
    m!"'fun_prop' can solve this, and is almost always faster"

/-- Suggest replacing the `continuity` tactic (and its `continuity?` variant)
with `fun_prop` if that also solves the goal. -/
register_option linter.tacticAnalysis.continuityToFunProp : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.continuityToFunProp,
  inherit_doc linter.tacticAnalysis.continuityToFunProp]
def continuityToFunprop := funPropReplacementWith #[`tacticContinuity, `tacticContinuity?]

/-- Suggest replacing the `measurability` tactic (and its variant `measurability?`, as well as the
currently unimplemented stubs `measurability!` and `measurability!?`) with `fun_prop`
if that also solves the goal.
`fun_prop` does not solve `MeasurableSet` goals, and not all measurability goals --- but when it
works, it is usually faster (and sometimes a lot faster).-/
register_option linter.tacticAnalysis.measurabilityToFunProp : Bool := {
  defValue := false
}

@[tacticAnalysis linter.tacticAnalysis.measurabilityToFunProp,
  inherit_doc linter.tacticAnalysis.measurabilityToFunProp]
def measurabilityToFunprop := funPropReplacementWith
  #[`tacticMeasurability, `tacticMeasurability?,
  -- These two are stubs, but we might as well lint for them also.
  `measurability!, `measurability!?]
