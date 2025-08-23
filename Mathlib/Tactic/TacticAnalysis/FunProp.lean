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
Define a pass that tries replacing a specific tactic with `fun_prop`.

`tacticKind` is the `SyntaxNodeKind` for the tactic's main parser,
for example `Mathlib.Tactic.linarith`.
-/
def funPropReplacementWith (tacticKind : SyntaxNodeKind) : TacticAnalysis.Config := .ofComplex {
  out := (List MVarId × MessageData)
  ctx := Syntax
  trigger _ stx := if stx.getKind == tacticKind
    then .accept stx else .skip
  test _stx goal := do
    let tac ← `(tactic| fun_prop)
    try
      let (goals, _) ← Lean.Elab.runTactic goal tac
      return (goals, m!"")
    catch _e => -- `fun_prop` throws an error if it fails.
      let name ← mkAuxDeclName `extracted
      let ((sig, _, _), _) ← (Mathlib.Tactic.ExtractGoal.goalSignature name goal).run
      return ([goal], m!"fun_prop did not prove {sig}")
  tell _stx _old new :=
    if new.1.1.isEmpty then m!"'fun_prop' can solve this, and is almost always faster"
    else none }

/-- Suggest replacing the `continuity` tactic (and its `continuity?` variant)
with `fun_prop` if that also solves the goal. -/
register_option linter.tacticAnalysis.continuityToFunProp : Bool := {
  defValue := false
}

-- TODO: can I combine these two linters into one?
@[tacticAnalysis linter.tacticAnalysis.continuityToFunProp,
  inherit_doc linter.tacticAnalysis.continuityToFunProp]
def continuityToFunprop := funPropReplacementWith `tacticContinuity

@[tacticAnalysis linter.tacticAnalysis.continuityToFunProp,
  inherit_doc linter.tacticAnalysis.continuityToFunProp]
def continuityToFunprop2 := funPropReplacementWith `tacticContinuity?

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
def measurabilityToFunprop := funPropReplacementWith `tacticMeasurability

@[tacticAnalysis linter.tacticAnalysis.measurabilityToFunProp,
  inherit_doc linter.tacticAnalysis.measurabilityToFunProp]
def measurabilityToFunprop2 := funPropReplacementWith `tacticMeasurability?

-- These two are stubs, but we might as well lint for them also.
@[tacticAnalysis linter.tacticAnalysis.measurabilityToFunProp,
  inherit_doc linter.tacticAnalysis.measurabilityToFunProp]
def measurabilityToFunprop3 := funPropReplacementWith `measurability!

@[tacticAnalysis linter.tacticAnalysis.measurabilityToFunProp,
  inherit_doc linter.tacticAnalysis.measurabilityToFunProp]
def measurabilityToFunprop4 := funPropReplacementWith `measurability!?
