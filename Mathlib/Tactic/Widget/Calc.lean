/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import Std.CodeAction

import Mathlib.Data.String.Defs
import Mathlib.Tactic.Widget.SelectPanelUtils

/-! # Calc widget

This file redefines the `calc` tactic so that is displays a widget panel allowing to create
new calc steps with holes specified by selected sub-expressions in the goal.
-/

section code_action
open Std CodeAction
open Lean Server RequestM

/-- Code action to create a `calc` tactic from the current goal. -/
@[tactic_code_action calcTactic]
def createCalc : TacticCodeAction := fun params _snap ctx _stack node => do
  let .node (.ofTacticInfo info) _ := node | return #[]
  if info.goalsBefore.isEmpty then return #[]
  let eager := {
    title := s!"Generate a calc block."
    kind? := "quickfix"
  }
  let doc ← readDoc
  return #[{
    eager
    lazy? := some do
      let tacPos := doc.meta.text.utf8PosToLspPos info.stx.getPos?.get!
      let endPos := doc.meta.text.utf8PosToLspPos info.stx.getTailPos?.get!
      let goal := info.goalsBefore[0]!
      let goalFmt ← ctx.runMetaM {} <| goal.withContext do Meta.ppExpr (← goal.getType)
      return { eager with
        edit? := some <|.ofTextEdit params.textDocument.uri
          { range := ⟨tacPos, endPos⟩, newText := s!"calc {goalFmt} := by sorry" }
      }
  }]
end code_action

open ProofWidgets
open Lean Meta

open Lean Server in

/-- Parameters for the calc widget. -/
structure CalcParams extends SelectInsertParams where
  /-- If this the first calc step? -/
  isFirst : Bool
  /-- indentation level of the calc block. -/
  indent : Nat
  deriving SelectInsertParamsClass, RpcEncodable

open Lean Meta

/-- A string representation for equality and inequalities.  -/
def Lean.Expr.relStr : Expr → String
| .const ``Eq _ => "="
| .const ``LE.le _ => "≤"
| .const ``LT.lt _ => "<"
| .const ``GE.ge _ => "≥"
| .const ``GT.gt _ => ">"
| _ => "Unknow relation"

/-- Return the link text and inserted text above and below of the calc widget. -/
def suggestSteps (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) (params : CalcParams) :
    MetaM (String × String) := do
  let subexprPos := getGoalLocations pos
  let some (rel, lhs, rhs) ← Lean.Elab.Term.getCalcRelation? goalType |
      throwError "invalid 'calc' step, relation expected{indentExpr goalType}"
  let relStr := rel.getAppFn.relStr
  let selectedLeft := subexprPos.filter (fun L ↦ #[0, 1].isPrefixOf L.toArray)
  let selectedRight := subexprPos.filter (fun L ↦ #[1].isPrefixOf L.toArray)

  let mut goalTypeWithMetaVarsLeft := goalType
  for pos in selectedLeft do
    goalTypeWithMetaVarsLeft ← insertMetaVar goalTypeWithMetaVarsLeft pos
  let some (_, newLhs, _) ← Lean.Elab.Term.getCalcRelation? goalTypeWithMetaVarsLeft | unreachable!
  let mut goalTypeWithMetaVarsRight := goalType
  for pos in selectedRight do
    goalTypeWithMetaVarsRight ← insertMetaVar goalTypeWithMetaVarsRight pos
  let some (_, _, newRhs) ← Lean.Elab.Term.getCalcRelation? goalTypeWithMetaVarsRight | unreachable!

  let lhsStr := (toString <| ← Meta.ppExpr lhs).renameMetaVar
  let newLhsStr := (toString <| ← Meta.ppExpr newLhs).renameMetaVar
  let rhsStr := (toString <| ← Meta.ppExpr rhs).renameMetaVar
  let newRhsStr := (toString <| ← Meta.ppExpr newRhs).renameMetaVar

  let spc := String.replicate params.indent ' '
  let insertedCode := match selectedLeft.isEmpty, selectedRight.isEmpty with
  | false, false =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {newRhsStr} := by sorry\n" ++
      s!"{spc}_ {relStr} {rhsStr} := by sorry"
    else
      s!"{spc}_ {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {newRhsStr} := by sorry\n" ++
      s!"{spc}_ {relStr} {rhsStr} := by sorry"
  | true, false  =>
  if params.isFirst then
      s!"{lhsStr} {relStr} {newRhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
    else
      s!"{spc}_ {relStr} {newRhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
  | false, true =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
    else
      s!"{spc}_ {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
  | true, true => "This should not happen"

  let stepInfo := match selectedLeft.isEmpty, selectedRight.isEmpty with
  | false, false => "Create two new steps"
  | true, false  => "Create a new step"
  | false, true => "Create a new step"
  | true, true => "This should not happen"
  return (stepInfo, toString insertedCode)

/-- Rpc function for the calc widget. -/
@[server_rpc_method]
def CalcPanel.rpc := mkSelectionPanelRPC suggestSteps
  "Please select subterms."
  "Calc 🔍"

/-- The calc widget. -/
@[widget_module]
def CalcPanel : Component CalcParams :=
  mk_rpc_widget% CalcPanel.rpc

namespace Lean.Elab.Term
open Meta

/-- Extract the first step of a calc block. This is a tiny improvement over
`getCalcFirstStep` from core. -/
def getCalcFirstStep' (step0 : TSyntax ``calcFirstStep) : TermElabM (TSyntax ``calcStep) :=
  withRef step0 do
  match step0  with
  | `(calcFirstStep| $term:term) =>
    `(calcStep| $term = _ := rfl)
  | `(calcFirstStep| $term := $proof) =>
    `(calcStep| $term := $proof)
  | _ => throwUnsupportedSyntax

/-- Extract calc steps. This is the same as `getCalcSteps` from core except it uses
the improved `getCalcFirstStep'`.

Beware this should be updated to track core once Mathlib gets
https://github.com/leanprover/lean4/commit/3e755dc0e199b40367a8ec9a592a343108a71c5a
(unless `getCalcFirstStep'` reaches core in between, in which both `getCalcFirstStep'` and
`getCalcSteps'` will become erasable).
-/
def getCalcSteps' (steps : TSyntax ``calcSteps) : TermElabM (Array (TSyntax ``calcStep)) :=
  match steps with
  | `(calcSteps| $step0:calcFirstStep $rest*) => do
    let step0 ← getCalcFirstStep' step0
    pure (#[step0] ++ rest)
  | _ => unreachable!

/- Elaborator for calc steps. Compared to `elabCalcSteps` from core, this inserts a
calc widget for each proof.  -/
def elabCalcStepsWithWidgets (indent : Nat) (steps : TSyntax ``calcSteps) : TermElabM Expr := do
  let mut result? := none
  let mut prevRhs? := none
  let mut isFirst := true
  for step in ← getCalcSteps' steps do

    let `(calcStep| $pred := $proofTerm) := step | unreachable!
    let type ← elabType <| ← do
      if let some prevRhs := prevRhs? then
        annotateFirstHoleWithType pred (← inferType prevRhs)
      else
        pure pred
    let some (_, lhs, rhs) ← getCalcRelation? type |
      throwErrorAt pred "invalid 'calc' step, relation expected{indentExpr type}"

    let some replaceRange := (← getFileMap).rangeOfStx? step | unreachable!
    let json := open scoped ProofWidgets.Json in json% {"replaceRange": $(replaceRange),
                                                        "isFirst": $(isFirst),
                                                        "indent": $(indent)}
    ProofWidgets.savePanelWidgetInfo proofTerm `CalcPanel (pure json)
    isFirst := false

    if let some prevRhs := prevRhs? then
      unless (← isDefEqGuarded lhs prevRhs) do
        let L := indentD m!"{lhs} : {← inferType lhs}"
        let R := indentD m!"{prevRhs} : {← inferType prevRhs}"
        throwErrorAt pred "invalid calc step, left-hand-side is{L}\nprevious right-hand-side is{R}"
    let proof ← withFreshMacroScope do elabTermEnsuringType proofTerm type
    result? := some <| ← do
      if let some (result, resultType) := result? then
        synthesizeSyntheticMVarsUsingDefault
        withRef pred do mkCalcTrans result resultType proof type
      else
        pure (proof, type)
    prevRhs? := rhs
  return result?.get!.1
end Lean.Elab.Term


namespace Lean.Elab.Tactic
open Meta

/-- Elaborator for the `calc` tactic mode variant with widgets. -/
elab_rules : tactic
| `(tactic|calc%$calcstx $stx) => withMainContext do
  let steps : TSyntax ``calcSteps := ⟨stx⟩
  let (val, mvarIds) ← withCollectingNewGoalsFrom (tagSuffix := `calc) do
    let target ← getMainTarget
    let tag ← getMainTag
    let some calcRange := (← getFileMap).rangeOfStx? calcstx | unreachable!
    let indent := calcRange.start.character
    dbg_trace indent
    runTermElab do
    let mut val ← Term.elabCalcStepsWithWidgets indent steps
    let mut valType ← inferType val
    unless (← isDefEq valType target) do
      let rec throwFailed :=
        throwError "'calc' tactic failed, has type{indentExpr valType}\n
          but it is expected to have type{indentExpr target}"
      let some (_, _, rhs) ← Term.getCalcRelation? valType | throwFailed
      let some (r, _, rhs') ← Term.getCalcRelation? target | throwFailed
      let lastStep := mkApp2 r rhs rhs'
      let lastStepGoal ← mkFreshExprSyntheticOpaqueMVar lastStep (tag := tag ++ `calc.step)
      (val, valType) ← Term.mkCalcTrans val valType lastStepGoal lastStep
      unless (← isDefEq valType target) do throwFailed
    return val
  (← getMainGoal).assign val
  replaceMainGoal mvarIds
