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
      s!"_ {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {newRhsStr} := by sorry\n" ++
      s!"{spc}_ {relStr} {rhsStr} := by sorry"
  | true, false  =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newRhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
    else
      s!"_ {relStr} {newRhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
  | false, true =>
    if params.isFirst then
      s!"{lhsStr} {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
    else
      s!"_ {relStr} {newLhsStr} := by sorry\n{spc}_ {relStr} {rhsStr} := by sorry"
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

namespace Lean.Elab.Tactic
open Meta

/-- Elaborator for the `calc` tactic mode variant with widgets. -/
elab_rules : tactic
| `(tactic|calc%$calcstx $stx) => do
  dbg_trace "Fooo"
  let steps : TSyntax ``calcSteps := ⟨stx⟩
  let some calcRange := (← getFileMap).rangeOfStx? calcstx | unreachable!
  let indent := calcRange.start.character
  let mut isFirst := true
  for step in ← Lean.Elab.Term.getCalcSteps steps do
    let some replaceRange := (← getFileMap).rangeOfStx? step | unreachable!
    let `(calcStep| $(_) := $proofTerm) := step | unreachable!
    let json := open scoped ProofWidgets.Json in json% {"replaceRange": $(replaceRange),
                                                        "isFirst": $(isFirst),
                                                        "indent": $(indent)}
    ProofWidgets.savePanelWidgetInfo proofTerm `CalcPanel (pure json)
    isFirst := false
  evalCalc (← `(tactic|calc%$calcstx $stx))
