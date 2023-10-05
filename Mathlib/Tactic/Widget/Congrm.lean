/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import Mathlib.Tactic.Widget.SelectPanelUtils
import Mathlib.Tactic.Congrm


/-! # Congrm widget

This file defines a `congrm?` tactic that displays a widget panel allowing to generate
a `congrm` call with holes specified by selecting subexpressions in the goal.
-/

open Lean Meta Server ProofWidgets


/-! # Gcongr widget -/

/-- Return the link text and inserted text above and below of the congrm widget. -/
@[nolint unusedArguments]
def makeCongrmString (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
    (_ : SelectInsertParams) : MetaM (String × String × Option (String.Pos × String.Pos)) := do
  let subexprPos := getGoalLocations pos
  unless goalType.isAppOf `Eq || goalType.isAppOf `Iff do
    throwError "The goal must be an equality or iff."
  let mut goalTypeWithMetaVars := goalType
  for pos in subexprPos do
    goalTypeWithMetaVars ← insertMetaVar goalTypeWithMetaVars pos

  let side := if subexprPos[0]!.toArray[0]! = 0 then 1 else 2
  let sideExpr := goalTypeWithMetaVars.getAppArgs[side]!
  let res := "congrm " ++ (toString (← Meta.ppExpr sideExpr)).renameMetaVar
  return (res, res, none)

/-- Rpc function for the congrm widget. -/
@[server_rpc_method]
def CongrmSelectionPanel.rpc := mkSelectionPanelRPC makeCongrmString
  "Use shift-click to select sub-expressions in the goal that should become holes in congrm."
  "Congrm 🔍"

/-- The congrm widget. -/
@[widget_module]
def CongrmSelectionPanel : Component SelectInsertParams :=
  mk_rpc_widget% CongrmSelectionPanel.rpc

open scoped Json in
/-- Display a widget panel allowing to generate a `congrm` call with holes specified by selecting
subexpressions in the goal.-/
elab stx:"congrm?" : tactic => do
  let some replaceRange := (← getFileMap).rangeOfStx? stx | return
  savePanelWidgetInfo stx ``CongrmSelectionPanel $ pure $ json% { replaceRange: $(replaceRange) }
