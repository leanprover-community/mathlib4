/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Tactic.Widget.SelectPanelUtils
import Mathlib.Tactic.Congrm
import Mathlib.Data.Real.Basic


import Lean.Meta.ExprLens
import Std.Lean.Position

import Mathlib.Tactic.Widget.SelectPanelUtils

/-! # Congrm widget

This file defines a `congrm?` tactic that displays a widget panel allowing to generate
a `congrm` call with holes specified by selecting subexpressions in the goal.
-/

open Lean Meta Server ProofWidgets


/-! # Gcongr widget -/

def makeCongrmString (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
  (_ : SelectInsertParams) : MetaM (String × String) := do
  let subexprPos := getGoalLocations pos
  unless goalType.isAppOf `Eq || goalType.isAppOf `Iff do
    throwError "The goal must be an equality or iff."
  let mut goalTypeWithMetaVars := goalType
  for pos in subexprPos do
    goalTypeWithMetaVars ← insertMetaVar goalTypeWithMetaVars pos

  let side := if subexprPos[0]!.toArray[0]! = 0 then 1 else 2
  let sideExpr := goalTypeWithMetaVars.getAppArgs[side]!
  let res := "congrm " ++ (toString (← Meta.ppExpr sideExpr)).renameMetaVar
  return (res, res)

@[server_rpc_method]
def CongrmSelectionPanel.rpc := mkSelectionPanelRPC makeCongrmString
  "Use shift-click to select sub-expressions in the goal that should become holes in congrm."
  "Congrm 🔍"

@[widget_module]
def CongrmSelectionPanel : Component SelectInsertParams :=
  mk_rpc_widget% CongrmSelectionPanel.rpc

open scoped Json in
/-- Display a widget panel allowing to generate a `congrm` call with holes specified by selecting
subexpressions in the goal.-/
elab stx:"congrm?" : tactic => do
  let some replaceRange := (← getFileMap).rangeOfStx? stx | return
  savePanelWidgetInfo stx ``CongrmSelectionPanel $ pure $ json% { replaceRange: $(replaceRange) }

/-! # Example usage -/

example {a b c d : ℕ} :
    Nat.pred a.succ * (d + (c + a.pred)) = Nat.pred b.succ * (b + (c + d.pred)) := by
  congrm?
  all_goals { sorry }
