/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Patrick Massot
-/
import Mathlib.Tactic.Widget.Util
import Mathlib.Tactic.GCongr
import Mathlib.Data.Real.Basic


import Lean.Meta.ExprLens
import Std.Lean.Position

import Mathlib.Tactic.Widget.Util

open Lean Meta Server ProofWidgets


/-! # Gcongr widget -/

def makeGCongrString (pos : Array Lean.SubExpr.GoalsLocation) (goalType : Expr) : MetaM String := do
  let subexprPos := pos.map (·.loc.target!)
  let goalType := goalType.consumeMData
  unless goalType.isAppOf `LE.le || goalType.isAppOf `LT.lt || goalType.isAppOf `Int.ModEq do
    panic! "The goal must be a ≤ or < or ≡."
  unless 0 < subexprPos.size do panic! "You need to select something"
  let mut goalTypeWithMetaVars := goalType
  for pos in subexprPos do
    goalTypeWithMetaVars ← insertMetaVar goalTypeWithMetaVars pos

  let side := if goalType.isAppOf `Int.ModEq then
                if subexprPos[0]!.toArray[0]! = 0 then 1 else 2
              else
                if subexprPos[0]!.toArray[0]! = 0 then 2 else 3
  let sideExpr := goalTypeWithMetaVars.getAppArgs[side]!
  return "gcongr " ++ (toString (← Meta.ppExpr sideExpr)).renameMetaVar

@[server_rpc_method]
def GCongrSelectionPanel.rpc := mkSelectionPanelRPC makeGCongrString
  "Use shift-click to select sub-expressions in the goal that should become holes in gcongr."
  "GCongr 🔍"

@[widget_module]
def GCongrSelectionPanel : Component SelectionPanelProps :=
  mk_rpc_widget% GCongrSelectionPanel.rpc

open scoped Json in
elab stx:"gcongr?" : tactic => do
  let some replaceRange := (← getFileMap).rangeOfStx? stx | return
  savePanelWidgetInfo stx ``GCongrSelectionPanel $ pure $ json% { replaceRange: $(replaceRange) }

/-! # Example usage -/

example {a b x c d : ℝ} (h1 : a + 1 ≤ b + 1) (h2 : c + 2 ≤ d + 2) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr x ^ 2 * ?_ + ?_
  all_goals { linarith }
