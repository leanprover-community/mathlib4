/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Tactic.Widget.SelectPanelUtils

/-! # Unfold widget

This file defines a `unfold?` tactic that displays a widget panel allowing to generate
an `unfold` call with name specified by selecting a subexpression in the infoview.
-/

open Lean Meta Server ProofWidgets

/-- If the given expression is a constant, return its name, if it is an application of a constant,
returns its name, otherwise return `none`. -/
def Lean.Expr.headName : Expr → Option Name
  | .const n .. => n
  | .app fn _ => fn.headName
  | _ => none

/-- Return the link text and inserted text for the unfold widget. -/
@[nolint unusedArguments]
def insertUnfold (locations : Array Lean.SubExpr.GoalsLocation) (goalType : Expr)
    (_ : SelectInsertParams) : MetaM (String × String × Option (String.Pos × String.Pos)) := do
  let some pos := locations[0]? | throwError "You must select something."
  let (fvar, subexprPos) ← match pos with
  | ⟨_, .target subexprPos⟩ => pure (none, subexprPos)
  | ⟨_, .hypType fvar subexprPos⟩ => pure (some fvar, subexprPos)
  | ⟨_, .hypValue fvar subexprPos⟩ => pure (some fvar, subexprPos)
  | _ => throwError "You must select something in the goal or in a local value."
  let (tgtExpr, loc) ← match fvar with
  | some fvarId => pure (← fvarId.getType, s!" at {← fvarId.getUserName} ")
  | none => pure (goalType, "")
  let some constName := (← Lean.Core.viewSubexpr subexprPos tgtExpr).headName
    | throwError "You must select a name."
  pure (s!"unfold {constName}{loc}", s!"unfold {constName}{loc}", none)

/-- Rpc function for the conv widget. -/
@[server_rpc_method]
def UnfoldSelectionPanel.rpc :=
mkSelectionPanelRPC insertUnfold
  "Use shift-click to select one constant that you want to unfold."
  "Unfold 🔍" (onlyGoal := false) (onlyOne := true)

/-- The conv widget. -/
@[widget_module]
def UnfoldSelectionPanel : Component SelectInsertParams :=
  mk_rpc_widget% UnfoldSelectionPanel.rpc

open scoped Json in
/-- Display a widget panel allowing to generate a `conv` call zooming to the subexpression selected
in the goal.-/
elab stx:"unfold?" : tactic => do
  let some replaceRange := (← getFileMap).rangeOfStx? stx | return
  savePanelWidgetInfo stx ``UnfoldSelectionPanel $ pure $ json% { replaceRange: $(replaceRange) }
