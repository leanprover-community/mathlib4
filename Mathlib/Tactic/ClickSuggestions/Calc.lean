/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.Widget.Calc
public import ProofWidgets.Component.Panel.Basic

/-!
# `calc` widget plugin for the `#infoview_search` widget

This file implements support for embedding the `calc` widget into the `#click_suggestions` widget.

We loop through the `Syntax` to check whether we are in a `calc` step.
If so, we return the `calc` widget corresponding to that `calc` step.
-/

meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Server ProofWidgets

/-- Return whether `stx` represends a `by` atom or a `by` block. -/
def isBy (stx : Syntax) : Bool :=
  stx.isToken "by" || stx.getNumArgs == 2 && stx[0].isToken "by"

/-- If `pos` is the starting position of the proof of a `calc` step,
return that `calc` step, and whether this is the first `calc` step. -/
partial def inCalcStep? (pos : String.Pos.Raw) (stx : Syntax) : Option (Syntax × Bool) := do
  match stx with
  | .node _ kind args =>
    if kind == ``calcFirstStep then
      if stx[1][1].getPos? == pos then
        return (stx, true)
    else if kind == ``calcStep then
      if stx[2].getPos? == pos then
        return (stx, false)
    args.firstM (inCalcStep? pos)
  | _ => none

/-- Return a `calc` widget if `stx` is a `by` appearing as a proof in a `calc` step. -/
public def getCalcWidget? (stx cmd : Syntax) (props : PanelWidgetProps) :
    RequestM (Option Html) := do
  unless isBy stx do return none
  let some pos := stx.getPos? | return none
  let some (calcStep, isFirst) := inCalcStep? pos cmd | return none
  let some replaceRange := (← RequestM.readDoc).meta.text.lspRangeOfStx? calcStep | return none
  let calcTask ← CalcPanel.rpc
    { props with replaceRange, isFirst, indent := replaceRange.start.character }
  let .ok calcWidget := calcTask.get | return none
  return calcWidget

end Mathlib.Tactic.ClickSuggestions
