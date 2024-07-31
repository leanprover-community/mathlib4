/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Lean.Widget.InteractiveGoal
import Lean.Elab.Deriving.Basic

/-! # SelectInsertParamsClass

Defines the basic class of parameters for a select and insert widget.

This needs to be in a separate file in order to initialize the deriving handler.
-/

open Lean Meta Server

/-- Structures providing parameters for a Select and insert widget. -/
class SelectInsertParamsClass (α : Type) where
  /-- Cursor position in the file at which the widget is being displayed. -/
  pos : α → Lsp.Position
  /-- The current tactic-mode goals. -/
  goals : α → Array Widget.InteractiveGoal
  /-- Locations currently selected in the goal state. -/
  selectedLocations : α → Array SubExpr.GoalsLocation
  /-- The range in the source document where the command will be inserted. -/
  replaceRange : α → Lsp.Range

namespace Lean.Elab
open Command Meta Parser Term

private def mkSelectInsertParamsInstance (declName : Name) : TermElabM Syntax.Command :=
  `(command|instance : SelectInsertParamsClass (@$(mkCIdent declName)) :=
    ⟨fun prop => prop.pos, fun prop => prop.goals,
     fun prop => prop.selectedLocations, fun prop => prop.replaceRange⟩)

/-- Handler deriving a `SelectInsertParamsClass` instance. -/
def mkSelectInsertParamsInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      elabCommand (← liftTermElabM do mkSelectInsertParamsInstance declName)
    return true
  else
    return false

initialize registerDerivingHandler `SelectInsertParamsClass mkSelectInsertParamsInstanceHandler
end Lean.Elab
