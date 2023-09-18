import Lean.Widget.InteractiveGoal
import Lean.Elab.Deriving.Ord

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

/-- Structures providing parameters for a Select and insert widget. -/
class SelectInsertHandlerParamsClass (α : Type) where
  /-- The current tactic-mode target. -/
  goalType : α → Expr
  /-- Locations currently selected in the goal state. -/
  selectedLocations : α → Array SubExpr.GoalsLocation

namespace Lean.Elab
open Command Meta Parser Term

private def mkSelectInsertParamsInstance (declName : Name) : TermElabM Syntax.Command :=
  `(command|instance : SelectInsertParamsClass (@$(mkCIdent declName)) :=
    ⟨fun prop => prop.pos, fun prop => prop.goals,
     fun prop => prop.selectedLocations, fun prop => prop.replaceRange⟩)

def mkSelectInsertParamsInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      elabCommand (← liftTermElabM do mkSelectInsertParamsInstance declName)
    return true
  else
    return false

initialize registerDerivingHandler `SelectInsertParamsClass mkSelectInsertParamsInstanceHandler


private def mkSelectInsertHandlerInstance (declName : Name) : TermElabM Syntax.Command :=
  `(command|instance : SelectInsertHandlerParamsClass (@$(mkCIdent declName)) :=
    ⟨fun prop => prop.goalType, fun prop => prop.selectedLocations⟩)

def mkSelectInsertHandlerInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      elabCommand (← liftTermElabM do mkSelectInsertHandlerInstance declName)
    return true
  else
    return false

initialize
  registerDerivingHandler `SelectInsertHandlerParamsClass mkSelectInsertHandlerInstanceHandler

end Lean.Elab
