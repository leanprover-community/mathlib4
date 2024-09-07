import Lean.Elab.Command
import Lean.Linter.Util

/-!
#  The "style.header" linter

The "style.header" linter emits a warning on a malformed header.
-/

open Lean Parser Elab

namespace Mathlib.Linter

/-- The "style.header" linter emits a warning on a malformed header. -/
register_option linter.style.header : Bool := {
  defValue := true
  descr := "enable the style.header linter"
}

namespace Style.header

@[inherit_doc Mathlib.Linter.linter.style.header]
def style.headerLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.header (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  unless isTerminalCommand stx do return

  Linter.logLint linter.style.header stx (m!"'{stx}' Nat subtraction")

initialize addLinter style.headerLinter

end Style.header

end Mathlib.Linter
