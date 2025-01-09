/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Mathlib.Tactic.Linter.Header

/-!
#  The "countExample" linter

The "countExample" linter emits a warning on `example`s.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The "countExample" linter emits a warning on `example`s. -/
register_option linter.countExample : Bool := {
  defValue := true
  descr := "enable the countExample linter"
}

namespace CountExample

@[inherit_doc Mathlib.Linter.linter.countExample]
def countExampleLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.countExample (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  if let some ex := stx.find? (·.isOfKind ``Lean.Parser.Command.example) then
    Linter.logLint linter.countExample ex m!"'{stx}' is an `example`"

initialize addLinter countExampleLinter

end CountExample

end Mathlib.Linter
