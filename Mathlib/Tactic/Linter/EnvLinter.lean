/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Init

/-!
#  The "envLinter" linter

The "envLinter" linter emits a warning at the end of a file if `#lint` reports an error.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The "envLinter" linter emits a warning at the end of a file if `#lint` reports an error. -/
register_option linter.envLinter : Bool := {
  defValue := true
  descr := "enable the envLinter linter"
}

namespace EnvLinter

@[inherit_doc Mathlib.Linter.linter.envLinter]
def envLinterLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.envLinter (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  if Parser.isTerminalCommand stx then
    let s ← get
    Command.elabCommand (← `(command| #lint))
    let msg := (← get).messages.reportedPlusUnreported
    set s
    if !(msg.filter (·.severity == .error)).isEmpty then
      for m in msg do
        Linter.logLint linter.envLinter stx (← m.toString)

initialize addLinter envLinterLinter

end EnvLinter

end Mathlib.Linter
