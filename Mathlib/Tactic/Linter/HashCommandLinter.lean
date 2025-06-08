/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

/-!
# `#`-command linter

The `#`-command linter produces a warning when a command starting with `#` is used *and*
* either the command emits no message;
* or `warningAsError` is set to `true`.

The rationale behind this is that `#`-commands are intended to be transient:
they provide useful information in development, but are not intended to be present in final code.
Most of them are noisy and get picked up anyway by CI, but even the quiet ones are not expected to
outlive their in-development status.
-/

namespace Mathlib.Linter

/--
The linter emits a warning on any command beginning with `#` that itself emits no message.
For example, `#guard true` and `#check_tactic True ~> True by skip` trigger a message.
There is a list of silent `#`-command that are allowed.
-/
register_option linter.hashCommand : Bool := {
  defValue := false
  descr := "enable the `#`-command linter"
}

namespace HashCommandLinter

open Lean Elab Linter

open Command in
/-- Exactly like `withSetOptionIn`, but recursively discards nested uses of `in`.
Intended to be used in the `hashCommand` linter, where we want to enter `set_option` `in` commands.
-/
private partial def withSetOptionIn' (cmd : CommandElab) : CommandElab := fun stx => do
  if stx.getKind == ``Lean.Parser.Command.in then
    if stx[0].getKind == ``Lean.Parser.Command.set_option then
      let opts ← Elab.elabSetOption stx[0][1] stx[0][3]
      withScope (fun scope => { scope with opts }) do
        withSetOptionIn' cmd stx[2]
    else
      withSetOptionIn' cmd stx[2]
  else
    cmd stx

/-- `allowed_commands` is the `HashSet` of `#`-commands that are allowed in 'Mathlib'. -/
private abbrev allowed_commands : Std.HashSet String := { "#adaptation_note" }

/-- Checks that no command beginning with `#` is present in 'Mathlib',
except for the ones in `allowed_commands`.

If `warningAsError` is `true`, then the linter logs an info (rather than a warning).
This means that CI will eventually fail on `#`-commands, but does not stop it from continuing.

However, in order to avoid local clutter, when `warningAsError` is `false`, the linter
logs a warning only for the `#`-commands that do not already emit a message. -/
def hashCommandLinter : Linter where run := withSetOptionIn' fun stx => do
  if getLinterValue linter.hashCommand (← getLinterOptions) &&
    ((← get).messages.reportedPlusUnreported.isEmpty || warningAsError.get (← getOptions))
  then
    if let some sa := stx.getHead? then
      let a := sa.getAtomVal
      if (a.get ⟨0⟩ == '#' && ! allowed_commands.contains a) then
        let msg := m!"`#`-commands, such as '{a}', are not allowed in 'Mathlib'"
        if warningAsError.get (← getOptions) then
          logInfoAt sa (msg ++ " [linter.hashCommand]")
        else Linter.logLint linter.hashCommand sa msg

initialize addLinter hashCommandLinter

end HashCommandLinter
