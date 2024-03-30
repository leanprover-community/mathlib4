/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
#  `#`-command linter

The `#`-command linter produces a warning when a command starting with `#` is used.
-/

namespace Mathlib.Linter

/--
Setting to `true` enables the '`#`-command' linter.  When `true`, Lean warns on any command
beginning with `#`.  For example, `#eval`, `#guard`, `#guard_msgs` all trigger a message.
-/
register_option linter.hashCommand : Bool := {
  defValue := false
  descr := "enable the `#`-command linter"
}

namespace HashCommandLinter

open Lean Elab

/-- Gets the value of the `linter.hashCommand` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.hashCommand o

open Command in
/-- Exactly like `withSetOptionIn`, but recursively discards any other use of `in`.
Intended to be used in the hashCommand linter,
where we don't need to handle non-`set_option` `in` commands. -/
private partial def withSetOptionIn' (cmd : CommandElab) : CommandElab := fun stx => do
  if stx.getKind == ``Lean.Parser.Command.in then
    if stx[0].getKind == ``Lean.Parser.Command.set_option then
      let opts ← Elab.elabSetOption stx[0][1] stx[0][2]
      Command.withScope (fun scope => { scope with opts }) do
        withSetOptionIn' cmd stx[2]
    else
      withSetOptionIn' cmd stx[2]
  else
    cmd stx

/-- `whitelist` is the array of `#`-commands that are allowed in 'Mathlib'. -/
private abbrev whitelist : Array String := #["#align", "#align_import", "#noalign"]

/-- Checks that no command beginning with `#` is present in 'Mathlib', except for the ones in
`whitelist`. -/
def hashCommandLinter : Linter where run := withSetOptionIn' fun stx => do
  let currentModule := (← getEnv).mainModule
  if getLinterHash (← getOptions) &&
     (currentModule.getRoot == `Mathlib || currentModule == `test.HashCommandLinter) then
    match stx.getHead? with
      | some sa =>
        let a := sa.getAtomVal
        if ("#".isPrefixOf a && whitelist.all (· != a)) then
          Linter.logLint linter.hashCommand sa
            m!"`#`-commands, such as '{a}', are not allowed in 'Mathlib'"
      | none => return

initialize addLinter hashCommandLinter
