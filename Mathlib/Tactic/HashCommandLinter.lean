/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Std.Lean.Command
import Std.Data.Array.Basic

/-!
#  `#`-command linter

The `#`-command linter produces a warning when a command starting with `#` is used.
-/

namespace Mathlib.Linter

/--
Enables the '`#`-command' linter. This will warn on any command beginning with `#`.
For example, `#eval, #guard, #guard_msgs` all trigger a message.
-/
register_option linter.hashCommand : Bool := {
  defValue := true
  descr := "enable the `#`-command linter"
}

namespace HashCommandLinter

open Lean Elab

/-- `getAtomStx stx` extracts the array of all `.atom` nodes in `stx`. -/
def getAtomStx : Syntax → Array Syntax
  | .node _ _ args => (args.attach.map fun ⟨a, _h⟩ => getAtomStx a).foldl (· ++ ·) default
  | s@(.atom ..) => #[s]
  | _ => default

/-- Gets the value of the `linter.hashCommand` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.hashCommand o

/-- `whiteList` is the array of `#`-commands that are allowed in 'Mathlib'. -/
private abbrev whiteList : Array String := #["#align", "#align_import", "#noalign"]

/-- Checks that no command beginning with `#` is present in 'Mathlib', except for the ones in
`whiteList`. -/
def hashCommandLinter : Linter where run := withSetOptionIn fun stx => do
  let currentModule := (← getEnv).mainModule
  if getLinterHash (← getOptions) &&
     (← getInfoState).enabled &&
     (currentModule.getRoot == `Mathlib || currentModule == `test.HashCommandLinter) then
    let sa := (getAtomStx stx)[0]!
    let a := sa.getAtomVal
    if ("#".isPrefixOf a && (!' ' ∈ a.toList) && whiteList.all (· != a)) then
      logWarningAt sa f!"`#`-commands, such as '{a}', are not allowed in 'Mathlib'\n\
      [linter.hashCommand]"

initialize addLinter hashCommandLinter
