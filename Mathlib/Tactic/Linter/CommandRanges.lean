/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Init -- `import Lean.Elab.Command` is enough

/-!
# The "commandRanges" linter

The "commandRanges" linter simply logs the `getRange?` and the `getRangeWithTrailing?`
for each command.

This is useful for the "removeDeprecations" automation, since it helps identifying the exact range
of each declaration that should be removed.

This linter is strictly tied to the `#clear_deprecations` command in
`Mathlib/Tactic/Linter/FindDeprecations.lean`.
-/

open Lean Elab Linter

namespace Mathlib.Linter

/--
The "commandRanges" linter logs the `getRange?` and the `getRangeWithTrailing?` for each command.
The format is `[start, end, trailing]`, where
* `start` is the start of the command,
* `end` is the end of the command, not including trailing whitespace and comments,
* `trailing` is the "syntactic end" of the command, so it contains all trailing whitespace and
  comments.

Thus, assuming that there has been no tampering with positions/synthetic syntax,
if the current command is followed by another command, then `trailing` for the previous command
coincides with `start` of the following.
-/
register_option linter.commandRanges : Bool := {
  defValue := false
  descr := "enable the commandRanges linter"
}

namespace CommandRanges

@[inherit_doc Mathlib.Linter.linter.commandRanges]
def commandRangesLinter : Linter where run stx := do
  unless Linter.getLinterValue linter.commandRanges (← getLinterOptions) do
    return
  if Parser.isTerminalCommand stx then
    return
  let ranges :=
    if let some rg := stx.getRange? then #[rg.start, rg.stop] else #[]
  let ranges : Array String.Pos :=
    if let some rg := stx.getRangeWithTrailing? then ranges.push rg.stop else ranges
  logInfo m!"{ranges}"

initialize addLinter commandRangesLinter

end CommandRanges

end Mathlib.Linter
