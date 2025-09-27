import Lean.Elab.Command

/-!
#  The "commandRanges" linter

The "commandRanges" linter simply logs the `getRange?` and the `getRangeWithTrailing?`
for each command.

This is useful for the "removeDeprecations" automation, since it helps identifying the exact range
of each declaration that should be removed.
-/

open Lean Elab Linter

namespace Mathlib.Linter

/-- The "commandRanges" linter logs the `getRange?` and the `getRangeWithTrailing?`
for each command. -/
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
  let fm ← getFileMap
  let positions := ranges.map fm.toPosition
  logInfo m!"{ranges}" -- {positions}"

initialize addLinter commandRangesLinter

end CommandRanges

end Mathlib.Linter
