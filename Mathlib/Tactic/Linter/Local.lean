import Lean.Elab.Command
import Mathlib.Util.ParseGit

/-!
#  The "localLinter" linter

The "localLinter" linter emits a warning somewhere.
-/

open Lean Elab

namespace Mathlib.Linter

/-- The "localLinter" linter emits a warning when there are multiple active goals. -/
register_option linter.localLinter : Bool := {
  defValue := true
  descr := "enable the localLinter linter"
}

initialize activeRangesExt : SimplePersistentEnvExtension GitDiff (Array GitDiff) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.push)
    addImportedFn := mkStateFromImportedEntries (·.push) {}
  }

elab "add_range " st:num en:num : command => do
  let fname ← getFileName
  let newEntry := {file := fname, rg := {first := st.getNat, last := en.getNat}}
  modifyEnv (activeRangesExt.addEntry · newEntry)

namespace LocalLinter

@[inherit_doc Mathlib.Linter.linter.localLinter]
def localLinterLinter : Linter where run stx := do
  unless Linter.getLinterValue linter.localLinter (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let activeRanges := activeRangesExt.getState (← getEnv)
  if let some rg := stx.getRange? then
    if ← overlaps activeRanges rg then
      Linter.logLint linter.localLinter stx m!"'{stx}' is in range!"

initialize addLinter localLinterLinter

end LocalLinter

end Mathlib.Linter
