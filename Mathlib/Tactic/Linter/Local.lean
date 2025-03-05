/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
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

def _root_.Lean.Syntax.inRange {m} [Monad m] [MonadLog m] [MonadEnv m] (stx : Syntax) : m Bool := do
  match stx.getRange? with
  | none => pure false
  | some rg => overlaps (activeRangesExt.getState (← getEnv)) rg

namespace LocalLinter

@[inherit_doc Mathlib.Linter.linter.localLinter]
def localLinterLinter : Linter where run stx := do
  unless Linter.getLinterValue linter.localLinter (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let activeRanges := activeRangesExt.getState (← getEnv)
  if ← stx.inRange then
    Linter.logLint linter.localLinter stx m!"'{stx}' is in range!"

initialize addLinter localLinterLinter

end LocalLinter

end Mathlib.Linter
