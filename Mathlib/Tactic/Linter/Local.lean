import Lean.Elab.Command

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


--initialize hintExtension : SimplePersistentEnvExtension (Nat × Nat) (List (Nat × Nat)) ←
--  registerSimplePersistentEnvExtension {
--    addEntryFn := (·.cons)
--    addImportedFn := mkStateFromImportedEntries (·.cons) {}
--  }

initialize activeRangesRef : IO.Ref (Array (Nat × Nat)) ← IO.mkRef ∅

namespace LocalLinter

@[inherit_doc Mathlib.Linter.linter.localLinter]
def localLinterLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.localLinter (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return

  Linter.logLint linter.localLinter stx m!"'{stx}' Nat subtraction"

initialize addLinter localLinterLinter

end LocalLinter

end Mathlib.Linter
