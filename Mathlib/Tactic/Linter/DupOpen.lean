import Lean.Elab.Command

/-!
#  The "dupOpen" linter

The "dupOpen" linter emits a warning when an `open` command opens an already open namespace.
-/

open Lean Elab Command

namespace Mathlib.Linter

def getReps {α} [BEq α] [Hashable α] (l : List α) : Array α := Id.run do
  let mut seen : Std.HashSet α := ∅
  let mut reps := #[]
  for a in l do
    if seen.contains a then
      reps := reps.push a
    else
      seen := seen.insert a
  return reps

/-- The "dupOpen" linter emits a warning when an `open` command opens an already open namespace. -/
register_option linter.dupOpen : Bool := {
  defValue := false
  descr := "enable the dupOpen linter"
}

namespace DupOpen

@[inherit_doc Mathlib.Linter.linter.dupOpen]
def dupOpenLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.dupOpen (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  if stx.isOfKind ``Parser.Command.open then
    let s ← getScope
    for rep in getReps (s.openDecls.map (s!"{·}")) do
      Linter.logLint linter.dupOpen stx m!"The namespace '{rep}' is already open."

initialize addLinter dupOpenLinter

end DupOpen

end Mathlib.Linter
