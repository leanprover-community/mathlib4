/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Init

/-!
#  The "dupOpen" linter

The "dupOpen" linter emits a warning when an `open` command opens an already open namespace.
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- Returns the array of repetitions in the input `l`. -/
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
  match stx with
  | `(open $os*) =>
    let s ← getScope
    let mut toReport : Std.HashSet (String.Range × Name × String):= ∅
    for rep in getReps (s.openDecls.map (s!"{·}")) do
      for o in os do
        if rep.endsWith o.getId.toString then
          toReport := toReport.insert (o.raw.getRange?.get!, o.getId, rep)
    for (rg, o, rep) in toReport do
      Linter.logLint linter.dupOpen (.ofRange rg)
        m!"The namespace '{o}' in '{rep}' is already open."
  | _ => return

initialize addLinter dupOpenLinter

end DupOpen

end Mathlib.Linter
