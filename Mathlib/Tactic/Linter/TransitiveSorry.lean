/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
#  The "transitiveSorry" linter

The "transitiveSorry" linter emits a warning on declarations that depend on `sorry`.
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- The "transitiveSorry" linter emits a warning on declarations that depend on `sorry`. -/
register_option linter.transitiveSorry : Bool := {
  defValue := true
  descr := "enable the transitiveSorry linter"
}

namespace TransitiveSorry

/-- Actually, not just `sorry`, but anything that appears in `exclusions` triggers the linter. -/
abbrev exclusions : NameSet := NameSet.empty
  |>.insert ``sorryAx

/-- input is the current namespace and a command -/
def getDeclId (ns : Name) (stx : Syntax) : Option (Syntax × Name) :=
  match stx.find? (·.isOfKind ``Parser.Command.declId) with
    | none => default
    | some did =>
      let n := did[0].getId
      let name :=
        if let `_root_ :: rest := n.components then
          rest.foldl .append default
        else
          ns ++ n
      some (did, name)

@[inherit_doc Mathlib.Linter.linter.transitiveSorry]
def transitiveSorryLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.transitiveSorry (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  if let some (did, declName) := getDeclId (← getCurrNamespace) stx then
  let (_, { visited, .. }) := CollectAxioms.collect declName |>.run (← getEnv) |>.run {}
  let mut disallowed : NameSet := {}
  for d in exclusions do
    if visited.contains d then
      disallowed := disallowed.insert d
  let txt? := match disallowed.toArray.qsort (·.toString < ·.toString) with
    | #[]  => none
    | #[d] => some m!"'{d}'"
    | arr  => some m!"{arr}"
  if let some txt := txt? then
    Linter.logLint linter.transitiveSorry did m!"'{declName}' relies on {txt}"

initialize addLinter transitiveSorryLinter

end TransitiveSorry

end Mathlib.Linter
