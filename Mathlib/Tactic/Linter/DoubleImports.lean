/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import ImportGraph.Imports
import Mathlib.Tactic.MinImports

/-! # The `doubleImports` linter

The `doubleImports` linter incrementally computes the minimal imports needed for each file to build.
Whenever it detects that a new command requires an increase in the (transitive) imports that it
computed so far, it emits a warning mentioning the bigger minimal imports.

Unlike the related `#min_imports` command, the linter takes into account notation and tactic
information.
It also works incrementally, accumulating increasing import information.
This is better suited, for instance, to split files.
-/

open Lean Elab Command

/-!
#  The "doubleImports" linter

The "doubleImports" linter tracks information about minimal imports over several commands.
-/

namespace Mathlib.Linter

/--
The `doubleImports` linter incrementally computes the minimal imports needed for each file to build.
Whenever it detects that a new command requires an increase in the (transitive) imports that it
computed so far, it emits a warning mentioning the bigger minimal imports.

Unlike the related `#min_imports` command, the linter takes into account notation and tactic
information.
It also works incrementally, providing information that is better suited, for instance, to split
files.
-/
register_option linter.doubleImports : Bool := {
  defValue := true
  descr := "enable the doubleImports linter"
}

namespace DoubleImports

open Mathlib.Command.MinImports

/-- `importsBelow tc ms` takes as input a `NameMap NameSet` `tc`, representing the
`transitiveClosure` of the imports of the current module, and a `NameSet` of module names `ms`.
It returns the modules that are transitively imported by `ms`, using the data in `tc`.
-/
def importsBelow (tc : NameMap NameSet) (ms : NameSet) : NameSet :=
  ms.fold (·.append <| tc.findD · default) ms

@[inherit_doc Mathlib.Linter.linter.doubleImports]
def doubleImportsLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.doubleImports (← getOptions) do
      return
    if (← get).messages.hasErrors then
      return
    if stx == (← `(command| set_option $(mkIdent `linter.doubleImports) true)) then return
    let env ← getEnv
    let id ← getId stx
    let newImports := getIrredundantImports env (← getAllImports stx id)

    if id != .missing then
      dbg_trace "imports for '{id}': {newImports.toArray.qsort (·.toString < ·.toString)}"

initialize addLinter doubleImportsLinter

end DoubleImports

end Mathlib.Linter
