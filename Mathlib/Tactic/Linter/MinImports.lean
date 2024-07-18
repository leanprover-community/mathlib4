/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import ImportGraph.Imports
import Mathlib.Tactic.MinImports

/-! # The `minImports` linter

The `minImports` linter incrementally computes the minimal imports needed for each file to build.
Whenever it detects that a new command requires an increase in the (transitive) imports that it
computed so far, it emits a warning mentioning the bigger minimal imports.

Unlike the related `#min_imports` command, the linter takes into account notation and tactic
information.
It also works incrementally, providing information that it better suited, for instance, to split
files.
-/

open Lean Elab Command

/-!
#  The "minImports" linter

The "minImports" linter tracks information about minimal imports over several commands.
-/

namespace Mathlib.Linter

/-- `minImportsRef` keeps track of cumulative imports across multiple commands. -/
initialize minImportsRef : IO.Ref NameSet ← IO.mkRef {}

/-- `#reset_min_imports` sets to empty the current list of cumulative imports. -/
elab "#reset_min_imports" : command => minImportsRef.set {}

/--
The `minImports` linter incrementally computes the minimal imports needed for each file to build.
Whenever it detects that a new command requires an increase in the (transitive) imports that it
computed so far, it emits a warning mentioning the bigger minimal imports.

Unlike the related `#min_imports` command, the linter takes into account notation and tactic
information.
It also works incrementally, providing information that it better suited, for instance, to split
files.
 -/
register_option linter.minImports : Bool := {
  defValue := false
  descr := "enable the minImports linter"
}

namespace MinImports

open Mathlib.Command.MinImports

/-- Gets the value of the `linter.minImports` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.minImports o

@[inherit_doc Mathlib.Linter.linter.minImports]
def minImportsLinter : Linter where run := withSetOptionIn fun stx => do
    unless linter.minImports.get (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    let prevImports ← minImportsRef.get
    --if stx.isOfKind ``Parser.Command.eoi then logInfo m!"{(← getEnv).imports.map (·.module)}"
    let newImports := getIrredundantImports (← getEnv) (← getAllImports stx)
    let tot := (newImports.append prevImports) --.erase `Lean.Parser.Command
    let redundant := (← getEnv).findRedundantImports tot.toArray
    let currImports := tot.diff redundant
    let currImpArray := currImports.toArray.qsort Name.lt
    if currImpArray != #[] &&
       currImpArray ≠ prevImports.toArray.qsort Name.lt then
      minImportsRef.modify fun _ => currImports
      Linter.logLint linter.minImports stx m!"Imports increased to\n{currImpArray}"

initialize addLinter minImportsLinter

end MinImports

end Mathlib.Linter
