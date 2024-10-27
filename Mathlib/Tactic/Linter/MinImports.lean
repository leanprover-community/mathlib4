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
It also works incrementally, accumulating increasing import information.
This is better suited, for instance, to split files.
-/

open Lean Elab Command

/-!
#  The "minImports" linter

The "minImports" linter tracks information about minimal imports over several commands.
-/

namespace Mathlib.Linter

/--
`ImportState` is the structure keeping track of the data that the `minImports` linter uses.
* `ig` is the import graph of the current file.
* `minImps` is the `NameSet` of minimal imports to build the file up to the current command.
* `impsSize` is the number of transitive imports to build the file up to the current command.
-/
structure ImportState where
  ig : Option (NameMap (Array Name)) := none
  minImps : NameSet := {}
  impsSize : Nat := 0
  deriving Inhabited

/--
`minImportsRef` keeps track of cumulative imports across multiple commands, using `ImportState`.
-/
initialize minImportsRef : IO.Ref ImportState ← IO.mkRef {}

/-- `#reset_min_imports` sets to empty the current list of cumulative imports. -/
elab "#reset_min_imports" : command => minImportsRef.set {}

/--
The `minImports` linter incrementally computes the minimal imports needed for each file to build.
Whenever it detects that a new command requires an increase in the (transitive) imports that it
computed so far, it emits a warning mentioning the bigger minimal imports.

Unlike the related `#min_imports` command, the linter takes into account notation and tactic
information.
It also works incrementally, providing information that is better suited, for instance, to split
files.
-/
register_option linter.minImports : Bool := {
  defValue := false
  descr := "enable the minImports linter"
}

namespace MinImports

open Mathlib.Command.MinImports

/-- `impsBelow ig ms` takes as input an `importGraph` `ig` and a `NameSet` of module names `ms`.
It returns the modules that are transitively imported by `ms`, using the data in `ig`.
-/
def importsBelow (ig : NameMap (Array Name)) (ms : NameSet) : NameSet :=
  (ig.upstreamOf ms).fold (σ := NameSet) (fun _ ↦ ·.insert ·) {}

@[inherit_doc Mathlib.Linter.linter.minImports]
def minImportsLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.minImports (← getOptions) do
      return
    if (← get).messages.hasErrors then
      return
    if stx == (← `(command| set_option $(mkIdent `linter.minImports) true)) then return
    let env ← getEnv
    -- the first time `minImportsRef` is read, it has `ig = none`; in this case, we set it to
    -- be the `importGraph` for the file.
    if (← minImportsRef.get).ig.isNone then minImportsRef.modify ({· with ig := env.importGraph})
    let impState ← minImportsRef.get
    let (importsSoFar, oldCumulImps) := (impState.minImps, impState.impsSize)
    -- when the linter reaches the end of the file or `#exit`, it gives a report
    if #[``Parser.Command.eoi, ``Lean.Parser.Command.exit].contains stx.getKind then
      let explicitImportsInFile : NameSet :=
        .fromArray ((env.imports.map (·.module)).erase `Init) Name.quickCmp
      let newImps := importsSoFar.diff explicitImportsInFile
      let currentlyUnneededImports := explicitImportsInFile.diff importsSoFar
      -- we read the current file, to do a custom parsing of the imports:
      -- this is a hack to obtain some `Syntax` information for the `import X` commands
      let fname ← getFileName
      let contents ← IO.FS.readFile fname
      -- `impMods` is the syntax for the modules imported in the current file
      let (impMods, _) ← Parser.parseHeader (Parser.mkInputContext contents fname)
      for i in currentlyUnneededImports do
        match impMods.find? (·.getId == i) with
          | some impPos => logWarningAt impPos m!"unneeded import '{i}'"
          | _ => dbg_trace f!"'{i}' not found"  -- this should be unreachable
      -- if the linter found new imports that should be added (likely to *reduce* the dependencies)
      if !newImps.isEmpty then
        -- format the imports prepending `import ` to each module name
        let withImport := (newImps.toArray.qsort Name.lt).map (s!"import {·}")
        -- log a warning at the first `import`, if there is one.
        logWarningAt ((impMods.find? (·.isOfKind `import)).getD default)
          m!"-- missing imports\n{"\n".intercalate withImport.toList}"
    let id ← getId stx
    let newImports := getIrredundantImports env (← getAllImports stx id)
    let tot := (newImports.append importsSoFar)
    let redundant := env.findRedundantImports tot.toArray
    let currImports := tot.diff redundant
    let currImpArray := currImports.toArray.qsort Name.lt
    if currImpArray != #[] &&
       currImpArray ≠ importsSoFar.toArray.qsort Name.lt then
      let newCumulImps := (importsBelow env.importGraph tot).size
      minImportsRef.set {minImps := currImports, impsSize := newCumulImps}
      let new := currImpArray.filter (!importsSoFar.contains ·)
      let redundant := importsSoFar.toArray.filter (!currImports.contains ·)
      Linter.logLint linter.minImports stx
        m!"Imports increased by {newCumulImps - oldCumulImps} to\n{currImpArray}\n\n\
          Now redundant: {redundant}\n\n\
          New imports: {new}\n"

initialize addLinter minImportsLinter

end MinImports

end Mathlib.Linter
