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
* `transClosure` is the import graph of the current file.
* `minImports` is the `NameSet` of minimal imports to build the file up to the current command.
* `importSize` is the number of transitive imports to build the file up to the current command.
-/
structure ImportState where
  /-- The transitive closure of the import graph of the current file.  The value is `none` only at
  initialization time, as the linter immediately sets it to its value for the current file. -/
  transClosure : Option (NameMap NameSet) := none
  /-- The minimal imports needed to build the file up to the current command. -/
  minImports   : NameSet := {}
  /-- The number of transitive imports needed to build the file up to the current command. -/
  importSize   : Nat := 0
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

/-- The `linter.minImports.increases` regulates whether the `minImports` linter reports the
change in number of imports, when it reports import changes.
Setting this option to `false` helps with test stability.
-/
register_option linter.minImports.increases : Bool := {
  defValue := true
  descr := "enable reporting increase-size change in the minImports linter"
}

namespace MinImports

open Mathlib.Command.MinImports

/-- `importsBelow tc ms` takes as input a `NameMap NameSet` `tc`, representing the
`transitiveClosure` of the imports of the current module, and a `NameSet` of module names `ms`.
It returns the modules that are transitively imported by `ms`, using the data in `tc`.
-/
def importsBelow (tc : NameMap NameSet) (ms : NameSet) : NameSet :=
  ms.fold (·.append <| tc.findD · default) ms

@[inherit_doc Mathlib.Linter.linter.minImports]
def minImportsLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.minImports (← getOptions) do
      return
    if (← get).messages.hasErrors then
      return
    if stx == (← `(command| set_option $(mkIdent `linter.minImports) true)) then return
    let env ← getEnv
    -- the first time `minImportsRef` is read, it has `transClosure = none`;
    -- in this case, we set it to be the `transClosure` for the file.
    if (← minImportsRef.get).transClosure.isNone then
      minImportsRef.modify ({· with transClosure := env.importGraph.transitiveClosure})
    let impState ← minImportsRef.get
    let (importsSoFar, oldCumulImps) := (impState.minImports, impState.importSize)
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
      let newCumulImps := -- We should always be in the situation where `getD` finds something
        (importsBelow (impState.transClosure.getD env.importGraph.transitiveClosure) tot).size
      minImportsRef.modify ({· with minImports := currImports, importSize := newCumulImps})
      let new := currImpArray.filter (!importsSoFar.contains ·)
      let redundant := importsSoFar.toArray.filter (!currImports.contains ·)
      -- to make `test` files more stable, we suppress the exact count of import changes if
      -- the `linter.minImports.increases` option is `false`
      let byCount :=  if Linter.getLinterValue linter.minImports.increases (← getOptions) then
                      m!"by {newCumulImps - oldCumulImps} "
                    else
                      m!""
      Linter.logLint linter.minImports stx <|
        m!"Imports increased {byCount}to\n{currImpArray}\n\n\
          New imports: {new}\n" ++
            if redundant.isEmpty then m!"" else m!"\nNow redundant: {redundant}\n"

initialize addLinter minImportsLinter

end MinImports

end Mathlib.Linter
