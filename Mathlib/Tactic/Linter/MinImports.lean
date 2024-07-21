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
    let importsSoFar ← minImportsRef.get
    -- when the linter reaches the end of the file or `#exit`, it gives a report
    if #[``Parser.Command.eoi, ``Lean.Parser.Command.exit].contains stx.getKind  then
      let explicitImportsInFile : NameSet :=
        .fromArray (((← getEnv).imports.map (·.module)).erase `Init) Name.quickCmp
      let newImps := importsSoFar.diff explicitImportsInFile
      let currentlyUnneededImports := explicitImportsInFile.diff importsSoFar
      -- we read the current file, to do a custom parsing of the imports:
      -- this is a hack to obtain some `Syntax` information for the `import X` commands
      let fil ← IO.FS.readFile (← getFileName)
      for i in currentlyUnneededImports do
        -- looking for the position of `import i`, so we split at ` i` and
        -- compute the length of the string until `...import| i`
        match fil.splitOn (" " ++ i.toString) with
          | a::_::_ =>
            let al := a.length
            -- create a syntax covering the range that should be occupied by import `i`
            let impPos : Syntax := .ofRange ⟨⟨al + 1⟩, ⟨al + i.toString.length + 1⟩⟩
            logWarningAt impPos m!"unneeded import '{i}'"
          | _ => dbg_trace f!"'{i}' not found"  -- this should be unreachable
      -- if the linter found new imports that should be added (likely to *reduce* the dependencies)
      if !newImps.isEmpty then
        -- format the imports prepending `import ` to each module name
        let withImport := (newImps.toArray.qsort Name.lt).map (s!"import {·}")
        -- create a syntax node supported, likely on the first imported module name
        let firstImport : Syntax := match fil.splitOn "import " with
          | a::_::_ => .ofRange ⟨⟨a.length⟩, ⟨a.length + "import".length⟩⟩
          | _ => .ofRange ⟨⟨0⟩, ⟨19⟩⟩
        logWarningAt firstImport m!"-- missing imports\n{"\n".intercalate withImport.toList}"
    let id ← getId stx
    let newImports := getIrredundantImports (← getEnv) (← getAllImports stx id)
    let tot := (newImports.append importsSoFar) --.erase `Lean.Parser.Command
    let redundant := (← getEnv).findRedundantImports tot.toArray
    let currImports := tot.diff redundant
    let currImpArray := currImports.toArray.qsort Name.lt
    if currImpArray != #[] &&
       currImpArray ≠ importsSoFar.toArray.qsort Name.lt then
      minImportsRef.modify fun _ => currImports
      Linter.logLint linter.minImports stx m!"Imports increased to\n{currImpArray}"

initialize addLinter minImportsLinter

end MinImports

end Mathlib.Linter
