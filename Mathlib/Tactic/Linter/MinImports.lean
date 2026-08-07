/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import ImportGraph.Imports.ImportGraph
public meta import ImportGraph.Graph.TransitiveClosure
public meta import Mathlib.Tactic.Linter.Header
public import Mathlib.Tactic.MinImports

/-! # The `minImports` linter

The `minImports` linter incrementally computes the minimal imports needed for each file to build.
Whenever it detects that a new command requires an increase in the (transitive) imports that it
computed so far, it emits a warning mentioning the bigger minimal imports.

Unlike the related `#min_imports` command, the linter takes into account notation and tactic
information.
It also works incrementally, accumulating increasing import information.
This is better suited, for instance, to split files.

The linter is a stateful linter (`Lean.Elab.Command.registerStatefulLinter`). It stores the
cumulative import information in its linter state, and the elaborator threads the state
through the commands of the file.
-/

meta section

open Lean Elab Command Linter

/-!
### The "minImports" linter

The "minImports" linter tracks information about minimal imports over several commands.
-/

namespace Mathlib.Linter

/--
`ImportState` is the persistent state of the `minImports` linter.
* `transClosure` is the import graph of the current file.
* `minImports` is the `NameSet` of minimal imports to build the file up to the current command.
* `importSize` is the number of transitive imports to build the file up to the current command.
-/
public structure ImportState where
  /-- The transitive closure of the import graph of the current file. The value is `none` only
  before the linter processes the first command. The linter then sets it to the value for the
  current file. -/
  transClosure : Option (NameMap NameSet) := none
  /-- The minimal imports needed to build the file up to the current command. -/
  minImports   : NameSet := {}
  /-- The number of transitive imports needed to build the file up to the current command. -/
  importSize   : Nat := 0
  deriving Inhabited

-- TODO: we could give `#import_bumps` reset semantics and deprecate `#reset_min_imports`.
/-- `#reset_min_imports` makes the `minImports` linter start again from empty cumulative
imports. -/
-- Only the linter can write the linter state. The elaborator does nothing: the `minImports`
-- linter detects the `resetMinImports` syntax kind and clears its state.
elab (name := resetMinImports) "#reset_min_imports" : command => pure ()

/--
The `minImports` linter incrementally computes the minimal imports needed for each file to build.
Whenever it detects that a new command requires an increase in the (transitive) imports that it
computed so far, it emits a warning mentioning the bigger minimal imports.

Unlike the related `#min_imports` command, the linter takes into account notation and tactic
information.
It also works incrementally, providing information that is better suited, for instance, to split
files.

Another important difference is that the `minImports` *linter* starts counting imports from
where the option is set to `true` *downwards*, whereas the `#min_imports` *command* looks at the
imports needed from the command *upwards*.
-/
public register_option linter.minImports : Bool := {
  defValue := false
  descr := "enable the minImports linter"
}

/-- The `linter.minImports.increases` regulates whether the `minImports` linter reports the
change in number of imports, when it reports import changes.
Setting this option to `false` helps with test stability.
-/
public register_option linter.minImports.increases : Bool := {
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
  ms.foldl (·.append <| tc.getD · default) ms

@[inherit_doc Mathlib.Linter.linter.minImports]
macro "#import_bumps" : command => `(
  -- We emit a message to prevent the `#`-command linter from flagging `#import_bumps`.
  run_cmd logInfo "Counting imports from here."
  set_option linter.minImports true)


@[inherit_doc Mathlib.Linter.linter.minImports]
def minImportsPost (readPrev : PrevStateFn) (stx : Syntax) (self : ImportState) :
    CommandElabM ImportState := do
  -- The reset applies also when the linter option is off. The linter then lints the
  -- `#reset_min_imports` command itself, against the empty state.
  let self := if stx.isOfKind ``resetMinImports then {} else self
  unless getLinterValue linter.minImports (← getLinterOptions) do
    return self
  if (← get).messages.hasErrors then
    return self
  if stx == (← `(command| #import_bumps)) then return self
  if stx == (← `(command| set_option $(mkIdent `linter.minImports) true)) then
    logInfo "Consider using '#import_bumps' instead of setting the linter option: \
            it also logs the position where the import count starts."
    return self
  let env ← getEnv
  -- On the first command that the linter processes, it computes the transitive closure of the
  -- imports of the file.
  let self := if self.transClosure.isNone then
      { self with transClosure := env.importGraph.transitiveClosure }
    else self
  let (importsSoFar, oldCumulImps) := (self.minImports, self.importSize)
  -- when the linter reaches the end of the file or `#exit`, it gives a report
  if #[``Parser.Command.eoi, ``Lean.Parser.Command.exit].contains stx.getKind then
    let explicitImportsInFile : NameSet :=
      .ofArray ((env.imports.map (·.module)).filter (!isInitImport ·))
    let newImps := importsSoFar \ explicitImportsInFile
    let currentlyUnneededImports := explicitImportsInFile \ importsSoFar
    -- `impMods` is the syntax for the modules imported in the current file. The state of the
    -- `header` linter provides it when the header checks ran. Otherwise, we read the current
    -- file and do a custom parsing of the imports: this is a hack to obtain some `Syntax`
    -- information for the `import X` commands.
    let headerStx := (readPrev Style.header.headerLinter).headerSyntax
    let impMods ← if headerStx.isMissing then do
        let fname ← getFileName
        let contents ← IO.FS.readFile fname
        let (impMods, _) ← Parser.parseHeader (Parser.mkInputContext contents fname)
        pure impMods.raw
      else
        pure headerStx
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
    return self
  let id ← getId stx
  let newImports := (getIrredundantImports env (← getAllImports stx id)).filter (!isInitImport ·)
  let tot := (newImports.append importsSoFar)
  let redundant := env.findRedundantImports tot.toArray
  let currImports := tot \ redundant
  let currImpArray := currImports.toArray.qsort Name.lt
  if currImpArray != #[] &&
     currImpArray ≠ importsSoFar.toArray.qsort Name.lt then
    let newCumulImps := -- We should always be in the situation where `getD` finds something
      (importsBelow (self.transClosure.getD env.importGraph.transitiveClosure) tot).size
    let new := currImpArray.filter (!importsSoFar.contains ·)
    let redundant := importsSoFar.toArray.filter (!currImports.contains ·)
    -- to make `test` files more stable, we suppress the exact count of import changes if
    -- the `linter.minImports.increases` option is `false`
    let byCount :=  if getLinterValue linter.minImports.increases (← getLinterOptions) then
                    m!"by {newCumulImps - oldCumulImps} "
                  else
                    m!""
    Linter.logLint linter.minImports stx <|
      m!"Imports increased {byCount}to\n{currImpArray}\n\n\
        New imports: {new}\n" ++
          if redundant.isEmpty then m!"" else m!"\nNow redundant: {redundant}\n"
    return { self with minImports := currImports, importSize := newCumulImps }
  return self

/--
The typed handle of the `minImports` linter. Other stateful linters can read the previous
`ImportState` of the linter through this handle.
-/
public initialize minImportsLinter : StatefulLinter ImportState Unit ←
  registerStatefulLinter {}
    (post := fun stx self _ readPrev _ => withSetOptionIn' (minImportsPost readPrev · self) stx)

end MinImports

end Mathlib.Linter
