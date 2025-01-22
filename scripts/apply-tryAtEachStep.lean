/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Cli.Basic
import Mathlib.Data.Nat.Notation

/-!
# Apply results of `tryAtEachStep` automatically

`lake exe apply-tryAtEachStep results.json`
simplest case, see docstring

`lake exe apply-tryAtEachStep --only Geometry/Manifolds Analysis Topology/Compactness results.json`
only apply changes to the respective directories (errors if these don't exist)

`lake exe apply-tryAtEachStep --files 10 results.json`
will only apply changes to the first 10 files.

This is a prototype, to be refined! TODO: add better docs :-)

-/

open Cli System.FilePath

open Lean

-- copy-pasted from batteries' `runLinter`
/-- Read the given file path and deserialize it as JSON. -/
def readJsonFile (α) [FromJson α] (path : System.FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

-- copy-pasted from batteries' runLinter
/-- Serialize the given value `a : α` to the file as JSON. -/
def writeJsonFile (α) [ToJson α] (path : System.FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty.push '\n'

-- Format of an entry in a tryAtEachStep-generated results file.
structure SuggestedChange where
  startLine: ℕ
  startCol: ℕ
  proofTermLengthReduction: ℕ
  parentName: String -- or a Name? ": "SetTheory.Game.small_setOf_birthday_lt",
  oldText: String -- "let S := ⋃ a ∈ Set.Iio o, {x : Game.{u} | birthday x < a}",
  newText: String
  message: String
  lengthReduction: ℕ -- of the text file, in bytes?
  goalIsProp: Bool
  -- e.g. "/home/dwrensha/src/compfiles/.lake/packages/mathlib/Mathlib/SetTheory/Game/Birthday.lean"
  -- XXX: should this be a path instead?
  filepath: String
  fewerSteps: Bool
deriving FromJson, ToJson


/-- Implementation of the `apply-tryAtEachStep` command line program. -/
def applyTryAtEachStepCli (args : Cli.Parsed) : IO UInt32 := do
  let resultsFileName := args.positionalArg! "resultsFile" |>.value
  -- let onlyDirectories := args.flag? "only" |>.map (·.value)
  -- FIXME: parse from the CLI args!
  let maximum : Option ℕ := none

  let path := System.mkFilePath (resultsFileName.split (System.FilePath.pathSeparators.contains ·))
  let changes ← readJsonFile (Array SuggestedChange) path
  let mut changesSoFar := 0
  for change in changes do
    if let some max := maximum then
      if changesSoFar >= max then break
    -- Sanity-check: the file at the given location should have the oldText.
    let path := System.mkFilePath (change.filepath.split (System.FilePath.pathSeparators.contains ·))
    let lines ← IO.FS.lines path
    match lines.get? change.startLine with
    | none => IO.println s!"warning: file {path} does not have a line {change.startLine}; ignoring\
      The results file must match the version of this project that you ran tryAtEachStep on!"
    | some line =>
      if line.length < change.startCol then
        IO.println s!"warning: file {path} at line {change.startLine} is shorter than {change.startCol} columns; ignoring
        The results file must match the version of this project that you ran tryAtEachStep on!"
      -- split line into before, current and next!

      --let currentText := line.split[change.startCol:]
        -- read the file and

    changesSoFar := changesSoFar + 1

  return 0

/-- Setting up command line options and help text for `lake exe apply-tryAtEachStep`. -/
-- so far, no help options or so: perhaps that is fine?
def apply_tryAtEachStep : Cmd := `[Cli|
  «apply-tryAtEachStep» VIA applyTryAtEachStepCli; ["0.0.1"]
  "Parse a `results.json` file obtained from running the `tryAtEachStep` tool on this project,
  and try to apply all proposed changes to the current working tree.

  This assumes the working tree matches the mathlib4 copy this was obtained from."

  -- FLAGS:
  --   only : Array String;  "Only apply changes to the following directories"
  --   files : Nat;  "Maximal number of files to which apply changes"

  ARGS:
    resultsFile: String; "Name of the .json file with the tool's results, e.g. results.json"

]

/-- The entry point to the `lake exe apply-tryAtEachStep` command. -/
def main (args : List String) : IO UInt32 := do apply_tryAtEachStep.validate args
