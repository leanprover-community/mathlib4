/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Cli.Basic
import Batteries.Tactic.Lint
import Batteries.Data.String.Matcher
import Lean.Elab.ParseImportsFast

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

/-- Implementation of the `apply-tryAtEachStep` command line program. -/
def applyTryAtEachStepCli (_args : Cli.Parsed) : IO UInt32 := do
  return 0

/-- Setting up command line options and help text for `lake exe apply-tryAtEachStep`. -/
-- so far, no help options or so: perhaps that is fine?
def apply_tryAtEachStep : Cmd := `[Cli|
  «apply-tryAtEachStep» VIA applyTryAtEachStepCli; ["0.0.1"]
  "Parse a `results.json` file obtained from running the `tryAtEachStep` tool on this project,
  and try to apply all proposed changes to the current working tree.

  This assumes the working tree matches the mathlib4 copy this was obtained from."

  FLAGS:
    only : Array String;  "Only apply changes to the following directories"
    files : Nat;  "Maximal number of files to which apply changes"

  ARGS:
    resultsFile: String; "Name of the .json file with the tool's results, e.g. results.json"

]

/-- The entry point to the `lake exe apply-tryAtEachStep` command. -/
def main (args : List String) : IO UInt32 := do apply_tryAtEachStep.validate args
